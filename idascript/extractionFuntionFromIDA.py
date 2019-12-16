# -*- coding: utf-8 -*-
"""
Created on Thu Jul  4 08:56:58 2019

@author: 42886
"""

import os
from sets import Set
from idaapi import *
from idc import *
from igraph import *
class FunctionGraph:
    Name="FunctionGraph"
    
    def __init__(self,graph):
        self.func_graph = graph       #关于一个个函数的信息
        self.vertexCount = 0            #节点数量
        self.currentVertex = None     #当前节点
        self.lastVertex = None          #最后一个节点
        self.firstEver = True
        self.debt_count = 0;
        
    def cutCurrent(self):
        if(self.currentVertex != None):
            self.lastVertex = self.currentVertex
            self.currentVertex = None
#            print "CUT"
            
    def addCode2CurrentVertex(self,addr):
        if(self.currentVertex==None):
            self.func_graph.add_vertex()   #函数的信息存储在这个列表里    func_graph是一个图类型的  因为我们在创建时使用的Graph函数   因此有add_vertex()方法   给这个图增加一个节点
            self.vertexCount+=1     #节点的数量
            self.currentVertex=self.func_graph.vs[self.vertexCount-1]   #将当前的节点赋值给这个变量  这个是一个节点对象
            self.currentVertex['code']=""       #这个节点的代码初始化为空字符     节点对象
            self.currentVertex['startEA']=int(addr)  #当前节点的开始地址   一个节点表示一个块   节点对象添加属性
            self.firstEver=False
            created=True
               
        else:
            created = False
        #search delete jump instruction(execlude call) for alignment   
        if GetOpType(addr,0) == o_near and self.func_graph['startEA'] <= GetOperandValue(addr,0) and GetOperandValue(addr,0) < self.func_graph['endEA']:
            self.currentVertex['jumpCodeRelative'] = GetMnem(addr) + " roffset_" + hex(  (addr-(GetOperandValue(addr,0)) + (1 << 32)) % (1 << 32)) + ";"   #GetMnem得到addr地址的操作码 GetOperandValue得到操作数
            self.currentVertex['jumpCodeOriginal'] = getOriginalCodeFromAddr(addr)
        else:
            self.currentVertex['code'] += getOriginalCodeFromAddr(addr)
            
        self.currentVertex['endEA'] = int(addr)
        
            
        return created
        
    def getVertexForAddr(self,addr):
        #addr need to between startEA and endEA
        ls = list(self.func_graph.vs.select(lambda x: x['startEA']<=int(addr) and x['endEA']>=int(addr)))
        #make sure we dont have a conflict
        assert (len(ls)<=1)

        if (len(ls)>0):
            #print "found!"
            return ls[0]
        else:
            #print "not found"
            return None
    
    def connectCorrentVertex2Addr(self,addr,fromCurrent):
        #if the addr between startEA and endEA,get a vertex which store addr's code
        assert (self.firstEver==False and self.currentVertex != None)
        otherEnd=self.getVertexForAddr(int(addr))
        if(otherEnd!=None):
            #edge --
            self.debt_count-=1
            if(fromCurrent):
                self.func_graph.add_edge(self.currentVertex,otherEnd)    #给图添加边并且添加权值：g.add_edges([(0,1)])
            else:
                self.func_graph.add_edge(otherEnd,self.currentVertex)
            
        else:
            self.debt_count+=1
        
        
    def getLastVertexEndEA(self):
        if (self.lastVertex != None):
            return self.lastVertex['endEA']
        else:
            return -1  
      
        
    def connectLast2CurrentVertex(self):
         self.func_graph.add_edge(self.lastVertex,self.currentVertex)
        
    
    
    def printNodes(self):
        for item in self.func_graph.vs:
            print ("start=[" +str(item['startEA']) + "] end=[" +str(item['endEA']) + "]"            )
    
    def Checkdebt(self):
#        print " debt==[" + str(self.debt_count) + "]"
        #assert (self.debt_count==0)
        pass
def get_apis(func_addr):
    calls = 0
    apis = []
    flags = get_func_attr(func_addr, FUNCATTR_FLAGS)#GetFunctionFlags(func_addr)
    # ignore library functions
    if flags & FUNC_LIB or flags & FUNC_THUNK:
        return calls, apis
    # list of addresses
    dism_addr = list(FuncItems(func_addr))
    for instr in dism_addr:
        tmp_api_address = ""
        if idaapi.is_call_insn(instr):
            # In theory an API address should only have one xrefs
            # The xrefs approach was used because I could not find how to
            # get the API name by address.
            for xref in XrefsFrom(instr, idaapi.XREF_FAR):
                if xref.to is None:
                    calls += 1
                    continue
                tmp_api_address = xref.to
                break
            # get next instr since api address could not be found
            if tmp_api_address == "":
                calls += 1
                continue
            api_flags = get_func_attr(tmp_api_address, FUNCATTR_FLAGS)#GetFunctionFlags(tmp_api_address)
            # check for lib code (api)
            if api_flags & idaapi.FUNC_LIB == True or api_flags & idaapi.FUNC_THUNK:
                tmp_api_name = get_name(tmp_api_address, ida_name.GN_VISIBLE | calc_gtn_flags(0, tmp_api_address)) #NameEx(0, tmp_api_address)
                if tmp_api_name:
                    apis.append(tmp_api_name)
            else:
                calls += 1
    return calls, apis

def getFunctions(functions_database):
    
    fileMD5=GetInputFileMD5()   #返回 IDA 加载的二进制文件的 MD5 值，通过这个值能够判断一个文件的不同版本是否 有改变。
    print (fileMD5)    #输出md5值
    total=1  #函数的个数
    callees=dict()
    call=list()
    for segment in Segments():    #返回目标程序中的所有段的开始地址
        
        if(SegName(segment) == ".text"):     #通过段内的某个地址，获得段名     这个循环的作用得到代码段里的所有的函数
            for functionEA in Functions(SegStart(segment),SegEnd(segment)):    #通过段内的某个地址，获得段尾的地址。通过段内的某个地址，获得段头的地址。返回一个列表，包含了从 StartAddress 到 EndAddress 之间的所有函数
                total=total+1
                function_chunks=[]    #存储每个块的信息
                #get block form functions
                func_iter = func_tail_iterator_t(idaapi.get_func(functionEA))   #利用 idaapi.get_func(ea)这个函数来获取函数的边界地址(起始和结束地址)    #创建迭代器
                #get func_iter iterator status is valid ?
                api = get_apis(functionEA)[1]

                for ref_ea in CodeRefsTo(functionEA, 0):
                    # Get the name of the referring function
                    caller_name = get_func_name(ref_ea)#GetFunctionName(ref_ea)
                    print ("--->"+caller_name+"+++")
                    # Add the current function to the list of functions
                    # called by the referring function
                    callees[caller_name] = callees.get(caller_name, Set())
                    callees[caller_name].add(functionEA)

                f_name = get_func_name(functionEA)
                if callees.has_key(f_name):
                    for calling in callees[f_name]:
                        call.append(calling)
                
                status=func_iter.main()    #迭代器
                
                while status:
                    #get block
                    chunk = func_iter.chunk()    #函数中的一个块
                    
                    #stroe start and end address of block as a tuple                   
                    function_chunks.append({'startEA':chunk.startEA,'endEA':chunk.endEA})  #把每个块的开始和结束地址放入function_chunks中
                    
                    status = func_iter.next()     #迭代器   迭代块
                    
                function_chunks.sort(key=lambda x:x['startEA'])
                
                funcgraph=Graph(0,[],True,{'startEA':GetFunctionAttr(functionEA,FUNCATTR_START),
                                                'endEA':GetFunctionAttr(functionEA,FUNCATTR_END),
                                                'name': GetFunctionName(functionEA),
                                                'fileMd5':fileMD5,
                                                'filePath':GetInputFilePath(),
                                                'api':api,
                                                'call':call,
                                                'chunks':function_chunks})
                functions_database.append(funcgraph)    #将一个函数的开始地址结束地址名字md5和路径和块的开始和结束地址增加到functions_database中
                
               
               
        
    print (total)

# from function to disasm text,where fileCode is with align information and pureCode is true pure code
def prepareInstrctionForFunc(func_database):    #func_database是存储一个函数的各种信息
    start=func_database['startEA']   #一个函数的开始地址
    end=func_database['endEA']      #一个函数的结束地址
    fileCode=""
    pureCode=""
    
    while(start<end):
        fileCode+=GetDisasm(start)+";"  #得到addr的反汇编语句
        pureCode+=getOriginalCodeFromAddr(start)
        start=NextHead(start,end)
        
        
        
    func_database['fileCode']= fileCode.replace('"',"'")    #将汇编指令加入其中
    func_database['pureCode']= pureCode.replace('"',"'")



# creat a CFG for function
def createFuncGraphs(func_database):        #传递的是每个函数的信息
    #init graph 
    funcGraph=FunctionGraph(func_database)  #创建一个对对象
    
    for chunk in func_database['chunks']:     #遍历一个函数的块的开始和结束地址
        funcstart=chunk['startEA']              #一个块的开始地址
        funcend=chunk['endEA']                  #一个块的结束地址
        
        for addr in Heads(funcstart,funcend):     #Heads得到两个地址之间所有的元素的地址
            if isCode(GetFlags(addr)):
                #treat each line as call 
                refaddr=CodeRefsTo(addr,0)   #返回一个列表，告诉我们 Address 处代码被什么地方引用了，Flow 告诉 IDAPython 是否要 跟踪这些代码。
                refaddr=list(filter(lambda x:x>=funcstart and x<funcend,refaddr))   #得到在函数开始和结束中间的所有的引用
                
                if((len(refaddr)>=1)):
                    #when get last block ,need to break
                    funcGraph.cutCurrent()
                    created=funcGraph.addCode2CurrentVertex(addr)    #addr表示每条指令的地址
                    
                    for ref in refaddr:
                        #connect relation ref->addr->GetOperandValue(head,0)
                        #If flag value is False ,edge is(ref,currentVertex),that is (ret,addr)
                        funcGraph.connectCorrentVertex2Addr(ref,False)
                else:
                    created=funcGraph.addCode2CurrentVertex(addr)
                
                if(created):
                   if(len(list(list(filter(lambda x:x==funcGraph.getLastVertexEndEA(),CodeRefsTo(addr,1)))))) :
                       funcGraph.connectLast2CurrentVertex()
                
                from_refs = CodeRefsFrom(addr, 0)   #返回一个列表，告诉我们 Address 地址上的代码引用何处的代码。
                from_refs = list(filter(lambda x: x>=funcstart and x<funcend, from_refs))
    
    
                if ((len(from_refs) >= 1)):
                    for ref in from_refs:
                        #If flag value is True ,edge is (currentVertex,ref)
                        funcGraph.connectCorrentVertex2Addr(ref,True)
                    funcGraph.cutCurrent()
    

                  
        

    funcGraph.Checkdebt()

    func_database['vertexCount'] = funcGraph.vertexCount 
                
#ida adds comments that we dont want for the compare...
def getOriginalCodeFromAddr(ea):
    line = GetMnem(ea)   #得到addr地址的操作码
    #print ea
    op1 = GetOpnd(ea,0) #第一个参数是地址，第二个long n是操作数索引。第一个操作数是0和第二个是1。
    op2 = GetOpnd(ea,1)

    if op1 != "":
        line += " " + op1
        if op2 != "":
            line += "," + op2
    line += ";"
#    print line
    return line   

# this will copy the graph attributes to the first vertex to bypass the bug with loading graph attributes
def copyGraphAttributesToRoot(g):
    #RLS!!    #print g.attributes()
    cleanUpGraph(g)
    #for v in g.vs:    #    cleanUpObject(v)    #END OF RLS

def copyIgraphObjectAttributes(srcObj,dstObj,excludeList):
    for attrib in srcObj.attributes():
        if excludeList != None and excludeList.count(attrib) == 0:
            dstObj[attrib] = srcObj[attrib]

def copyGraphAtributesFromRoot(g):
    for attrib in g.vs[0].attributes():
        #pass
        #print str(attrib) + str(g[attrib])
        if (attrib.find(graphAttribPrefix)==0):
            g[attrib.replace(graphAttribPrefix,'')] = g.vs[0][attrib]
            g.vs[0][attrib] = None
            del g.vs[0][attrib]

        #del g[attrib]

# this will remove all the things we dont need from the graph..(so they could be garbge collected)
def cleanUpGraph(obj):
    obj['fileCode']=""
    del obj['fileCode']
    obj['pureCode'] = ""
    del obj['pureCode']
    
def doIt():
    idaapi.autoWait()
    outputdir="D:\\Datac\\IDAData\\v102"
    
    if os.path.exists(outputdir):    #创建一个目录
        print ("File exists")
        pass
    else:
        print ("No File exists,now create it")
        os.mkdir(outputdir)
     
    functionPipeLine=[prepareInstrctionForFunc,createFuncGraphs]
    
    #extraction function from file ,and store in functions
    functions=[]
    getFunctions(functions)     #functions的每个元素为一个函数的各种信息
    #call prepareInstrctionForFunc  and  createFuncGraphs
    for func in functions:    #func是存储一个函数的信息
        for pipelinestage in functionPipeLine:
            pipelinestage(func)
            
    
    MaxVertex=1
    g=None
    Name=""
    counter=0

    
    excludedList=list()
    excludedList.append("TwinID")
    
    for func in functions:
        filenameGml=func['name'].replace('?','')+".gml"
        filenameDsm=func['name'].replace('?','')+".dsm"   #为后面创建文件时起名做准备

        filenameCallApi=func['name'].replace('?','')+".txt"
        f=open(os.path.join(outputdir,filenameDsm),"w")     #创建文件
        f.write(func['pureCode'])       #将每个函数的指令写入文件
        f.close
        f=open(os.path.join(outputdir,filenameCallApi),"w")     #创建文件 
        f.write("api:\n")
        for i in func['api']:
            f.write(str(i)+'\n')
        f.write("call:\n")
        for i in func['call']:
            f.write(str(hex(i))+'\n')
        f.close
    
        if func['vertexCount']>MaxVertex:
            MaxVertex=func['vertexCount']
            g=func
            Name=func['name']
        
        #del filecode and purecode
        copyGraphAttributesToRoot(func)
       
        
        rootNode=func.vs[0]
        # Do BFS of func
        iter=func.bfsiter(rootNode , OUT  ,True)    #图遍历
        
        newFuncGraph = Graph(0,[],True)   #创建一个新图
        
        #copy graph with exclude information,None :no exclude
        copyIgraphObjectAttributes(func,newFuncGraph,None)      #将func图属性复制到新图
        
        for (node,dist,parent) in iter:            #
            newFuncGraph.add_vertex()    #给这个图添加节点
            currentVertexId = len(newFuncGraph.vs)-1
            currentVertex = newFuncGraph.vs[currentVertexId]    #获取当前节点    对象
            
            copyIgraphObjectAttributes(node,currentVertex,excludedList)
            currentVertex['id'] = currentVertexId
            node['twinID'] = currentVertexId
            
            if (parent != None):
                newFuncGraph.add_edge(parent['twinID'],currentVertexId)

            MakeComm(currentVertex['startEA'],"NODEID=" + str(currentVertexId))

        #in the second pass we will set the nodes entry and exit nodes
        
        newRootNode = newFuncGraph.vs[0]
        newIter = newFuncGraph.bfsiter(newRootNode,OUT,False)
        
        for node in newIter:
            node['outNodes'] = "<" + ",".join(map(lambda x:str(x['id']), node.neighbors(OUT))) + ">"
            node['inNodes'] = "<" + ",".join(map(lambda x:str(x['id']), node.neighbors(IN))) + ">"


        graphFullPath = os.path.join(outputdir,filenameGml)

        if (not (os.path.exists(graphFullPath))):
            newFuncGraph.write_gml(graphFullPath)     #写入文件
            #print counter
            counter+=1

            # if counter==500:
            #     break
        else:
            print ("Not re-writing - " + func['name'] + " (in - " + graphFullPath + ")")

    if counter<500:
        print ("max - " + str(MaxVertex) + " name=" + Name)
    else:
        print ("partial result, run again (igraph bug, cannot load too many files..")
        raise "hell"
        Exit(1)

if __name__ == '__main__':
    doIt()
 
    
    

"""
2）用graph对象可对图中的节点和边进行增删改查，添加属性，如：

g.vs["name"] = ["Alice", "Bob", "Claire", "Dennis", "Esther", "Frank", "George"]

g.vs为节点对象序列，上面这一句是给节点添加“name”属性并赋值


给图添加边并且添加权值：g.add_edges([(0,1)])


add_vertex(Graph).
增加节点
"""