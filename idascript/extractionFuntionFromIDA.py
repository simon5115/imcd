# -*- coding: utf-8 -*-
"""
Created on Thu Jul  4 08:56:58 2019

@author: 42886
"""

import os



from idaapi import *
from idc import *

from igraph import *

class FunctionGraph:
    Name="FunctionGraph"
    
    def __init__(self,graph):
        self.func_graph = graph
        self.vertexCount = 0
        self.currentVertex = None
        self.lastVertex = None
        self.firstEver = True
        self.debt_count = 0;
        
    def cutCurrent(self):
        if(self.currentVertex != None):
            self.lastVertex = self.currentVertex
            self.currentVertex = None
#            print "CUT"
            
    def addCode2CurrentVertex(self,addr):
        if(self.currentVertex==None):
            self.func_graph.add_vertex()
            self.vertexCount+=1
            self.currentVertex=self.func_graph.vs[self.vertexCount-1]
            self.currentVertex['code']=""
            self.currentVertex['startEA']=int(addr)
            
            self.firstEver=False
            
            created=True
               
        else:
            created = False
        #search delete jump instruction(execlude call) for alignment   
        if GetOpType(addr,0) == o_near and self.func_graph['startEA'] <= GetOperandValue(addr,0) and GetOperandValue(addr,0) < self.func_graph['endEA']:
            self.currentVertex['jumpCodeRelative'] = GetMnem(addr) + " roffset_" + hex(  (addr-(GetOperandValue(addr,0)) + (1 << 32)) % (1 << 32)) + ";"
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
                self.func_graph.add_edge(self.currentVertex,otherEnd)
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



def getFunctions(functions_database):
    
    fileMD5=GetInputFileMD5()
    print (fileMD5)
    total=1
    for segment in Segments():
        
        if(SegName(segment) == ".text"):
            for functionEA in Functions(SegStart(segment),SegEnd(segment)):
                total=total+1
                function_chunks=[]
                #get block form functions
                func_iter = func_tail_iterator_t(idaapi.get_func(functionEA))
                #get func_iter iterator status is valid ?
                status=func_iter.main()
                
                while status:
                    #get block
                    chunk = func_iter.chunk()
                    
                    #stroe start and end address of block as a tuple                   
                    function_chunks.append({'startEA':chunk.startEA,'endEA':chunk.endEA})
                    
                    status = func_iter.next()
                    
                function_chunks.sort(key=lambda x:x['startEA'])
                
                funcgraph=Graph(0,[],True,{'startEA':GetFunctionAttr(functionEA,FUNCATTR_START),
                                                'endEA':GetFunctionAttr(functionEA,FUNCATTR_END),
                                                'name': GetFunctionName(functionEA),
                                                'fileMd5':fileMD5,
                                                'filePath':GetInputFilePath(),
                                                'chunks':function_chunks})
                functions_database.append(funcgraph)
                
               
               
        
    print (total)

# from function to disasm text,where fileCode is with align information and pureCode is true pure code
def prepareInstrctionForFunc(func_database):
    start=func_database['startEA']
    end=func_database['endEA']
    fileCode=""
    pureCode=""
    
    while(start<end):
        fileCode+=GetDisasm(start)+";"
        pureCode+=getOriginalCodeFromAddr(start)
        start=NextHead(start,end)
        
        
        
    func_database['fileCode']= fileCode.replace('"',"'")
    func_database['pureCode']= pureCode.replace('"',"'")
         


    


# creat a CFG for function
def createFuncGraphs(func_database):
    #init graph 
    funcGraph=FunctionGraph(func_database)
    
    for chunk in func_database['chunks']:
        funcstart=chunk['startEA']
        funcend=chunk['endEA']
        
        for addr in Heads(funcstart,funcend):
            if isCode(GetFlags(addr)):
                #treat each line as call 
                refaddr=CodeRefsTo(addr,0)
                refaddr=list(filter(lambda x:x>=funcstart and x<funcend,refaddr))
                
                if((len(refaddr)>=1)):
                    #when get last block ,need to break
                    funcGraph.cutCurrent()
                    created=funcGraph.addCode2CurrentVertex(addr)
                    
                    for ref in refaddr:
                        #connect relation ref->addr->GetOperandValue(head,0)
                        #If flag value is False ,edge is(ref,currentVertex),that is (ret,addr)
                        funcGraph.connectCorrentVertex2Addr(ref,False)
                else:
                    created=funcGraph.addCode2CurrentVertex(addr)
                
                if(created):
                   if(len(list(list(filter(lambda x:x==funcGraph.getLastVertexEndEA(),CodeRefsTo(addr,1)))))) :
                       funcGraph.connectLast2CurrentVertex()
                
                from_refs = CodeRefsFrom(addr, 0)
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
    line = GetMnem(ea)
    #print ea
    op1 = GetOpnd(ea,0)
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
    outputdir="D:\\Datac\\IDAData\\v101"
    
    if os.path.exists(outputdir):
        print ("File exists")
        pass
    else:
        print ("No File exists,now create it")
        os.mkdir(outputdir)
     
    functionPipeLine=[prepareInstrctionForFunc,createFuncGraphs]
    
    #extraction function from file ,and store in functions
    functions=[]
    getFunctions(functions)
    #call prepareInstrctionForFunc  and  createFuncGraphs
    for func in functions:
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
        filenameDsm=func['name'].replace('?','')+".dsm"
        
        f=open(os.path.join(outputdir,filenameDsm),"w")
        f.write(func['pureCode'])
        f.close
    
        if func['vertexCount']>MaxVertex:
            MaxVertex=func['vertexCount']
            g=func
            Name=func['name']
        
        #del filecode and purecode
        copyGraphAttributesToRoot(func)
       
        
        rootNode=func.vs[0]
        # Do BFS of func
        iter=func.bfsiter(rootNode , OUT  ,True)
        
        newFuncGraph = Graph(0,[],True)
        
        #copy graph with exclude information,None :no exclude
        copyIgraphObjectAttributes(func,newFuncGraph,None)
        
        for (node,dist,parent) in iter:
            newFuncGraph.add_vertex()
            currentVertexId = len(newFuncGraph.vs)-1
            currentVertex = newFuncGraph.vs[currentVertexId]
            
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
            newFuncGraph.write_gml(graphFullPath)
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
 
    
    
