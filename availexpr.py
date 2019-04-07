#!/usr/bin/env python3
import sys
import pycparser
import a02output
'''
An expression x + y is available at a point p if every path, from the entry node
to p evaluates x + y, and aft er the last such evaluation prior to reaching p,
there are no subsequent assignments to x or y.For the available-expressions
data-flow schema 

we say that a block kills expression x + y if it assigns (or may
assign) x or y and does not subsequently recompute x + y.

A block generates expression x + y if it definitely evaluates x + y and does not 
subsequently define x or y.

Determine, for each program point, which expressions must already have been computed,
and not later modified, on all paths to theprogram point.
OUT[ENTRY] = 0

OUT[B] = e_genB U (IN[B] - e_killB)

IN[B] = n whereP a predecessor of B  OUT[P] .
'''
frameDict = {}
framedBlockGlobalRes = []
class BlockFrame(object):
    def __init__(self, block, blockId):
        self.id = blockId
        self.block = block
        self.inData = []
        self.outData = []
        self.liveData = []
        self.genData = []
        self.killData = []
        self.defVar = {}
        self.useVar = {}
        self.conId = []
        self.modified = []

    def addIn(self):
        global frameDict
        for x in self.conId:
            preOutData = frameDict[x].outData.copy()
            if preOutData is not None:
                for i in preOutData:
                    if self.inData.__contains__(i):
                        continue
                    self.inData.append(i)

    def createOutData(self):
        locDef = []#gen
        locUse = []#kill
        for k in self.defVar.keys():
            locDef.append(self.defVar[k])
        for k in self.useVar.keys():
            locUse.append(self.useVar[k])
        # print(self.id,"kill", locUse)
        # print(self.id, "gen", locDef)
        self.genData = locDef.copy()
        self.killData = locUse.copy()
        for expression in self.inData.copy():
            print("expr",expression)
            vBuilder = ""
            for v in expression:
                print(expression)
                if not v.isalnum():
                    if len(vBuilder)>0:
                        if vBuilder[0] == "t":
                            print(vBuilder)
                            if self.modified.__contains__(vBuilder):
                                self.killData.append(expression)
                                break
                    vBuilder = ""
                else:
                    vBuilder+=str(v)
        inSet = set(self.inData.copy())
        killSet = set(self.killData.copy())#gen
        #print("mod",self.killData)
        remainingSet = inSet-killSet
        exterSet = set(remainingSet)
        genSet = set(locDef)
        missingSet = exterSet - genSet
        self.outData = locDef + list(missingSet)

    def printData(self):
        print(" ")
        print (self.id)
        print ("inData", self.inData)
        print ("killData", self.killData)
        print ("genData", self.genData)
        print ("outData", self.outData)
    def setFacts(self, analysisObject):
        if self.id == "ENTRY":
            analysisObject.add_node_facts(self.id, "IN",self.inData)
            analysisObject.add_node_facts(self.id, "OUT", self.outData)
        else:
            analysisObject.add_node_facts(self.id, "IN",self.inData)
            analysisObject.add_node_facts(self.id, "GEN", self.genData)
            analysisObject.add_node_facts(self.id, "KILL", self.killData)
            analysisObject.add_node_facts(self.id, "OUT", self.outData)

#x.add_node_facts("B001", "GEN", ["x"])



def start(f1, f2):
    global framedBlockGlobalRes
    inputfileName = f1
    outputFileName = f2
    x = a02output.A02Output()
    x.readCode(inputfileName,3)
    blockObjs = x.blockSetObj
    framedBlocks = setFrameBlocks(blockObjs)
    framedDict = {}
    for fB in framedBlocks:
        if type(fB.block) == str:
            framedDict[fB.block] = fB
        else:
            framedDict[fB.block.id] = fB
    frameDict1 = trav(framedBlocks[0], framedDict).copy()
    for k in frameDict1.keys():
        if k == "ENTRY":
            continue
        frameDict1[k].addIn()
        frameDict1[k].createOutData()
    for fB in framedBlocks:
        fB.printData()
    for fB in framedBlocks:
        fB.setFacts(x)
    x.write(outputFileName)
    for fB in framedBlocks:
        fB.printData()
    return x


def main():
    inputfileName = sys.argv[1]
    outputFileName = sys.argv[2]
    start(inputfileName, outputFileName)

def setFrameBlocks(blockObjs):
    global frameDict
    resBlocks = []
    for b in blockObjs:
        bf = None
        if type(b) == str:
            bf = BlockFrame(b,b)
        else:
            bf = BlockFrame(b, b.id)
        frameDict[bf.id] = bf
        resBlocks.append(bf)
    return resBlocks
'''
OUT[ENTRY] = 0

OUT[B] = e_genB U (IN[B] - e_killB)

IN[B] = n whereP a predecessor of B  OUT[P] .
'''


visitedBlocks = {}
def trav(currFramedBlock, framedDict):
    currB = currFramedBlock.block
    global visitedBlocks
    visitedBlocks[currFramedBlock] = None
    if currB.id == "ENTRY":
        currFramedBlock.outData = []
    else:
        currFramedBlock = processBlock(currFramedBlock)
    for i in range(0, len(currB.connect)):
        con = currB.connect[i]
        framedCon = None
        if type(con) == str:
            framedCon = framedDict[con]
        else:
            framedCon = framedDict[con.id]
        if visitedBlocks.__contains__(framedCon):
            continue
        else:
            trav(framedCon, framedDict)
        framedCon.conId.append(currFramedBlock.id)
    frameDict[currFramedBlock.id] = currFramedBlock
    return frameDict

#
# editedBlocks = {}
# def editConnectsBlocks(currBlock):
#     global visitedEmptyBlocks
#     global editedBlocks
#     editedBlocks[currBlock] = None
#     for i in range(0, len(currBlock.connect)):
#         con = currBlock.connect[i]
#         currBlock.connect[i] = visitedEmptyBlocks[con]
#         if editedBlocks.__contains__(con):
#             continue


'''
we say that a block kills expression x + y if it assigns (or may
assign) x or y and does not subsequently recompute x + y.

A block generates expression x + y if it definitely evaluates x + y and does not 
subsequently define x or y.
'''
def processBlock(currFramedBlock):
    currB = currFramedBlock.block
    exprDict = {}# defined var -> expr  #generate
    usedVar = {}  # var from expr -> key of effected experDict
    killedDict = {}
    modifiedVar = []
    for x in range(0,len(currB.instructions)):
        i = currB.instructions[x]
        preAssign = []
        postAssign = []  # varId, lines
        usageCase = False
        oper = ""
        StringBuilder = ""
        procIf = False
        for c in i:
            proc = True
            if not c.isalnum():
                if StringBuilder == "if":
                    procIf = True
                    break
                if c == "=" and not usageCase:
                    usageCase = True
                    proc = False
                if len(StringBuilder)>0:
                    if StringBuilder[0] == "t":
                        if usageCase:
                            postAssign.append(StringBuilder)
                        else:
                            preAssign.append(StringBuilder)
                elif ((c is not '\n' and c is not ";") and usageCase and proc and len(postAssign)>0):
                    oper+=c
                StringBuilder = ""
            else:
                StringBuilder+=c
        if procIf:
            continue
        if usageCase:
            print(currFramedBlock.id, "gen", preAssign, postAssign, oper)
            if len(preAssign) == 1:
                if not modifiedVar.__contains__(preAssign[0]):
                    modifiedVar.append(preAssign[0])
                    if usedVar.__contains__(preAssign[0]):
                        usedKeys = usedVar[preAssign[0]]
                        for k in usedKeys:
                            if exprDict.__contains__(k):
                                killedDict[exprDict[k]] = exprDict[k]
                                del exprDict[k]
                if len(postAssign) == 2 and len(oper)>0:
                    exprDict[preAssign[0]] = str(postAssign[0]+" "+oper+" "+postAssign[1])
                    print(currFramedBlock.id, "gen", exprDict[preAssign[0]] )
                    if killedDict.__contains__(exprDict[preAssign[0]]):
                        del killedDict[exprDict[preAssign[0]]]
                    temp = []
                    if usedVar.__contains__(postAssign[0]):
                        temp = usedVar[postAssign[0]]
                    temp.append(preAssign[0])
                    usedVar[postAssign[0]] = temp
                    temp1 = []
                    if usedVar.__contains__(postAssign[1]):
                        temp1 = usedVar[postAssign[1]]
                    temp1.append(preAssign[0])
                    usedVar[postAssign[1]] = temp1
                else:
                    continue
        else:
            continue
    # currFramedBlock.killData = killedDict.keys()
    currFramedBlock.useVar = killedDict
    currFramedBlock.defVar = exprDict
    currFramedBlock.modified = modifiedVar
    print(currFramedBlock.id, "gen", currFramedBlock.defVar)
    print(currFramedBlock.id, "kill", currFramedBlock.useVar)
    return currFramedBlock










if __name__ == "__main__":
    main()