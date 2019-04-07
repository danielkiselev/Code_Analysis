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
dDictGlobal = {}
class BlockFrame(object):
    def __init__(self, block, blockId):
        global dDictGlobal
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
        self.defToVar = {}
        self.dDict = {}
        for i in block.instructions:
            defType = None
            if i[0] == "d":
                defBuilder = "d"
                for c in range(1, len(i)):
                    if i[c].isdigit():
                        defBuilder += i[c]
                    else:
                        if len(defBuilder) > 1:
                            defType = defBuilder
                        break
            if defType is not None:
                self.dDict[defType] = i[len(defType): len(i)-2]
                dDictGlobal[defType] = i[len(defType): len(i)-2]

    def addIn(self):
        global frameDict
        for x in self.conId:
            preOutData = frameDict[x].outData.copy()
            if preOutData is not None:
                for i in preOutData:
                    if self.inData.__contains__(i):
                        continue
                    self.inData.append(i)

    def killCheck(self):
        global killerVarDict
        for g in self.genData:
            if killerVarDict.__contains__(self.defToVar[g]):
                for affected in killerVarDict[self.defToVar[g]]:
                    if self.dDict.__contains__(affected):
                        continue
                    else:
                        self.killData.append(affected)
        print("killer: ",self.id, self.killData)

    def createOutData(self):
        leftOver = list(set(self.inData) - set(self.killData))
        self.outData = list(set(self.genData + leftOver))

    def printData(self):
        print(" ")
        print (self.id)
        print ("inData", self.inData)
        print ("killData", self.killData)
        print ("genData", self.genData)
        print ("outData", self.outData)
    def setFacts(self, analysisObject):
        global dDictGlobal
        oldGenData = self.genData.copy()
        for i in range(0, len(oldGenData )):
            self.genData[i]+= self.dDict[oldGenData [i]]
        oldKillData = self.killData.copy()
        for i in range(0, len(oldKillData )):
            self.killData[i]+= dDictGlobal[oldKillData [i]]
        if self.id == "ENTRY":
            analysisObject.add_node_facts(self.id, "IN",self.inData)
            analysisObject.add_node_facts(self.id, "OUT", self.outData)
        else:
            analysisObject.add_node_facts(self.id, "IN",self.inData)
            analysisObject.add_node_facts(self.id, "GEN", self.genData)
            analysisObject.add_node_facts(self.id, "KILL", self.killData)
            analysisObject.add_node_facts(self.id, "OUT", self.outData)

#x.add_node_facts("B001", "GEN", ["x"])



def main():
    inputfileName = sys.argv[1]
    outputFileName = sys.argv[2]
    x = a02output.A02Output()
    x.readCode(inputfileName, 4)
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
        frameDict1[k].killCheck()
        frameDict1[k].addIn()
        frameDict1[k].createOutData()
    for fB in framedBlocks:
        fB.printData()
    for fB in framedBlocks:
        fB.setFacts(x)
    x.write(outputFileName)
    for fB in framedBlocks:
        fB.printData()


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

killerVarDict = {}

def processBlock(currFramedBlock):
    global killerVarDict
    currB = currFramedBlock.block
    genDict = {}# defined var -> expr  #generate
    usedVar = {}  # var from expr -> key of effected experDict
    killedDict = {}
    killed = []
    defToVar = {}
    localKillerVarDict = {}
    for x in range(0,len(currB.instructions)):
        i = currB.instructions[x]
        defType = None
        if i[0] == "d":
            defBuilder = "d"
            for c in range(1,len(i)):
                check = str(i[c])
                if check.isdigit():
                    defBuilder+=i[c]
                else:
                    if len(defBuilder)>1:
                        defType = defBuilder
                    break
        preAssign = ""
        postAssign = []  # varId, lines
        usageCase = False
        oper = ""
        StringBuilder = ""
        procIf = False
        if defType is None:
            continue
        for index in range(len(defType),len(i)):
            c = i[index]
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
                            preAssign += (StringBuilder)
                    else:
                        procDigit = True
                        for s in StringBuilder:
                            if not s.isdigit():
                                procDigit = False
                                break
                        if procDigit:
                            postAssign.append(StringBuilder)
                elif ((c is not '\n' and c is not ";") and usageCase and proc and len(postAssign)>0):
                    oper+=c
                StringBuilder = ""
            else:
                StringBuilder+=c
        if procIf:
            continue
        if usageCase:
            print(currFramedBlock.id, "gen", preAssign, postAssign, oper)
            temp = []
            if killerVarDict.__contains__(preAssign):
                temp = killerVarDict[preAssign]
            temp.append(defType)
            killerVarDict[preAssign] = temp
            if genDict.__contains__(preAssign):
                temp1 = []
                if localKillerVarDict.__contains__(preAssign):
                    temp1 = localKillerVarDict[preAssign]
                    if not temp1.__contains__(defType):
                        temp1.append(defType)
                if not temp1.__contains__(genDict[preAssign]):
                    temp1.append(defType)
                localKillerVarDict[preAssign] = temp1
            genDict[preAssign] = defType
            defToVar[defType] = preAssign
        else:
            continue
    currFramedBlock.killData = list(killedDict.keys())
    currFramedBlock.genData = list(genDict.values())
    currFramedBlock.useVar = killedDict
    currFramedBlock.defVar = genDict
    currFramedBlock.defToVar = defToVar
    print(currFramedBlock.id, "local gen", currFramedBlock.genData)
    print(currFramedBlock.id, "local kill", currFramedBlock.killData)
    return currFramedBlock










if __name__ == "__main__":
    main()