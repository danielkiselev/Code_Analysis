#!/usr/bin/env python3
import sys
import pycparser
import a02output
'''
Gen[s]The set of variables that are used in s before any assignment.
Kill[s] The set of variables that are assigned a value in s (in many books[clarification needed], 
KILL (s) is also defined as the set of variables assigned a value in s before any use, but this does not change the solution of the dataflow equation):

'''

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

    def addOut(self, childBlock):
        if childBlock is not None:
            exterList = childBlock.inData
            locList = self.outData
            exterSet = set(exterList)
            locSet = set(locList)
            missingSet = exterSet - locSet
            self.outData = locList + list(missingSet)
    def createInData(self):
        locDef = []
        locUse = []
        for k in self.defVar.keys():
            locDef.append(k)
        for k in self.useVar.keys():
            locUse.append(k)
        self.genData = locUse
        self.killData = locDef
        outSet = set(self.inData)
        defSet = set(locDef)
        remainingSet = outSet-defSet
        exterSet = set(remainingSet)
        locSet = set(locUse)
        missingSet = exterSet - locSet
        self.inData = locUse + list(missingSet)
    def printData(self):
        print(" ")
        print (self.id)
        print ("inData", self.inData)
        print ("definedVar", self.killData)
        print ("usageVar", self.genData)
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

def main():
    inputfileName = sys.argv[1]
    outputFileName = sys.argv[2]
    x = a02output.A02Output()
    x.readCode(inputfileName,2)
    blockObjs = x.blockSetObj
    framedBlocks = setFrameBlocks(blockObjs)
    framedDict = {}
    for fB in framedBlocks:
        if type(fB.block) == str:
            framedDict[fB.block] = fB
        else:
            framedDict[fB.block.id] = fB
    framedBlocks[0] = trav(framedBlocks[0], framedDict)
    for fB in framedBlocks:
        fB.printData()
    for fB in framedBlocks:
        fB.setFacts(x)
    x.write(outputFileName)
    for fB in framedBlocks:
        fB.printData()


def setFrameBlocks(blockObjs):
    resBlocks = []
    for b in blockObjs:
        bf = None
        if type(b) == str:
            bf = BlockFrame(b,b)
        else:
            bf = BlockFrame(b, b.id)
        resBlocks.append(bf)
    return resBlocks

visitedBlocks = {}
def trav(currFramedBlock, framedDict):
    currB = currFramedBlock.block
    global visitedBlocks
    visitedBlocks[currFramedBlock] = None
    if type(currB) == str:
        return currFramedBlock
    processBlock(currFramedBlock)
    for i in range(0, len(currB.connect)):
        con = currB.connect[i]
        framedCon = None
        if type(con) == str:
            framedCon = framedDict[con]
        else:
            framedCon = framedDict[con.id]
        if visitedBlocks.__contains__(framedCon):
            continue
        currFramedBlock.addOut(trav(framedCon, framedDict))
    currFramedBlock.createInData()
    return currFramedBlock

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


def processBlock(currFramedBlock):
    currB = currFramedBlock.block
    definedVar = {} #varId, lines
    useVar = {} #varId, lines
    for x in range(0,len(currB.instructions)):
        i = currB.instructions[x]
        preAssign = []
        usageCase = False
        StringBuilder = ""
        for c in i:
            if not c.isalnum():
                if c == "=":
                    usageCase = True
                if len(StringBuilder)>0:
                    if StringBuilder[0] == "t":
                        if usageCase:
                            temp = []
                            if useVar.__contains__(StringBuilder):
                                temp = useVar[StringBuilder]
                            temp.append(x)
                            useVar[StringBuilder] = temp
                        else:
                            preAssign.append(StringBuilder)
                StringBuilder = ""
            else:
                StringBuilder+=c
        if usageCase:
            for pAs in preAssign:
                temp = []
                if definedVar.__contains__(pAs):
                    temp = definedVar[pAs]
                temp.append(x)
                definedVar[pAs] = temp
        else:
            for pAs in preAssign:
                if definedVar.__contains__(pAs):
                    continue
                temp = []
                if useVar.__contains__(pAs):
                    temp = useVar[pAs]
                temp.append(x)
                useVar[pAs] = temp
    currFramedBlock.defVar = definedVar
    currFramedBlock.useVar = useVar











if __name__ == "__main__":
    main()