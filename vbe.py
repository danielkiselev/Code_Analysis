#!/usr/bin/env python3
import sys
import pycparser
import a02output
import copy
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
# frameDict = {}
dDictGlobal = {}
framedBlockGlobalRes = []
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
        self.anticipated = {}
        self.localKillerVarDict = {}
        self.exprDict = {}
        self.externalAnticipated = {}
        self.internalAnticipated = []
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

    def addIn(self, framedDict):
        for x in self.conId:
            preOutData = framedDict[x].outData.copy()
            if preOutData is not None:
                for i in preOutData:
                    if self.inData.__contains__(i):
                        continue
                    self.inData.append(i)


    def addOut(self, childBlock):
        childAnti = childBlock.anticipated.copy()
        if self.id =="ENTRY":
            return
        for key in self.exprDict:
            if childBlock.localKillerVarDict.__contains__(key):
                for toCheck in childBlock.localKillerVarDict[key]:
                    if childAnti.__contains__(toCheck):
                        if self.genData.__contains__(toCheck):
                            continue
                        else:
                            self.killData.append(toCheck)
                            del childAnti[toCheck]
        for key in childAnti:
            self.anticipated[key] = childAnti[key]
        print("anti", self.anticipated)

    def killCheck(self):
        toKill = list(set(self.genData) - set(self.outData))
        self.killData = list(set(self.killData) |set(toKill))


    def createOutData(self, childBlock):
        print("arrived")
        merge = list(set(self.inData + self.genData))
        extAnti = list(childBlock.anticipated.copy())
        leftOver = list(set(merge) & set(extAnti))
        self.outData = list(set(self.outData) | set(leftOver))


        for gD in self.genData:
            for eA in extAnti:
                if gD == eA:
                    self.internalAnticipated.append(gD)


    def addIn(self, frameDict1):
        for cId in self.conId:
            frameCon = frameDict1[cId]
            for externalOut in frameCon.outData:
                self.inData.append(externalOut)

    def printData(self):
        print(" ")
        print (self.id)
        print ("inData", self.inData)
        print ("killData", self.killData)
        print ("genData", self.genData)
        print ("outData", self.outData)

    def setFacts(self, analysisObject):
        # global dDictGlobal
        # oldGenData = self.genData.copy()
        # for i in range(0, len(oldGenData )):
        #     self.genData[i]+= self.dDict[oldGenData [i]]
        # oldKillData = self.killData.copy()
        # for i in range(0, len(oldKillData )):
        #     self.killData[i]+= dDictGlobal[oldKillData [i]]
        if self.id == "ENTRY":
            analysisObject.add_node_facts(self.id, "IN",self.inData)
            analysisObject.add_node_facts(self.id, "OUT", self.outData)
        else:
            analysisObject.add_node_facts(self.id, "IN",self.inData)
            analysisObject.add_node_facts(self.id, "GEN", self.genData)
            analysisObject.add_node_facts(self.id, "KILL", self.killData)
            analysisObject.add_node_facts(self.id, "OUT", self.outData)

#x.add_node_facts("B001", "GEN", ["x"])


def iteration(frameDict, framedBlocks):
    proc = True
    currentBlocks = copy.deepcopy(framedBlocks)
    currentDict = copy.deepcopy(frameDict)
    while (proc):
        resDict = copy.deepcopy(trav(currentDict["ENTRY"], currentDict))
        resDict1 = copy.deepcopy(trav1(resDict["ENTRY"], resDict))
        proc = checkChange(currentBlocks,currentDict, resDict1)
        currentDict = copy.deepcopy(resDict1)
        if proc:
            global visitedBlocks
            visitedBlocks = {}
            temp=[]
            for k in resDict1.keys():
                temp.append(resDict1[k])
            currentBlocks = copy.deepcopy(temp)
    return currentDict


def checkChange(currentBlocks,currentDict, resDict):
    for cB in currentBlocks:
        resBlock = resDict[cB.id]
        if resBlock.inData == cB.inData:
            print("pass")
        else:
            print("Fail", resBlock.inData)
            return True
        if resBlock.outData == cB.outData:
            print("pass")
        else:
            print("Fail", resBlock.outData)
            return True
        if resBlock.genData == cB.genData:
            print("pass")
        else:
            print("Fail", resBlock.genData)
            return True
        if resBlock.killData == cB.killData:
            print("pass")
        else:
            print("Fail", resBlock.killData)
            return True
    return False


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

def start(f1,f2):
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
    resDict = iteration(copy.deepcopy(framedDict), copy.deepcopy(framedBlocks))
    framedBlocksRes = []
    for k in resDict.keys():
        framedBlocksRes.append(resDict[k])
    for fB in framedBlocksRes:
        fB.printData()
    for fB in framedBlocksRes:
        fB.setFacts(x)
    x.write(outputFileName)
    for fB in framedBlocksRes:
        fB.printData()
    return x


def main():
    inputfileName = sys.argv[1]
    outputFileName = sys.argv[2]
    x = start(inputfileName, outputFileName)


'''
OUT[ENTRY] = 0

OUT[B] = e_genB U (IN[B] - e_killB)

IN[B] = n whereP a predecessor of B  OUT[P] .
'''

# framedDict ={}
# visitedBlocks = {}
# def trav(currFramedBlock):
#     global framedDict
#     currB = currFramedBlock.block
#     global visitedBlocks
#     visitedBlocks[currFramedBlock] = None
#     if currB.id == "ENTRY":
#         currFramedBlock.outData = []
#     else:
#         currFramedBlock = processBlock(currFramedBlock)
#     for i in range(0, len(currB.connect)):
#         con = currB.connect[i]
#         framedCon = None
#         if type(con) == str:
#             framedCon = framedDict[con]
#         else:
#             framedCon = framedDict[con.id]
#         if visitedBlocks.__contains__(framedCon):
#             currFramedBlock.addOut(framedCon)
#         else:
#             framedCon = trav(framedCon)
#             currFramedBlock.addOut(framedCon)
#     frameDict[currFramedBlock.id] = currFramedBlock
#     return currFramedBlock

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
        framedCon.conId.append(currFramedBlock.id)
        if visitedBlocks.__contains__(framedCon):
            continue
        else:
            framedDict = trav(framedCon, framedDict)
    for i in range(0, len(currB.connect)):
        con = currB.connect[i]
        framedCon = None
        if type(con) == str:
            framedCon = framedDict[con]
        else:
            framedCon = framedDict[con.id]
        currFramedBlock.addOut(framedCon)
    framedDict[currFramedBlock.id] = currFramedBlock
    return framedDict

visitedBlocks1 = {}
def trav1(currFramedBlock, framedDict):
    currB = currFramedBlock.block
    global visitedBlocks1
    visitedBlocks1[currFramedBlock] = None
    if currB.id == "ENTRY":
        currFramedBlock.outData = []
    for i in range(0, len(currB.connect)):
        con = currB.connect[i]
        framedCon = None
        if type(con) == str:
            framedCon = framedDict[con]
        else:
            framedCon = framedDict[con.id]
        currFramedBlock.createOutData(framedCon)
    for i in range(0, len(currB.connect)):
        con = currB.connect[i]
        framedCon = None
        if type(con) == str:
            framedCon = framedDict[con]
        else:
            framedCon = framedDict[con.id]
        framedCon.inData = currFramedBlock.outData
        if visitedBlocks1.__contains__(framedCon):
            continue
        else:
            framedDict = trav1(framedCon, framedDict)
    framedDict[currFramedBlock.id] = currFramedBlock
    return framedDict


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
    exprDict = {}
    localKillerVarDict = {}
    for x in range(0,len(currB.instructions)):
        i = currB.instructions[x]
        preAssign = ""
        postAssign = []  # varId, lines
        usageCase = False
        oper = ""
        StringBuilder = ""
        procIf = False
        for index in range(0,len(i)):
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
            if len(preAssign) >0:
                exprDict[preAssign] = preAssign
                if localKillerVarDict.__contains__(preAssign):
                    for check in localKillerVarDict[preAssign]:
                        if genDict.__contains__(check):
                            if not killed.__contains__(check):
                                killed.append(check)
                            del genDict[check]
                if len(postAssign) == 2 and len(oper)>0:
                    genDict[str(postAssign[0]+" "+oper+" "+postAssign[1])] = [postAssign[0],postAssign[1]]
                    print(currFramedBlock.id, "gen4", genDict[str(postAssign[0]+" "+oper+" "+postAssign[1])] )
                    temp = []
                    if localKillerVarDict.__contains__(postAssign[0]):
                        temp = localKillerVarDict[postAssign[0]]
                    temp.append(str(postAssign[0]+" "+oper+" "+postAssign[1]))
                    localKillerVarDict[postAssign[0]] = temp
                    temp1 = []
                    if localKillerVarDict.__contains__(postAssign[1]):
                        temp1 = localKillerVarDict[postAssign[1]]
                    temp1.append(str(postAssign[0]+" "+oper+" "+postAssign[1]))
                    localKillerVarDict[postAssign[1]] = temp1
                continue
            else:
                continue
        else:
            continue
    currFramedBlock.localKillerVarDict = localKillerVarDict
    print("gen dict end",genDict)
    currFramedBlock.genData = list(genDict.keys())
    currFramedBlock.anticipated = genDict
    currFramedBlock.exprDict = exprDict
    currFramedBlock.killData = killed
    print(currFramedBlock.id, "local gen", currFramedBlock.anticipated)
    print(currFramedBlock.id, "local kill", currFramedBlock.killData)
    return currFramedBlock










if __name__ == "__main__":
    main()
