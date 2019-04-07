#!/usr/bin/env python3
import yaml
import sys
import gen3ac
import genbb
import buildcfg
import copy
import os
class A02Output(object):
    def __init__(self):
        self.nodes = []
        self.edges = {} # node -> {succ1, succ2, succ3, ...}
        self.facts = {}
        self.blockSetObj = [] # connections are block objects
        self.blockSetId = [] #connections are id's of blocks
        self.blockDict = {}
        self.header = None
        self.blocksOG = []
    '''
Calls gen3ac and receives stringArray, which is sent to gennbb to create blocks.
Remove any empty/useless blocks from genbb. 
Convert the blocks with id's as connections into blocks with other blocks as connections and store them into a dictionary.
Deep Refactor the blocks' id proper sequential order
Create a cfg with buildcfg
Create nodes for local cfg/yaml
    '''
    def readCode(self, inputFile):
        StringArray = []
        if type(inputFile) is list:
            StringArray  = inputFile
            for line in StringArray:
                if self.header is None:
                    self.header = line
        else:
            filePath = str(inputFile)
            fileName = os.path.basename(filePath)
            f = None
            try:
                original = filePath
                f = open(original, 'r+')
            except IOError:
                print("Error: File does not appear to exist.")
                sys.exit(0)
            lineData0 = []  # original
            lineData1 = []  # result
            resData = []
            for line in f:
                if self.header is None:
                    self.header = line
                lineData0.append(line)
            f.close()
            StringArray = lineData0
        blocks = genbb.scanString(StringArray)
        self.blocksOG = copy.deepcopy(blocks)
        for b in blocks:
            instructs = []
            for l in b.lineObj:
                localTemp = l.code
                if len(l.remove)>0:
                    localTemp = "".join(localTemp.rsplit(l.remove))
                    if len(localTemp) == 0:
                        continue
                    elif localTemp[0] == ";":
                        continue
                    else:
                        instructs.append(localTemp)
                        continue
                else:
                    if len(localTemp) == 0:
                        continue
                    instructs.append(localTemp)
            b.instructions = []
            b.instructions = instructs
        for i in range(0, len(blocks)):
            self.blockDict[blocks[i].id] = blocks[i]
        objBlocks = blocks
        for i in range(0, len(blocks)):
            objCon = []
            for con in blocks[i].connect:
                if self.blockDict.__contains__(con):
                    objCon.append(self.blockDict[con])
                else:
                    objCon.append(con)
            objBlocks[i].connect = objCon
        resBlockStart = removeEmptyBlocks(objBlocks[0])
        starterDict = {}
        resBlockDict = fetchBlocks(resBlockStart,starterDict)#convert to dictionary of block with block connections
        resBlockObjs = []
        for k in resBlockDict.keys():
            resBlockObjs.append(resBlockDict[k])
        self.blockSetObj = resBlockObjs
        blocksCFG = resBlockObjs
        for b in blocksCFG:
            if type(b) == str:
                continue
            conId = []
            for i in range(0, len(b.connect)):
                if type(b.connect[i]) == str:
                    conId.append(b.connect[i])
                    continue
                conId.append(b.connect[i].id)
            b.connect = conId
        blocksCFGRes = []
        for b in blocksCFG:
            proc = True
            if type(b) == str:
                blocksCFGRes.append(b)
                continue
            for con in b.connect:
                if type(con) is not str:
                    proc = False
            if proc:
                blocksCFGRes.append(b)
        blocksCFG = blocksCFGRes
        self.blockSetId = blocksCFGRes
        self.refactorBB()
        blocksCFGRes = self.blockSetId
        return blocksCFGRes

    def refactorBB(self):
        counter = 1
        locBlockSetId = self.blockSetId
        locDictCounter = {}
        locDictId = {}
        listCounter = []
        refactorDict = {}
        for i in range(0, len(locBlockSetId)):
            if type(locBlockSetId[i]) == str:
                continue
            locDictId[locBlockSetId[i].countVal] = locBlockSetId[i]
            listCounter.append(locBlockSetId[i].countVal)
        listCounter.sort()
        for key in listCounter:
            if key == "ENTRY":
                continue
            elif key == "EXIT":
                continue
            else:
                locDictCounter[key] = counter
                counter+=1
        newBlockSet = []
        updatedIdTranDict = {}
        for key in locDictCounter.keys():
            ogBB = locDictId[key]
            newId = locDictCounter[key]
            ogId = ogBB.id
            ogBB.reAssign(newId)
            updatedIdTranDict[ogId] = ogBB.id
            newBlockSet.append(ogBB)
        updatedIdTranDict["ENTRY"] = "ENTRY"
        updatedIdTranDict["EXIT"] = "EXIT"
        resBlockSetId = genbb.updateBlockConnections(newBlockSet, updatedIdTranDict)
        objBlocks = copy.deepcopy(resBlockSetId)
        self.blockDict.clear()
        self.blockDict["ENTRY"] = "ENTRY"
        self.blockDict["EXIT"] = "EXIT"
        for i in range(0, len(resBlockSetId)):
            if type(resBlockSetId[i]) == str:
                continue
            else:
                self.blockDict[resBlockSetId[i].id] = resBlockSetId[i]
        for i in range(0, len(resBlockSetId)):
            if type(resBlockSetId[i]) == str:
                objBlocks[i] = resBlockSetId[i]
                continue
            objCon = []
            for con in resBlockSetId[i].connect:
                if self.blockDict.__contains__(con):
                    objCon.append(self.blockDict[con])
                else:
                    objCon.append(con)
            objBlocks[i].connect = objCon
        self.blockSetObj = objBlocks
        self.blockSetId = resBlockSetId



        #
        #
        #
        #     b = tempBlockCopyID[i]
        #     if type(b) == str:
        #         continue
        #     else:
        #         tempID = str(counter).zfill(3);
        #         counter += 1
        #         newId = "BB" + tempID
        #         tempDictId[b.id] = newId
        #         tempBlockCopyID[i].id = newId
        # for b in tempBlockCopyID:
        #     if type(b) == str:
        #         continue
        #     for i in range(0, len(b.connect)):
        #         con = b.connect[i]
        #         if tempDictId.__contains__(con):
        #             b.connect[i] = tempDictId[con]
        # starterDict = {}
        # resBlockDict = fetchBlocks(tempBlockCopyID[0], starterDict)
        # resBlockObjs = []
        # for k in resBlockDict.keys():
        #     resBlockObjs.append(resBlockDict[k])
        # self.blockSetObj = resBlockObjs
        # self.blockSetId = tempBlockCopyID
        # for b in self.blockSetId:
        #     if type(b) == str:
        #         print("string", b)
        #     else:
        #         print(b.id)


visitedFetchBlocks = {}
def fetchBlocks(currBlock, resBlocks):
    global visitedFetchBlocks
    visitedFetchBlocks[currBlock] = True
    if type(currBlock) == str:
        resBlocks[currBlock] = currBlock
        return resBlocks
    resBlocks[currBlock.id] = currBlock
    for i in range(0, len(currBlock.connect)):
        if visitedFetchBlocks.__contains__(currBlock.connect[i]):
            continue
        resBlocks = fetchBlocks(currBlock.connect[i], resBlocks)
    return resBlocks

visitedEmptyBlocks = {}#currBlock => Possible Reassignment
def removeEmptyBlocks(currBlock):
    global visitedEmptyBlocks
    visitedEmptyBlocks[currBlock] = None
    if type(currBlock) == str:
        visitedEmptyBlocks[currBlock] = currBlock
        return currBlock
    for i in range(0, len(currBlock.connect)):
        con = currBlock.connect[i]
        if visitedEmptyBlocks.__contains__(con):
            continue
        resCon = removeEmptyBlocks(con)
        if len(currBlock.instructions) == 0:
            visitedEmptyBlocks[currBlock] = resCon
            return resCon
        else:
            currBlock.connect[i] = resCon
    visitedEmptyBlocks[currBlock] = currBlock
    return currBlock

editedBlocks = {}
def editConnectsBlocks(currBlock):
    global visitedEmptyBlocks
    global editedBlocks
    editedBlocks[currBlock] = None
    for i in range(0, len(currBlock.connect)):
        con = currBlock.connect[i]
        currBlock.connect[i] = visitedEmptyBlocks[con]
        if editedBlocks.__contains__(con):
            continue
        else:
            currBlock.connect[i] = editConnectsBlocks(con)
    return currBlock
