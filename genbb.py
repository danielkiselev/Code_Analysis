#!/usr/bin/env python3
import pycparser
import argparse
import sys
import io
import os
import re
import string
code = list(string.ascii_lowercase)
counter = 1
vcounter = 0
header = ""
class BasicBlock:
    def __init__(self):
        global code
        global counter
        self.node = code[counter]
        self.countVal = counter
        tempID = str(counter).zfill(3);
        counter+=1
        self.id = "BB"+tempID
        self.connect = []
        self.connect1 = []
        self.instructionsVN = []
        self.instructions = []
        self.lineObj = []
        self.visits = {}
        self.varVal = {}
        self.exit = False

    def addInstruct(self, instruct, line):
        self.instructions.append(instruct)
        self.lineObj.append(line)
        line.parentBlock = self.id

    def formConnections(self):
        lines = self.lineObj
        for l in lines:
            if len(l.connect)>0:
                for c in l.connect:
                    self.connect.append(c.parentBlock)
                for c in l.connect1:
                    self.connect1.append(c.parentBlock)
    def reAssign(self, newIdCount):
        tempID = str(newIdCount).zfill(3);
        self.id = "BB" + tempID
        self.countVal = newIdCount


class Token:
    def __init__(self, code, varType):
        global vcounter
        self.varCode = vcounter
        vcounter+=1
        self.var = code
        self.varType = varType # 1=t, 2=label, 3 = goto label, 4 = return


class LineData:
    def __init__(self, code):
        self.leader = False
        self.code = code
        self.vars = []
        self.connect = []
        self.connect1 = []
        self.parentBlock = None
        self.exit = False
        self.remove = ""

    def addVar(self, v):
        if v.varType == "2":
            self.remove = v.var+":"
        if v.varType == "3":
            self.remove = "goto "+v.var
        if v.varType == "4":
            self.exit = True
        self.vars.append(v)
    def addConnect(self, con):
        self.connect.append(con)
    def addConnect1(self, con):
        self.connect1.append(con)


def updateBlockConnections(blocks, idTransDict):
    resBlocks = []
    for b in blocks:
        for i in range(0,len(b.connect)):
            ogCon = b.connect[i]
            b.connect[i] = idTransDict[ogCon]
            # print(b.connect[i])
        resBlocks.append(b)
    return resBlocks





def scan(filePath, clone):
    global header
    filePath = str(filePath)
    fileName = os.path.basename(filePath)
    f = None
    try:
        original = filePath
        f = open(original, 'r+')
    except IOError:
        print("Error: File does not appear to exist.")
        sys.exit(0)
    lines = []#original
    localLineData = []
    resData = []#result
    for line in f:
        lines.append(line)
        resData.append(lineParser(line))
    f.close()
    if clone is None:
        header = resData[0]
        resData = resData[1:-1]
    resData = lineInspector(resData)
    blocks = blockBuilder(resData)
    for b in blocks:
        b.formConnections()
    if clone is None:
        return blocks
    outPath = os.path.dirname("/"+clone)
    if not os.path.exists(outPath):
        os.makedirs(outPath)
    out = open(clone, 'w')
    out.writelines(printBlocks(blocks))
    out.close()
    return blocks

def scanString(stringData):
    global header
    global counter
    global vcounter
    vcounter = 0
    counter = 1
    header = ""
    f = stringData
    lines = []#original
    localLineData = []
    resData = []#result
    for line in f:
        lines.append(line)
        resData.append(lineParser(line))
    header = resData[0]
    resData = resData[1:-1]
    resData = lineInspector(resData)
    blocks = blockBuilder(resData)
    for b in blocks:
        b.formConnections()
    for i in range(0,len(blocks)):
        b = blocks[i]
        used = []
        for c in b.connect:
            proc = True
            for u in used:
                if u == c:
                    proc = False
            if proc:
                used.append(c)
        if b.exit:
            b.connect = []
            b.connect.append("EXIT")
        elif len(used) == 0 and (i+1)<len(blocks):
            b.connect.append(blocks[i+1].id)
        else:
            b.connect = used
    return blocks

def printBlocks(blockList):
    StringBuilder = ""
    for b in blockList:
        # print(b.id+":")
        StringBuilder += b.id+":\n"
        for instruct in b.instructions:
            # print("      "+instruct)
            StringBuilder +="      "+ instruct
    return StringBuilder



def blockBuilder(localLineData):
    blockList = []
    currBlock = None
    for line in localLineData:
        if line.leader:
            if currBlock is None:
                currBlock = BasicBlock()
                currBlock.addInstruct(line.code, line)
                if line.exit:
                    currBlock.exit = True
                continue
            else:
                blockList.append(currBlock)
                currBlock = BasicBlock()
                currBlock.addInstruct(line.code, line)
                if line.exit:
                    currBlock.exit = True
                continue
        else:
            currBlock.addInstruct(line.code, line)
            if line.exit:
                currBlock.exit = True
    if currBlock is not None:
        currBlock.exit = True
        blockList.append(currBlock)
    return blockList






def lineInspector(lines):
    Targeted = []
    LocLines = []
    targetDict = {}
    for i in range(0, len(lines)):
        line = lines[i]
        # print(line.code)
        if i == 0:
            line.leader = True
            LocLines.append(line)
            continue
        for v in line.vars:
            if v.varType == "3":
                if targetDict.__contains__(v.var):
                    tempDict = targetDict[v.var]
                    tempDict.append(i)
                    targetDict[v.var] = tempDict
                else:
                    tempDict = []
                    tempDict.append(i)
                    targetDict[v.var] = tempDict
                if i<(len(lines)-1):
                    lines[i+1].leader = True
                    if str(line.code[0]+line.code[1]) == "if":
                        # print(line.code+"proc")
                        line.addConnect(lines[i + 1])
                Targeted.append(v.var)
        LocLines.append(line)
    # print(Targeted)
    return lineTarget(Targeted, LocLines, targetDict)

def lineTarget(targets, lines, targetDict):
    LocLines = []
    for i in range(0, len(lines)):
        line = lines[i]
        for v in line.vars:
            for target in targets:
                if target == (v.var) and v.varType == "2":
                    tempDict = targetDict[target]
                    for items in tempDict:
                        lines[items].addConnect(line)
                    line.leader = True
        lines[i] = line
        LocLines.append(line)
    LocLines = lines
    return LocLines




def lineParser(line):
    locLine = line[0:-2]
    toCheck = []
    StringBuilder = ""
    locVar = LineData(line)
    for c in locLine:
        if c == "_":
            StringBuilder += c
        elif(c == " " ):
            if len(StringBuilder) > 0:
                toCheck.append(StringBuilder)
                StringBuilder = ""
        elif (not c.isdigit() and not c.isalpha() ):
            if len(StringBuilder) > 0:
                toCheck.append(StringBuilder)
                StringBuilder = ""
        else:
            StringBuilder += c
    if len(StringBuilder)>0:
        toCheck.append(StringBuilder)
        StringBuilder = ""
    for k in range(0,len(toCheck)):
        part = toCheck[k]
        varBuild = ""
        offSet = 0
        proc = False
        if part == "return":
            t = Token("return", str(4))
            locVar.addVar(t)
            continue
        if part[0] == "t":
            pass
        elif part[0] == "L":
            varBuild+="L"
            offSet = 1
            pass
        else:
            proc = True
        for i in range(offSet,len(part)):
            if i == offSet:
                varBuild += part[i]
                continue
            if part[i].isdigit():
                varBuild += part[i]
                continue
            else:
                proc = True
                break
        if not proc:
            t = None
            if offSet == 1:
                if k>0:
                    if toCheck[k-1] == "goto":
                        t = Token(varBuild, str(3))
                    else:
                        t = Token(varBuild, str(2))
                else:
                    t = Token(varBuild, str(2))
            else:
                t = Token(varBuild, str(1))
            locVar.addVar(t)
    TempString = ""
    for v in locVar.vars:
        TempString+=" "+v.var+ " type: "+ v.varType+"  |"
    #print(locLine + "  |"+TempString )
    return locVar

def externalPreprocessor(linesStart):
    lines = []
    localLineData = []
    StringBuilder = ""
    resData = []#result
    for line in linesStart:
        lines.append(line)
        resData.append(lineParser(line))
    resData = lineInspectorExt(resData)
    for data in resData:
        StringBuilder+=data.code
        localLineData.append(data.code)
    return StringBuilder



def lineInspectorExt(lines):
    Targeted = []
    LocLines = []
    for i in range(0, len(lines)):
        line = lines[i]
        # print(line.code)
        if i == 0:
            line.leader = True
            LocLines.append(line)
            continue
        for v in line.vars:
            if v.varType == "3":
                if i<(len(lines)-1):
                    lines[i+1].leader = True
                Targeted.append(v.var)
        LocLines.append(line)
    #print(Targeted)
    return lineTargetExt(Targeted, LocLines)

def lineTargetExt(targets, lines):
    LocLines = []
    for i in range(0, len(lines)):
        good = True
        line = lines[i]
        for v in line.vars:
            if v.varType == "1":
                if v.var == line.code[0:-2]:
                    good = False
                    break
            for target in targets:
                if target == (v.var) and v.varType == "2":
                    LocLines.append(line)
                if v.varType == "2":
                    good = False
        if good:
            LocLines.append(line)
    return LocLines




def main():
    x = scan(str(sys.argv[1]),str(sys.argv[2]))

if __name__ == '__main__':
    main()
