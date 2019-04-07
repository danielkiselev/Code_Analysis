'''
for i=0 to n - 1, where the block has n operations ‘‘Ti <-  Li Opi Ri’’ var <- lvar op rvar
1. get the value numbers for Li and Ri
2. construct a hash key from Opi and the value numbers for Li and Ri
3.
    if :the hash key is already present in the table then
        replace operation i with a copy of the value into Ti and
        associate the value number with Ti
    else:
        insert a new value number into the table at the hash key location
        record that new value number for Ti

python vn.py input-from-3ac.c output.c
Note the input is from the first exercise. Build a CFG and apply value numbering to each basic block, eliminating as
many redundant expressions as you can.
Write the transformed AST to output.c.
'''

import buildcfg
import helperCFG
import graphviz
import genbb
import sys

codeDict = {}#key = id, data = node
symbol = {"(", ")", "+", "-", "*", "/", "==", "!=", "<", "<=", ">", ">=", "=", "&&", "||", "&", "|", "<<", ">>"}
oldBlocks = []

def getVn(f1, f2):
    global codeDict
    global oldBlocks
    fileName = f2
    x = helperCFG.A02Output()
    blocksCFG = x.readCode(f1)
    resCode = []
    resCode.append(str(x.header))
    blocks = x.blocksOG
    buildcfg.starter(fileName[0:-1]+"dot",blocksCFG )
    ListConnect(blocks)
    blocksVN = []
    for b in blocks:
        blocksVN.append(lvn(b))
    for b in blocksVN:
        for i in b.instructionsVN:
            resCode.append(str(i))
    resCode.append("}")
    oldBlocks = blocksVN
    for line in resCode:
        print(line)
    return resCode

def main():# args input-from-3ac.c output.c
    resCode = getVn(sys.argv[1],sys.argv[2])
    fileName = sys.argv[2]
    clone = fileName
    # outPath = os.path.dirname(clone)
    # if not os.path.exists(outPath):
    #     os.makedirs(outPath)
    out = open(clone, 'w')
    out.writelines(resCode)
    out.close()


def printBlocks(blockList):
    StringBuilder = ""
    for b in blockList:
        print(b.id+":")
        StringBuilder += b.id+":\n"
        for instruct in b.instructionsVN:
            print("      "+instruct)
            StringBuilder +="      "+ instruct
    return StringBuilder

def lvn(block):
    global symbol
    # print('\n',block.id)
    blockData = {}
    for i in block.lineObj:
        pre = ""
        currLine = i.code
        StringBuilder = ""
        # print(currLine)
        resVal = None
        proc = False
        lVal = None
        rVal = None
        oper = None
        var = None
        for c in currLine:
            if c == " " or c == ";":
                # print (StringBuilder)
                if StringBuilder == "=" and not proc:
                    proc = True
                elif(proc):
                    if symbol.__contains__(StringBuilder):
                        oper = StringBuilder
                    else:
                        val = calcVal(StringBuilder, blockData)
                        # print(StringBuilder, val)
                        if val is not None:
                            if lVal is None:
                                lVal = val
                            elif (rVal is None) and (oper is not None):
                                rVal = val
                            # print(val)
                        # else:
                        #     # print("no Val", StringBuilder)
                elif(StringBuilder[0] == "t"):
                    # print("t____", StringBuilder)
                    good = True
                    for c1 in StringBuilder:
                        if not c1.isalnum():
                            good = False
                    if good:
                        var = StringBuilder
                elif not proc:
                    pre+=StringBuilder
                StringBuilder = ""
            else:
                StringBuilder += c
        # print(var,lVal, rVal, oper)
        if (lVal is not None) and (rVal is not None) and (oper is not None)and(var is not None):
            lVal = str(lVal)
            rVal = str(rVal)
            lVal = lVal.rstrip('0').rstrip('.') if '.' in lVal else lVal
            rVal = rVal.rstrip('0').rstrip('.') if '.' in rVal else rVal
            resVal = eval(str(lVal)+" "+str(oper)+" "+ str(rVal))
            if blockData.__contains__(resVal):
                resVal = blockData.get(resVal)
            else:
                blockData[resVal] = var
            block.instructionsVN.append(pre+" "+var+" =  "+str(resVal)+";\n")
            #
        elif (lVal is not None) and(var is not None) and (oper is None):
            lVal = str(lVal)
            lVal = lVal.rstrip('0').rstrip('.') if '.' in lVal else lVal
            if blockData.__contains__(lVal):
                lVal = blockData.get(resVal)
            else:
                blockData[eval(lVal)] = var
            block.instructionsVN.append(pre+" "+var+"  = "+ str(lVal)+";\n")
        else:
            block.instructionsVN.append(currLine)
    return block







def calcVal(s, blockData):#finds the value of an equation.
    val = None
    # print(val, s)
    if blockData.__contains__(s):
        val = blockData.get(s)
    elif s.isdigit():
        val = float(s)
    return val


def ListConnect(blocks):
    global codeDict
    for b in blocks:
        if type(b) == str:
            continue
        codeDict[b.id] = b.node

if __name__ == '__main__':
    main()
