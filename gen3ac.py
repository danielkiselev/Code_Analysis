#!/usr/bin/env python3
import pycparser
import argparse
import sys
import io
import os

import re
RE_CHILD_ARRAY = re.compile(r'(.*)\[(.*)\]')
RE_INTERNAL_ATTR = re.compile('__.*__')

constInt = {}
constIntCounter = 0
constString = {}
constStringCounter = 0
signDict = {}#variable name == key, unsigned int or int as type
finCode = []
labelCounter = 0
aCount = 0
labBool = False
procTrack = {}
tempHoldCode = []


class Stack:
    def __init__(self):
        self.items = []

    def isEmpty(self):
        return self.items == []

    def push(self, item):
        global procTrack
        procTrack[item] = 0
        self.items.append(item)

    def pop(self):
        return self.items.pop()

    def peek(self):
        procTrack[self.items[len(self.items) - 1]] = 1
        return self.items[len(self.items) - 1]

    def size(self):
        return len(self.items)

breakStack = Stack()#contains break labels
contStack = Stack()#contains break labels





class treeNode:
    def __init__(self, family,nType ,code):
        self.family = family # at the start of the tree node when u print ast
        self.nType = nType# _nodetype
        self.code = code#if it's legitimate code then we have string otherwise None
        self.children = []

    def addChild(self, child):
        self.children.append(child)


def parseParam(n):#where type is paramList
    stringBuilder = ""
    for child in n.children:
        if child.nType == "Decl" and child.family == "params":  # parameter decelerations
            if stringBuilder is not "":
                stringBuilder += ", "
            locVar = child.code
            locType = ""
            for subchild in child.children:
                if subchild.nType == "PtrDecl":
                    for subsubchild in subchild.children:
                        for subsubsubchild in subsubchild.children:
                            locType = subsubsubchild.code
                    locType += " *"
                    stringBuilder += locType+locVar
                else:
                    for subsubchild in subchild.children:
                        if(subsubchild.code == "unsigned', 'int"):
                            locType = "unsigned int"
                        elif (subsubchild.code == "unsigned', 'char"):
                            locType = "unsigned char"
                        elif (subsubchild.code == "unsigned', 'long"):
                            locType = "unsigned long"
                        else:
                            locType = subsubchild.code
                    stringBuilder+=locType
                    stringBuilder+= " "
                    stringBuilder+=locVar
        elif child.code == "None" and child.family == "params":
            for subchild in child.children:
                for subsubchild in subchild.children:
                    if subsubchild.code == "void":
                        return "void"

    return stringBuilder

def funcDec(n):
    global finCode
    stringBuilder = ""
    parameters = ""
    if n.family == "decl" and n.nType == "Decl":
        for child in n.children:
            for subchild in child.children:
                if subchild.nType == "TypeDecl":
                    for subsubchild in subchild.children:
                        if(subsubchild.code == "unsigned', 'int"):
                            stringBuilder += "unsigned int"
                        elif (subsubchild.code == "unsigned', 'char"):
                            stringBuilder += "unsigned char"
                        elif (subsubchild.code == "unsigned', 'long"):
                            stringBuilder += "unsigned long"
                        else:
                            stringBuilder += subsubchild.code
                if subchild.nType == "ParamList":
                    parameters = parseParam(subchild)
        stringBuilder += " "
        stringBuilder += str(n.code)
        stringBuilder += "("
        stringBuilder += parameters
        stringBuilder += "){"
        finCode.append(stringBuilder)


def ifParse(n):
    global aCount
    global labelCounter
    global finCode
    global constIntCounter
    global constStringCounter
    global constInt
    global breakStack
    global contStack
    global signDict
    if n.nType == "Constantstring":
        constString[n.code] = "t" + str(constIntCounter)
        finCode.append("char *t" + str(constIntCounter) + " = " + n.code + "")
        n.code = "t" + str(constIntCounter)
        constIntCounter += 1
    if n.nType == "Constantint":
        constInt[n.code] = "t" + str(constIntCounter)
        signDict[constInt[n.code]] = "int"
        finCode.append("int t" + str(constIntCounter) + " = " + n.code + "")
        n.code = "t" + str(constIntCounter)
        constIntCounter += 1
    if n.nType == "Constantchar":
        constInt[n.code] = "t" + str(constIntCounter)
        signDict["t" + str(constIntCounter)] = "char"
        finCode.append("char t" + str(constIntCounter) + " = " + n.code + "")
        n.code = "t" + str(constIntCounter)
        constIntCounter += 1
    if n.nType == "Constantlong":
        constInt[n.code] = "t" + str(constIntCounter)
        signDict["t" + str(constIntCounter)] = "long"
        finCode.append("long t" + str(constIntCounter) + " = " + n.code + "")
        n.code = "t" + str(constIntCounter)
    if(len(n.children) == 0):
        intTypeTemp = signDict[n.code]
        locCount = constIntCounter
        constIntCounter += 1
        locVar = "t" + str(locCount)
        signDict[locVar] = intTypeTemp
        finCode.append(intTypeTemp + " " + locVar + " = "+ n.code)
        return locVar
    else:
        if n.nType == "ArrayRef":#used to also check for "cond"
            left = ""
            right = ""
            locCount = constIntCounter
            constIntCounter += 1
            locVar = "t"+str(locCount)
            intType = "int"
            for condition in n.children:
                if condition.family == "name":
                    locCount = constIntCounter
                    constIntCounter += 1
                    ptrVar = "t" + str(locCount)
                    # print(signDict)
                    # print(condition.code)
                    # print("int Data", constInt)
                    finCode.append(signDict[condition.code]+" *" + ptrVar + " = " + "&"+condition.code[1:len(condition.code)] + "[0]")
                    #finCode.append("int *" + ptrVar + " = " + "&"+condition.code[1:len(condition.code)] + "[0]")
                    left = ptrVar#    int t7 =  *t1 ;//    int *t7 =  &t1[0] ;
                if condition.family == "subscript":
                    right = ifParse(condition)#    int t6 = t7 + t8;//    int t6 = *(t7 + t8);
            intTypeL = ""
            intTypeR = ""
            if left in signDict:
                intTypeL= signDict[left]
            if right in signDict:
                intTypeR= signDict[right]
            if intTypeL == "unsigned int" or intTypeR == "unsigned int":
                intType = "unsigned int"
            if intTypeL == "char" or intTypeR == "char":
                intType = "char"
            signDict[locVar] = intType
            finCode.append(intType+" "+locVar+" = *("+left+" "+"+"+" "+right+")")
            return locVar
        else:
            left = ""
            right = ""
            operator = n.code
            if operator == "&&":
                tLabel = "L_" + str(labelCounter)
                labelCounter += 1
                stepLabel = "L_" + str(labelCounter)
                labelCounter += 1
                lstate = ""
                rstate = ""
                for condition in n.children:
                    if condition.family == "left":
                        left = ifParse(condition)
                        lstate = "if( " + left + " != 0 ) goto " + stepLabel
                        finCode.append(lstate)
                        finCode.append(str("goto " + breakStack.peek() + ""))
                        finCode.append(str(stepLabel + ":"))
                    if condition.family == "right":
                        right = ifParse(condition)
                        rstate = "if( " + right + " != 0) goto " + tLabel
                        finCode.append(rstate)
                        finCode.append(str("goto " + breakStack.peek() + ""))
                        finCode.append(str(tLabel + ":"))
                locCount = constIntCounter
                constIntCounter += 1
                locVar = "t" + str(locCount)
                signDict[locVar] = ""
                finCode.append("int " + locVar + " = 1")
                return locVar
            elif operator == "||":
                tLabel = "L_" + str(labelCounter)
                labelCounter += 1
                stepLabel = "L_" + str(labelCounter)
                labelCounter += 1
                lstate = ""
                rstate = ""
                for condition in n.children:
                    if condition.family == "left":
                        left = ifParse(condition)
                        lstate = "if( " + left + " ) goto " + tLabel
                        finCode.append(lstate)
                        finCode.append(str("goto " + stepLabel + ""))
                        finCode.append(str(stepLabel + ":"))
                    if condition.family == "right":
                        right = ifParse(condition)
                        rstate = "if( " + right + " ) goto " + tLabel
                        finCode.append(rstate)
                        finCode.append(str("goto " + breakStack.peek() + ""))
                finCode.append(str(tLabel + ":"))
                locCount = constIntCounter
                constIntCounter += 1
                locVar = "t" + str(locCount)
                signDict[locVar] = ""
                finCode.append("int " + locVar + " = 1")
                return locVar
            else:
                locCount = constIntCounter
                constIntCounter += 1
                for condition in n.children:
                    if condition.family == "left":
                        left = ifParse(condition)
                    if condition.family == "right":
                        right = ifParse(condition)
                intTypeL = ""
                intTypeR = ""
                if left in signDict:
                    intTypeL = signDict[left]
                if right in signDict:
                    intTypeR = signDict[right]
                intType = "int"
                if (intTypeL == "unsigned int" or intTypeR == "unsigned int"):
                    intType = "unsigned int"
                if (intTypeL == "char" or intTypeR == "char"):
                    intType = "char"
                if (intTypeL == "unsigned char" or intTypeR == "unsigned char"):
                    intType = "unsigned char"
                if (intTypeL == "long" or intTypeR == "long"):
                    intType = "long"
                if (intTypeL == "unsigned long" or intTypeR == "unsigned long"):
                    intType = "unsigned long"
                locVar = "t"+str(locCount)
                signDict[locVar] = intType
                finCode.append(intType+" "+locVar+" = "+left+" "+operator+" "+right+"")
                return locVar

def forLoop(n):
    global finCode
    global labelCounter
    global labBool
    global contStack
    global procTrack
    global breakStack
    global tempHoldCode
    global constIntCounter
    labelContinue = "L_" + str(labelCounter)
    labelCounter += 1
    tLabel = "L_" + str(labelCounter)
    labelCounter += 1
    fLabel = "L_" + str(labelCounter)
    labelCounter += 1
    tLabel1 = "L_" + str(labelCounter)
    labelCounter += 1
    nextChild = None
    contStack.push(labelContinue)
    breakStack.push(fLabel)
    for child in n.children:
        if(child.family =="init"):
            bodyParse(child)
        if child.family == "cond":
            finCode.append(str(tLabel1 + ":"))
            operator = child.code
            left = ""
            right =""
            for condition in child.children:
                if condition.family == "left":
                    left = ifParse(condition)
                if condition.family == "right":
                    right = ifParse(condition)
            res = "t" + str(constIntCounter)
            signDict[res] = "int"
            constIntCounter += 1
            finCode.append("int " + res + " = " + left + " " + operator + " " + right)
            ifstate = "if( " + res + " != 0 ) goto " + tLabel + ""
            # ifstate = "if( " + left + " " + operator + " " + right + " ) goto " + tLabel + ""
            finCode.append(ifstate)
            finCode.append(str("goto " + fLabel + ""))
            finCode.append(str(tLabel + ":"))
        if child.family == "next":
            nextChild = (child)
        if child.family == "stmt":
            bodyParse(child)
    if procTrack[labelContinue] == 1:
        finCode.append(labelContinue+":")
    loopIter = bodyParse(nextChild)
    if len(tempHoldCode) > 0:
        for i in tempHoldCode:
            finCode.append(i)
        tempHoldCode = []
    finCode.append(loopIter+"")
    finCode.append(str("goto " + tLabel1 + ""))
    finCode.append(str(fLabel + ":"))
    contStack.pop()
    breakStack.pop()




def whileLoop(n):
    global finCode
    global labelCounter
    global contStack
    global breakStack
    global signDict
    global constIntCounter
    startLabel = "L_" + str(labelCounter)
    labelCounter += 1
    endLabel = "L_" + str(labelCounter)
    labelCounter += 1
    passCondLabel = "L_" + str(labelCounter)
    labelCounter += 1
    nextChild = None
    breakStack.push(endLabel)
    contStack.push(passCondLabel)
    finCode.append(str(startLabel+ ":"))
    for child in n.children:#n == "While"
        if child.family == "cond":
            operator = child.code
            left = ""
            right = ""
            for condition in child.children:
                if condition.family == "left":
                    left = ifParse(condition)
                if condition.family == "right":
                    right = ifParse(condition)
            res = "t" + str(constIntCounter)
            signDict[res] = "int"
            constIntCounter += 1
            finCode.append("int " + res + " = " + left + " " + operator + " " + right)
            ifstate = "if( " + res + " != 0 ) goto " + passCondLabel + ""
            # finCode.append(ifstate)
            # ifstate = "if( " + left + " " + operator + " " + right + " ) goto " + passCondLabel
            finCode.append(ifstate)
            finCode.append(str("goto " + endLabel + ""))
            finCode.append(str(passCondLabel + ":"))
        if child.family == "stmt":
            bodyParse(child)
            finCode.append(str("goto " + startLabel + ""))
    finCode.append(str(endLabel + ":"))
    contStack.pop()
    breakStack.pop()

def doWhileLoop(n):
    global finCode
    global labelCounter
    global labBool
    global labelContinue
    global contStack
    global breakStack
    global signDict
    global constIntCounter

    startLabel = "L_" + str(labelCounter)
    labelCounter += 1
    checkCondLabel = "L_" + str(labelCounter)
    labelCounter += 1
    endLabel = "L_" + str(labelCounter)
    labelCounter += 1
    breakStack.push(endLabel)
    contStack.push(checkCondLabel)
    nextChild = None
    finCode.append(str(startLabel+ ":"))
    for child in n.children:#n == "While"
        if child.family == "stmt":
            for condition in child.children:
                bodyParse(condition)
    finCode.append(str(checkCondLabel + ":"))
    for child in n.children:#n == "While"
        if child.family == "cond":
            operator = child.code
            left = ""
            right = ""
            for condition in child.children:
                if condition.family == "left":
                    left = ifParse(condition)
                if condition.family == "right":
                    right = ifParse(condition)
            res = "t" + str(constIntCounter)
            signDict[res] = "int"
            constIntCounter += 1
            finCode.append("int " + res + " = " + left + " " + operator + " " + right)
            ifstate = "if( "+res+" != 0 ) goto " + startLabel
            finCode.append(ifstate)
            finCode.append("goto "+endLabel)
    finCode.append(str(endLabel + ":"))
    contStack.pop()
    breakStack.pop()

    # res = "t" + str(constIntCounter)
    # signDict[res] = "int"
    # constIntCounter += 1
    # finCode.append("int " + res + " = " + left + " " + operator + " " + right)
    # ifstate = "if( " + res + " != 0 ) goto " + tLabel + ""
    # finCode.append(ifstate)
    # finCode.append(str("goto " + fLabel + ""))

def switchHandler(n):
    global finCode
    global labelCounter
    global labBool
    global labelContinue
    global contStack
    global breakStack
    global constIntCounter
    global signDict
    checkVar = ""
    startLabel = "L_" + str(labelCounter)
    labelCounter += 1
    endLabel = "L_" + str(labelCounter)
    labelCounter += 1
    breakStack.push(endLabel)
    finCode.append(str(startLabel + ":"))
    passCondLabel = "L_" + str(labelCounter)
    labelCounter += 1
    for child in n.children:
        if child.family == "cond":
            checkVar = child.code
        if child.family == "stmt":
            for case in child.children:
                if case.nType == "Case":
                    testVar = ""
                    nextCondLabel = "L_" + str(labelCounter)
                    labelCounter += 1
                    for expr in case.children:
                        if expr.family == "expr":
                            testVar = expr.code
                            res = "t" + str(constIntCounter)
                            signDict[res] = "int"
                            constIntCounter += 1
                            finCode.append("int " + res + " = " +   checkVar + " == " + testVar )
                            ifstate = "if( " + res + " != 0 ) goto " + passCondLabel
                            finCode.append(ifstate)
                            finCode.append(str("goto " +nextCondLabel))
                            finCode.append(str(passCondLabel + ":"))
                        else:
                            bodyParse(expr)
                    finCode.append(str(nextCondLabel + ":"))
                    passCondLabel = "L_" + str(labelCounter)
                    labelCounter += 1
                elif case.nType == "Default":
                    for expr in case.children:
                        finCode.append(bodyParse(expr))
    finCode.append(str(endLabel + ":"))
    breakStack.pop()



#responsible for all body parsing
def bodyParse(n):
    global labelCounter
    global finCode
    global labBool
    global labelContinue
    global breakStack
    global contStack
    global constIntCounter
    global signDict
    global tempHoldCode
    if len(tempHoldCode) > 0:
        for i in tempHoldCode:
            finCode.append(i)
        tempHoldCode = []
    if n.nType == "Constantstring":
        constString[n.code] = "t" + str(constIntCounter)
        finCode.append("char *t" + str(constIntCounter) + " = " + n.code + "")
        n.code = "t" + str(constIntCounter)
        constIntCounter += 1
    if n.nType == "Constantint":
        constInt[n.code] = "t" + str(constIntCounter)
        signDict[constInt[n.code]] = "int"
        finCode.append("int t" + str(constIntCounter) + " = " + n.code + "")
        n.code = "t" + str(constIntCounter)
        constIntCounter += 1
    if n.nType == "Constantchar":
        constInt[n.code] = "t" + str(constIntCounter)
        signDict["t" + str(constIntCounter)] = "char"
        finCode.append("char t" + str(constIntCounter) + " = " + n.code + "")
        n.code = "t" + str(constIntCounter)
        constIntCounter += 1
    if n.nType == "Constantlong":
        constInt[n.code] = "t" + str(constIntCounter)
        signDict["t" + str(constIntCounter)] = "long"
        finCode.append("long t" + str(constIntCounter) + " = " + n.code + "")
        n.code = "t" + str(constIntCounter)
        constIntCounter += 1
    if n.nType == "Break":
        procTrack[contStack.peek()] = 1
        finCode.append("goto "+breakStack.peek())
    if n.nType == "Continue":
        procTrack[contStack.peek()] = 1
        finCode.append("goto "+contStack.peek())
    if n.nType == "Return":
        res = "return "
        for child in n.children:
            res += bodyParse(child)
        finCode.append(res)
    if n.nType == "Compound":
        compData = []
        for child in n.children:
            compData.append(bodyParse(child))
        for data in compData:
            finCode.append(data)
    if n.nType == "For":
        forLoop(n)
    if n.nType == "BinaryOp":
        op = n.code
        left = ""
        right=""
        for child in n.children:
            if child.family == "left":
                left = bodyParse(child)
            if child.family == "right":
                right = bodyParse(child)
        intTypeL = ""
        intTypeR = ""
        if left in signDict:
            intTypeL = signDict[left]
        if right in signDict:
            intTypeR = signDict[right]
        intType = "int"
        if (intTypeL == "unsigned int" or intTypeR == "unsigned int"):
            intType = "unsigned int"
        if (intTypeL == "char"):
            intType = "char"
        if (intTypeR == "char"):
            intType = "char"
        if (intTypeL == "unsigned char" or intTypeR == "unsigned char"):
            intType = "unsigned char"
        if (intTypeL == "long" or intTypeR == "long"):
            intType = "long"
        if (intTypeL == "unsigned long" or intTypeR == "unsigned long"):
            intType = "unsigned long"
        res = "t" + str(constIntCounter)
        signDict[res] = intType
        constIntCounter += 1
        finCode.append(intType+" " + res + " = " + left + " "+op+" "+right)
        return res
    if n.nType == "Switch":
        switchHandler(n)
    if n.nType == "UnaryOp":
        locData = n.code
        part = ""
        intType = "int"
        if n.children is not []:
            for child in n.children:
                part = child.code
                if part in signDict:
                    intType = signDict[part]
        if locData == "p++":
            res = "t" + str(constIntCounter)
            constIntCounter += 1
            finCode.append(intType+" " + res + " = " + part)
            signDict[res] = intType
            tempHoldCode.append(part + " = " + res + " + 1")
            return res
        elif locData == "++":
            res = "t" + str(constIntCounter)
            constIntCounter += 1
            signDict[res] = intType
            finCode.append(intType+" " + res + " = " + part)
            finCode.append(part + " = " + res + " + 1")
            return part
        if locData == "p--":
            res = "t" + str(constIntCounter)
            constIntCounter += 1
            finCode.append(intType+" " + res + " = " + part)
            signDict[res] = intType
            tempHoldCode.append(part + " = " + res + " - 1")
            return res
        elif locData == "--":
            res = "t" + str(constIntCounter)
            constIntCounter += 1
            finCode.append(intType+" " + res + " = " + part)
            signDict[res] = intType
            finCode.append(part + " = " + res + " - 1")
            return part
        else:
            locData += part
            return locData
    if n.nType == "While":  # while
        whileLoop(n)
    if n.nType == "DoWhile":
        doWhileLoop(n)
    if n.nType == "If":  # if case
        operator = ""
        left = ""
        right = ""
        tLabel = "L_" + str(labelCounter)
        labelCounter += 1
        fLabel = "L_" + str(labelCounter)
        labelCounter += 1
        tLabel1 = "L_" + str(labelCounter)
        labelCounter += 1
        falseProc = False
        for child in n.children:
            if child.family == "cond" and child.nType == "ArrayRef":
                ifstate = "if( "+ifParse(child)+" != 0 ) goto "+tLabel+""
                finCode.append(ifstate)
                finCode.append(str("goto " + fLabel + ""))
            if child.family == "cond" and child.nType == "BinaryOp":
                operator = child.code
                if operator == "&&":
                    stepLabel = "L_" + str(labelCounter)
                    labelCounter += 1
                    for condition in child.children:
                        if condition.family == "left":
                            left = ifParse(condition)
                            lstate = "if( " + left + " != 0 ) goto " + stepLabel
                            finCode.append(lstate)
                            finCode.append(str("goto " + fLabel + ""))
                            finCode.append(str(stepLabel + ":"))
                        if condition.family == "right":
                            right = ifParse(condition)
                            rstate = "if( " + right + " != 0) goto " + tLabel
                            finCode.append(rstate)
                            finCode.append(str("goto " + fLabel + ""))
                else:
                    for condition in child.children:
                        if condition.family == "left":
                            left = ifParse(condition)
                        if condition.family == "right":
                            right = ifParse(condition)
                    res = "t" + str(constIntCounter)
                    signDict[res] = "int"
                    constIntCounter += 1
                    finCode.append("int " + res + " = " + left + " " + operator + " " + right)
                    ifstate = "if( " +res+ " != 0 ) goto " + tLabel + ""
                    finCode.append(ifstate)
                    finCode.append(str("goto " + fLabel + ""))
            if child.family == "iftrue":
                finCode.append(str(tLabel + ":"))
                res = bodyParse(child)
                if res is not "":
                    finCode.append(res + "")
                finCode.append(str("goto " + tLabel1 + ""))
                finCode.append(str(fLabel + ":"))
            if child.family == "iffalse":
                falseProc = True
                res = bodyParse(child)
                if res is not "":
                    finCode.append(res + "")
        finCode.append(str(tLabel1 + ":"))
    if n.nType == "Assignment":
        lVal = ""
        rVal = ""
        op = n.code
        for child in n.children:
            if child.family == "lvalue":
                lVal = bodyParse(child)
            if child.family == "rvalue":
                rVal = bodyParse(child)
        finCode.append(str(lVal+" "+op+" "+rVal+""))
        if len(tempHoldCode)>0:
            for i in tempHoldCode:
                finCode.append(i)
            tempHoldCode = []
        return ""
    if n.nType == "FuncCall":
        #print("funccall arrived")
        func = ""
        for child in n.children:
            if child.nType == "ID":
                func = child.code
                func+="( "
            if child.nType == "ExprList":
                for subChild in child.children:
                    func+=bodyParse(subChild)
                    func+=", "
                func = func[0:-2]
        func+=" )"
        if n.family == "block_items":
            finCode.append(func)
            return ""
        return func
    else:
        return n.code











def walkTree(n):
    global constString
    global constInt
    global constIntCounter
    global constStringCounter
    global finCode
    global signDict
    if n.nType is not None:
        if n.family == "decl":
            funcDec(n)
        if n.nType == "Decl" and n.family == "params":#parameter decelerations
            locType = ""
            for child in n.children:
                for subchild in child.children:
                    locType += subchild.code
            if locType is "":
                pass
            for child in n.children:
                if child.nType == "PtrDecl":
                    locType = ""
                    for subchild in child.children:
                        for subsubchild in subchild.children:
                            locType+=subsubchild.code
                    #print(locType)
                    constInt[n.code] = "*t" + str(constIntCounter)
                    if locType == "unsigned', 'int":
                        signDict[constInt[n.code]] = "unsigned int"
                        finCode.append("unsigned int *t" + str(constIntCounter) + " = &" + n.code + "[0]")
                        constIntCounter += 1
                    elif locType == "int":
                        signDict[constInt[n.code]] = "int"
                        finCode.append("int *t" + str(constIntCounter) + " = &" + n.code + "[0]")
                        constIntCounter += 1
                    elif locType == "long":
                        signDict[constInt[n.code]] = "long"
                        finCode.append("long *t" + str(constIntCounter) + " = &" + n.code + "[0]")
                        constIntCounter += 1
                    if locType == "unsigned', 'long":
                        signDict[constInt[n.code]] = "unsigned long"
                        finCode.append("unsigned long *t" + str(constIntCounter) + " = &" + n.code + "[0]")
                        constIntCounter += 1
                    return n
            if locType == "unsigned', 'int":
                constInt[n.code] = "t" + str(constIntCounter)
                signDict[constInt[n.code]] = "unsigned int"
                finCode.append("unsigned int t" + str(constIntCounter)+" = "+n.code+"")
                constIntCounter += 1
            elif locType == "int":
                constInt[n.code] = "t" + str(constIntCounter)
                signDict[constInt[n.code]] = "int"
                finCode.append("int t" + str(constIntCounter)+" = "+n.code+"")
                constIntCounter += 1
            elif locType == "unsigned', 'char":
                constInt[n.code] = "t" + str(constIntCounter)
                signDict[constInt[n.code]] = "unsigned char"
                finCode.append("unsigned char t" + str(constIntCounter)+" = "+n.code+"")
                constIntCounter += 1
            elif locType == "char":
                constInt[n.code] = "t" + str(constIntCounter)
                signDict[constInt[n.code]] = "char"
                finCode.append("char t" + str(constIntCounter)+" = "+n.code+"")
                constIntCounter += 1
            elif locType == "unsigned', 'long":
                constInt[n.code] = "t" + str(constIntCounter)
                signDict[constInt[n.code]] = "unsigned long"
                finCode.append("unsigned long t" + str(constIntCounter)+" = "+n.code+"")
                constIntCounter += 1
            elif locType == "long":
                constInt[n.code] = "t" + str(constIntCounter)
                signDict[constInt[n.code]] = "long"
                finCode.append("long t" + str(constIntCounter)+" = "+n.code+"")
                constIntCounter += 1
            elif locType == "void":
                pass
            ## make a case for unsigned int and char
        elif n.nType == "Decl":#generaldeclerations
            locType = ""
            for child in n.children:
                for subchild in child.children:
                    locType = subchild.code
                if locType == "int":
                    constInt[n.code] = "t" + str(constIntCounter)
                    signDict[constInt[n.code]] = "int"
                    finCode.append("int t" + str(constIntCounter))
                    n.code = "t" + str(constIntCounter)
                    constIntCounter += 1
                elif locType == "unsigned', 'int":
                    constInt[n.code] = "t" + str(constIntCounter)
                    signDict[constInt[n.code]] = "unsigned int"
                    finCode.append("unsigned int t" + str(constIntCounter))
                    constIntCounter += 1
                elif locType == "char":
                    constInt[n.code] = "t" + str(constIntCounter)
                    signDict[constInt[n.code]] = "char"
                    finCode.append("char t" + str(constIntCounter))
                    constIntCounter += 1
                elif locType == "unsigned', 'char":
                    constInt[n.code] = "t" + str(constIntCounter)
                    signDict[constInt[n.code]] = "unsigned char"
                    finCode.append("unsigned char t" + str(constIntCounter))
                    constIntCounter += 1
                elif locType == "long":
                    constInt[n.code] = "t" + str(constIntCounter)
                    signDict[constInt[n.code]] = "long"
                    finCode.append("long t" + str(constIntCounter))
                    constIntCounter += 1
                elif locType == "unsigned', 'long":
                    constInt[n.code] = "t" + str(constIntCounter)
                    signDict[constInt[n.code]] = "unsigned long"
                    finCode.append("unsigned long t" + str(constIntCounter))
                    constIntCounter += 1
                elif locType == "void":
                    pass
            ## make a case for unsigned int and char
        elif n.nType == "ID":#identifier
            if constInt.__contains__(n.code):
                n.code = constInt[n.code]
            elif constString.__contains__(n.code):
                n.code = constString[n.code]
            else:
                pass
    for child in range(0,len(n.children)):
        n.children[child] = walkTree(n.children[child])
    return n

def printTree(n, level, size):
    print(' '*size +'      '*(level-1) + '+-----'*(level > 0) +"Family:" +n.family )
    if n.nType is not "":
        print(' '*size +'      '*(level-1) + '+-----'*(level > 0) +"Type:"+n.nType )
    if n.code is not "":
        print(' '*size +'      '*(level-1) + '+-----'*(level > 0) + "Code:"+str(n.code))
    size += len(n.nType)
    for child in n.children:
        printTree(child, level+1, size)

def to_dict(node):
    NodeClass = node.__class__
    result = {}
    result['_nodetype'] = NodeClass.__name__
    for attr in NodeClass.attr_names:
        loc = str(getattr(node, attr))
        if loc  == "[]":
            continue
        else:
            result[attr] = loc
    for child_name, child in node.children():
        match = RE_CHILD_ARRAY.match(child_name)
        if match:
            array_name, array_index = match.groups()
            result[array_name] = result.get(array_name, [])
            result[array_name].append(to_dict(child))
        else:
            result[child_name] = to_dict(child)
    return result

def bodyController(n):
    if n.family == "body":
        for child in n.children:
            n = bodyParse(child)
    else:
        for child in n.children:
            child = bodyController(child)
    return n

def main():
    global constInt
    global constString
    global finCode
    fileName=sys.argv[1]
    outputFileName = sys.argv[2]
    ast = pycparser.parse_file(fileName, use_cpp=True)
    #ast.show()
    r = to_dict(ast)
    rootN = treeNode("root", "", "")  # family,nType ,code
    n = trav(r ,0,rootN )
    n = walkTree(n)
    printTree(n, 0, 0)
    bodyController(n)
    # print("int Data", constInt)
    # print("dict type Data", signDict)
    # print("String Data", constString)
    StringBuilder = ""
    for line in range(0, len(finCode)):
        if finCode[line] == "":
            continue
        if line is not 0:
      #      print(finCode[line]+";")
            StringBuilder+=finCode[line]+";"+"\n"

        else:
     #       print(finCode[line])
            StringBuilder += finCode[line] + "\n"
    #print("}")
    StringBuilder += "}"
    clone = outputFileName
    # outPath = os.path.dirname(clone)
    # if not os.path.exists(outPath):
    #     os.makedirs(outPath)
    out = open(clone, 'w')
    out.writelines(StringBuilder)
    out.close()
    parser = pycparser.CParser()
    # ast1 = parser.parse(StringBuilder, fileName)
    # ast1.show()
    #printTree(n, 0, 0)





def trav(data, counter, currNode):
    global ident
    for k, v in data.items():
        if type(v) is str:
            if(k  == "_nodetype"):
                currNode.nType = v
            if(k  == "type"):
                currNode.nType += v
            elif(k  == "name" or k == "op"):
                currNode.code = v
            elif (k == "names"):
                currNode.code = v[2:-2]
            if (k == "value"):
                currNode.code = v
            #print(" "*counter,"{0} : {1}".format(k, v))
        elif isinstance(v, dict):
            #print(" " * (counter+5), "{0}".format(k))
            t1 = treeNode(k, "", "")  # family,nType ,code
            currNode.addChild(trav(v, counter+5, t1))
        else:
            for i in v:
                #print(" " * (counter+5), "{0}".format(k))
                t1 = treeNode(k,"", "")#family,nType ,code
                currNode.addChild(trav(i, counter + 5, t1))
    return currNode

def beginSteps(fileName):
    global constInt
    global constString
    global finCode
    ast = pycparser.parse_file(fileName, use_cpp=True)
    # ast.show()
    r = to_dict(ast)
    rootN = treeNode("root", "", "")  # family,nType ,code
    n = trav(r, 0, rootN)
    n = walkTree(n)
    printTree(n, 0, 0)
    bodyController(n)
    # print("int Data", constInt)
    # print("dict type Data", signDict)
    # print("String Data", constString)
    StringBuilder = []
    for line in range(0, len(finCode)):
        if finCode[line] == "":
            continue
        if line is not 0:
            #      print(finCode[line]+";")
            StringBuilder.append(finCode[line] + ";" + "\n")

        else:
            #       print(finCode[line])
            StringBuilder.append(finCode[line] + "\n")
    # print("}")
    StringBuilder.append("}")
    return StringBuilder



if __name__ == "__main__":
    main()
