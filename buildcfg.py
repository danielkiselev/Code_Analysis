#!/usr/bin/env python3
import graphviz
import genbb
import sys
import helperCFG
codeDict = {}
gBlocks = []

def main():
    global codeDict
    global gBlocks
    fileName = sys.argv[2]
    x = helperCFG.A02Output()
    blocks = x.readCode(sys.argv[1])
    gBlocks = blocks
    #print(len(blocks))
    ListConnect(blocks)
    dot = graphviz.Digraph(comment=fileName)
    prev = "ENTRY"
    dot.node('$', prev)
    dot.node('-', "EXIT")
    resBlock = []
    for i in range(0, len(blocks)):
        b = blocks[i]
        if type(b) == str:
            continue
        if i == 0:
            dot.edge('$', b.node, constraint='false')
        StringBuilder = ""
        for ins in b.instructions:
            StringBuilder += ins
        dot.node(b.node, (b.id + "\n" + StringBuilder))
        prev = b.id
        edgesHold = []
        used = []
        for c in b.connect:
            proc = True
            if c == "EXIT":
                dot.edge(b.node, '-', constraint='false')
                break
            for u in used:
                if u == c:
                    proc = False
            if proc:
                used.append(c)
                if codeDict.__contains__(c):
                    edgesHold.append(b.node + codeDict[c])
        for c in b.connect1:
            proc = True
            for u in used:
                if u == c:
                    proc = False
            if proc:
                used.append(c)
                edgesHold.append(b.node + codeDict[c])
        # print(edgesHold)
        dot.edges(edgesHold)
    #print(dot.source)  # doctest: +NORMALIZE_WHITESPACE
    dot.render(fileName, view=False)  # doctest: +

def starter(fileName, Blocks):
    global codeDict
    global gBlocks
    blocks = Blocks
    ListConnect(blocks)
    dot = graphviz.Digraph(comment=fileName)
    prev = "ENTRY"
    dot.node('$', prev)
    dot.node('-', "EXIT")
    resBlock = []
    for i in range(0, len(blocks)):
        b = blocks[i]
        if type(b) == str:
            continue
        if i == 0:
            dot.edge('$', b.node, constraint='false')
        StringBuilder = ""
        for ins in b.instructions:
            StringBuilder += ins
        dot.node(b.node, (b.id + "\n" + StringBuilder))
        prev = b.id
        edgesHold = []
        used = []
        for c in b.connect:
            proc = True
            if c == "EXIT":
                dot.edge(b.node, '-', constraint='false')
                break
            for u in used:
                if u == c:
                    proc = False
            if proc:
                used.append(c)
                if codeDict.__contains__(c):
                    edgesHold.append(b.node + codeDict[c])
        for c in b.connect1:
            proc = True
            for u in used:
                if u == c:
                    proc = False
            if proc:
                used.append(c)
                edgesHold.append(b.node + codeDict[c])
        # print(edgesHold)
        dot.edges(edgesHold)
    #print(dot.source)  # doctest: +NORMALIZE_WHITESPACE
    dot.render(fileName, view=False)  # doctest: +

def ListConnect(blocks):
    global codeDict
    for b in blocks:
        if type(b) == str:
            continue
        codeDict[b.id] = b.node



if __name__ == '__main__':
    main()


