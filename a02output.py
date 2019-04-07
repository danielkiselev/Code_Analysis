#!/usr/bin/env python3
from __future__ import print_function
import yaml
import sys
import gen3ac
import genbb
import buildcfg
import copy
import vn

class A02Output(object):
    def __init__(self):
        self.nodes = []
        self.edges = {} # node -> {succ1, succ2, succ3, ...}
        self.facts = {}
        self.blockSetObj = [] # connections are block objects
        self.blockSetId = [] #connections are id's of blocks
        self.blockDict = {}
        self.blocksOG = []


    def add_cfg_node(self, node_name, node_successor_list):
        """Add a node (node_name) and its successors.

           node_name is a string naming the basic block. Two special
           names, ENTRY and EXIT can also be used.

           node_successor_list is a list of basic block names.

           Example usage: `add_cfg_node("BB001", ["BB002", "BB003"])`
        """
        assert node_name not in self.edges, "Node `%s` duplicated" % (node_name,)
        self.nodes.append(node_name)
        self.edges[node_name] = node_successor_list

    def add_node_facts(self, node_name, fact_name, facts):
        """Add dataflow facts to a node.

           node_name is the string naming the basic block. Two special
           names, ENTRY and EXIT can also be used.

           fact_name is one of "IN", "OUT", "GEN" and "KILL".

           Example usage: `add_node_facts("ENTRY", "IN", [])`
        """
        
        if fact_name not in ("IN", "OUT", "GEN", "KILL"):            
            print("Warning: Factname '%s' for node '%s' is not one of the standard names (IN, OUT, GEN, KILL). Hope you know what you're doing." % (fact_name, node_name,),
                  file=sys.stderr)
            
        assert node_name in self.edges, "Topology of CFG must be specified completely before adding dataflow facts. I.e., add_cfg_node was not called on node '%s'" % (node_name,)

        if node_name not in self.facts:
            self.facts[node_name] = {}

        f = self.facts[node_name]

        assert fact_name not in f, "Fact `%s' duplicated for node `%s'" % (fact_name, node_name,)

        f[fact_name] = facts

    def check(self):
        """Perform some sanity checks. """

        assert "ENTRY" in self.edges, "No `ENTRY` node found"
        assert "EXIT" in self.edges, "No `EXIT` node found"

        assert len(self.edges["ENTRY"]) > 0, "Entry node should have at least one successor"

        assert len(self.edges["EXIT"]) == 0, "Exit node should have 0 successors"
        
        # this can never happen, but check anyway
        for n in self.nodes:
            assert n in self.edges, "Node '%s' has no edges defined" % (n,)

        # this can never happen, but check anyway
        for n in self.edges:
            for s in self.edges[n]:
                assert s in self.edges, "Node '%s' appears in edges for node '%s', but not in nodes" % (s, n) # this usually means no add_cfg_node call was made for node s

        assert all([isinstance(s, str) for s in self.nodes]), "Node names must be strings"
 
    def get_output(self):
        """Serialize graph topology and facts as a YAML string"""

        self.check()

        out = []

        for n in self.nodes:
            ne = {}
                        
            ne['name'] = n
            ne['edges'] = self.edges[n]
            ne['facts'] = self.facts[n]

            out.append(ne)

        return yaml.dump(out)

    def write(self, outputfile):
        """Write out the CFG to the file `outputfile` (which must be the name of a file)."""

        with open(outputfile, "w") as f:
            f.write(self.get_output())

        print("Wrote output to '%s'." % (outputfile,), file=sys.stderr)

    '''
Calls gen3ac and receives stringArray, which is sent to gennbb to create blocks.
Remove any empty/useless blocks from genbb. 
Convert the blocks with id's as connections into blocks with other blocks as connections and store them into a dictionary.
Deep Refactor the blocks' id proper sequential order
Create a cfg with buildcfg
Create nodes for local cfg/yaml
    '''
    def readCode(self, inputFile, exCode):
        StringArray = gen3ac.beginSteps(inputFile)
        resStringArray = vn.getVn(StringArray, inputFile)
        blocks = genbb.scanString(resStringArray)
        self.blocksOG = copy.deepcopy(blocks)
        StringArray = resStringArray
        if exCode == 4:#reaching def
            counter = 0
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
                            if len(localTemp) >= 2:
                                if localTemp[0:2] == "if":
                                    instructs.append(localTemp)
                                    continue
                                else:
                                    instructs.append("d"+str(counter)+": "+localTemp)
                                    counter+=1
                                    continue
                            else:
                                instructs.append("d" + str(counter) + ": " + localTemp)
                                counter += 1
                                continue
                    else:
                        if len(localTemp) == 0:
                            continue
                        instructs.append("d" + str(counter) + ": " + localTemp)
                        counter+=1
                b.instructions = []
                b.instructions = instructs
        else:
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
        buildcfg.starter("c_out/"+inputFile[0:-1]+"dot", self.blocksOG)
        for i in range(0, len(self.blockSetId)):
            print(i, self.blockSetId[i].id)
        entryBlock = genbb.BasicBlock()
        entryBlock.id = "ENTRY"
        entryBlock.countVal = "ENTRY"
        exitBlock = genbb.BasicBlock()
        exitBlock.id = "EXIT"
        exitBlock.countVal = "EXIT"
        entryBlockObj = copy.deepcopy(entryBlock)
        entryBlockObj.connect = []
        entryBlockObj.connect.append(self.blockDict["BB001"])
        entryBlock.connect.append("BB001")
        exitBlockObj = copy.deepcopy(exitBlock)
        self.blockDict["ENTRY"] = entryBlockObj
        self.blockDict["EXIT"] = exitBlockObj
        self.blockSetId.insert(0, entryBlock)
        for i in range(0, len(self.blockSetId)):
            print(10,self.blockSetId[i].id)
        self.blockSetObj.insert(0, entryBlock)
        for i in range(0, len(self.blockSetId)):
            print(11,self.blockSetId[i].id, self.blockSetId[i].connect)
        self.blockSetId.append(exitBlock)
        self.blockSetObj.append(exitBlock)
        for i in range(0, len(self.blockSetId)):
            print(self.blockSetId[i].id)
        for i in range(0, len(self.blockSetId)):
            b = self.blockSetId[i]
            if type(b) == str:
                continue
            else:
                self.add_cfg_node(b.id, b.connect)

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
    # if type(currBlock) == str:
    #     visitedEmptyBlocks[currBlock] = currBlock
    #     return currBlock
    # if len(currBlock.instructions) == 0:
    #     if len(currBlock.connect) > 0:
    #         locCon = None
    #         if visitedEmptyBlocks.__contains__(currBlock.connect[0]):
    #             locCon = visitedEmptyBlocks[currBlock.connect[0]]
    #         else:
    #             locCon = removeEmptyBlocks(currBlock.connect[0])
    #         visitedEmptyBlocks[currBlock] = currBlock.connect[0]
    #     else:
    #         visitedEmptyBlocks[currBlock] = currBlock
    #     return visitedEmptyBlocks[currBlock]
    # for i in range(0, len(currBlock.connect)):
    #     con = currBlock.connect[i]
    #     resCon = None
    #     if visitedEmptyBlocks.__contains__(con):
    #         resCon = visitedEmptyBlocks[con]
    #     else:
    #         resCon = removeEmptyBlocks(con)
    #     currBlock.connect[i] = resCon
    # visitedEmptyBlocks[currBlock] = currBlock
    # return currBlock




if __name__ == "__main__":
    print (" ")
'''
 # assume this program 
    #  def minimum(xh, y):
    #      x = xh * 2
    #
    #      if x > y:
    #         r = y
    #      else:
    #         r = x
    # 
    #      return r

    # build the CFG first
    x.add_cfg_node("ENTRY", ["B001"])
    x.add_cfg_node("B001", ["B002", "B003"])
    x.add_cfg_node("B002", ["B004"])
    x.add_cfg_node("B003", ["B004"])
    x.add_cfg_node("B004", ["EXIT"])
    x.add_cfg_node("EXIT", [])

    # then add data flow facts
    x.add_node_facts("ENTRY", "IN", [])
    x.add_node_facts("ENTRY", "OUT", []) 
    
    x.add_node_facts("B001", "IN", [])
    x.add_node_facts("B001", "GEN", ["x"])
    x.add_node_facts("B001", "KILL", ["x"])
    x.add_node_facts("B001", "OUT", ["x"])

    x.add_node_facts("B002", "IN", ["x"])
    x.add_node_facts("B002", "GEN", ["r"])
    x.add_node_facts("B002", "KILL", ["r"])
    x.add_node_facts("B002", "OUT", ["x", "r"])

    x.add_node_facts("B003", "IN", ["x"])
    x.add_node_facts("B003", "GEN", ["r"])
    x.add_node_facts("B003", "KILL", ["r"])
    x.add_node_facts("B003", "OUT", ["x", "r"])

    x.add_node_facts("B004", "IN", ["x", "r"])
    x.add_node_facts("B004", "GEN", [])
    x.add_node_facts("B004", "KILL", [])
    x.add_node_facts("B004", "OUT", ["x", "r"])

    x.add_node_facts("EXIT", "IN", ["x", "r"])
    x.add_node_facts("EXIT", "GEN", [])
    x.add_node_facts("EXIT", "KILL", [])
    x.add_node_facts("EXIT", "OUT", ["x", "r"])

    x.write("output.yaml")


int minimum(int x, int y){
int t0 = x;
int t1 = y;
int t2;
int t3 = t0;
int t4 = t1;
if( t3 > t4 ) goto L_0;
goto L_1;
L_0:;
t2 = t1;
goto L_2;
L_1:;
t2 = t0;
L_2:;
return t2;
}



'''
