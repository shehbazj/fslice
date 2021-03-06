import sys
import os
import re
from collections import defaultdict
from nonTypedBlocks import getSourceTaintInICMPs

"""
 Collect all taints involved in ICMP Operations
 ICMP Format:
 ICMPBlock 6684 229 1

 Check if Taints are values -> discard
 Check if Taints are Objects -> get the blocks taint that the object refers to.
 Check usage of that block Taint. If it is being used for "A", "M", The taint cannot be a FIELD.
 Check usage of that block taint. If it is a POINTER, the block cannot be a FIELD.
 if a taint is a pointer, it is not a field taint.
 if a taint is being compared to a non-constant, the taint is not a field taint.
 if a taint is being used for A, it is not a field constant.
 if a taint is being compared to another taint that has A or M, it is not a field constant.

"""

traceFile="/tmp/testfs.py"

def getAnnotation(taint):
    with open(traceFile, 'r') as f:
        for line in f:
            if taint+'=' in line:
                if '=V' in line:
                    return 'V'
                elif '=M' in line:
                    return 'M'
                elif '=O' in line:
                    return 'O'
                else: 
                    return 'X'

def getTaintLine(taint):
    with open(traceFile, 'r') as f:
        for line in f:
            if taint+'=' in line:
                return line

#concatinates block number and offsets in the form of a map key
# key = b92.20-21-22-23
# offsetStr = 20.21.22.23

def generateKeyAndOffsetString(taintLine,blockNumber):
    blockTaint = taintLine.split('(')[1].split(',')[0].split('t')[1]
    offsets = re.findall("\[(.+?)\]",taintLine)
    key = 'b'+str(blockNumber)+'.'+'-'.join(offsets)
    offsetStr = '-'.join(offsets)
    return (key,offsetStr)

# check that offset is not a pointer. if it is a pointer (i.e. a key in MapAll)
# do not select the entity as a map.
# sample taint line
# t6513=O(t6511,6513,t6511[21],t6511[22],t6511[23],t6511[24])

def offsetIsPointer(blockField, blockNumber, MapAll,offsetStr,key):
    if key in MapAll:
        return True
    return False

def comparedTaintIsConstant(taint):
    if taint is None:
        print "ERROR - ICMP value corrupted"
        return
    taintVal = 't'+taint+'='
    with open(traceFile, 'r') as f:
        inputlines = f.readlines()
        for lines in inputlines:
            if taintVal in lines:
                if 'V' in lines:
                    return True
    return False

def taintDoesBinaryOperation(taint):
    taintVal = 't'+taint
    with open(traceFile, 'r') as f:
        inputlines = f.readlines()
        for lines in inputlines:
            if taintVal+',' in lines or taintVal+'=' in lines:
                #print taintVal, lines
                if 'A' in lines:
                    #print taintVal , lines
                    return True
    #print "taint ", taintVal, " does not have 'A' operation"
    return False

#ICMPBlock 509 64 35 # 509 - taint number of compared instruction, 64 block number 35 taint of comparator value

#def taintInBacktrace(taint):
    

def getFieldAnnotation(MapAll, taintBlockMap):
    # get all source block taints that are used as ICMP instructions while reaching
    # to their destinaition block
    referredSrcTaints = getSourceTaintInICMPs(taintBlockMap)
    blockField = defaultdict(list)
    with open(traceFile, 'r') as f:
        input_lines = f.readlines()
        icmp_lines = list()
        for lines in input_lines:
            if 'ICMP' in lines:
                icmp_lines.append(lines)
                taint_Blocknumber_Comparatortaint = lines.split(' ')
                # select ICMP lines that have all 3 values - taint, block number and fieldtaint
                if len(taint_Blocknumber_Comparatortaint) == 4:
                    taint = taint_Blocknumber_Comparatortaint[1]
                    blockNumber = taint_Blocknumber_Comparatortaint[2]
                    comparatorTaint = taint_Blocknumber_Comparatortaint[3].rstrip()
                    annotation = getAnnotation(taint)
                    #if taint being compared is that of a constant V or a memory allocation M, it cannot be  
                    #field value. the annotation that has field value is only an O object or a B block
                    if annotation == 'M' or annotation == 'V':
                        continue
                    # if taint is not being referred between source and destination block, 
                    # do not process this as a potential field annotation
                    if taint not in referredSrcTaints:
                        continue
                    elif annotation == 'O':
                        taintLine = getTaintLine(taint)
                        #print "TAINT LINE IS ",taintLine
                        (key, offsetStr) = generateKeyAndOffsetString(taintLine,blockNumber)
                        #print "KEY ", key, " OFFSETSTR", offsetStr
                        # check if offset is pointer
                        if offsetIsPointer(blockField, blockNumber,MapAll,offsetStr,key) is False:
                        # check if taint being compared to is a constant value
                            if comparedTaintIsConstant(comparatorTaint) is True:
                                if taintDoesBinaryOperation(taint) is False:
                                    if offsetStr not in blockField[blockNumber]:
                                        blockField[blockNumber].append(offsetStr)
    return blockField

if __name__ == "__main__":
    
    mapAll = defaultdict(list)
    print "calling : getFieldAnnotation"
    blockField = getFieldAnnotation(mapAll, taintBlockMap)
    for blockNum,Offset in blockField.items():
        print blockNum,Offset
    if mapAll is None:
        print "** WARNING ** mapAll was not initialized, offsetStr may be Null\
             please call the function from generateAnnotations.py"
