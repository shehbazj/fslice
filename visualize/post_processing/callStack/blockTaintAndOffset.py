#! /usr/bin/python

# gives us block number, taint of a block write operation, and the offset range that was written on that particular write

import argparse
from collections import defaultdict
import re

BLOCK_SIZE = 64
blockContents = defaultdict(list)
blockIntervalSet = defaultdict(list)
blockAllocationCountSet = defaultdict(list)

def insertTaintAndOffset(writeTaint, startOffset, endOffset, blockTaintStructOffset):
    if writeTaint not in blockTaintStructOffset:
        blockTaintStructOffset[writeTaint] = str(startOffset)+'-'+str(endOffset)
    else:
        prevStartOffset = blockTaintStructOffset[writeTaint].split('-')[0]
        prevEndOffset = blockTaintStructOffset[writeTaint].split('-')[1]
        blockTaintStructOffset[writeTaint] = str(prevStartOffset)+'-'+str(endOffset)
    return blockTaintStructOffset

def getSection(myList):
    intervalList = list()
    startOffset = myList[0]
    for i in range(1,len(myList)):
        if myList[i] - myList[i-1] == 1:
            continue
        else:
           # print startOffset, myList[i-1]
            intervalList.append(str(startOffset)+'-'+str(myList[i-1]))
            startOffset = myList[i]
    intervalList.append(str(startOffset)+'-'+str(myList[len(myList)-1]))
    return intervalList

def evaluateWritePath(traceFile, writeTaint, prevReadTaint, blockNumber, zeroConstantTaint, blockTaintStructOffset):
    """
    for write path, compare all writes with previous read taints. If there are offsets where
    sub-element of a block is assigned a taint other than immediately preceding read call,
    that byte was recently allocated. other bytes remain unassigned in this write operation.

    :param traceFile:
    :param writeTaint:
    :param prevReadTaint:
    :param blockNumber:
    :param zeroConstantTaint:
    :return: list consisting of BLOCK_SIZE elements; either 'A' or 'U'.
    """

    blockContents = ['U'] * BLOCK_SIZE
    global blockIntervalSet
    global blockAllocationCountSet

    with open(traceFile, 'r') as f:
        input_lines = f.readlines()
        # print writeTaint
        count = 0
        offsets = defaultdict(list)
        offset = -1
        continuous_writes = False
        for line in input_lines:
            if (writeTaint + '[') in line:
                continuous_writes = True
                # print(writeTaint, line)
                offset = int(line.split('[')[1].split(']')[0])
                leftTaint = line.split('=')[0].split('[')[0]
                rightTaint = line.split('=')[1].split('[')[0]

                if rightTaint == zeroConstantTaint: # assigning zero
                    blockContents[int(offset)] = 'Z'
                elif prevReadTaint is None:
                    blockContents[int(offset)] = rightTaint 
                    count+=1
                    offsets[int(blockNumber)].append(offset)
                elif rightTaint != prevReadTaint:
                    blockContents[int(offset)] = rightTaint
                    count+=1
                    offsets[int(blockNumber)].append(offset)
            else:
                if continuous_writes == True:
                    blockAllocationCountSet[blockNumber].append(str(count))
                    #print blockAllocationCountSet[blockNumber]
                    if len(offsets[int(blockNumber)]) != 0:
                        blockIntervalSet[blockNumber].extend(getSection(offsets[int(blockNumber)]))
                continuous_writes = False
    # block contents contains the new taints assigned to it. We need a count on individual
    # new taints assigned to each block. each new bunch of taints (except 'Z') corresponds
    # to a new structure
    
    index = 0
    prev_byte = blockContents[index]
    index+=1
    startOffset = 0

    while (index < BLOCK_SIZE):
        if (blockContents[index] != prev_byte):
            endOffset = index - 1
            if prev_byte != 'Z' and prev_byte != 'U':
                #print blockNumber, writeTaint , prev_byte , startOffset, endOffset
                blockTaintStructOffset = insertTaintAndOffset(writeTaint, startOffset, endOffset, blockTaintStructOffset)
            prev_byte = blockContents[index]
            startOffset = index
        index+=1
    endOffset = BLOCK_SIZE - 1
    if prev_byte != 'Z' and prev_byte != 'U':
        #print blockNumber, writeTaint, prev_byte , startOffset , endOffset
        blockTaintStructOffset = insertTaintAndOffset(writeTaint, startOffset, endOffset,blockTaintStructOffset)

"""
1.  Create list of all block_lines of the form B() # r or B() # w where r and w specify read 
    and write path respectively.
2.  Create a blockTaintDict for each block => {taint1 read, taint2 write , ...}
3.  Iterate over block_lines:
    a) Process write Path
    Iterate through each blocks' taint list.
        -> if the previous taint is read, keep track of that taint in prevTaint variable
        -> else record the taint as writeTaint. call evaluateWritePath
    b) Process read Path
        call evaluateReadPath

    return blockContents (marked 'A' or 'Z' or 'U') 
    and blockIntervalSet -> map of block => { list of write intervals }
    and blockAllocationCountSet -> map of block => { list of write sizes }
"""

def blockTaintAndOffset(traceFile):
    global blockContents
    global blockIntervalSet
    taintBlockMap = {}
    blockTaintStructOffset = {}

    blockTaintDict = defaultdict(list)
    zeroConstantTaint = None

    block_lines = []
    with open(traceFile, 'r') as f:
        input_lines = f.readlines()
        for line in input_lines:
            if 'B(' in line:
                block_lines.append(line)
            elif 'V(0' in line:
                zeroConstantTaint = re.findall(r'(t\d+)=', line)[0]

    assert zeroConstantTaint

    for blockLine in block_lines:
        blockNum = re.findall(r'B\(' + re.escape(str(BLOCK_SIZE)) + '\,(\d+)\,', blockLine)
        taint = re.findall(r'(t\d+)=', blockLine)
        readOrWrite = re.findall(r'\ (r|w)', blockLine)
        # print(taint, blockNum, readOrWrite)
        blockTaintDict[int(blockNum[0])].append(taint[0] + '.' + readOrWrite[0])
        taintBlockMap[taint[0]] = blockNum[0]
        # print blockNum.group()

    for blockNumber,TaintList in blockTaintDict.items():
        prevTaint = None
        for taint in TaintList:
            if 'r' in taint: # taint for block in read path
                prevTaint = taint.split('.')[0]
            else: # taint for block in write path
                writeTaint = taint.split('.')[0]
                # if prevTaint != None:
                evaluateWritePath(traceFile, writeTaint, prevTaint, blockNumber, zeroConstantTaint, blockTaintStructOffset)
                # print blockNumber,blockContents[blockNumber].count('A')
    return (taintBlockMap, blockTaintStructOffset)

# input - taint file
# output - dictionary of <blockId, contentList> where contentList contains either 'A' or 'U'
# depending on whether the byte is allocated or unallocated.
if __name__ == "__main__":
    """ Main Start """

    taintBlockMap = {}
    blockTaintStructOffset = {}
    parser = argparse.ArgumentParser()
    parser.add_argument('trace_file', type=str, help="The path to the trace file.")
    args = parser.parse_args()
    (taintBlockMap, blockTaintStructOffset) = blockTaintAndOffset(args.trace_file)

    for taint, offset in blockTaintStructOffset.items():
        print taintBlockMap[taint], taint, offset
