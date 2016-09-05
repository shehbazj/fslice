import argparse
from collections import defaultdict
import re

BLOCK_SIZE = 64
blockContents = defaultdict(list)


def evaluateWritePath(traceFile, writeTaint, prevReadTaint, blockNumber, zeroConstantTaint):
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

    global blockContents

    if blockNumber not in blockContents:
        blockContents[int(blockNumber)] = ['U'] * BLOCK_SIZE

    with open(traceFile, 'r') as f:
        input_lines = f.readlines()
        # print writeTaint
        count = 0
#        continuous_writes = False
        for line in input_lines:
            if (writeTaint + '[') in line:
#                continuous_writes = True
                # print(writeTaint, line)
                offset = int(line.split('[')[1].split(']')[0])
                leftTaint = line.split('=')[0].split('[')[0]
                rightTaint = line.split('=')[1].split('[')[0]

                if rightTaint == zeroConstantTaint: # assigning zero
                    blockContents[int(blockNumber)][int(offset)] = 'Z'
                elif prevReadTaint is None:
                    blockContents[int(blockNumber)][int(offset)] = 'A'
                    count+=1
                elif rightTaint != prevReadTaint:
                    blockContents[int(blockNumber)][int(offset)] = 'A'
                    count+=1
#            else:
#                if continuous_writes == True:
#                    print blockNumber, count
#                continuous_writes = False

def removePadding():
    """
    Start from last content byte and eliminate all 'Z' marked bytes. If there
    are non trailing bytes marked as 'Z', mark them as allocated ('A').
    """
    global blockContents

    for block,contentList in blockContents.items():
        content = BLOCK_SIZE - 1
        padding = True

	if blockContents[block][content] == 'Z':
	    while blockContents[block][content] == 'Z' and content >= 0:
	        if padding and blockContents[block][content] == 'Z':
	            blockContents[block][content] = 'U'
	        else:
	            padding = False
	            if blockContents[block][content] == 'Z':
	                blockContents[block][content] = 'A'
	        content -= 1


def evaluateReadPath(traceFile, readTaint, blockNumber):
    """
    Only a few structures are accessed during the read path. They are not modified.
    Check if any byte inside a block is accessed as an Object. If yes, mark that offset
    as allocated ('A').

    :param traceFile:
    :param readTaint:
    :param blockNumber:
    """
    global blockContents

    offsetList = set()
    with open(traceFile, 'r') as f:
        input_lines = f.readlines()
        for line in input_lines:
            if readTaint+'[' in line and 'O' in line:
                TaintAndOffsetList = re.findall(readTaint + r'\[\d+\]', line)
                for items in TaintAndOffsetList:
                    # offsetList.extend(re.findall('\[(\d+)\]', items))
                    offsetList |= set(re.findall('\[(\d+)\]', items))
		    for offset in offsetList:
			if blockNumber not in blockContents:
				blockContents[int(blockNumber)][int(offset)] = 'A'

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
"""


def getAllocatedBytes(traceFile):
    global blockContents

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
#    print("Taint assigned for V(0): {}".format(zeroConstantTaint))

    # print block_lines
    for blockLine in block_lines:
        blockNum = re.findall(r'B\(' + re.escape(str(BLOCK_SIZE)) + '\,(\d+)\,', blockLine)
        taint = re.findall(r'(t\d+)=', blockLine)
        readOrWrite = re.findall(r'\ (r|w)', blockLine)
        # print(taint, blockNum, readOrWrite)
        blockTaintDict[int(blockNum[0])].append(taint[0] + '.' + readOrWrite[0])
        # print blockNum.group()

    for blockNumber,TaintList in blockTaintDict.items():
        prevTaint = None
        for taint in TaintList:
            if 'r' in taint: # taint for block in read path
                prevTaint = taint.split('.')[0]
            else: # taint for block in write path
                writeTaint = taint.split('.')[0]
                # if prevTaint != None:
                evaluateWritePath(traceFile, writeTaint, prevTaint, blockNumber, zeroConstantTaint)
                removePadding()
                # print blockNumber,blockContents[blockNumber].count('A')

    for blockNumber,TaintList in blockTaintDict.items():
        for taint in TaintList:
            if 'r' in taint:
                readTaint = taint.split('.')[0]
                evaluateReadPath(traceFile, readTaint, blockNumber)

    return blockContents

# input - taint file
# output - dictionary of <blockId, contentList> where contentList contains either 'A' or 'U'
# depending on whether the byte is allocated or unallocated.
if __name__ == "__main__":
    """ Main Start """

    parser = argparse.ArgumentParser()
    parser.add_argument('trace_file', type=str, help="The path to the trace file.")
    args = parser.parse_args()
    blockContents = getAllocatedBytes(args.trace_file)

    for key, values in blockContents.items():
        print key, values.count('A')
