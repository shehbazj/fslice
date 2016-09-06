""" 

Automate annotation generation

The script takes a trace file as an input and generates annotations

a) block number - fsstruct - size and offset
b) block number - pointer - size and offset
c) block number - field
d) pointer "when" clause
e) type all fsstructs - a) based on size b) based on pointer type c) based on weather field is present or not d) control flow execution
f) determine vectors
g) determine fsconst [OPTIONAL]

"""

import os
from getAllocatedBytes import getAllocatedBytes
from nonTypedBlocks import getTypeInfo

traceFile = "/tmp/testfs.py"

"""
Prints each block content in the form block Number, offset , size
Input:
    blockFStruct : block = > { count1, count 2...}
    blockContents : block => {'A',...'Z',...,'U'}
    nonTypedBlocks : list of all block numbers that do not contain pointers
    typedBlocks : list of all block numbers that contain pointers
"""

def printFSStructSizes(blockIntervalSet, blockAllocationCountSet, nonTypedBlocks, typedBlocks):
    for block, items in blockIntervalSet.items():
        print 'BLOCK :' , block
        print 'FSSTRUCT : ', blockIntervalSet[block], ' COUNT : ', blockAllocationCountSet[block]
        if str(block) in nonTypedBlocks:
            print 'DATA'
        else:
            print 'METADATA'


if __name__ == "__main__":
    """ Main Start """

    if os.path.isfile(traceFile) is 0:
        print "Did not find /tmp/testfs.py. did you run ./init.sh? "
        exit

    nonTypedBlocks = []
    typedBlocks = []

    print "processing getAllocatedBytes"
    (blockContents, blockIntervalSet, blockAllocationCountSet) = getAllocatedBytes(traceFile)
    (typedBlocks,nonTypedBlocks) = getTypeInfo()
    printFSStructSizes(blockIntervalSet, blockAllocationCountSet ,nonTypedBlocks,typedBlocks)
