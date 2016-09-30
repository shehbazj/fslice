#!/usr/bin/python

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
from collections import defaultdict
from getAllocatedBytes import getAllocatedBytes
from nonTypedBlocks import getTypeInfo
from nonTypedBlocks import generatePointerMaps
from getFieldAnnotation import getFieldAnnotation

traceFile = "/tmp/testfs.py"

FSStructMap = defaultdict(list)

"""
Prints each block content in the form block Number, offset , size
Input:
    blockFStruct : block = > { count1, count 2...}
    blockContents : block => {'A',...'Z',...,'U'}
    nonTypedBlocks : list of all block numbers that do not contain pointers
    typedBlocks : list of all block numbers that contain pointers
"""

def printFSStructSizes(blockIntervalSet, blockAllocationCountSet, nonTypedBlocks, typedBlocks, MapAll):
    for block, items in blockIntervalSet.items():
        print 'BLOCK :' , block
        print 'FSSTRUCT : ', blockIntervalSet[block], ' COUNT : ', blockAllocationCountSet[block]
        for srcBlock, destBlock in MapAll.items():
            if 'b'+str(block)+'.' in srcBlock:
                print 'POINTER ', srcBlock, 'DEST BLOCK(S) ',destBlock
                if set(destBlock) < set(nonTypedBlocks):
                    print 'TYPE : DATA_POINTER'
                else:
                    print 'TYPE : METADATA_POINTER'
        if str(block) in fieldAnnotations and fieldAnnotations[str(block)]:
            print 'FIELD ',fieldAnnotations[str(block)]

def createFSStructs(blockIntervalSet, blockAllocationCountSet, nonTypedBlocks, typedBlocks, MapAll):
    # block Interval Set: ['0-3', '4-7', '8-11', '12-15', '16-19', '20-23', '24-27', '28-31', '32-35', '36-39', '40-43', '44-47', '48-51']
    # block Allocation Count Set: ['4', '4', '4', '4', '4', '4', '4', '4', '4', '4', '4', '4', '4']
        
    for block, items in blockIntervalSet.items():
        for pos in range(0, len(items)):
            offsetInterval = blockIntervalSet[block][pos]
            start = offsetInterval.split('-')[0]
            end = offsetInterval.split('-')[1]
            key = str(block) + '-' + start + '-' + end
            structureSize = int(end) - int(start) + 1
            FSStruct = ['D'] * int(structureSize)
            FSStructMap[key] = FSStruct

    keylist = FSStructMap.keys()
    keylist.sort()    
    for key in keylist:
        print key, '-' , FSStructMap[key]

                                    
def removeDuplicates(dupMap):
    for key,value in dupMap.items():
        dupMap[key] = set(dupMap[key])
    return dupMap

if __name__ == "__main__":
    """ Main Start """

    if os.path.isfile(traceFile) is 0:
        print "Did not find /tmp/testfs.py. did you run ./init.sh? "
        exit

    nonTypedBlocks = []
    typedBlocks = []
    taintBlockMap = {}
        
    #print "processing getAllocatedBytes"
    (blockContents, blockIntervalSet, blockAllocationCountSet) = getAllocatedBytes(traceFile)

    #blockIntervalSet = removeDuplicates(blockIntervalSet)

    print "processing get Type Info"
    (typedBlocks,nonTypedBlocks,taintBlockMap) = getTypeInfo()
    print "get Maps"
    (MapTtoT, MapTtoNT) = generatePointerMaps(typedBlocks,nonTypedBlocks)
    print "get Field Annotations"
    MapAll = dict(MapTtoT.items() + MapTtoNT.items())
    fieldAnnotations = getFieldAnnotation(MapAll, taintBlockMap)

    #fieldAnnotations = removeDuplicates(fieldAnnotations)

    printFSStructSizes(blockIntervalSet, blockAllocationCountSet ,nonTypedBlocks,typedBlocks, MapAll)
    createFSStructs(blockIntervalSet, blockAllocationCountSet, nonTypedBlocks, typedBlocks, MapAll)
