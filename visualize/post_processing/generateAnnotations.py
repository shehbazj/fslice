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
from getAllocatedBytes import getAllocatedBytes
from nonTypedBlocks import getTypeInfo
from nonTypedBlocks import generatePointerMaps
from getFieldAnnotation import getFieldAnnotation

traceFile = "/tmp/testfs.py"

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
            if 'b'+str(block) in srcBlock:
                print 'POINTER ', srcBlock, 'DEST BLOCK(S) ',destBlock
                if set(destBlock) < set(nonTypedBlocks):
                    print 'TYPE : DATA_POINTER'
                else:
                    print 'TYPE : METADATA_POINTER'
            if str(block) in fieldAnnotations and fieldAnnotations[str(block)]:
                print 'FIELD ',fieldAnnotations[str(block)]

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
        
    #print "processing getAllocatedBytes"
    (blockContents, blockIntervalSet, blockAllocationCountSet) = getAllocatedBytes(traceFile)

    blockIntervalSet = removeDuplicates(blockIntervalSet)

    (typedBlocks,nonTypedBlocks) = getTypeInfo()
    (MapTtoT, MapTtoNT) = generatePointerMaps(typedBlocks,nonTypedBlocks)
    print "MapTtoNT:=>"
    for key, value in MapTtoNT.items():
        print key,value

    print "MapToT:=>"
    for key,value in MapTtoT.items():
        print key,value

    print "MapAll:=>"
    MapAll = dict(MapTtoT.items() + MapTtoNT.items())
    for key,items in MapAll.items():
        print key, items
    fieldAnnotations = getFieldAnnotation(MapAll)    

    fieldAnnotations = removeDuplicates(fieldAnnotations)

    printFSStructSizes(blockIntervalSet, blockAllocationCountSet ,nonTypedBlocks,typedBlocks, MapAll)