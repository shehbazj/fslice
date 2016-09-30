import argparse
import re
from collections import defaultdict
from blockTaintAndOffset import blockTaintAndOffset

trace_file = "/tmp/testfs.py"

def classifyBlocks(stackMap):
    taintBlockMap = {}
    blockTaintStructOffset = {}
    print "Using default trace file at /tmp/testfs.py"
    (taintBlockMap,blockTaintStructOffset) = blockTaintAndOffset(trace_file)

    #for taint, offset in blockTaintStructOffset.items():
    #    print taintBlockMap[taint], taint, offset

    for stack, taintList in stackMap.items():
        print stack
        for taint in set(taintList):
            if taint in taintBlockMap and taint in blockTaintStructOffset: 
                print taintBlockMap[taint], blockTaintStructOffset[taint], taint
            else:
                print taint , " not tracked!"

if __name__ == "__main__":
    """ Main Start """

    stackMap = defaultdict(list)

    with open("blockTrace.tmp", 'r') as f:
        
        input_lines = f.readlines()
        for line in input_lines:
            if "read_blocks" in line: # do not add read_blocks call
                stackTrace = None
                continue 
            elif "write_blocks" in line: # write_blocks stack trace
                stackTrace = line
            else:
                if stackTrace is not None: # dont keep read_blocks
                    stackMap[stackTrace].append(line.strip('\n'))

    classifyBlocks(stackMap)
