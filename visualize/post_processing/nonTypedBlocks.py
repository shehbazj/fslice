# gives all blocks whose sub elements have not been accessed
# usage ./nonTypedBlocks.py operations blockTaints TaintBlockFile
# usage ./nonTypedBlocks.py operations blockTaints TaintBlockFile

import sys
import os
from returnBlockNoAndOffset import returnBlockNoAndOffset
from collections import defaultdict

def usage():
	print "usage ./nonTypedBlocks.py operations blockTaints TaintBlockFile"
	sys.exit()

if __name__ == "__main__":
    """ Main Start """

if len(sys.argv) != 4:
	usage()

# Right hand side of all taint assignment operations
operations = list(open(sys.argv[1],'r'))
operations = map(lambda s: s.strip(), operations)

# taint number of blocks
blockTaints = list(open(sys.argv[2],'r'))
blockTaints = map(lambda s: s.strip(), blockTaints)

# hash <taint - blockNum>
taintBlockMap = {}

# dictionary of the form <blockNum - t9,t500 > each block may have multiple taints
 
blockTaintDictionary = defaultdict(list)
with open(sys.argv[3],'r') as f:
	for line in f:
		(taint, block) = line.split()
		taintBlockMap[taint] = block
		blockTaintDictionary[block].append(taint)	

#print blockTaintDictionary

#print operations 
#print blockTaints 
#print taintBlockMap

# list of blocks that have Types i.e. their substructure elements have been accessed on RHS
typedBlockTaintList = [] 
nonTypedBlocks = []

# for each block taint, see if it occurs on RHS as taint[]. Also, see if its alias taints i.e.
# other taints of the same block number have taint[]. If such taint exists, add it to typedBlockTaintList.
# if block taints' sub structure elements are not accessed, or its alias elements are not accessed, 
# type it as NON_TYPED Block and print it
for taint in blockTaints:
	blockTaintStr=taint+'['
	isNonTypedBlock=True
	for op in operations:
		if blockTaintStr in op:
			isNonTypedBlock=False
			break
	block=taintBlockMap[taint]
	if isNonTypedBlock is True:
		#print "BLocks taint dict: ",blockTaintDictionary[block]," Typed block taint list: ",typedBlockTaintList 
		if list(set(blockTaintDictionary[block]) & set(typedBlockTaintList)) == []:
			#print "no common elements ",blockTaintDictionary[block]," ",typedBlockTaintList
			#print taint,taintBlockMap[taint] # Non Typed Block
			nonTypedBlocks.append(taintBlockMap[taint])
	else:
		typedBlockTaintList.append(taint)
		if block in nonTypedBlocks:
			nonTypedBlocks.remove(block)
		#print "Added new element ",taint," for block ",taintBlockMap[taint]," List is now",typedBlockTaintList

print "NON-TYPED OR UNINITIALIZED BLOCKS"
print list(sorted(set(nonTypedBlocks)))

def getBackTraceBlock(block, taintList):
	print "In getBackTraceBlock ",block,taintList
	#table = [{}]
	srcBlockOffsetMap = {}
	for taint in taintList:
		(srcBlockNo,offsetList) = returnBlockNoAndOffset(taint, '/tmp/testfs.py')
		if srcBlockNo is not None:
			srcBlockOffsetMap[srcBlockNo]=offsetList
			#table.append(srcBlockOffsetMap)
	return srcBlockOffsetMap# (srcBlockNo,table)


#typedBlocks = []
#print "TYPED BLOCKS"
#for taint in typedBlockTaintList:
#	typedBlocks.append(taintBlockMap[taint])
#
#print list(sorted(set(typedBlocks)))

# Now we find the backtrace of each blocks taint to obtain 

for destinationBlock in blockTaintDictionary:
	print "============"
	#print block, blockTaintDictionary[block]
	sourceBlockAndOffset = getBackTraceBlock(destinationBlock, blockTaintDictionary[destinationBlock])
	print destinationBlock,sourceBlockAndOffset 
#	for key in sourceBlockAndOffset:
#		print key,srcBlock[key]
