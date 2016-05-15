# gives all blocks whose sub elements have not been accessed
# usage ./nonTypedBlocks.py operations blockTaints TaintBlockFile
# usage ./nonTypedBlocks.py operations blockTaints TaintBlockFile

import sys
import os
from returnBlockNoAndOffset import returnBlockNoAndOffset
from forwardTraceContainsBlock import forwardTraceContainsBlock
from collections import defaultdict

def usage():
	print "usage ./nonTypedBlocks.py operations blockTaints TaintBlockFile"
	sys.exit()

# Right hand side of all taint assignment operations
def loadOperations(operationsFile):
	operations = list(open(operationsFile,'r'))
	operations = map(lambda s: s.strip(), operations)
	return operations

# taint number of blocks
def loadBlockTaints(blockTaintFile):
	blockTaints = list(open(sys.argv[2],'r'))
	blockTaints = map(lambda s: s.strip(), blockTaints)
	return blockTaints

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

def initDataStructures(taintBlockFile): # <tNo BlockNo>
	with open(sys.argv[3],'r') as f:
		for line in f:
			(taint, block) = line.split()
			taintBlockMap[taint] = block
			blockTaintDictionary[block].append(taint)	
	return (taintBlockMap, blockTaintDictionary)

if __name__ == "__main__":
	""" Main Start """

	if len(sys.argv) != 4:
		usage()
	
	operations = loadOperations(sys.argv[1])
	blockTaints = loadBlockTaints(sys.argv[2])
	
	taintBlockMap = {} # hash <taint - blockNum>
	blockTaintDictionary = defaultdict(list) # <BNum - t1,t2,t3>
	
	(taintBlockMap,blockTaintDictionary) = initDataStructures(sys.argv[3])
	
	#print blockTaintDictionary
	#print operations 
	#print blockTaints 
	#print taintBlockMap
	
	# list of blocks that have Types i.e. their substructure elements have been accessed on RHS
	typedBlockTaintList = [] 
	nonTypedBlocks = []
	typedBlocks = []
	
	# for each block taint, see if it occurs on RHS as taint[]. Also, see if its alias taints i.e.
	# other taints of the same block number have taint[]. If such taint exists, add it to typedBlockTaintList.
	# if block taints' sub structure elements are not accessed, or its alias elements are not accessed, 
	# type it as NON_TYPED Block and print it
	for taint in taintBlockMap:
		isNonTypedBlock=True
		block=taintBlockMap[taint]
		if forwardTraceContainsBlock(taint,'/tmp/testfs.py') is False: # not Typed
			if list(set(blockTaintDictionary[block]) & set(typedBlockTaintList)) == []:
				#print "Non Typed Block",block # Non Typed Block
				nonTypedBlocks.append(block)
			else:	
				#print "Typed Block", block, taint
				typedBlocks.append(block)
				typedBlockTaintList.append(taint)
				while block in nonTypedBlocks:
					nonTypedBlocks.remove(block)
		else:
			print "FWD trace from ",taint,block," leading to another block"
			typedBlocks.append(block)
			typedBlockTaintList.append(taint)
			while block in nonTypedBlocks:
				nonTypedBlocks.remove(block)
	
	print "NON-TYPED OR UNINITIALIZED BLOCKS"
	nonTypedBlocks = list(sorted(set(nonTypedBlocks)))
	print nonTypedBlocks
	
	print "TYPED BLOCKS"
	typedBlocks = list(sorted(set(typedBlocks)))
	print typedBlocks
	
	
	#typedBlocks = []
	#print "TYPED BLOCKS"
	#for taint in typedBlockTaintList:
	#	typedBlocks.append(taintBlockMap[taint])
	#
	#print list(sorted(set(typedBlocks)))
	
	# Now we find the backtrace of each blocks taint to obtain 
	
	##for destinationBlock in blockTaintDictionary:
	#for destinationBlock in nonTypedBlocks:
	#	print "============"
	#	#print block, blockTaintDictionary[block]
	#	sourceBlockAndOffset = getBackTraceBlock(destinationBlock, blockTaintDictionary[destinationBlock])
	#	print destinationBlock,sourceBlockAndOffset 
	##	for key in sourceBlockAndOffset:
	##		print key,srcBlock[key]
