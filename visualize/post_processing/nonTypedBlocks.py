# gives all blocks whose sub elements have not been accessed
# usage ./nonTypedBlocks.py operations blockTaints TaintBlockFile
# usage ./nonTypedBlocks.py operations blockTaints TaintBlockFile

import sys
import os
from returnBlockNoAndOffset import returnBlockNoAndOffset
from forwardTraceContainsBlock import forwardTraceContainsBlock
from forwardTraceReferencesSubelements import forwardTraceReferencesSubelements
from collections import defaultdict
from pprint import pprint

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
	#print "In getBackTraceBlock ",block,taintList
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

def deriveType(taintBlockMap,blockTaintDictionary):
	for taint in taintBlockMap:
		isNonTypedBlock=True
		block=taintBlockMap[taint]
		if forwardTraceContainsBlock(taint,'/tmp/testfs.py') is False: # not Typed
		#if forwardTraceReferencesSubelements(taint,'/tmp/testfs.py') is False: # not Typed
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
	return (typedBlocks,nonTypedBlocks)	

def getBlocksWithSubStructuresAccessed(nonTypedBlocks,taintBlockMap,blockTaintDictionary):
	subStructReferedBlocks = []
	typedBlocks = []
	for taint in taintBlockMap:
		if taintBlockMap[taint] not in nonTypedBlocks:
			continue
		isNonTypedBlock=True
		block=taintBlockMap[taint]
		#if forwardTraceContainsBlock(taint,'/tmp/testfs.py') is False: # not Typed
		if forwardTraceReferencesSubelements(taint,'/tmp/testfs.py') is False: # not Typed
			if list(set(blockTaintDictionary[block]) & set(typedBlockTaintList)) == []:
				#print "Non Typed Block",block # Non Typed Block
				subStructReferedBlocks.append(block)
			else:	
				#print "Typed Block", block, taint
				typedBlocks.append(block)
				typedBlockTaintList.append(taint)
				while block in subStructReferedBlocks:
					subStructReferedBlocks.remove(block)
		else:
			print "Sub Struct Refered From ",taint,block," leading to another block"
			typedBlocks.append(block)
			typedBlockTaintList.append(taint)
			while block in subStructReferedBlocks:
				subStructReferedBlocks.remove(block)
	return typedBlocks

if __name__ == "__main__":
	""" Main Start """

#	if len(sys.argv) != 4:
#		usage()
#	
	operations = loadOperations(sys.argv[1])
	blockTaints = loadBlockTaints(sys.argv[2])
#	
	taintBlockMap = {} # hash <taint - blockNum>
	MAP = {}
	SRC1 = defaultdict(list) 
	SRC2 = defaultdict(list) 
	blockTaintDictionary = defaultdict(list) # <BNum - t1,t2,t3>
#	
	(taintBlockMap,blockTaintDictionary) = initDataStructures(sys.argv[3])

	# list of blocks that have Types i.e. their substructure elements have been accessed on RHS
	typedBlockTaintList = [] 
	nonTypedBlocks = []
	typedBlocks = []

#	# derive Non-Typed Blocks	
#	(typedBlocks, nonTypedBlocks) = deriveType(taintBlockMap, blockTaintDictionary)
#	print "NON-TYPED OR UNINITIALIZED BLOCKS"
#	nonTypedBlocks = list(sorted(set(nonTypedBlocks)))
#	print nonTypedBlocks
#	
#	print "TYPED BLOCKS"
#	typedBlocks = list(sorted(set(typedBlocks)))
#	print typedBlocks
#
#	subStructureAccessedBlocks = getBlocksWithSubStructuresAccessed(nonTypedBlocks,taintBlockMap, blockTaintDictionary)
#	subStructureAccessedBlocks = list(sorted(set(subStructureAccessedBlocks)))
#	subStructureAccessedBlocks = [x for x in subStructureAccessedBlocks if x not in typedBlocks] 
#	print "SUB-STRUCTURE ACCESSED BLOCKS"
#	print subStructureAccessedBlocks
#
#	unknownBlocks = [x for x in nonTypedBlocks if x not in subStructureAccessedBlocks]
#	print "NON-TYPED BLOCKS"
#	print unknownBlocks 
#
#
#	
#	# get source block and offset for each destination block  
#	# generate backTraces

	nonTypedBlocks = ['1', '10', '11', '12', '13', '14', '15', '16', '17', '18', '19', '197', '198', '199', '2', '20', '200', '202', '203', '204', '205', '206', '207', '208', '209', '21', '210', '212', '213', '214', '215', '216', '217', '218', '219', '22', '220', '221', '222', '223', '224', '225', '226', '227', '228', '23', '230', '231', '232', '233', '234', '24', '25', '26', '27', '28', '29', '3', '30', '31', '32', '33', '34', '35', '36', '37', '38', '39', '4', '40', '41', '42', '43', '44', '45', '46', '47', '48', '49', '5', '50', '51', '52', '53', '54', '55', '56', '57', '58', '59', '6', '60', '61', '62', '63', '7', '8', '9'] 
	typedBlocks = ['0', '192', '193', '194', '195', '196', '201', '211', '229', '64', '65', '66', '67'] 

	for destinationBlock in nonTypedBlocks:
		#print "============"
		#print block, blockTaintDictionary[block]
		srcBlockOffsetMap = getBackTraceBlock(destinationBlock, blockTaintDictionary[destinationBlock])
		#print destinationBlock,srcBlockOffsetMap 
		for blk in srcBlockOffsetMap:
			key = 'b'+str(blk)+'.'+str('-'.join(srcBlockOffsetMap[blk]))
			SRC1[key].append(destinationBlock)
			#print key,'==>',SRC[key]
	#	for key in sourceBlockAndOffset:
	#		print key,srcBlock[key]

	print "NON-TYPED BLOCK SRC PTRS"
	for index in SRC1:
		SRC1[index] = list(sorted(set(SRC1[index])))
		print index,SRC1[index]

	for block in typedBlocks:
		#print "============"
		srcBlockOffsetMap = getBackTraceBlock(block, blockTaintDictionary[block])
		#print block,srcBlockOffsetMap
		for blk in srcBlockOffsetMap:
			key = 'b'+str(blk)+'.'+str('-'.join(srcBlockOffsetMap[blk]))
			SRC2[key].append(block)
			#print key,'==>',SRC[key]

	print "TYPED BLOCK SRC PTRS"
	for index in SRC2:
		SRC2[index] = list(sorted(set(SRC2[index])))
		print index,SRC2[index]
