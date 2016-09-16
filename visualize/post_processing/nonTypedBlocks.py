# gives all blocks whose sub elements have not been accessed
# usage ./nonTypedBlocks.py operations blockTaints TaintBlockFile

import sys
import os
from getSourceBlockNumberAndOffset import getSourceBlockNumberAndOffset
from forwardTraceContainsBlock import forwardTraceContainsBlock
from forwardTraceReferencesSubelements import forwardTraceReferencesSubelements
from getAllocatedBytes import getAllocatedBytes
from collections import defaultdict
from getSourceBlock import getSourceBlock
from getIntermediateICMPs import getIntermediateICMPs

traceFile = "/tmp/testfs.py"

blockSize = 64

# Map from Block Number => block contents which can be 'U' or 'D*',
# where D* is a label / type for a block.
blockContentMap = defaultdict(list)

# Map from Block Number => block contents which can be 'A' or 'U',
# where 'A' stands for allocated, and 'U' for unallocated
blockAllocatedContents = defaultdict(list)

# Map from Block Number => blockLabel, where block label is 'D0,D1,D2'...
blockLabelMap = {}

# condensed version of blockContentMap. Contains Block and a template of the
# form B10 = {0-3 => D0, 4-20 => D1, 21-63 => U}
#templates = defaultdict(map)

# blockDPMap - contains contents of block as Data or Pointer Fields
blockDPMap = defaultdict(list)

# blockDSMap - map from block number to the internal basic structure
blockDSMap = defaultdict(map)

# blockPTMap - map from block Number to Partial Type
# for rules on partial Typing, see createPartialTypes()
blockPTMap = {}

# partial type Counter. for any new type found, PTCount is incremented by 1
PTCount = 0

# blockDestToSrcMap - map from destination block to source block(s)
blockDestToSrcMap = defaultdict(list)

# blockCTMap - map from block Number to Complete Type
blockCTMap = {}

taintBlockMap = {} # hash <taint - blockNum>
MapTtoNT = defaultdict(list) 
MapTtoT = defaultdict(list) 
blockTaintDictionary = defaultdict(list) # <BNum - t1,t2,t3>
typedBlockTaintList = [] 
srcBlkTaintAsICMP = []
    
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

def getSourceBlockandOffset(block, taintList):
	#print "In getBackTraceBlock ",block,taintList
	#table = [{}]
	srcBlockOffsetMap = {}
	for taint in taintList:
		(srcBlockNo,offsetList) = getSourceBlockNumberAndOffset(taint, traceFile)
		if srcBlockNo is not None:
			srcBlockOffsetMap[srcBlockNo]=offsetList
			#table.append(srcBlockOffsetMap)
	return srcBlockOffsetMap# (srcBlockNo,table)

def initDataStructures(): # <tNo BlockNo>
        taintOffsetToBlock = defaultdict(list)
	with open(traceFile,'r') as f:
		for line in f:
                    blockStr = "B("+str(blockSize)+","
                    if blockStr in line:
                        taint = line.split("=")[0]
                        block = line.split(",")[1]
                        offsetTaint = line.split(",")[3].split('t')[1]
                        taintBlockMap[taint] = block
                        taintOffsetToBlock[offsetTaint] = block
                        blockTaintDictionary[block].append(taint)
	return (taintBlockMap, blockTaintDictionary, taintOffsetToBlock)

# taintOffsetToBlock is a map of taintOffset -> block

def getSourceDestinationBlocks(taintOffsetToBlock):
    srcDestBlockMap = defaultdict(list)
    for destOffsetTaint,destBlock in taintOffsetToBlock.items():
        srcBlock = getSourceBlock(destOffsetTaint,traceFile)
        if srcBlock is not None:
            if destBlock not in srcDestBlockMap[srcBlock]:
                srcDestBlockMap[srcBlock].append(destBlock)
    return srcDestBlockMap

# looks for forwardTraces of each block taint. If some offset of a block is being used
# for referring to another block, it is classified as typedBlock. Otherwise it is classified
# as nonTypedBlock (i.e. data block)

def getTypeInfo():
        print "Initializing Data Structures"
        typedBlocks = []
        nonTypedBlocks = []
	(taintBlockMap,blockTaintDictionary,taintOffsetToBlock) = initDataStructures()
	for taint in taintBlockMap:
		isNonTypedBlock=True
		block=taintBlockMap[taint]
		if forwardTraceContainsBlock(taint, traceFile ) is False: # not Typed
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
	#		print "FWD trace from ",taint,block," leading to another block"
			typedBlocks.append(block)
			typedBlockTaintList.append(taint)
			while block in nonTypedBlocks:
				nonTypedBlocks.remove(block)
	return (list(sorted(set(typedBlocks))), list(sorted(set(nonTypedBlocks))), taintBlockMap)

def markLeafBlocks(MapTtoNT):
	global blockDPMap
	global blockContentMap
	global blockLabelMap
	for k,destBlockList in MapTtoNT.items():
		#print "leaf Blocks ",destBlockList
		for destinationBlock in destBlockList:
			blockContentMap[destinationBlock] = ['U']*blockSize
			blockLabelMap[destinationBlock] = 'D0'
			blockDPMap[int(destinationBlock)] = ['U']*blockSize 
			
# Helper function for getPartialType()
# matches b1 and b2 contents after discarding 'U'

def matchWithoutUnallocatedBytes(block1 , block2):
	global blockAllocatedContents
	if len(blockDSMap[block1]) != len(blockDSMap[block2]):
		return False
	for i in range(len(blockDSMap[block1])):
		if blockDSMap[block1][i] == 'U' or blockDSMap[block2][i] == 'U':
			continue
		if blockDSMap[block1][i] != blockDSMap[block2][i]:
			return False
	return True

# Helper function for getPartialType()
# isSubStructure(block1, block2) checks if block1 can be obtained from
# block2 repeated multiple times.

def isSubStructure(block1, block2):
	global blockDSMap
	b1length = len(blockDSMap[block1])
	b2length = len(blockDSMap[block2])
	
	if b1length == 0 or b2length == 0:
		return False	

	if b1length % b2length == 0:
		numSubStructures = b1length / b2length
		smallerStructure = blockDSMap[block2]
		largerStructure = blockDSMap[block1]
	elif b2length % b1length == 0:
		numSubStructures = b2length / b1length
		smallerStructure = blockDSMap[block1]
		largerStructure = blockDSMap[block2]
	else:
		return False
	
	if smallerStructure * numSubStructures == largerStructure:
		return True
	else:
		return False

# Helper function for getPartialTypes()
# checks if type exists for a block, if not, creates new type, assigns it
# to both blockToBeTyped and block

def assignType(blockToBeTyped, block):
	global blockPTMap
	global PTCount
	if block in blockPTMap:
		blockPTMap[blockToBeTyped] = blockPTMap[block]
	else:
		PTCount += 1
		blockPTMap[block] = PTCount
		blockPTMap[blockToBeTyped] = PTCount

# Helper function for createPartialTypes()
# checks matching rules and returns type

def getPartialType(blockToBeTyped):
	global blockAllocatedContents
	global blockPTMap
	global PTCount 
	for block, contents in blockDSMap.items():
		if blockToBeTyped in blockPTMap: # block already has a partial Type
			return #blockPTMap[blockToBeTyped]

		if block == blockToBeTyped:	
			# skip self
			continue

		if blockDSMap[block] == blockDSMap[blockToBeTyped]:
			# exact match
			#print "MATCH: ",block, blockToBeTyped
			#return assignType(block)
			assignType(blockToBeTyped, block)
			return	
			
			# check if one block is a substructure of another block
		if isSubStructure(block, blockToBeTyped) == True:
			assignType(blockToBeTyped,block)
			return
		# TODO for blocks with 'U', we should try and replace 'U' with 'D'
		# and 'P' and see if a template can be created. This should be done
		# 'before' the classification starts. currently we are doing exact
		# match of 2 lists by avoiding 'U's
	
		if blockDSMap[block].count('U') !=0 or \
			blockDSMap[blockToBeTyped].count('U') !=0:
			# check if there is a match after discarding unallocated bytes
			if matchWithoutUnallocatedBytes(block, blockToBeTyped) == True:
				assignType(blockToBeTyped,block)
				return
	
		# no match, create and return new Type
	PTCount += 1
	blockPTMap[blockToBeTyped] = PTCount	

# from a blockDSMap, create partial types, i.e. cluster blocks based on
# information of bytes - wheather they are 'D', 'P' or 'U' (data, pointer
# or unallocated).

# RULE SET:
# 1)	if there are only 'P' in a DS Map, group them with other 'P*' blocks
# 2)	if there are only 'D' in a DS Map, group them with other 'D*' blocks
# 3)	if there is an exact match between Data Structures, group them together
# 4)	if a block is a subset of another block, group them together
# 5)	if a block contains unallocated bytes, we first mark them as 'P', and 
# 	see if the block matches any other block. Next, try marking 'U' as 'D'
# 	and match the blocks.
# 6)	if none of the above rules match, create new partialType entry


def createPartialTypes():
	global blockAllocatedContents
	global blockPTMap
	
	for block, contents in blockDSMap.items():
		pointerCount = contents.count('P') + contents.count('P*')
		unknownCount = contents.count('U')
		dataCount = contents.count('D') + contents.count('D*')
		#print block, pointerCount, unknownCount, dataCount
		if pointerCount == 0 and unknownCount == 0: # all Data
			if dataCount != 0:
				blockDSMap[block] = ['D*']
		elif dataCount == 0 and unknownCount == 0: # all pointer
			if pointerCount != 0:
				blockDSMap[block] = ['P*']
		getPartialType(block)
	#	print "ASSIGNED ", block, "TYPE : " , blockPTMap[block]
		
# Input - key of the form srcBlock.Offset1-Offset2-Offset3-Offset4
# Output - (srcBlockNumber , {Offset1, Offset2, Offset3, Offset4} )
# eg key b201.15-16-17-18

def getBlockAndOffset(k):
	blockNum = int(k.split('.')[0].split('b')[1])
	offsetList = k.split('.')[1].split('-')
	intOffsetList = []
	for offset in offsetList:
		intOffsetList.append(int(offset))
	return (blockNum, intOffsetList)		

# Input - list of blockContents {D,P, U...} of block Size
# Output - List of all ptr Indexes - For blockContents as { DDDDPPDDDDPP }
# the pointer index list is {4,10}

def getPtrIndex(blockContents):
	ptrList = []
	index = 0
	while index < blockSize:
		if blockContents[index] is 'U' or blockContents[index] is 'D':
			index+=1
			continue
		if blockContents[index] is 'P':
			ptrList.append(index)
			while index < blockSize and blockContents[index] is 'P':
				index+=1
	return ptrList


# checks if 'D' or 'P' element in blockContents is variable. if the element
# is constant, return the size of 'D' or 'P' field (i.e. number of consequitive
# bytes). If element is variable, return -1.

def elementIsVariable(element, blockContents):
        firstElementFieldSize = 0
        currentElementFieldSize = 0
        count = 0
        index = 0
        while index < len(blockContents):
                count = 0
                if blockContents[index] == element:
                        while index < len(blockContents) and blockContents[index] == element:
                                count += 1
                                index += 1
                        if firstElementFieldSize == 0:
                                firstElementFieldSize = count
                                continue
                        else:
                                currentElementFieldSize = count
                                if firstElementFieldSize != currentElementFieldSize:
                                        return -1
                index += 1
        return firstElementFieldSize
	
			
# helper Function for createBlockDSMap
# if number of pointers for all pointer clusters in a block
# are same, variable type is the 'D' the data field.
# if data field is constant, 'D' is constant and 'P' may be variable
# else, both D and P are variable.

# The last category might be a constant pointer field - with 
# pointer bytes uninitialized. Detecting a struct with uninitialized
# pointer fields as a constant sized field is not possible because
# we cannot know whether unallocated bytes are data or
# pointer fields.

def generateVariableStruct(blockContents):
        structure = []
        element = blockContents[0] # can be 'D' or 'P'
        count = elementIsVariable(element,blockContents)
        index = 0
        if count > 0: # element has constant size
                structure = [element] * count
                index = count # scan from next element
        else:  # variable list
                structure.append(element + '*')

        while index < len(blockContents): # get next elements size
                if blockContents[index] != element:
                        count = elementIsVariable(blockContents[index],blockContents)
                        if count > 0: # element has constant size
                                structure.extend( [blockContents[index]] * count)
                        else:
                                structure.append(blockContents[index] + '*')
                        return structure
                index+=1
        return structure

# create basic datastructures inside every block. 
# mapping: { blockNumber => { D,D,D,D,P,P,P,P }
# this represents the basic struct inside the block. We obtain the size of 
# a structure by finding the difference between start of two pointer clusters 
# within a block.
# A basic structure of a block may contain multiple pointer fields. In this case, we 
# re-create the structure when we look at destination blocks of pointer fields.
# this is done when we go bottom up and detect type of destination blocks
# See comparator() for comparision rules.

def createBlockDSMap():
	global blockDPMap
	global blockDSMap
	for blockNumber,blockContents in blockDPMap.items():
		startPtrIndexList = getPtrIndex(blockContents)		
		listSize = len(startPtrIndexList)
		if listSize is 0: # no pointers
				# remove trailing unallocated bytes
			index = len(blockDPMap[blockNumber]) -1
			while blockDPMap[blockNumber][index] == 'U' and index >=0:
				index -=1
			blockDSMap[blockNumber] = blockDPMap[blockNumber][0:index + 1]
		if listSize is 1: # 1 pointer
			# copy everything except trailing unallocated bytes marked 'U'
			index = len(blockDPMap[blockNumber])
			for byte in reversed(blockDPMap[blockNumber]):
				if byte == 'U':
					index-=1
				else: 
					break
			blockDSMap[blockNumber]	= blockDPMap[blockNumber][0:index]
		if listSize >= 2: # 2 or more pointers

			# see diff between pointer offsets. if the difference is constant,
			# struct has constant size, no variable elements.
			# if struct has variable size, check whether P field or D field is 
			# variable. 
			# If pointer field is variable, we place *P while typing blocks. 
			# If data field is variable, we place * after D

			firstPtr = startPtrIndexList[0]
			secondPtr = startPtrIndexList[1]
			structSize = secondPtr - firstPtr
			firstDiff = structSize
			index = 2
			variableField = False
			while index < len(startPtrIndexList):
				secondPtr = startPtrIndexList[index]
				firstPtr = startPtrIndexList[index - 1]
				nextDiff = secondPtr - firstPtr
				if firstDiff == nextDiff:
					index+=1
					continue
				else: # variable size structure detected
					variableField = True
					blockDSMap[blockNumber] = \
						generateVariableStruct(blockDPMap[blockNumber])
					break
			
			if variableField == False:	# check if data field is variable, by
						# checking if data field terminates and pointer
						# field starts after each structure inside block.
				for i in range(0 , len(blockDPMap[blockNumber]) - structSize, structSize):
					if blockDPMap[blockNumber][i+structSize - 1] != 'D':
						variableField = True
					if blockDPMap[blockNumber][i+structSize] != 'P':
						variableField = True
			if variableField == True:
				blockDSMap[blockNumber] = \
						generateVariableStruct(blockDPMap[blockNumber])

			if variableField == False:
				# choose structure from block having max number of pointers
				# there might be structure with sparse pointers. hence we 
				# go for structure with maximum number of pointers in a block
				# to reach nearer to typing.
				maxPtrCount = 0
				for i in range( 0, blockSize, structSize):
					structInstance = blockDPMap[blockNumber][i:i+structSize]
					ptrCount = structInstance.count('P');
					if ptrCount > maxPtrCount:
						maxPtrStructInstance = structInstance 
						maxPtrCount = ptrCount
				blockDSMap[blockNumber] = maxPtrStructInstance
				continue

# mark bytes in DP map which were marked 'U' (Unknown) as 'D' (Data) if they are marked
# 'A' (Allocated) in blockAllocatedContents 
			
def markUnallocatedBytes():
	global blockAllocatedContents
	global blockDPMap
	for block in blockDPMap:
		length = min( blockAllocatedContents[block].__len__() , blockDPMap[block].__len__()) 
		for i in range(length):
			if blockDPMap[block][i] == 'U' and blockAllocatedContents[block][i] == 'A':
				blockDPMap[block][i] = 'D'
	
# create a map of {blockNumber => { U , U , U , P , P , P }}
# where the list contains Block Size entries, each entry representing a byte
# where U stands for unassigned/unallocated byte. P stands for a pointer byte

def setBlockDPMap(Map):
	global blockDPMap
	for k,v in Map.items():
		(blockNumber, offsetList) = getBlockAndOffset(k)
		if blockNumber not in blockDPMap:
			blockDPMap[blockNumber] = ['U']*blockSize
		for offset in offsetList:
			blockDPMap[blockNumber][offset] = 'P'

def createBlockDPMap():
	global MapTtoNT
	global MapTtoT
	global blockAllocatedContents
        discardMap = defaultdict(list)
	setBlockDPMap(MapTtoNT)
	setBlockDPMap(MapTtoT)
	markLeafBlocks(MapTtoNT) # required to set all leaf Blocks with 'U'
	(blockAllocatedContents,discardMap) = getAllocatedBytes(traceFile)
#	for block,contents in blockAllocatedContents.items():
#		print block, contents
	markUnallocatedBytes()

# getRootBlock 
# TODO determine root block by looking at incoming edge count = 0

def getRootBlock():
	return 0

# search for root Type and assign it a new type, if its current type list contains other
# blocks. This is to specify a separate root type for the superblock.

def isolateRootType(root): 
	global PTCount
	global blockPTMap
	global blockCTMap
	rootType = blockPTMap[root]
	moreElements = False # more elements of same type as root
	for block, partialType in blockPTMap.items():
		if block == root:
			continue
		if partialType == rootType:
			moreElements = True
			break
	if moreElements == False:
		return rootType
	else:
		PTCount += 1
		blockCTMap[root] = PTCount
		del blockPTMap[root]
	return blockCTMap[root]

	
# data blocks are conventionally those blocks which do not have any source pointers from 
# them to other blocks. however there are other blocks (bitmap blocks) which do not have
# source pointers from them leading to other blocks. However, they do not have any parent
# other than the source block. we classify these blocks as metadata blocks and assign
# different types to each of the blocks. we can futher classify them as bitmap blocks based
# on access patterns (i.e. 1 byte gets accessed)

def isolateDataType(root):
	global PTCount
	global MapTtoNT
	global MapTtoT
	global blockPTMap

	prevPTCount = PTCount
	dataBlockList = []
	# get all blocks of type 'D*' from blockDSMap
	for block, dataStructure in blockDSMap.items():
		if dataStructure == ['D*']:
			dataBlockList.append(block)

	print "dataBlockList" , dataBlockList	
	
	for block in dataBlockList:
		sourceBlockList = []
		for src, dest in MapTtoNT.items():
			#print block, src,dest
			if str(block) in dest:
				sourceBlockList.append(int(src.split('.')[0].split('b')[1]))
		for src, dest in MapTtoT.items():
			#print block, src, dest
			if str(block) in dest:
				sourceBlockList.append(int(src.split('.')[0].split('b')[1]))
	
		print "BLOCK SrcBlockList:", block, sourceBlockList
		
		if root in sourceBlockList and len(sourceBlockList) == 1: 
			# the only source element is 0
			if PTCount == prevPTCount:
				PTCount+=1
			print "assigning block ",block, "type" , PTCount
			blockCTMap[block] = PTCount
			del blockPTMap[block]

	for block, dataStructure in blockDSMap.items():
		if dataStructure == ['D*'] and blockCTMap[block] <= prevPTCount:
			return blockPTMap[block]
	
# change pointer from 'P' to 'CP'X'' (complete pointer) or 'PP'X'' (partial pointer) 
# in all source blocks, where X is the type number of the destination blocks. return 
# all source blocks that got marked

def markSrcPointers(rootBlock, destinationBlocks):
	global blockDestToSrcMap 
	global blockDPMap
	global block

	srcBlockList = []

	for destBlock in destinationBlocks:
		if len(blockDestToSrcMap[destBlock]) > 1 and '0' not in blockDestToSrcMap[destBlock]:
			print "XXX: Multiple source pointers spotted"
			print destBlock, blockDestToSrcMap[destBlock]
	#		print "Terminating Algorithm"
	#		assert 0
		if destBlock in blockCTMap:
			destType = 'CP'+str(blockCTMap[destBlock])
		else:
			destType = 'PP'+str(blockPTMap[destBlock])
		
		for srcBlockAndOffset, content in MapTtoT.items():
			if str(destBlock) in content:
				srcBlock = srcBlockAndOffset.split(".")[0].split("b")[1]
				offsetList = srcBlockAndOffset.split(".")[1].split("-")
				if srcBlock == str(rootBlock):
					continue
				for offset in offsetList:
					if blockDPMap[int(srcBlock)][int(offset)] == 'P':
						blockDPMap[int(srcBlock)][int(offset)] = destType
					else:
						blockDPMap[int(srcBlock)][int(offset)] = \
							blockDPMap[int(srcBlock)][int(offset)] + '.' + \
							 str(destType)
				if srcBlock not in srcBlockList:
					srcBlockList.append(srcBlock)

		for srcBlockAndOffset, content in MapTtoNT.items():
			if str(destBlock) in content:
				srcBlock = srcBlockAndOffset.split(".")[0].split("b")[1]
				offsetList = srcBlockAndOffset.split(".")[1].split("-")
				if srcBlock == str(rootBlock):
					continue
				for offset in offsetList:
					if blockDPMap[int(srcBlock)][int(offset)] == 'P':
						blockDPMap[int(srcBlock)][int(offset)] = destType
					else:
						blockDPMap[int(srcBlock)][int(offset)] = \
							blockDPMap[int(srcBlock)][int(offset)] + '.' + \
							 str(destType)
				if srcBlock not in srcBlockList:
					srcBlockList.append(srcBlock)
	return srcBlockList


# check all blocks of type block have same pointer fields. If the pointer 'P' is assigned
# to any block, assign it 'PT'X'', where X is the partial pointer type to some other block
# if any of the blocks in that class do not match, create new type, assign new type to that
# block, assign all blocks that had destination blocks as that block a new type.
# if all blocks in the class of blocks have pointer of type CT'X', then assign them the same
# type, add them to blockCTMap

#def testType(block):
#	if block in blockCTMap: # block already completely typed
#		return
#
#	sameTypedBlocks = []
#	if block in blockCTMap: # block already has complete type
#		return	
#	else:
#		blockType = blockPTMap[block]
#	for block, PT in blockPTMap:
#		if PT == blockType:
#			sameTypedBlocks.append(block)
#	
#	for blocks in sameTypedBlocks:
#		if 'P' in blockDPMap[block]: # block needs to be assigned partial/complete Type
#						
#		else if 'PP' in blockDPMap[block]: # partial types in blockDPMap
#
#		else: # either all data blocks or CP blocks.. this block is also a complete type

# assign partial types - assigns PP'X' to all block contents replacing earlier 'P', where
# X is the partial type of the destination block
# uses partial type list and generates complete Type based on the type of pointers

def createCompleteType(rootType, dataType):
	destinationBlocks = []

#	First, assign all partial pointers to the block Contents
	
#	print "rootType", rootType, "dataType", dataType
	for block, pType in blockPTMap.items():
#		if pType == dataType:
#			print "block ", block, "PT Map Type", blockPTMap[block], "dataType", dataType
		destinationBlocks.append(block)
#		blockCTMap[block] = pType # data blocks assigned complete type
#		del blockPTMap[block]

#	print destinationBlocks
			
	#while blockCTMap != blockPTMap:
	sourceBlocks = markSrcPointers(0, destinationBlocks) # XXX remove 0 and replace with root block
	print "sourceBlocks = " , sourceBlocks
#	for srcBlock in sourceBlocks:
#		testType(srcBlock) 			

def generatePointerMaps(typedBlocks, nonTypedBlocks):
	for destinationBlock in nonTypedBlocks:
		srcBlockOffsetMap = getSourceBlockandOffset(destinationBlock, blockTaintDictionary[destinationBlock])
		for blk in srcBlockOffsetMap:
			key = 'b'+str(blk)+'.'+str('-'.join(srcBlockOffsetMap[blk]))
			MapTtoNT[key].append(destinationBlock)
			if blk not in blockDestToSrcMap[int(destinationBlock)]:
				blockDestToSrcMap[int(destinationBlock)].append(blk)

	for destinationBlock in typedBlocks:
		srcBlockOffsetMap = getSourceBlockandOffset(destinationBlock, blockTaintDictionary[destinationBlock])
		for blk in srcBlockOffsetMap:
			key = 'b'+str(blk)+'.'+str('-'.join(srcBlockOffsetMap[blk]))
			MapTtoT[key].append(destinationBlock)
			if blk not in blockDestToSrcMap[int(destinationBlock)]:
				blockDestToSrcMap[int(destinationBlock)].append(blk)
        return (MapTtoT, MapTtoNT)

# returns list of all source taints that are referred in ICMP instructions while approaching
# the destination taint.

def getSourceTaintInICMPs(taintBlockMap):
    # get all block taints.
    # get all blocks source block taints.
    # get all ICMP instructions, and their operator blocks between source and destination blocks.
    # if ICMP is present, get taint of the ICMP comparator instruction

    for taint, blocks in taintBlockMap.items():
#        print taint, blocks
        srcBlockTaint = getIntermediateICMPs(taint)
       # print srcBlockTaint
        if srcBlockTaint is not None:
            srcBlkTaintAsICMP.extend(srcBlockTaint)
    return list(set(srcBlkTaintAsICMP))
    

if __name__ == "__main__":
	""" Main Start """

	nonTypedBlocks = []
	typedBlocks = []

	print "derive Non-Typed and Typed Blocks"
	(typedBlocks, nonTypedBlocks, taintBlockMap) = getTypeInfo()
	print "NON-TYPED OR UNINITIALIZED BLOCKS"
	print nonTypedBlocks
	
	print "TYPED BLOCKS"
	print typedBlocks

	# get source block and offset for each destination block  
	# generate backTraces

        (MapTtoT, MapTtoNT) = generatePointerMaps(typedBlocks, nonTypedBlocks)

        srcBlkTaintAsICMP = getSourceTaintInICMPs(taintBlockMap)
        print "SRC Block Taint as ICMP = ",srcBlkTaintAsICMP

	print "MAP T to T"
	for index in MapTtoT:
		MapTtoT[index] = list(sorted(set(MapTtoT[index])))
		print index,MapTtoT[index]
        
        print "MAP T to NT"
        for index in MapTtoNT:
                MapTtoNT[index] = list(sorted(set(MapTtoNT[index])))
                print index,MapTtoNT[index]
