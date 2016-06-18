# gives all blocks whose sub elements have not been accessed
# usage ./nonTypedBlocks.py operations blockTaints TaintBlockFile

import sys
import os
from returnBlockNoAndOffset import returnBlockNoAndOffset
from forwardTraceContainsBlock import forwardTraceContainsBlock
from forwardTraceReferencesSubelements import forwardTraceReferencesSubelements
from getAllocatedBytes import getAllocatedBytes
from collections import defaultdict
from pprint import pprint

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
templates = defaultdict(map)

# blockDPMap - contains contents of block as Data or Pointer Fields
blockDPMap = defaultdict(list)

# blockDSMap - map from block number to the internal basic structure
blockDSMap = defaultdict(map)

# blockPTMap - map from block Number to Partial Type
# for rules on partial Typing, see createPartialTypes()
blockPTMap = {}

PTCount = 0

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

# looks for forwardTraces of each block taint. If some offset of a block is being used
# for referring to another block, it is classified as typedBlock. Otherwise it is classified
# as nonTypedBlock (i.e. data block)

def getTypeInfo(taintBlockMap,blockTaintDictionary):
	for taint in taintBlockMap:
		isNonTypedBlock=True
		block=taintBlockMap[taint]
		if forwardTraceContainsBlock(taint,'/tmp/testfs.py') is False: # not Typed
			if list(set(blockTaintDictionary[block]) & set(typedBlockTaintList)) == []:
				nonTypedBlocks.append(block)
			else:	
				typedBlocks.append(block)
				typedBlockTaintList.append(taint)
				while block in nonTypedBlocks:
					nonTypedBlocks.remove(block)
		else:
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
			typedBlocks.append(block)
			typedBlockTaintList.append(taint)
			while block in subStructReferedBlocks:
				subStructReferedBlocks.remove(block)
	return typedBlocks

def blockExists(key,MapTtoT):
	blockNum = key.split('.')[0].split('b')[1]
	for key in MapTtoT:
		if blockNum in key.lower():
			return True
	return False
		
# penultimate blocks are those blocks which only have non-typed blocks (leaf blocks) in the tree as destination pointers
# if any blocks contain both non-typed blocks and typed-blocks, they are not considered penultimate blocks.

def getPenultimateBlocks(MapTtoT, MapTtoNT):
	penultimateBlockMap = {}
	for key in MapTtoNT:
		if blockExists(key,MapTtoT) is False:
			penultimateBlockMap[key] = MapTtoNT[key]
	return penultimateBlockMap

# refresh block map list, after some blocks have been typed, delete them
def removeTypedBlocks(penultimateBlockMap,MapTtoT,MapTtoNT):
	MapTtoNT = { k : v for k, v in MapTtoNT.items() if k not in penultimateBlockMap}
	return (penultimateBlockMap,MapTtoT,MapTtoNT)	
	
# returns Map of type {DX : [B0,B1,B2]}
def createLabelMap():
	global blockLabelMap
	print "createLabelMap"
	labelBlockMap = defaultdict(list)
	for block,label in blockLabelMap.items():
		labelBlockMap[label].append(block)
	print "labelBlockMap---"
	#for label,blockList in labelBlockMap.items():
	#	print label,blockList
	return labelBlockMap			
	
def derivePattern(block):
	global blockContentMap
	pattern = {}
	index = 0

	if block in blockContentMap:
		contents = blockContentMap[block]
	else:
		return pattern
	while True:
		start_idx = index
		value = contents[index]
		while (index < (len(contents))) and (value in contents[index]):
			index+=1
		pattern[str(start_idx) + '-' + str(index - 1)] = value
		if index >= (len(contents) -1):
			break

	print "block ",block," pattern ",pattern
	return pattern

# this function will partition same labeled blocks or join different labeled blocks based
# on rules. It updates corresponding entries in blockLabelMap and blockContentMap

def clusterTypes():
	global blockLabelMap
	global blockContentMap
	global templates
	labelBlockMap = createLabelMap()
	for label,blockList in labelBlockMap.items():
		for block in blockList:
			templates[block] = derivePattern(block)
#	for label,blockList in labelBlockMap.items():
#		cluster(blockList)	

# creates a label for a block which is 1 larger than the maximum label in the block content
	
def labelBlocks():
	global blockLabelMap
	global blockContentMap
	for k,v in blockContentMap.items():
		labelList = []
		for element in v:
			if 'D' in element:
				labelList.append(element)
		if labelList:	# found block pointers
				# TODO currently dumb algorithm, categorizes all blocks based on 
				# contents of the blocks. need to bring more intelligence - based
				# on start offset etc.
			label = max(labelList).split('D')[1]
			if k not in blockLabelMap:
				blockLabelMap[k] = 'D'+str(int(label)+1)
			else:
				print "WARNING: Label Needs to be Updated!!!"
		else:	# no block pointers found
			if k not in blockLabelMap:
				blockLabelMap[k] = 'D0'

# fill blockContentMap with types
# from Map, detect the source block and offsets. From destination, check for the maximum label
# among destination blocks, assign 1 higher label to source block.

def createTemplate(Map):
	global blockContentMap
	ptrType = ''
	srcPtrType = 'D1'
	for k,v in Map.items():
		blockNum = k.split('.')[0].split('b')[1]
		if blockNum not in blockContentMap:
			blockContentMap[blockNum] = ['U']*blockSize
			if not ptrType:
				ptrType = 'D0'
		else:
			if not [s for s in blockContentMap[blockNum] if 'D' in s]:
				if not ptrType:
					ptrType = 'D0'
			else:
				if not ptrType:
					ptrType = max([s for s in blockContentMap[blockNum] if 'D' in s])
					srcPtrType = 'D'+str(int(ptrType.split('D')[1])+1)

		offset = k.split('.')[1]
		offsetList = offset.split('-')
		#print "createTemplate => blockNum ",blockNum
		if blockNum not in blockLabelMap:
			blockLabelMap[blockNum] = srcPtrType
		for off in offsetList:
			for destBlock in v:
				if destBlock in blockLabelMap: # if multiple data labels are pointed to by src offset,
								# choose largest label and assign it to blockContentMap
					ptrType = blockLabelMap[destBlock]
			blockContentMap[blockNum][int(off)] = ptrType

#	for block in blockContentMap:
#		print block,blockContentMap[block]
	
# for all leaf blocks, initialize blockContentMap and blockLabelMap
# blockContentMap contains each block Number -> { D0, U, U }
# where D0 means pointer to block of type D0. U stands for unused field
# all destination blocks in MapTtoNT are data blocks. Mark them as D0
# blockLabelMap is a map from block Number -> label {D0, D1, D2}

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
			
def getSourcePointerMap(destinationblockList,MapTtoT, MapTtoNT):
	sourcePointerMap = defaultdict(list)
	for block in destinationblockList:
		blockNum = block.split('b')[1]
		for k,v in MapTtoT.items():
			if blockNum in v:
				sourcePointerMap[k] = blockNum
		for k,v in MapTtoNT.items():
			if blockNum in v:
				sourcePointerMap[k] = blockNum
	return sourcePointerMap

def getSourceBlocks(sourcePointerMap):
	sourceBlockList = []
	for block in sourcePointerMap:
		blockNum = block.split('.')[0].split('b')[1]
		sourceBlockList.append(blockNum)
	return sourceBlockList

def scanMap(sourceBlockList,Map):
	nextLevelList = []
	ptrType = 'D0'
	print "scanMap"
	for block in sourceBlockList:
		print "block - ",block
		for srcBlk, destBlockList in Map.items():
			srcBlock = srcBlk.split('.')[0].split('b')[1]
			if srcBlock == block:
				print "srcBlock", srcBlock ," is block ",block
				for destBlk in destBlockList:
					if destBlk not in blockLabelMap:
						# check if it exists in blockContentMap
						if destBlk not in blockContentMap:
							nextLevelList.append(block)
						else:
							createTemplate({srcBlk : destBlk})	
					else:
						createTemplate({srcBlk : destBlockList})
						labelBlocks()
	print "nextLevelList",nextLevelList
	return sorted(set(nextLevelList))	

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
		

# if all destination blocks of source block list are typed, type the source
# block list as well. Return list of blocks that were not typed. These will
# be typed in the next iteration.

def assignLevel(sourceBlockList,MapTtoT, MapTtoNT): 
	nextLevelList = []
	nextLevelList = scanMap(sourceBlockList,MapTtoT)
	nextLevelList.append(scanMap(sourceBlockList,MapTtoNT))
	if not nextLevelList:	
		return []
	return (nextLevelList)


def getNextLevelBlocks(blockList,MapTtoT, MapTtoNT):
	#print blockList
	global blockLabelMap
	sourcePointerMap = getSourcePointerMap(blockList,MapTtoT, MapTtoNT)
	sourceBlockList = getSourceBlocks(sourcePointerMap)
	sourceBlockList = sorted(set(sourceBlockList))
	print "source Block List ",sourceBlockList
	typedBlockList = assignLevel(sourceBlockList,MapTtoT,MapTtoNT) 	
	for block in blockLabelMap:
		print block, blockLabelMap[block]
	return []

def extractSrcBlocks(Map):
	srcBlockList = []
	for src in Map:
		blockNum = src.split('.')[0]
		if blockNum not in srcBlockList:
			srcBlockList.append(blockNum)
	#print "srcBlockList",srcBlockList
	return srcBlockList

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
					#print 'blockNumber',blockNumber,'offset' ,i+structSize , 'length of list', len(blockDPMap[blockNumber])
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
	value = 0
	for block in blockDPMap:
		length = min( blockAllocatedContents[block].__len__() , blockDPMap[block].__len__()) 
		for i in range(length):
			if blockDPMap[block][i] == 'U' and blockAllocatedContents[block][i] == 'A':
				blockDPMap[block][i] = 'D'
	#		else:
	#			print block, '[',i , '] = ', blockDPMap[block][i], blockAllocatedContents[block][i]
	#print block, "DP" , blockDPMap[block]
	#print block, "Allocated" , blockAllocatedContents[block]
	
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
	setBlockDPMap(MapTtoNT)
	setBlockDPMap(MapTtoT)
	markLeafBlocks(MapTtoNT) # required to set all leaf Blocks with 'U'
	blockAllocatedContents = getAllocatedBytes('/tmp/testfs.py')
#	for block,contents in blockAllocatedContents.items():
#		print block, contents
	markUnallocatedBytes()

# Input - 2 maps [Typed Blocks=>Typed Blocks] [Typed Blocks => Non Typed Blocks]
# The backward clustering algorithm

# blocks can either be Typed, Partially Typed, Partially Typed and Temporarily 
# labelled, Not-Typed

# -- Typed - all pointer types in a block are known. 
# -- Partially Typed - all or some pointers point to blocks which are not yet typed.
# -- Partially Typed and Temporarily labelled - 2 blocks having same temporary label
#    are same if their non-typed pointers eventually turn out to be of the same type.
# -- Not-Typed - None of the pointers are typed yet

# Backward Taint Algorithm

# 1. mark Leaf Blocks
# 2. mark penultimate blocks (blocks pointing to leaf blocks)
# 3. keep marking next level until you reach blocks where pointers
#    point to non-typed blocks. mark these blocks as partially typed.
# 4. at the end of each iteration, compare blocks according to classification rules **.
#    if 2 partially typed blocks pattern match assuming non-typed pointers are of the 
#    same type, the blocks are given a Temporary Label. 
# 5. At the end of each iteration, if
#    a) the source blocks of all temporary labeled blocks is same **, give the source 
#    blocks a temporary label.
#    b) If all destination blocks of all blocks with the same temporary label were typed
#    in previous iteration, check if the destination label is the same **.	
#       i) if destination label of all destination blocks is same, change temporary label 
#	to permanent label.
#       ii) if destination label is not the same, split temporary label such that 
#	new permanent labels are formed, where all blocks of 1 label have the same 
# 	structure.
#	propagate this to other source temporary labels, (i.e. split other source 
#	temporary labels) such that the source labels now point to same typed blocks

#    ** refer clustering algorithm for definition of same typed blocks
	
def classifyBlocks(MapTtoT,MapTtoNT):
	markLeafBlocks(MapTtoNT)
	labelBlocks()
	# blocks that exist in MapTtoNT and not in MapTtoT
	penultimateBlockMap = getPenultimateBlocks(MapTtoT, MapTtoNT)
	#(penultimateBlockMap,MapTtoT, MapTtoNT) = removeTypedBlocks(penultimateBlockMap, MapTtoT, MapTtoNT)
	createTemplate(penultimateBlockMap)
	labelBlocks()

	## TODO nextLevel Blocks should ideally contain all blocks and not just the blocks above the src block...
	nextLevelBlocks = extractSrcBlocks(penultimateBlockMap)
	done = False
	while nextLevelBlocks or done is False:
		nextLevelBlocks = getNextLevelBlocks(nextLevelBlocks,MapTtoT, MapTtoNT)
		done = True
	clusterTypes()
	labelBlocks()
	return (penultimateBlockMap, MapTtoT, MapTtoNT)

if __name__ == "__main__":
	""" Main Start """

	if len(sys.argv) != 4:
		usage()
	
	operations = loadOperations(sys.argv[1])
	blockTaints = loadBlockTaints(sys.argv[2])

	taintBlockMap = {} # hash <taint - blockNum>
	MAP = {}
	MapTtoNT = defaultdict(list) 
	MapTtoT = defaultdict(list) 
	blockTaintDictionary = defaultdict(list) # <BNum - t1,t2,t3>
	
	(taintBlockMap,blockTaintDictionary) = initDataStructures(sys.argv[3])

	# list of blocks that have Types i.e. their substructure elements have been accessed on RHS
	typedBlockTaintList = [] 
	nonTypedBlocks = []
	typedBlocks = []

	# derive Non-Typed Blocks	
	(typedBlocks, nonTypedBlocks) = getTypeInfo(taintBlockMap, blockTaintDictionary)
	print "NON-TYPED OR UNINITIALIZED BLOCKS"
	nonTypedBlocks = list(sorted(set(nonTypedBlocks)))
	print nonTypedBlocks
	
	print "TYPED BLOCKS"
	typedBlocks = list(sorted(set(typedBlocks)))
	print typedBlocks

	subStructureAccessedBlocks = getBlocksWithSubStructuresAccessed(nonTypedBlocks,taintBlockMap, blockTaintDictionary)
	subStructureAccessedBlocks = list(sorted(set(subStructureAccessedBlocks)))
	subStructureAccessedBlocks = [x for x in subStructureAccessedBlocks if x not in typedBlocks] 
	print "SUB-STRUCTURE ACCESSED BLOCKS"
	print subStructureAccessedBlocks

	unknownBlocks = [x for x in nonTypedBlocks if x not in subStructureAccessedBlocks]
	print "NON-TYPED BLOCKS"
	print unknownBlocks 

	# get source block and offset for each destination block  
	# generate backTraces

	for destinationBlock in nonTypedBlocks:
		srcBlockOffsetMap = getSourceBlockandOffset(destinationBlock, blockTaintDictionary[destinationBlock])
		for blk in srcBlockOffsetMap:
			key = 'b'+str(blk)+'.'+str('-'.join(srcBlockOffsetMap[blk]))
			MapTtoNT[key].append(destinationBlock)

	for block in typedBlocks:
		srcBlockOffsetMap = getSourceBlockandOffset(block, blockTaintDictionary[block])
		for blk in srcBlockOffsetMap:
			key = 'b'+str(blk)+'.'+str('-'.join(srcBlockOffsetMap[blk]))
			MapTtoT[key].append(block)

	print "TYPED BLOCK SRC PTRS"
	for index in MapTtoT:
		MapTtoT[index] = list(sorted(set(MapTtoT[index])))
		print index,MapTtoT[index]

	createBlockDPMap()
	#for k,v in blockDPMap.items():
	#	print k,' => ' , v.count('D') + v.count ('P')
	#	print k,' => ' , v
#
	createBlockDSMap()
	createPartialTypes()
	for blockNumber, template in blockDSMap.items():
		print "-------------------"
		print blockNumber, template

	print 'PARTIAL TYPE LIST'
	global PTCount
	for Type in range(PTCount+1):
		print 'TYPE', Type
		for block in blockPTMap:
			if blockPTMap[block] == Type:
				print block,','
	
#	(penultimateBlockMap,MapTtoT,MapTtoNT) = classifyBlocks(MapTtoT, MapTtoNT)
#	for block in sorted(penultimateBlockMap):
#		print block,penultimateBlockMap[block]
