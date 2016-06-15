# input - taint file
# output - dictionary of <blockId, contentList> where contentList contains either 'A' or 'U'
# depending on whether the byte is allocated or unallocated.

import argparse
from collections import defaultdict
import re

# for all assignment operations of writeTaints, if prevReadTaint is not the value assigned,
# it is a newly allocated byte. other bytes remain unassigned in this write operation.
# return - list of 64 elements - either 'A' or 'U'

blockContents = defaultdict(list)

# for write path, compare all writes with previous read taints. If there are offsets where
# sub-element of a block is assigned a taint other than immediately predecessing read call,
# that byte was recently allocated.

def evaluateWritePath(traceFile,writeTaint, prevReadTaint,blockNumber):
	global blockContents 
	if blockNumber not in blockContents:
		blockContents[int(blockNumber)] = ['U'] * 64
	with open(traceFile, 'r') as f:
		input_lines = f.readlines()
#		print writeTaint
		for line in input_lines:
			if writeTaint+'[' in line:
#				print writeTaint,line
				offset = line.split('[')[1].split(']')[0]
				leftTaint = line.split('=')[0].split('[')[0]
				rightTaint = line.split('=')[1].split('[')[0]
				if rightTaint == 't1': # assiging zero 
					blockContents[int(blockNumber)][int(offset)] = 'Z'
				elif prevReadTaint == None:
					blockContents[int(blockNumber)][int(offset)] = 'A'
				elif rightTaint != prevReadTaint:
					blockContents[int(blockNumber)][int(offset)] = 'A'

# start from last content byte. eliminate all 'Z' marked bytes from the contents List
# if there are non trailing bytes marked 'Z', mark them as allocated.

def removePadding():
	global blockContents
	for block,contentList in blockContents.items():
		content = 63
		padding = True
		if blockContents[block][content] == 'Z':
			while blockContents[block][content] == 'Z' and content >= 0:
				if padding == True and blockContents[block][content] == 'Z':
					blockContents[block][content] = 'U'
				else:
					padding = False
					if blockContents[block][content] == 'Z':
						blockContents[block][content] = 'A'
				content -= 1
				

# few structures are only read during the read path. They are not modified.
# Check if any byte inside a block is accessed as an Object. If yes, mark that offset
# as allocated

def evaluateReadPath(traceFile,readTaint,blockNumber):
	global blockContents
	offsetList = []
	with open(traceFile, 'r') as f:
		input_lines = f.readlines()
		for line in input_lines:
			if readTaint+'[' in line and 'O' in line:
				TaintAndOffsetList = re.findall(readTaint+r'\[\d+\]',line)
				for items in TaintAndOffsetList:
					offsetList.extend(re.findall('\[(\d+)\]',items))
				for offset in offsetList:
					blockContents[int(blockNumber)][int(offset)] = 'A'				

# returns a map of Block == > {Contents}. where contents are either 'U' or 'A' depending
# on whether the offset is unallocated or allocated respectively.

def getAllocatedBytes(traceFile):

	global blockContents

	blockTaintDict = defaultdict(list)
	block_lines = []
	with open(traceFile, 'r') as f:
		input_lines = f.readlines()
		for line in input_lines:
			if 'B(' in line:
				block_lines.append(line)

#	print block_lines		
	for blockLine in block_lines:
		blockNum = re.findall(r'B\(64\,(\d+)\,',blockLine)
		taint = re.findall(r'(t\d+)=',blockLine)
		readOrWrite = re.findall(r'\ (r|w)',blockLine)
#		print taint, blockNum, readOrWrite
		blockTaintDict[int(blockNum[0])].append(taint[0]+'.'+readOrWrite[0])
#		print blockNum.group()
#		blockTaintDict[]
	
	for blockNumber,TaintList in blockTaintDict.items():
		prevTaint = None
		for taint in TaintList:
			if 'r' in taint:
				prevTaint = taint.split('.')[0]
			else: # write
				writeTaint = taint.split('.')[0]
			#	if prevTaint != None:
				evaluateWritePath(traceFile,writeTaint,prevTaint,blockNumber)
				removePadding()
			#	print blockNumber,blockContents[blockNumber].count('A')

	for blockNumber,TaintList in blockTaintDict.items():
		for taint in TaintList:
			if 'r' in taint:
				readTaint = taint.split('.')[0]
				evaluateReadPath(traceFile,readTaint,blockNumber)

#	for blockNumber in blockTaintDict:
#		print blockNumber,blockContents[blockNumber].count('A')

	return blockContents
#
#if __name__ == "__main__":
#	""" Main Start """
#
#       	parser = argparse.ArgumentParser()
#       	parser.add_argument('trace_file', type=str, help="The path to the trace file.")
#       	args = parser.parse_args()
#	blockContents = getAllocatedBytes(args.trace_file)
