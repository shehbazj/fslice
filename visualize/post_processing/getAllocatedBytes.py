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

def getAllocatedBytes(traceFile,writeTaint, prevReadTaint,blockNumber):
	global blockContents 
	if blockNumber not in blockContents:
		blockContents[blockNumber] = ['U'] * 64
	with open(traceFile, 'r') as f:
		input_lines = f.readlines()
#		print writeTaint
		for line in input_lines:
			if writeTaint+'[' in line:
#				print writeTaint,line
				offset = line.split('[')[1].split(']')[0]
				leftTaint = line.split('=')[0].split('[')[0]
				rightTaint = line.split('=')[1].split('[')[0]
				if prevReadTaint == None:
					blockContents[blockNumber][int(offset)] = 'A'
				elif rightTaint != prevReadTaint:
					blockContents[blockNumber][int(offset)] = 'A'

if __name__ == "__main__":
	""" Main Start """
	global blockContents
	parser = argparse.ArgumentParser()
	parser.add_argument('trace_file', type=str, help="The path to the trace file.")
	args = parser.parse_args()

	blockTaintDict = defaultdict(list)
	block_lines = []
	with open(args.trace_file, 'r') as f:
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
		blockTaintDict[blockNum[0]].append(taint[0]+'.'+readOrWrite[0])
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
				getAllocatedBytes(args.trace_file,writeTaint,prevTaint,blockNumber)
			#	print blockNumber,blockContents[blockNumber].count('A')

	for blockNumber in blockTaintDict:
		print blockNumber,blockContents[blockNumber].count('A')
		
#		print blockNumber, Taints

