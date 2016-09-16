import argparse
import re
import sys

#if __name__ == "__main__":
#    """ Main Start """

# for a given destination block taint Value, returns the source block and the offset
# list of the source block that was pointing to the destination block

def getSourceBlockNumberAndOffset(taint_val,trace_file):
	with open(trace_file, 'r') as f:
		relevant_lines = []
		flag = None
		#printFunctionNames = None
		isFirstLine = True 
		srcBlockNum = 0

		taint_str = taint_val + '='
		relevant = set([taint_str])

		for line in reversed(f.readlines()):
			if line[0] == '#':
				continue
			line = line.strip()
			curset = set(re.findall(r"t[0-9]+=", line))
		 	if relevant.intersection(curset) and len(curset):
				if isFirstLine:
					srcBlockNum = re.findall('B\(64\,(.+?)\,',line)
					isFirstLine = False
		 		cur = re.findall(r"t[0-9]+", line)
		 		sol = []
		 		for taint in cur:
		 			sol.append(taint + '=')
				relevant |= set(sol)
				relevant_lines.append(line)
	#			if printFunctionNames == True:
	#				flag = True

	#		if printFunctionNames == True:
	#			if line.endswith("()") and flag:
	#				relevant_lines.append(line)
	#				flag = False

		#backTraceFile = str('backtrace/'+srcBlockNum[0]+'.'+taint_val)
		#print backTraceFile
		#fo = open (backTraceFile,"wb")	
		for line in relevant_lines:
			#fo.write(line)
			#fo.write('\n')
			if 'O' in line:
				offsetList = re.findall('t[0-9]+\[(.+?)\]',line)
				#print offsetList
			if 'B' in line and taint_str not in line:
				bno = re.findall('B\(64\,(.+?)\,',line)
				#fo.close()
				return (bno[0],offsetList)	
	#fo.close()
	return (None,None)

if __name__ == "__main__":
    print getSourceBlockNumberAndOffset(sys.argv[1],"/tmp/testfs.py")
