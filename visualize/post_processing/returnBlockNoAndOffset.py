import argparse
import re

#if __name__ == "__main__":
#    """ Main Start """

def returnBlockNoAndOffset(taint_val,trace_file):
	with open(trace_file, 'r') as f:
		relevant_lines = []
		flag = None
		printFunctionNames = None

		taint_str = taint_val + '='
		relevant = set([taint_str])

		for line in reversed(f.readlines()):
			if line[0] == '#' and printFunctionNames != True:
				continue
			line = line.strip()
			curset = set(re.findall(r"t[0-9]+=", line))
		 	if relevant.intersection(curset) and len(curset):
		 		cur = re.findall(r"t[0-9]+", line)
		 		sol = []
		 		for taint in cur:
		 			sol.append(taint + '=')
				relevant |= set(sol)
				relevant_lines.append(line)
				if printFunctionNames == True:
					flag = True

			if printFunctionNames == True:
				if line.endswith("()") and flag:
					relevant_lines.append(line)
					flag = False

		for line in relevant_lines:
			if 'O' in line:
				offsetList = re.findall('t[0-9]+\[(.+?)\]',line)
				#print offsetList
			if 'B' in line and taint_str not in line:
				bno = re.findall('B\(64\,(.+?)\,',line)
				return (bno[0],offsetList)	
	return (None,None)
