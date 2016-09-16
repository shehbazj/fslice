import argparse
import re
import sys

# for a given destination block taint Value, returns the source block and the offset
# list of the source block that was pointing to the destination block

trace_file = "/tmp/testfs.py"

def getIntermediateICMPs(taint_val):
	with open(trace_file, 'r') as f:
		relevant_lines = []
                potentialICMP = []
                icmpblockTaint = []
		flag = None
		isFirstLine = True 
		srcBlockNum = 0

		taint_str = taint_val + '='
		relevant = set([taint_str])

		for line in reversed(f.readlines()):
                        if isFirstLine is False and "ICMP" in line: 
                        # start keeping tab of ICMPs after destination taint has been
                        # intercepted. this trims all icmps before the destination 
                        # block is read
                                relevant_lines.append(line)
			if line[0] == '#':
                        # remove all comments from taintFile
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
		for line in relevant_lines:
                        if "ICMP" in line: # copy all icmp lines
                                potentialICMP.append(line)
                                continue
			if 'B(' in line and taint_str not in line:
				bno = re.findall('B\(64\,(.+?)\,',line)
                                potentialICMP = list(set(potentialICMP))
                                for p in potentialICMP:
                                    icmpblk = p.split(' ')[2]
                                    if icmpblk == bno[0]:
                                        icmpblockTaint.append(p.split(' ')[1])
                                        return icmpblockTaint 
        
if __name__ == "__main__":
    print getIntermediateICMPs(sys.argv[1])
