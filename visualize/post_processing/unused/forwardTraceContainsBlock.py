import argparse
import re

def forwardTraceContainsBlock(taint_val,trace_file):
#	print "for taint",taint_val," trace file ",trace_file
	with open(trace_file, 'r') as f:
		curset = set() 
		relevant_lines = []
		flag = True
		printFunctionNames = None
		taint_val_eq = taint_val + '='

        # Forward pass
		relevant = set([taint_val])

		for line in (f.readlines()):
			if line[0] == '#' or taint_val_eq in line:
				continue
			line = line.strip()
           # Match
			curlineset = {}
			curlineset = set(re.findall(r"t[0-9]+", line))
			if relevant.intersection(curlineset) and len(curlineset):
				for taint in curlineset:
					assignedTaint=taint+'='
					#print "assignedTaint",assignedTaint
					if assignedTaint in line:
					#	print "added taint ",taint," to relevant set"
						relevant.add(taint)
					#	print relevant
				#print "Curset =",curset," relevant = ", relevant
				relevant_lines.append(line)
				if 'B(' in line:
					#print line
					return True	
				for taint in curset:
					if taint not in relevant:
						relevant.add(taint)
				
					
		for line in (relevant_lines):
			#print line
			if 'B(' in line:
           			return True
	return False
