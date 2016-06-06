import argparse
import re
import os

def forwardTraceReferencesSubelements(taint_val,trace_file):
#	print "for taint",taint_val," trace file ",trace_file
	with open(trace_file, 'r') as f:
		curset = set() 
		relevant_lines = []
		flag = True
		fo = None
		fwdTraceFile = None 
		printFunctionNames = None
		taint_val_eq = taint_val + '='
		taint_val_substruct = taint_val + '['

        # Forward pass
		relevant = set([taint_val])

		for line in (f.readlines()):
			if line[0] == '#' in line:
				continue
			if taint_val_eq in line:
				srcBlockNum = re.findall('B\(64\,(.+?)\,',line)
				fwdTraceFile = str('forwardTrace/b'+srcBlockNum[0]+'.'+taint_val)
				fo =open(fwdTraceFile,"wb")
				line = re.sub("\,t[0-9]+\)",")",line)
				fo.write(line)
				continue
			line = line.strip()
           # Match
			curlineset = {}
			curlineset = set(re.findall(r"t[0-9]+", line))
			if relevant.intersection(curlineset) and len(curlineset):
				fo.write(line)
				fo.write('\n')	
				#print line
				for taint in curlineset:
					assignedTaint=taint+'='
					#print "assignedTaint",assignedTaint
					if assignedTaint in line:
					#	print "added taint ",taint," to relevant set"
						relevant.add(taint)
				#print "Curset =",curset," relevant = ", relevant
				relevant_lines.append(line)
				RHS = line.split("=")[1];
				#if taint_val_substruct in RHS and 'O' in RHS:
				#if taint_val_substruct in RHS:
				#	return True	
				for taint in curset:
					if taint not in relevant:
						relevant.add(taint)
				
	
		#print fwdTraceFile
		for line in (relevant_lines):
			RHS = line.split("=")[1];
			#if 'O' in RHS and taint_val_substruct in RHS:
			if taint_val_substruct in RHS:
				fo.close()				
           			return True
		if fo is not None:
			fo.close()
	os.remove(fwdTraceFile)
	return False
