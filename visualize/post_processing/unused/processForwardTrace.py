# Read file in forwardTrace
# canonicalize taint numbers

import re
import sys


for filename in sys.argv[1:]:
#filename = sys.argv[fileno]
	count = 0
	taintNumMap = {}
	print filename
	firstLine = True
	forwardTraceTemplateFile='forwardTraceTemplate/'+filename
	fo = open(forwardTraceTemplateFile,"wb")
	with open(filename, 'r') as f:
		for line in (f.readlines()):
			line = line.strip()
			taint = line.split('=')[0]
			#print taint
			taintNumMap[taint] = 't'+str(count);
			line = re.sub(r"\, [0-9]+\)",")",line)
			line = re.sub(r"\,[0-9]+\,",",",line)
			count = count+1
	
			if line[0] is '#' or firstLine:
				firstLine=False
				continue
			line = line.split('#')[0]
			line = line.strip()
			for taint in taintNumMap:
				line = line.replace(taint, taintNumMap[taint])
			fo.write(line)
			fo.write("\n")
			#print line
	fo.close()
