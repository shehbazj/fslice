import argparse
import re
import sys

"""
    Input - destination block taint 
    Output - source block number / None
"""
def getSourceBlock(taint_val, trace_file):

    with open(trace_file, 'r') as f:

        taint_str = None
        input_lines = None
        relevant_lines = []
        taint_str = 't' + taint_val + '='
        input_lines = reversed(f.readlines())
        
        relevant = set([taint_str])
        for line in input_lines:
            if line[0] == '#':
                continue

            # Match
            line = line.strip()
            curset = set(re.findall(r"t[0-9]+=", line))
            if len(curset) and relevant.intersection(curset):
                cur = re.findall(r"t[0-9]+", line)
                sol = []

                for taint in cur:
                    sol.append(taint + '=')
                relevant |= set(sol)
                relevant_lines.append(line)

        for line in relevant_lines:
        # t10=B(64,0,t7,t9, 10)
            if 'B' in line:
                return line.split(',')[1]
            #print(line)
        return None

if __name__ == "__main__":
    srcBlk = getSourceBlock(sys.argv[1], "/tmp/testfs.py")
    print srcBlk
