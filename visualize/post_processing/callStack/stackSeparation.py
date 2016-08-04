import argparse
import re
from collections import defaultdict

if __name__ == "__main__":
    """ Main Start """

    stackMap = defaultdict(list)

    with open("blockTrace", 'r') as f:
        
        input_lines = f.readlines()
        for line in input_lines:
            if "()" in line:
                stackTrace = line
            else:
                stackMap[stackTrace].append(line.strip('\n'))

    for stack, blockList in stackMap.items():
        print stack, set(blockList)
