""" 

Automate annotation generation

The script takes a trace file as an input and generates annotations

a) block number - fsstruct - size and offset
b) block number - pointer - size and offset
c) block number - field
d) pointer "when" clause
e) type all fsstructs - a) based on size b) based on pointer type c) based on weather field is present or not d) control flow execution
f) determine vectors
g) determine fsconst [OPTIONAL]

"""

"""
Prints each block content in the form block Number, offset , size
"""

def printFSStructSizes(blockContents):
    for block,contents in blockContents.items():
        position = 0
        while position < len(contents):
            if contents[position] is 'A':
            startOffset = position
            while position < len(contents) and contents[position] is 'A':
            position+=1
            endOffset = position
            print 'BLOCK ', block ,' OFFSET <',startOffset, '-',endOffset,'>', \
                'SIZE ',endOffset - startOffset, '\n'
            else:
            position+=1

import os
from getAllocatedBytes import getAllocatedBytes

if __name__ == "__main__":
    """ Main Start """


    if os.path.isfile("/tmp/testfs.py") is 0:
        print "Did not find /tmp/testfs.py. did you run ./init.sh? "
        exit

    blockContents = getAllocatedBytes("/tmp/testfs.py")
    printFSStructSizes(blockContents)

     
