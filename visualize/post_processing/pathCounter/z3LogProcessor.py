#!/usr/bin/python

import argparse
import re
import sys
import os
import subprocess

if __name__ == "__main__":
    """ Main Start """

    lines = tuple(open("/tmp/path", 'r'))
    currentLine="#!/usr/bin/python"
    currentLine+= "\n"
    count=0
    for line in lines:
        if "GETMODEL" in line:
            #print "found GETMODEL ", count
            #print currentLine
            fName = "TEST"+str(count) + ".py"
            #print "created TESTCASE ", fName
            textFile = open(fName, "w")
            textFile.write(currentLine)
            textFile.close()
            currentLine = '#!/usr/bin/python'
            currentLine+= "\n"
            count +=1
            continue
        else:
            currentLine += line
    for c1 in range (1, count):
        fname = "TEST"+str(c1)+".py"
        print "TEST"+str(c1)
        execfile(fname)
#        subprocess.call(fname, shell=True)
