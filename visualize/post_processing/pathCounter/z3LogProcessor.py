#!/usr/bin/python

import argparse
import re
import sys
import os
import subprocess

# collect all array index offsets from the trace

# TODO make tuple of <arrayTaint , offset>

def getOffsetTaints(lines):
    offsets = []
    for line in lines:
        if '[' in line and ']' in line:
            taintObj = line[line.find("[")+1:line.find("]")]
            if taintObj is not '':
                offsets.append(taintObj)
    return list(set(offsets))

symbolicObjects = set()

# return true even if 1 token is symbolic

def isSymbolic(var):
    global symbolicObjects
    allTaints = re.findall('t[\d]+' , var)
    for t in allTaints:
        if t in symbolicObjects:
            return True
        return False

def isConcrete(var):
    return not(isSymbolic(var))

def processAssignment(lhs, rhs):
    global symbolicObjects
    if lhs is None or rhs is None:
        return None
    if "t" not in lhs:
        print "LHS , RHS Sent ", lhs ,  " " , rhs
        return None
    currentLine = ''
    if( isConcrete(lhs) and isConcrete(rhs)):
        currentLine += (lhs + "=" + rhs + "\n")
    elif(isConcrete(lhs) and isSymbolic(rhs)):
        symbolicObjects.add(lhs)
        currentLine += (lhs + "=" + rhs + "\n")
    elif(isSymbolic(lhs) and isConcrete(rhs)):
        symbolicObjects.remove(lhs)
        currentLine += (lhs + "=" + rhs + "\n")
    elif(isSymbolic(lhs) and isSymbolic(rhs)):
        currentLine += ("s.add(" + lhs + "==" + rhs + ")" + "\n")
    return currentLine

def processArray(arr, idx, lhs):
    currentStr = ''
    global symbolicObjects
    idxList = re.findall('[\d]+|t[\d]+',idx)
    if not idxList:
  #      print "return none"
        return None
    if type (idx) is int: # concrete or symbolic element
                        # can be retrived from the array
        if isSymbolic(arr):
            symbolicObjects.add(lhs)
        currentStr += lhs + " = " + arr + "[" + idx + "]" + "\n"
  #      print "returning ", currentStr 
        return currentStr
    else:
        if idx not in symbolicObjects:
            currentStr += (idx + " = Int('" + idx + "')" + "\n")
            symbolicObjects.add(idx)
        symbolicObjects.add(lhs)
        currentStr += ( lhs + "=" + "Int('"+ arr + "_" + idx + "')" + "\n")
  #      print "returning ", currentStr 
        return currentStr
        
def process(line):
    if "=" not in line:
   #     print "#WARNING , no = in line " , line
        return None
    if "add" in line:
   #     print "#WARNING, add in line", line
        return None
    lhs = line.split('=')[0].rstrip()
    rhs = line.split('=')[1].rstrip()
    if "[" in rhs and "]" in rhs:
        arr = rhs.split("[")[0].rstrip()
        idx = rhs[rhs.find("[")+1:rhs.find("]")]
 #       print "line = ", line, "XXXX ARRAY = " , arr , " INDEX = ", idx
        return processArray(arr , idx , lhs)
    else:
        return processAssignment(lhs, rhs)

if __name__ == "__main__":
    """ Main Start """

    head = tuple(open("header", 'r'))
    foot = tuple(open("footer", 'r'))
    lines = tuple(open("/tmp/path", 'r'))
    #offsetList = getOffsetTaints(lines)

    header = ""
    footer = ""
    currentLine = ""
    for curr in head:
        header += curr

    for curr in foot:
        footer += curr
    count=0
    for line in lines:
        if "GETMODEL" in line:
            fName = "TEST"+str(count) + ".py"
            textFile = open(fName, "w")
            textFile.write(header)
            textFile.write(currentLine)
            textFile.write(footer)
            textFile.close()
            count +=1
            currentLine = ""
            continue
        else:
            if count is not 0 and line[0] is not '#':
                processedLine = process(line)
                if processedLine is None:
                    currentLine += line
                else:
                    currentLine += processedLine
#    print currentLine 
    for c1 in range (1, count):
        fname = "TEST"+str(c1)+".py"
        print "TEST"+str(c1)
        execfile(fname)
