#!/usr/bin/python

import argparse
import re
import sys
import os
import subprocess
from collections import defaultdict

# collect all array index offsets from the trace

# TODO make tuple of <arrayTaint , offset>

offsets = defaultdict(list)

# symbolic array objects
# each list of arrObjects[count]
# represents list of symbols sym that got assigned by
# sym = getElement(t_array, t_index, name_t_array, name_t_index)

arrObjects = defaultdict(list)

# symbolic indexes
# each list indexes[count]
# represents list of index symbols that got assigned by
# sym = getElement(t_array, index, name_t_array, name_index)

indexes = defaultdict(list)


def generateIndexConstraints(count):
    objList = arrObjects[count]
    indexConstraintString = '' 
    indexList = indexes[count]
    for i in range(len(objList)):
        for j in range(i + 1, len(objList)):
            indexConstraintString += ( "s.add(Implies(" + indexList[i][0] + " == " + indexList[j][0] + "," + objList[i][0] + " == " + objList[j][0] + "))\n" )
    return indexConstraintString

def getOffsetTaints():
    count=0
    offsetList = []
    arrObjectList = []
    indexList = []
    lines = tuple(open("/tmp/path", 'r'))
    for line in lines:
        if "GETMODEL" in line:
            offsets[count] = list(set(offsetList))
            arrObjects[count] = arrObjectList
            indexes[count] = indexList
            count = count + 1
            offsetList = []
            arrObjectList = []
            indexList = []

        elif 'getElement' in line:
            taintObj = line.split(",")[1]
            if taintObj is not '':
                offsetList.append(taintObj)
            #print line
            arrObj = line.split("=")[0].rsplit()
            arrObjectList.append(arrObj)
            index = line.split(",")[1].rsplit()
            indexList.append(index)
    
        

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
        return None
    var_idx = globals()[idx]
    if type (var_idx) is int: # concrete or symbolic element
                        # can be retrived from the array
        print "idx ", idx , " is INTEGER"
        if isSymbolic(arr):
            symbolicObjects.add(lhs)
        currentStr += lhs + " = " + arr + "[" + idx + "]" + "\n"
        return currentStr
    else:
        print "index type is ", type (var_idx)
        #if idx not in symbolicObjects:
        #    currentStr += (idx + " = Int('" + idx + "')" + "\n")
        #    symbolicObjects.add(idx)
        symbolicObjects.add(lhs)
        currentStr += ( lhs + "=" + "Int('"+ arr + "_" + idx + "')" + "\n")
        return currentStr
        
def process(line, offList):
 #   return None
    if "=" not in line:
        return None
    if "add" in line:
        return None
    lhs = line.split("=")[0].rstrip()
    rhs = line.split("=")[1].rstrip()
    for idx in offList:
        if lhs == idx:
            line += ( "indexCheck("+ lhs + "," + rhs + ", get_var_name("+ lhs + "=" + lhs + "))\n" )
            return line
    return None

if __name__ == "__main__":
    """ Main Start """

    head = tuple(open("header", 'r'))
    foot = tuple(open("footer", 'r'))
    lines = tuple(open("/tmp/path", 'r'))

    getOffsetTaints()
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
            indexConstraintString = generateIndexConstraints(count)
            textFile.write(indexConstraintString)
            textFile.write(footer)
            textFile.close()
            count +=1
            currentLine = ""
            continue
        else:
            if count is not 0 and line[0] is not '#':
                processedLine = process(line, offsets[count])
                if processedLine is None:
                    currentLine += line
                else:
                    currentLine += processedLine
    for c1 in range (1, count):
        fname = "TEST"+str(c1)+".py"
        print "TEST"+str(c1)
        execfile(fname)
