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

arrElements = defaultdict(list)

# symbolic indexes
# each list indexes[count]
# represents list of index symbols that got assigned by
# sym = getElement(t_array, index, name_t_array, name_index)

indexes = defaultdict(list)

# p_scanned_taints and i_scanned_taints store all initialized
# pXX and iXX taints that we encounter in the trace file.
# we use these two data structures to build rwList - which is 
# a log of all READ and WRITE taints that have both integer and
# pointer values.

p_scanned_taints = []
i_scanned_taints = []
rwList = []

def generatePointerConstraints(count):
    # read rw file
    # if READ or WRITE happens for i
    # if p exists for i
    # add to rwList

    retStr = ''
    _wList = [] 
    for i in range(1 , len(rwList)):
        elem1 = rwList[i]
        if 'w' in elem1:
            continue
        else:
            _wList = []
            elem1Taint = elem1.split("r")[1].rstrip()
            for j in reversed(range(0, i)):
                elem2 = rwList[j]
                print "elem1 = ", elem1, "elem2 = ", elem2
                if 'w' in elem2:
                    elem2Taint = elem2.split("w")[1].rstrip()
                    _wList.append(elem2Taint)
                    # if W1 W2 R3 happened, R3 == W2 implies elem_read3 == elem_write2
                    # if W1 W2 R3 happened, R3 != W2 && R3 == W1 implies elem_read3 == elem_write1
                    # elem2 is being added in reversed order of writes. i.e. W2 added first, W1 appended later
                    # so we scan _wList from bottom to top, comparing each element pointer with elem1
                    # and negating all intermediate write pointer positions
                    writeString = ''
                    AndStr = ''
                    AndTerm = ''
                    for wElem in reversed(range(0,len(_wList) - 1)):
                        wElemTaint = _wList[wElem]
                        writeString += ( ", p" + elem1Taint + " != p" + wElemTaint )
                        AndStr = "And("
                        AndTerm = ")"
                    string = "s.add(Implies(" + AndStr + " p" + elem1Taint + " == p" + elem2Taint + writeString + AndTerm + ", i" + elem1Taint + " == i" + elem2Taint + "))"
                    retStr += (string + "\n")
                        
                else:
                # XXX use _wList
                    elem2Taint = elem2.split("r")[1].rstrip()
                    writeString = ''
                    AndStr = ''
                    AndTerm = ''
                    for wElem in range(len(_wList)):
                        AndStr = "And("
                        AndTerm = ")"
                        writeString += (", p" + elem1Taint + " != p" + _wList[wElem] )
                    string = "s.add(Implies(" + AndStr +" p" + elem1Taint + " == p" + elem2Taint + writeString + AndTerm + ", i" + elem1Taint + " == i" + elem2Taint + "))"
                    retStr += (string + "\n")
    return retStr                      
                

    # for each element in rwList starting from element 2::
    # write prev List = []
    # for each prev element::
    # if element is read, for each prev element
    # if prev element is read, 
    # p_current == p_prev ==> elem_current == elem_prev_read
    # if prev element is write, add to write list
    # when a read is encountered,
    # p_current != write_p1 && p_current != write_p2
    # && p_current == p_prev_read => elem_current == elem_prev_read

    #rwFile = "TEST" + count + ".rw"
    #rwlist = tuple(open(rwFile, 'r'))
    #for line in rwlist:
                        
 
def getOffsetTaints():
    count=0
    offsetList = []
    arrObjectList = []
    arrElementList = []
    indexList = []
    lines = tuple(open("/tmp/path", 'r'))
    for line in lines:
        if "GETMODEL" in line:
            offsets[count] = list(set(offsetList))
            arrObjects[count] = arrObjectList
            arrElements[count] = arrElementList
            indexes[count] = indexList
            count = count + 1
            offsetList = []
            arrObjectList = []
            arrElementList = []
            indexList = []

        elif 'getElement' in line:
            taintObj = line.split(",")[1]
            if taintObj is not '':
                offsetList.append(taintObj)
            #print line
            arrObj = line.split("(")[1].split(",")[0].rsplit()
            arrObjectList.append(arrObj)
            arrElem = line.split("=")[0]
            arrElementList.append(arrElem)
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
        
def process(line, offList, arrList):
    if line[0] is '#':
        return line
    if "=" not in line:
        return None
    if "add" in line:
        return None
    lhs = line.split("=")[0].rstrip()
    rhs = line.split("=")[1].rstrip()
    if "name" in lhs:
        return None
    if 'i' in lhs:
        i_scanned_taints.append(lhs.split("i")[1])
    elif 'p' in lhs:
        p_scanned_taints.append(lhs.split("p")[1])
    else:
        print "ERROR, found ", lhs
    
    if "getElement" in rhs:
        elementIndex = rhs.split(",")[1].rstrip()
        line += ( "indexCheck("+ elementIndex + ",get_var_name("+ elementIndex + "=" + elementIndex + "))\n")
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
            print "TEST" , str(count) 
            fName = "TEST"+str(count) + ".py"
            textFile = open(fName, "w")
            textFile.write(header)
            textFile.write(currentLine)
            pointerConstraintString = generatePointerConstraints(count)
            textFile.write(pointerConstraintString)
            textFile.write(footer)
            textFile.close()
            count +=1
            currentLine = ""
#            print "ISCANNED TAINTS ",i_scanned_taints
#            print "PSCANNED TAINTS ",p_scanned_taints
            print "RWList TAINTS ",rwList
            p_scanned_taints = []
            i_scanned_taints = []
            rwList = []
            # truncate already existing rw file
            with open("TEST"+str(count)+".rw", "w"):
                pass
            continue
        else:
            # .rw file contains all taints that were read
            # corresponding to load operation or written
            # corresponding to store operation
            if "READ i" in line or "WRITE i" in line:
                if "READ" in line:
                    action = 'r'
                else:
                    action = 'w'
                taintVal = line.split("i ")[1].rstrip()
                #print "taintVal = ", taintVal
                if taintVal in i_scanned_taints and taintVal in p_scanned_taints:
                    rwList.append(action + taintVal)
                    fName = "TEST"+str(count) + ".rw"
                    textFile = open(fName, "a")
                    textFile.write(line)
                    textFile.close()
                #else:
                #    print "taintVal ", taintVal , " not in ISCANNED ", i_scanned_taints, " or ", " PSCANNED ", p_scanned_taints
            if count is not 0:
                processedLine = process(line, offsets[count], arrObjects[count])
                if processedLine is None:
                    currentLine += line
                else:
                    currentLine += processedLine


    for c1 in range (1, count):
        fname = "TEST"+str(c1)+".py"
        print "TEST"+str(c1)
        outName = "TEST"+str(c1)+".res"
        rwLog = "TEST"+str(c1)+".rw"

#       run TEST1.py and output to TEST1.res
        sys.stdout = open(outName, "w")
        execfile(fname)

#       run arrayGenerator.py with argument TEST1.res TEST1.rw
        sys.stdout = sys.__stdout__
        subprocess.call( ["python", 'arrayGenerator.py' , outName , rwLog ] );
