#!/usr/bin/python

import argparse
import re
import sys
import os
import subprocess
from collections import defaultdict

# value is map of <ixx, NUMBER>, <pxx , NUMBER> and <pxxixx , NUMBER>
# tuples from the TESTxx.res file

# we track all READ variables. For each READ i XX, we check if a 
# corresponding p XX exists. If it does, and array does not have
# an element at position p xx, we set the value of array at position 
# p xx as i xx

# VALIDATION is done by keeping track of WRITEs as well. for each
# write encountered, we keep track of which index was the WRITE on.
# if a second read takes place from an index position which has not
# been written to, we raise flag.

MAXOFFSET = 15

values = defaultdict(list)
arr = [-9999] * MAXOFFSET
writeOffsets = [ False ] * MAXOFFSET
#arrList = list()
#arrAddrList = defaultdict(list)

if __name__ == "__main__":
    """ Main Start """
    
# initialize values MAP with all ixx, pxx, pxxixx values obtained
# from solver
    
    varlist = tuple(open(sys.argv[1], 'r'))
    for line in varlist:
        if 'unsat' in line:
            print "unsat"
            sys.exit()
        lhs = line.split('=')[0].strip()
        if '[' in lhs:
            lhs = lhs.split('[')[1]
        rhs = line.split('=')[1].strip()
        if ']' in rhs:
            rhs = rhs.split(']')[0]
        if ',' in rhs:
            rhs = rhs.split(',')[0]
        values[lhs] = rhs

# scan .rw
# if READ i XX is encountered, check if p XX exists.
# if WRITE [p xx] is 1 discard and move to next value
# if WRITE [p xx] is 0 check if arr[p xx] is set
# if value not set, arr[p xx] = i xx
# if value set, and arr[p xx] != i xx RAISE ERROR

    rwlist = tuple(open(sys.argv[2], 'r'))
    for line in rwlist:
        if "READ i" in line:
            taintVal = line.split(' ')[2].strip()
            taintKey = ("i" + taintVal).strip()
            pointerTaint = ("p" + str(taintVal)).strip()
            if pointerTaint in values:
                offset = int(values[pointerTaint])
                if writeOffsets[offset] == False:
                    if arr [offset] == -9999:
                        arr[offset] = values[taintKey]
                        print "SET VALUE ", arr[offset], " at offset ", offset
                    elif arr[offset] != values [taintKey]: 
                        # duplicate entries
                        print "ERROR at Offset ", offset," new value ", values[taintKey] , " at offset ", offset, " pointerTaint ", pointerTaint
        if "WRITE i" in line:
            print "found write ", line.strip()
            taintVal = line.split(' ')[2]
            pointerTaint = 'p' + taintVal
            print "Pointer Taint ", pointerTaint
            if pointerTaint in values:
                offset = values[pointerTaint]
                print "WRITE at ", offset, " value ", values['i' + taintVal] 
                writeOffsets[offset] = True        
                        
    for idx in range(len(arr)):
        if arr[idx]  == -9999:
            arr[idx] = '*'

    print arr
#    print values
