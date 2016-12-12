#!/usr/bin/python

import itertools
import sys

labelId = 0
removeConstants = None

class SYMBOLIC_STR:
    def __init__(self):
        self._str = 'a'
        self._len = 1

class SYMBOLIC_INT:
    def __init__(self):
        self._num = 0

def num_to_taint_object(str):
	return getattr(sys.modules[__name__], str)

def STRLEN(sym):
    if sym.__class__.__name__ == SYMBOLIC_STR.__name__:
        #symint = SYMBOLIC_INT()
        #symint._num = len(sym._str)
        return sym
    if type(sym).__name__ == 'str':
        return len(sym)
    assert(0)

def genSym(length):
    return 'a' * length

def ICMP(op1, op2, op):
    if op1.__class__.__name__ == SYMBOLIC_STR.__name__:
        if type(op2).__name__ == 'int':
            if op == 'ICMP_ULE':
                if ( op1._len < op2):
                    print "CURRENT SYM: ", op1._str
                    print "NEW SYM: ", genSym(op2)
                else:
                    print "CURRENT SYM: ", genSym(op2)
                    print "NEW SYM: ", op1._str

def V( a, b):
	return a;

def operate(op, op1, op2):
	if op is "add":
		return op1 + op2
	elif op is "mul":
		return op1 * op2
	elif op is "sdiv":
		return op1 / op2
	elif op is "udiv":
		return op1 / op2
	else:
		print "Undefined Binary Operation"

def generateLabel(op,op1,op2):
	global labelId
	labelId+=1
	label = "L"+str(labelId)
	if removeConstants is True:
		if isinstance(op1,int):
			op1 = 'C'
		if isinstance(op2,int):
			op2 = 'C'
	print label,op,op1,op2
	return label

def A( op, op1, op2, discard):
	global labelId
	if isinstance(op1,int) and isinstance(op2,int):
		return operate(op, op1, op2)

	elif isinstance(op1,basestring) and isinstance(op2,int):
		if op2 == 0:
			#print op1
			return op1
		return generateLabel(op,op1,op2)

	elif ((isinstance(op1,basestring) and isinstance(op2,list)) or
	(isinstance(op1,list) and isinstance(op2,basestring)) or
	(isinstance(op1,list) and isinstance(op2,list))):
		return generateLabel(op,op1,op2)
		
	elif isinstance(op1,list) and isinstance(op2, int):
		#if op2 == 0:
		#	print "returning ",op1
		#	return op1
		#print op,op1,op2
		mylist = []
		mylist.append(op)
		mylist.append('B')
		mylist.append(op1[-1])  # add block number
		mylist.append(op1[0])	# add block start
		mylist.append(op1[-2])	# add block end
		if removeConstants is True:
			mylist.append('C')
		else:
			mylist.append(op2)	# add op2
		labelId+=1
		label = "L" + str(labelId)
		print label,mylist
		return label
	else:
		print "No case matched for",op,op1,op2
		return []

# returns list containing all indexes block number and block taint

def B( bsize, bnum, bsizeTaint, bnumTaint, discard):
	#print 'B [',str(bnum),']'
	mylist = []
	for i in range(0,bsize):
		mylist.append(i)
	mylist.append(bnum)
	#print mylist
	print "B"+str(bnum),bnumTaint
	return mylist

# returns list of indexes and block number

def O(*arg):
	mylist = []
	for name in range(2,len(arg)):
		mylist.append(arg[name])
	mylist.append((arg[0])[-1])	# append block number
	return mylist

if __name__ == "__main__":
    """ Main Start """

