#!/usr/bin/python

import itertools
import sys

labelId = 0
removeConstants = None

class SYMBOLIC_STR:
    def __init__(self, taintNo):
        seedstr = 'a'
        self._data = seedstr
        self._selfTaint = taintNo
        self._relation = ''
        self._relationTaint = self
        self._relationOperand = 0

    def printf(self):
        print "STRING = ", self._data
        print "LENGTH = ", self._len
        print "SELF TAINT = ", self._selfTaint
        print "RELATION = ", self._relation
        print "RELATION TAINT = ", self._relationTaint._selfTaint
        print "RELATION VALUE = ", self._relationvalue

def num_to_taint_object(str):
	return getattr(sys.modules[__name__], str)

def STRLEN(sym, strlenTaint):
    if sym.__class__.__name__ == SYMBOLIC_STR.__name__:
        newstr = SYMBOLIC_STR(sym._selfTaint)
        newstr._data = len(sym._data)
        newstr._selfTaint = strlenTaint
        newstr._relation = "strlen"
        newstr._relationTaint = sym
        newstr._relationOperand = 0
        return newstr

def N(size, discard):
    return [0] * size

def D(size, discard):
    return [0] * size

def genSym(length):
    return [] * length

def evaluateExpression(op1, op2, op):
    if op == "ICMP_EQ":
        return op1 == op2
    elif op == "ICMP_UGT":
        return op1 > op2
    elif op == "ICMP_UGE":
        return op1 >= op2
    elif op == "ICMP_ULT":
        return op1 < op2
    elif op == "ICMP_ULE":
        return op1 <= op2
    elif op == "ICMP_SGT":
        return op1 > op2
    elif op == "ICMP_SGE":
        return op1 >= op2
    elif op == "ICMP_SLT":
        return op1 < op2
    elif op == "ICMP_SLE":
        return op1 <= op2
    else:
        print "TODO: evaluateExpression for ", op1, op2, op

def getSymOpValue(op1, op2, op, evaluateTo):
    if evaluateTo == False:
        op = complement(op)
    # generate values of op1 for which op1 - op - op2 evaluates to True
    if ((op is "ICMP_UGE") or (op is "ICMP_ULE") or (op is "ICMP_SGE") or (op is "ICMP_SLE") or(op is "ICMP_EQ")):
        return op2
    elif ((op is "ICMP_UGT") or (op is "ICMP_SGT")):
        return op2 + 1
    elif ((op is "ICMP_ULT") or (op is "ICMP_SLT")):
        return op2 - 1
    
def invert(newValue, relation, relationOperand):
    if relation == "strlen":
        return 'a' * newValue
    if relation == "add":
        return newValue - relationOperand
    if relation == "sub":
        return newValue + relationOperand
    if relation == "div":
        return newValue * relationOperand
    if relation == "mul":
        return newValue / relationOperand

def generateSymbol(symbol, newValue):
    print "t",symbol._selfTaint
  #  if symbol._relation != '':
  #      symValue = invert(newValue, symbol._relation, symbol._relationOperand)
  #      print symValue, "t", symbol._relationTaint, symbol._relation
  #      generateSymbol(symbol._relationTaint, symValue)

def generateConcreteValue(symOp, constOp, op):
    if type(constOp).__name__ == 'int':
        isExpressionFalse = evaluateExpression(symOp._data, constOp, op)
        # if isExpressionFalse is False, we need to evaluate a value for symOp
        # for which expression is True
        # alternatively, for True expression, isExpresionFalse is False, so we
        # generate symbol for which complement of the expression is True
        # i.e. op1 - complement(op) - op2 is True
        symOpValue = getSymOpValue(symOp._data, constOp, op, isExpressionFalse)
        generateSymbol(symOp,symOpValue)
    else:
        print "TODO: generateConcreteValue() for non int op values", symOp._data, constOp, op

def complement(op):
    if op == "ICMP_EQ":
        return "ICMP_NE"
    elif op == "ICMP_UGT":
        return "ICMP_ULE"
    elif op == "ICMP_UGE":
        return "ICMP_ULT"
    elif op == "ICMP_ULT":
        return "ICMP_UGE"
    elif op == "ICMP_ULE":
        return "ICMP_UGT"
    elif op == "ICMP_SGT":
        return "ICMP_SLE"
    elif op == "ICMP_SGE":
        return "ICMP_SLT"
    elif op == "ICMP_SLT":
        return "ICMP_SGE"
    elif op == "ICMP_SLE":
        return "ICMP_SGT"    

def ICMP(op1, op2, op):
    if op1.__class__.__name__ == SYMBOLIC_STR.__name__:
        print "SYMBOLIC COMPARISION ", op1._selfTaint, op2 , op
        generateConcreteValue(op1, op2, op)
    if op2.__class__.__name__ == SYMBOLIC_STR.__name__:
        print "SYMBOLIC COMPARISION ", op1, op2._selfTaint, op
        generateConcreteValue(op2, op1, complement(op))

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
        elif op is "sub":
                return op1 - op2
	else:
		print "Undefined Binary Operation"

def S(size, discard):
    return [0] * size

def M(size, b, c,d, e=0):
    return [0] * size

def A( op, op1, op2, retTaint):
        if op1.__class__.__name__ == SYMBOLIC_STR.__name__ and isinstance(op2,int):
            oldlen = op1._data
            newsym = SYMBOLIC_STR(retTaint)
            newsym._data =  operate(op, op1._data, op2)
            newsym._relation = op
            newsym._relationTaint = op1
            newsym._relationOperand = op2
            newsym._selfTaint = retTaint
	    return newsym
        return [0] * 64

def B( bsize, bnum, bsizeTaint, bnumTaint, discard):
    return [0] *bsize
#	#print 'B [',str(bnum),']'
#	mylist = []
#	for i in range(0,bsize):
#		mylist.append(i)
#	mylist.append(bnum)
#	#print mylist
#	print "B"+str(bnum),bnumTaint
#	return mylist

# returns list of indexes and block number

def O(*arg):
	mylist = []
#	for name in range(2,len(arg)):
#		mylist.append(arg[name])
#	mylist.append((arg[0])[-1])	# append block number
	return mylist

if __name__ == "__main__":
    """ Main Start """
    t0 = 0
