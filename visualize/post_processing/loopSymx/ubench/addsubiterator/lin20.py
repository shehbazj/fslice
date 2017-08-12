#!/usr/bin/python

from z3 import *

def IntArr(prefix, sz, N):
  """Create a vector with N Bit-Vectors of size sz"""
  return [ BitVec('%s__%s' % (prefix, i), sz) for i in range(N) ]

def get_var_name(**kwargs): return kwargs.keys()[0]



def getElement(arr , idx, name1, name2, name3):
    #if type(idx) is int:
    #    return arr[idx]
#    name = name1+name2
#    symVar = Int(name)
    symVar = Int(name3)
    return symVar

def indexCheck(lhs, lhsName):
    #if type(lhs) is int:
    #    return ''
    #else:
    lhs  = Int(lhsName)
    #s.add(lhs ==rhs)
    s.add(lhs >= 0)

def getZ3VariableFromString(s, varString):
    if(s.check() != z3.sat):
        return None
    m = s.model()
    for c in m.decls():
        n = c.name()
        if n == varString:
            return c
    assert (0), "z3 String varString does not exist"

def addArrayConstraints(s):
    m = s.model()
    idxList = []
    arrList = []
    for c in m.decls():
        n = c.name()
        if n.count('t') == 2:
            print "#array element ", n, m[c]
            idx =  n[n.rfind("t"): len(n) ]
            print "#index taint = ", idx
            idxList.append(idx)
            arrList.append(n)
    print "#arrList = ", arrList
    print "#idxList = ", idxList
    for i in range(len(arrList)):
        obj_i_name = arrList[i]
        taint_i_name = obj_i_name[obj_i_name.rfind("t"): len(obj_i_name)]
        #obj_i = getZ3VariableFromString(s,obj_i_name)
        obj_i = get_var_name(obj_i_name=obj_i_name)
        #taint_i = getZ3VariableFromString(s,taint_i_name)
        taint_i = get_var_name(taint_i_name=taint_i_name)
        if obj_i is None or taint_i is None:
            print "#either obj_i ", obj_i_name, " or taint_i ", taint_i_name, " did not get instantiated" 
            return None
        for j in range(len(arrList)):
            if(i == j):
                continue
            obj_j_name = arrList[j]
            taint_j_name = obj_j_name[obj_j_name.rfind("t"): len(obj_j_name)]
            #obj_j = getZ3VariableFromString(s,obj_j_name)
            obj_j = get_var_name(obj_j_name=obj_j_name)
            #taint_j = getZ3VariableFromString(s,taint_j_name)
            taint_j = get_var_name(taint_j_name=taint_j_name)
            if obj_j is None or taint_j is None:
                print "#either obj_j ", obj_j_name, " or taint_j ", taint_j_name, " did not get instantiated"
                return None
            print "====BEFORE ADDING CONSTRAINT==="
            for c in s.assertions():
	        print c
            new_s = Solver()
            new_s = s
            new_s.add(Implies(obj_i != obj_j , taint_i != taint_j))
            print "====AFTER ADDING CONSTRAINT==="
            for c in new_s.assertions():
	        print c
            s = new_s
#            if(obj_i != obj_j):
#                print "#obj_i ", obj_i_name," obj_j ", obj_j_name, " are not equal"
#                print "adding constraint, i != j for taints ", taint_i_name, " and ", taint_j_name 
#         #       s.push()
#                print "====BEFORE ADDING CONSTRAINT==="
#            	for c in s.assertions():
#		    print c
#                s.add((taint_i != taint_j))
#                print "===AFTER ADDING CONSTRAINT==="
#            	for c in s.assertions():
#		    print c
#                if s.check() == z3.unsat:
#                    return None
#                #else:
#                #    print s.model()
    return s

def CharArr(prefix, sz, N):
  """Create a vector with N Bit-Vectors of size sz"""
  return [ BitVec('%s__%s' % (prefix, i), sz) for i in range(N) ]

def CharArr2D(prefix):
    return [[]]

def extendList(var, num, prefix):
    listSize = len(var)
    if num - listSize > 0:
        incrementSize = num-listSize
        for val in range(incrementSize):
            var.append( BitVec('%s__%s' % (prefix, listSize + val), 32))

def BitVectorToInt(var):
    if type(var) is int:    # if already int dont do anything
        return
    elif is_bv(var) and var.size() == 32: # if bitvector is int of size
        # 32, then return Integer equavalent
        ctx = var.ctx
        return ArithRef(Z3_mk_bv2int(ctx.ref(), var.as_ast(), 0), ctx)
    else:       # if bitvector is that of char, return as is
            # since all character operations happen on bitvector
        return var

def ConstIntArr(var, size):
#  	return [ BitVec('%s__%s' % (var, i), 32) for i in range(size) ]
    return []

def indexSanitizer(index, arrSize, s):
	s.push()
	s.add(index < 0)
	if(s.check() == z3.sat):
		print "NEGATIVE INDEX POSSIBLE"
		print (s.model())
	s.pop()
	
	s.push()
	s.add(index >= arrSize)
	if(s.check() == z3.sat):
		print "OVERFLOW INDEX POSSIBLE"
		print (s.model())
	s.pop()

	s.push()
	s.add(index >=0 , index < arrSize)
	if(s.check() != z3.sat):
		print "VALID ARRAY INDEX NOT POSSIBLE"
		s.pop()
		return -1
	else:
		index = s.model()[index]
		return index

set_param('smt.bv.enable_int2bv',True)

s = Solver()


counter1 =Int('counter1')
s.add(counter1 >= 0)
s.add(counter1 <= 1)
negcounter1 =Int('negcounter1')
s.add(negcounter1 >= 0)
s.add(negcounter1 <= 1)
counter2 =Int('counter2')
s.add(counter2 >= 0)
s.add(counter2 <= 1)
negcounter2 =Int('negcounter2')
s.add(negcounter2 >= 0)
s.add(negcounter2 <= 1)
counter3 =Int('counter3')
s.add(counter3 >= 0)
s.add(counter3 <= 1)
negcounter3 =Int('negcounter3')
s.add(negcounter3 >= 0)
s.add(negcounter3 <= 1)
counter4 =Int('counter4')
s.add(counter4 >= 0)
s.add(counter4 <= 1)
negcounter4 =Int('negcounter4')
s.add(negcounter4 >= 0)
s.add(negcounter4 <= 1)
counter5 =Int('counter5')
s.add(counter5 >= 0)
s.add(counter5 <= 1)
negcounter5 =Int('negcounter5')
s.add(negcounter5 >= 0)
s.add(negcounter5 <= 1)
counter6 =Int('counter6')
s.add(counter6 >= 0)
s.add(counter6 <= 1)
negcounter6 =Int('negcounter6')
s.add(negcounter6 >= 0)
s.add(negcounter6 <= 1)
counter7 =Int('counter7')
s.add(counter7 >= 0)
s.add(counter7 <= 1)
negcounter7 =Int('negcounter7')
s.add(negcounter7 >= 0)
s.add(negcounter7 <= 1)
counter8 =Int('counter8')
s.add(counter8 >= 0)
s.add(counter8 <= 1)
negcounter8 =Int('negcounter8')
s.add(negcounter8 >= 0)
s.add(negcounter8 <= 1)
counter9 =Int('counter9')
s.add(counter9 >= 0)
s.add(counter9 <= 1)
negcounter9 =Int('negcounter9')
s.add(negcounter9 >= 0)
s.add(negcounter9 <= 1)
counter10 =Int('counter10')
s.add(counter10 >= 0)
s.add(counter10 <= 1)
negcounter10 =Int('negcounter10')
s.add(negcounter10 >= 0)
s.add(negcounter10 <= 1)
counter11 =Int('counter11')
s.add(counter11 >= 0)
s.add(counter11 <= 1)
negcounter11 =Int('negcounter11')
s.add(negcounter11 >= 0)
s.add(negcounter11 <= 1)
counter12 =Int('counter12')
s.add(counter12 >= 0)
s.add(counter12 <= 1)
negcounter12 =Int('negcounter12')
s.add(negcounter12 >= 0)
s.add(negcounter12 <= 1)
counter13 =Int('counter13')
s.add(counter13 >= 0)
s.add(counter13 <= 1)
negcounter13 =Int('negcounter13')
s.add(negcounter13 >= 0)
s.add(negcounter13 <= 1)
counter14 =Int('counter14')
s.add(counter14 >= 0)
s.add(counter14 <= 1)
negcounter14 =Int('negcounter14')
s.add(negcounter14 >= 0)
s.add(negcounter14 <= 1)
counter15 =Int('counter15')
s.add(counter15 >= 0)
s.add(counter15 <= 1)
negcounter15 =Int('negcounter15')
s.add(negcounter15 >= 0)
s.add(negcounter15 <= 1)
counter16 =Int('counter16')
s.add(counter16 >= 0)
s.add(counter16 <= 1)
negcounter16 =Int('negcounter16')
s.add(negcounter16 >= 0)
s.add(negcounter16 <= 1)
counter17 =Int('counter17')
s.add(counter17 >= 0)
s.add(counter17 <= 1)
negcounter17 =Int('negcounter17')
s.add(negcounter17 >= 0)
s.add(negcounter17 <= 1)
counter18 =Int('counter18')
s.add(counter18 >= 0)
s.add(counter18 <= 1)
negcounter18 =Int('negcounter18')
s.add(negcounter18 >= 0)
s.add(negcounter18 <= 1)
counter19 =Int('counter19')
s.add(counter19 >= 0)
s.add(counter19 <= 1)
negcounter19 =Int('negcounter19')
s.add(negcounter19 >= 0)
s.add(negcounter19 <= 1)
counter20 =Int('counter20')
s.add(counter20 >= 0)
s.add(counter20 <= 1)
negcounter20 =Int('negcounter20')
s.add(negcounter20 >= 0)
s.add(negcounter20 <= 1)
s.add( counter20 * 20 + negcounter20 * -20 + counter2 * 2 + negcounter2 * -2 + counter3 * 3 + negcounter3 * -3 + counter4 * 4 + negcounter4 * -4 + counter5 * 5 + negcounter5 * -5 + counter6 * 6 + negcounter6 * -6 + counter7 * 7 + negcounter7 * -7 + counter8 * 8 + negcounter8 * -8 + counter9 * 9 + negcounter9 * -9 + counter10 * 10 + negcounter10 * -10 + counter11 * 11 + negcounter11 * -11 + counter12 * 12 + negcounter12 * -12 + counter13 * 13 + negcounter13 * -13 + counter14 * 14 + negcounter14 * -14 + counter15 * 15 + negcounter15 * -15 + counter16 * 16 + negcounter16 * -16 + counter17 * 17 + negcounter17 * -17 + counter18 * 18 + negcounter18 * -18 + counter19 * 19 + negcounter19 * -19 + counter20 * 20 + negcounter20 * -20 == 13)
x=s.check()
if(x == z3.sat):
	m = s.model()
	print m
else:
	print unsat
