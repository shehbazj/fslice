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
counter2 =Int('counter2')
s.add(counter2 >= 0)
s.add(counter2 <= 1)
counter3 =Int('counter3')
s.add(counter3 >= 0)
s.add(counter3 <= 1)
counter4 =Int('counter4')
s.add(counter4 >= 0)
s.add(counter4 <= 1)
counter5 =Int('counter5')
s.add(counter5 >= 0)
s.add(counter5 <= 1)
counter6 =Int('counter6')
s.add(counter6 >= 0)
s.add(counter6 <= 1)
counter7 =Int('counter7')
s.add(counter7 >= 0)
s.add(counter7 <= 1)
counter8 =Int('counter8')
s.add(counter8 >= 0)
s.add(counter8 <= 1)
counter9 =Int('counter9')
s.add(counter9 >= 0)
s.add(counter9 <= 1)
counter10 =Int('counter10')
s.add(counter10 >= 0)
s.add(counter10 <= 1)
counter11 =Int('counter11')
s.add(counter11 >= 0)
s.add(counter11 <= 1)
counter12 =Int('counter12')
s.add(counter12 >= 0)
s.add(counter12 <= 1)
counter13 =Int('counter13')
s.add(counter13 >= 0)
s.add(counter13 <= 1)
counter14 =Int('counter14')
s.add(counter14 >= 0)
s.add(counter14 <= 1)
counter15 =Int('counter15')
s.add(counter15 >= 0)
s.add(counter15 <= 1)
counter16 =Int('counter16')
s.add(counter16 >= 0)
s.add(counter16 <= 1)
counter17 =Int('counter17')
s.add(counter17 >= 0)
s.add(counter17 <= 1)
counter18 =Int('counter18')
s.add(counter18 >= 0)
s.add(counter18 <= 1)
counter19 =Int('counter19')
s.add(counter19 >= 0)
s.add(counter19 <= 1)
counter20 =Int('counter20')
s.add(counter20 >= 0)
s.add(counter20 <= 1)
counter21 =Int('counter21')
s.add(counter21 >= 0)
s.add(counter21 <= 1)
counter22 =Int('counter22')
s.add(counter22 >= 0)
s.add(counter22 <= 1)
counter23 =Int('counter23')
s.add(counter23 >= 0)
s.add(counter23 <= 1)
counter24 =Int('counter24')
s.add(counter24 >= 0)
s.add(counter24 <= 1)
counter25 =Int('counter25')
s.add(counter25 >= 0)
s.add(counter25 <= 1)
counter26 =Int('counter26')
s.add(counter26 >= 0)
s.add(counter26 <= 1)
counter27 =Int('counter27')
s.add(counter27 >= 0)
s.add(counter27 <= 1)
counter28 =Int('counter28')
s.add(counter28 >= 0)
s.add(counter28 <= 1)
counter29 =Int('counter29')
s.add(counter29 >= 0)
s.add(counter29 <= 1)
counter30 =Int('counter30')
s.add(counter30 >= 0)
s.add(counter30 <= 1)
counter31 =Int('counter31')
s.add(counter31 >= 0)
s.add(counter31 <= 1)
counter32 =Int('counter32')
s.add(counter32 >= 0)
s.add(counter32 <= 1)
counter33 =Int('counter33')
s.add(counter33 >= 0)
s.add(counter33 <= 1)
counter34 =Int('counter34')
s.add(counter34 >= 0)
s.add(counter34 <= 1)
counter35 =Int('counter35')
s.add(counter35 >= 0)
s.add(counter35 <= 1)
counter36 =Int('counter36')
s.add(counter36 >= 0)
s.add(counter36 <= 1)
counter37 =Int('counter37')
s.add(counter37 >= 0)
s.add(counter37 <= 1)
counter38 =Int('counter38')
s.add(counter38 >= 0)
s.add(counter38 <= 1)
counter39 =Int('counter39')
s.add(counter39 >= 0)
s.add(counter39 <= 1)
counter40 =Int('counter40')
s.add(counter40 >= 0)
s.add(counter40 <= 1)
counter41 =Int('counter41')
s.add(counter41 >= 0)
s.add(counter41 <= 1)
counter42 =Int('counter42')
s.add(counter42 >= 0)
s.add(counter42 <= 1)
counter43 =Int('counter43')
s.add(counter43 >= 0)
s.add(counter43 <= 1)
counter44 =Int('counter44')
s.add(counter44 >= 0)
s.add(counter44 <= 1)
counter45 =Int('counter45')
s.add(counter45 >= 0)
s.add(counter45 <= 1)
counter46 =Int('counter46')
s.add(counter46 >= 0)
s.add(counter46 <= 1)
counter47 =Int('counter47')
s.add(counter47 >= 0)
s.add(counter47 <= 1)
counter48 =Int('counter48')
s.add(counter48 >= 0)
s.add(counter48 <= 1)
counter49 =Int('counter49')
s.add(counter49 >= 0)
s.add(counter49 <= 1)
counter50 =Int('counter50')
s.add(counter50 >= 0)
s.add(counter50 <= 1)
counter51 =Int('counter51')
s.add(counter51 >= 0)
s.add(counter51 <= 1)
counter52 =Int('counter52')
s.add(counter52 >= 0)
s.add(counter52 <= 1)
counter53 =Int('counter53')
s.add(counter53 >= 0)
s.add(counter53 <= 1)
counter54 =Int('counter54')
s.add(counter54 >= 0)
s.add(counter54 <= 1)
counter55 =Int('counter55')
s.add(counter55 >= 0)
s.add(counter55 <= 1)
counter56 =Int('counter56')
s.add(counter56 >= 0)
s.add(counter56 <= 1)
counter57 =Int('counter57')
s.add(counter57 >= 0)
s.add(counter57 <= 1)
counter58 =Int('counter58')
s.add(counter58 >= 0)
s.add(counter58 <= 1)
counter59 =Int('counter59')
s.add(counter59 >= 0)
s.add(counter59 <= 1)
counter60 =Int('counter60')
s.add(counter60 >= 0)
s.add(counter60 <= 1)
counter61 =Int('counter61')
s.add(counter61 >= 0)
s.add(counter61 <= 1)
counter62 =Int('counter62')
s.add(counter62 >= 0)
s.add(counter62 <= 1)
counter63 =Int('counter63')
s.add(counter63 >= 0)
s.add(counter63 <= 1)
counter64 =Int('counter64')
s.add(counter64 >= 0)
s.add(counter64 <= 1)
counter65 =Int('counter65')
s.add(counter65 >= 0)
s.add(counter65 <= 1)
counter66 =Int('counter66')
s.add(counter66 >= 0)
s.add(counter66 <= 1)
counter67 =Int('counter67')
s.add(counter67 >= 0)
s.add(counter67 <= 1)
counter68 =Int('counter68')
s.add(counter68 >= 0)
s.add(counter68 <= 1)
counter69 =Int('counter69')
s.add(counter69 >= 0)
s.add(counter69 <= 1)
counter70 =Int('counter70')
s.add(counter70 >= 0)
s.add(counter70 <= 1)
counter71 =Int('counter71')
s.add(counter71 >= 0)
s.add(counter71 <= 1)
counter72 =Int('counter72')
s.add(counter72 >= 0)
s.add(counter72 <= 1)
counter73 =Int('counter73')
s.add(counter73 >= 0)
s.add(counter73 <= 1)
counter74 =Int('counter74')
s.add(counter74 >= 0)
s.add(counter74 <= 1)
counter75 =Int('counter75')
s.add(counter75 >= 0)
s.add(counter75 <= 1)
counter76 =Int('counter76')
s.add(counter76 >= 0)
s.add(counter76 <= 1)
counter77 =Int('counter77')
s.add(counter77 >= 0)
s.add(counter77 <= 1)
counter78 =Int('counter78')
s.add(counter78 >= 0)
s.add(counter78 <= 1)
counter79 =Int('counter79')
s.add(counter79 >= 0)
s.add(counter79 <= 1)
counter80 =Int('counter80')
s.add(counter80 >= 0)
s.add(counter80 <= 1)
counter81 =Int('counter81')
s.add(counter81 >= 0)
s.add(counter81 <= 1)
counter82 =Int('counter82')
s.add(counter82 >= 0)
s.add(counter82 <= 1)
counter83 =Int('counter83')
s.add(counter83 >= 0)
s.add(counter83 <= 1)
counter84 =Int('counter84')
s.add(counter84 >= 0)
s.add(counter84 <= 1)
counter85 =Int('counter85')
s.add(counter85 >= 0)
s.add(counter85 <= 1)
counter86 =Int('counter86')
s.add(counter86 >= 0)
s.add(counter86 <= 1)
counter87 =Int('counter87')
s.add(counter87 >= 0)
s.add(counter87 <= 1)
counter88 =Int('counter88')
s.add(counter88 >= 0)
s.add(counter88 <= 1)
counter89 =Int('counter89')
s.add(counter89 >= 0)
s.add(counter89 <= 1)
counter90 =Int('counter90')
s.add(counter90 >= 0)
s.add(counter90 <= 1)
counter91 =Int('counter91')
s.add(counter91 >= 0)
s.add(counter91 <= 1)
counter92 =Int('counter92')
s.add(counter92 >= 0)
s.add(counter92 <= 1)
counter93 =Int('counter93')
s.add(counter93 >= 0)
s.add(counter93 <= 1)
counter94 =Int('counter94')
s.add(counter94 >= 0)
s.add(counter94 <= 1)
counter95 =Int('counter95')
s.add(counter95 >= 0)
s.add(counter95 <= 1)
counter96 =Int('counter96')
s.add(counter96 >= 0)
s.add(counter96 <= 1)
counter97 =Int('counter97')
s.add(counter97 >= 0)
s.add(counter97 <= 1)
counter98 =Int('counter98')
s.add(counter98 >= 0)
s.add(counter98 <= 1)
counter99 =Int('counter99')
s.add(counter99 >= 0)
s.add(counter99 <= 1)
counter100 =Int('counter100')
s.add(counter100 >= 0)
s.add(counter100 <= 1)
s.add( counter100 * 100 + counter2 * 2 + counter3 * 3 + counter4 * 4 + counter5 * 5 + counter6 * 6 + counter7 * 7 + counter8 * 8 + counter9 * 9 + counter10 * 10 + counter11 * 11 + counter12 * 12 + counter13 * 13 + counter14 * 14 + counter15 * 15 + counter16 * 16 + counter17 * 17 + counter18 * 18 + counter19 * 19 + counter20 * 20 + counter21 * 21 + counter22 * 22 + counter23 * 23 + counter24 * 24 + counter25 * 25 + counter26 * 26 + counter27 * 27 + counter28 * 28 + counter29 * 29 + counter30 * 30 + counter31 * 31 + counter32 * 32 + counter33 * 33 + counter34 * 34 + counter35 * 35 + counter36 * 36 + counter37 * 37 + counter38 * 38 + counter39 * 39 + counter40 * 40 + counter41 * 41 + counter42 * 42 + counter43 * 43 + counter44 * 44 + counter45 * 45 + counter46 * 46 + counter47 * 47 + counter48 * 48 + counter49 * 49 + counter50 * 50 + counter51 * 51 + counter52 * 52 + counter53 * 53 + counter54 * 54 + counter55 * 55 + counter56 * 56 + counter57 * 57 + counter58 * 58 + counter59 * 59 + counter60 * 60 + counter61 * 61 + counter62 * 62 + counter63 * 63 + counter64 * 64 + counter65 * 65 + counter66 * 66 + counter67 * 67 + counter68 * 68 + counter69 * 69 + counter70 * 70 + counter71 * 71 + counter72 * 72 + counter73 * 73 + counter74 * 74 + counter75 * 75 + counter76 * 76 + counter77 * 77 + counter78 * 78 + counter79 * 79 + counter80 * 80 + counter81 * 81 + counter82 * 82 + counter83 * 83 + counter84 * 84 + counter85 * 85 + counter86 * 86 + counter87 * 87 + counter88 * 88 + counter89 * 89 + counter90 * 90 + counter91 * 91 + counter92 * 92 + counter93 * 93 + counter94 * 94 + counter95 * 95 + counter96 * 96 + counter97 * 97 + counter98 * 98 + counter99 * 99 + counter100 * 100 == 75)
x=s.check()
if(x == z3.sat):
	m = s.model()
	print m
else:
	print unsat
