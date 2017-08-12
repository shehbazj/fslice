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


counter0=Int('counter0')
s.add(counter0 == 0)
s0= Int('s0')
counter1=Int('counter1')
s.add(counter1==If(s0 == 50,counter0 + 1, counter0 - 1))
s1=Int('s1')
counter2=Int('counter2')
s.add(counter2==If(s1 == 50,counter1 + 2, counter1 - 2))
s2=Int('s2')
counter3=Int('counter3')
s.add(counter3==If(s2 == 50,counter2 + 3, counter2 - 3))
s3=Int('s3')
counter4=Int('counter4')
s.add(counter4==If(s3 == 50,counter3 + 4, counter3 - 4))
s4=Int('s4')
counter5=Int('counter5')
s.add(counter5==If(s4 == 50,counter4 + 5, counter4 - 5))
s5=Int('s5')
counter6=Int('counter6')
s.add(counter6==If(s5 == 50,counter5 + 6, counter5 - 6))
s6=Int('s6')
counter7=Int('counter7')
s.add(counter7==If(s6 == 50,counter6 + 7, counter6 - 7))
s7=Int('s7')
counter8=Int('counter8')
s.add(counter8==If(s7 == 50,counter7 + 8, counter7 - 8))
s8=Int('s8')
counter9=Int('counter9')
s.add(counter9==If(s8 == 50,counter8 + 9, counter8 - 9))
s9=Int('s9')
counter10=Int('counter10')
s.add(counter10==If(s9 == 50,counter9 + 10, counter9 - 10))
s10=Int('s10')
counter11=Int('counter11')
s.add(counter11==If(s10 == 50,counter10 + 11, counter10 - 11))
s11=Int('s11')
counter12=Int('counter12')
s.add(counter12==If(s11 == 50,counter11 + 12, counter11 - 12))
s12=Int('s12')
counter13=Int('counter13')
s.add(counter13==If(s12 == 50,counter12 + 13, counter12 - 13))
s13=Int('s13')
counter14=Int('counter14')
s.add(counter14==If(s13 == 50,counter13 + 14, counter13 - 14))
s14=Int('s14')
counter15=Int('counter15')
s.add(counter15==If(s14 == 50,counter14 + 15, counter14 - 15))
s15=Int('s15')
counter16=Int('counter16')
s.add(counter16==If(s15 == 50,counter15 + 16, counter15 - 16))
s16=Int('s16')
counter17=Int('counter17')
s.add(counter17==If(s16 == 50,counter16 + 17, counter16 - 17))
s17=Int('s17')
counter18=Int('counter18')
s.add(counter18==If(s17 == 50,counter17 + 18, counter17 - 18))
s18=Int('s18')
counter19=Int('counter19')
s.add(counter19==If(s18 == 50,counter18 + 19, counter18 - 19))
s19=Int('s19')
counter20=Int('counter20')
s.add(counter20==If(s19 == 50,counter19 + 20, counter19 - 20))
s20=Int('s20')

counter_final=Int('counter_final')
s.add(counter_final == 13)
s.add(counter_final == counter20)
x=s.check()
if(x == z3.sat):
	m = s.model()
	print m
else:
	print unsat
