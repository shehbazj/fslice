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


count1=Int('count1')
s.add(count1 <= 1)
s.add(count1 >= 0)
count2=Int('count2')
s.add(count2 <= 1)
s.add(count2 >= 0)
count3=Int('count3')
s.add(count3 <= 1)
s.add(count3 >= 0)
count4=Int('count4')
s.add(count4 <= 1)
s.add(count4 >= 0)
count5=Int('count5')
s.add(count5 <= 1)
s.add(count5 >= 0)
count6=Int('count6')
s.add(count6 <= 1)
s.add(count6 >= 0)
count7=Int('count7')
s.add(count7 <= 1)
s.add(count7 >= 0)
count8=Int('count8')
s.add(count8 <= 1)
s.add(count8 >= 0)
count9=Int('count9')
s.add(count9 <= 1)
s.add(count9 >= 0)
count10=Int('count10')
s.add(count10 <= 1)
s.add(count10 >= 0)
count11=Int('count11')
s.add(count11 <= 1)
s.add(count11 >= 0)
count12=Int('count12')
s.add(count12 <= 1)
s.add(count12 >= 0)
count13=Int('count13')
s.add(count13 <= 1)
s.add(count13 >= 0)
count14=Int('count14')
s.add(count14 <= 1)
s.add(count14 >= 0)
count15=Int('count15')
s.add(count15 <= 1)
s.add(count15 >= 0)
count16=Int('count16')
s.add(count16 <= 1)
s.add(count16 >= 0)
count17=Int('count17')
s.add(count17 <= 1)
s.add(count17 >= 0)
count18=Int('count18')
s.add(count18 <= 1)
s.add(count18 >= 0)
count19=Int('count19')
s.add(count19 <= 1)
s.add(count19 >= 0)
count20=Int('count20')
s.add(count20 <= 1)
s.add(count20 >= 0)
count21=Int('count21')
s.add(count21 <= 1)
s.add(count21 >= 0)
count22=Int('count22')
s.add(count22 <= 1)
s.add(count22 >= 0)
count23=Int('count23')
s.add(count23 <= 1)
s.add(count23 >= 0)
count24=Int('count24')
s.add(count24 <= 1)
s.add(count24 >= 0)
count25=Int('count25')
s.add(count25 <= 1)
s.add(count25 >= 0)
count26=Int('count26')
s.add(count26 <= 1)
s.add(count26 >= 0)
count27=Int('count27')
s.add(count27 <= 1)
s.add(count27 >= 0)
count28=Int('count28')
s.add(count28 <= 1)
s.add(count28 >= 0)
count29=Int('count29')
s.add(count29 <= 1)
s.add(count29 >= 0)
count30=Int('count30')
s.add(count30 <= 1)
s.add(count30 >= 0)
count31=Int('count31')
s.add(count31 <= 1)
s.add(count31 >= 0)
count32=Int('count32')
s.add(count32 <= 1)
s.add(count32 >= 0)
count33=Int('count33')
s.add(count33 <= 1)
s.add(count33 >= 0)
count34=Int('count34')
s.add(count34 <= 1)
s.add(count34 >= 0)
count35=Int('count35')
s.add(count35 <= 1)
s.add(count35 >= 0)
count36=Int('count36')
s.add(count36 <= 1)
s.add(count36 >= 0)
count37=Int('count37')
s.add(count37 <= 1)
s.add(count37 >= 0)
count38=Int('count38')
s.add(count38 <= 1)
s.add(count38 >= 0)
count39=Int('count39')
s.add(count39 <= 1)
s.add(count39 >= 0)
count40=Int('count40')
s.add(count40 <= 1)
s.add(count40 >= 0)
count41=Int('count41')
s.add(count41 <= 1)
s.add(count41 >= 0)
count42=Int('count42')
s.add(count42 <= 1)
s.add(count42 >= 0)
count43=Int('count43')
s.add(count43 <= 1)
s.add(count43 >= 0)
count44=Int('count44')
s.add(count44 <= 1)
s.add(count44 >= 0)
count45=Int('count45')
s.add(count45 <= 1)
s.add(count45 >= 0)
count46=Int('count46')
s.add(count46 <= 1)
s.add(count46 >= 0)
count47=Int('count47')
s.add(count47 <= 1)
s.add(count47 >= 0)
count48=Int('count48')
s.add(count48 <= 1)
s.add(count48 >= 0)
count49=Int('count49')
s.add(count49 <= 1)
s.add(count49 >= 0)
count50=Int('count50')
s.add(count50 <= 1)
s.add(count50 >= 0)
count51=Int('count51')
s.add(count51 <= 1)
s.add(count51 >= 0)
count52=Int('count52')
s.add(count52 <= 1)
s.add(count52 >= 0)
count53=Int('count53')
s.add(count53 <= 1)
s.add(count53 >= 0)
count54=Int('count54')
s.add(count54 <= 1)
s.add(count54 >= 0)
count55=Int('count55')
s.add(count55 <= 1)
s.add(count55 >= 0)
count56=Int('count56')
s.add(count56 <= 1)
s.add(count56 >= 0)
count57=Int('count57')
s.add(count57 <= 1)
s.add(count57 >= 0)
count58=Int('count58')
s.add(count58 <= 1)
s.add(count58 >= 0)
count59=Int('count59')
s.add(count59 <= 1)
s.add(count59 >= 0)
count60=Int('count60')
s.add(count60 <= 1)
s.add(count60 >= 0)

s.add((count1 * 1) + (count2 * 2) + (count3 * 3) + (count4 * 4) + (count5 * 5) + (count6 * 6) + (count7 * 7) + (count8 * 8) + (count9 * 9) + (count10 * 10) + (count11 * 11) + (count12 * 12) + (count13 * 13) + (count14 * 14) + (count15 * 15) + (count16 * 16) + (count17 * 17) + (count18 * 18) + (count19 * 19) + (count20 * 20) + (count21 * 21) + (count22 * 22) + (count23 * 23) + (count24 * 24) + (count25 * 25) + (count26 * 26) + (count27 * 27) + (count28 * 28) + (count29 * 29) + (count30 * 30) + (count31 * 31) + (count32 * 32) + (count33 * 33) + (count34 * 34) + (count35 * 35) + (count36 * 36) + (count37 * 37) + (count38 * 38) + (count39 * 39) + (count40 * 40) + (count41 * 41) + (count42 * 42) + (count43 * 43) + (count44 * 44) + (count45 * 45) + (count46 * 46) + (count47 * 47) + (count48 * 48) + (count49 * 49) + (count50 * 50) + (count51 * 51) + (count52 * 52) + (count53 * 53) + (count54 * 54) + (count55 * 55) + (count56 * 56) + (count57 * 57) + (count58 * 58) + (count59 * 59) + (count60 * 60)  == 75)
x=s.check()
if(x == z3.sat):
        m = s.model()
        print m
else:   
        print unsat


