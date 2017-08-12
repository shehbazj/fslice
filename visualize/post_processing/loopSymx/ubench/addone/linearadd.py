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
count2=Int('count2')
count3=Int('count3')
count4=Int('count4')
count5=Int('count5')
count6=Int('count6')
count7=Int('count7')
count8=Int('count8')
count9=Int('count9')
count10=Int('count10')
count11=Int('count11')
count12=Int('count12')
count13=Int('count13')
count14=Int('count14')
count15=Int('count15')
count16=Int('count16')
count17=Int('count17')
count18=Int('count18')
count19=Int('count19')
count20=Int('count20')
count21=Int('count21')
count22=Int('count22')
count23=Int('count23')
count24=Int('count24')
count25=Int('count25')
count26=Int('count26')
count27=Int('count27')
count28=Int('count28')
count29=Int('count29')
count30=Int('count30')
count31=Int('count31')
count32=Int('count32')
count33=Int('count33')
count34=Int('count34')
count35=Int('count35')
count36=Int('count36')
count37=Int('count37')
count38=Int('count38')
count39=Int('count39')
count40=Int('count40')
count41=Int('count41')
count42=Int('count42')
count43=Int('count43')
count44=Int('count44')
count45=Int('count45')
count46=Int('count46')
count47=Int('count47')
count48=Int('count48')
count49=Int('count49')
count50=Int('count50')
count51=Int('count51')
count52=Int('count52')
count53=Int('count53')
count54=Int('count54')
count55=Int('count55')
count56=Int('count56')
count57=Int('count57')
count58=Int('count58')
count59=Int('count59')
count60=Int('count60')
count61=Int('count61')
count62=Int('count62')
count63=Int('count63')
count64=Int('count64')
count65=Int('count65')
count66=Int('count66')
count67=Int('count67')
count68=Int('count68')
count69=Int('count69')
count70=Int('count70')
count71=Int('count71')
count72=Int('count72')
count73=Int('count73')
count74=Int('count74')
count75=Int('count75')
count76=Int('count76')
count77=Int('count77')
count78=Int('count78')
count79=Int('count79')
count80=Int('count80')
count81=Int('count81')
count82=Int('count82')
count83=Int('count83')
count84=Int('count84')
count85=Int('count85')
count86=Int('count86')
count87=Int('count87')
count88=Int('count88')
count89=Int('count89')
count90=Int('count90')
count91=Int('count91')
count92=Int('count92')
count93=Int('count93')
count94=Int('count94')
count95=Int('count95')
count96=Int('count96')
count97=Int('count97')
count98=Int('count98')
count99=Int('count99')
count100=Int('count100')

s.add(count1 >= 0)
s.add(count2 >= 0)
s.add(count3 >= 0)
s.add(count4 >= 0)
s.add(count5 >= 0)
s.add(count6 >= 0)
s.add(count7 >= 0)
s.add(count8 >= 0)
s.add(count9 >= 0)
s.add(count10 >= 0)
s.add(count11 >= 0)
s.add(count12 >= 0)
s.add(count13 >= 0)
s.add(count14 >= 0)
s.add(count15 >= 0)
s.add(count16 >= 0)
s.add(count17 >= 0)
s.add(count18 >= 0)
s.add(count19 >= 0)
s.add(count20 >= 0)
s.add(count21 >= 0)
s.add(count22 >= 0)
s.add(count23 >= 0)
s.add(count24 >= 0)
s.add(count25 >= 0)
s.add(count26 >= 0)
s.add(count27 >= 0)
s.add(count28 >= 0)
s.add(count29 >= 0)
s.add(count30 >= 0)
s.add(count31 >= 0)
s.add(count32 >= 0)
s.add(count33 >= 0)
s.add(count34 >= 0)
s.add(count35 >= 0)
s.add(count36 >= 0)
s.add(count37 >= 0)
s.add(count38 >= 0)
s.add(count39 >= 0)
s.add(count40 >= 0)
s.add(count41 >= 0)
s.add(count42 >= 0)
s.add(count43 >= 0)
s.add(count44 >= 0)
s.add(count45 >= 0)
s.add(count46 >= 0)
s.add(count47 >= 0)
s.add(count48 >= 0)
s.add(count49 >= 0)
s.add(count50 >= 0)
s.add(count51 >= 0)
s.add(count52 >= 0)
s.add(count53 >= 0)
s.add(count54 >= 0)
s.add(count55 >= 0)
s.add(count56 >= 0)
s.add(count57 >= 0)
s.add(count58 >= 0)
s.add(count59 >= 0)
s.add(count60 >= 0)
s.add(count61 >= 0)
s.add(count62 >= 0)
s.add(count63 >= 0)
s.add(count64 >= 0)
s.add(count65 >= 0)
s.add(count66 >= 0)
s.add(count67 >= 0)
s.add(count68 >= 0)
s.add(count69 >= 0)
s.add(count70 >= 0)
s.add(count71 >= 0)
s.add(count72 >= 0)
s.add(count73 >= 0)
s.add(count74 >= 0)
s.add(count75 >= 0)
s.add(count76 >= 0)
s.add(count77 >= 0)
s.add(count78 >= 0)
s.add(count79 >= 0)
s.add(count80 >= 0)
s.add(count81 >= 0)
s.add(count82 >= 0)
s.add(count83 >= 0)
s.add(count84 >= 0)
s.add(count85 >= 0)
s.add(count86 >= 0)
s.add(count87 >= 0)
s.add(count88 >= 0)
s.add(count89 >= 0)
s.add(count90 >= 0)
s.add(count91 >= 0)
s.add(count92 >= 0)
s.add(count93 >= 0)
s.add(count94 >= 0)
s.add(count95 >= 0)
s.add(count96 >= 0)
s.add(count97 >= 0)
s.add(count98 >= 0)
s.add(count99 >= 0)
s.add(count100 >= 0)

s.add(count1 <= 1)
s.add(count2 <= 1)
s.add(count3 <= 1)
s.add(count4 <= 1)
s.add(count5 <= 1)
s.add(count6 <= 1)
s.add(count7 <= 1)
s.add(count8 <= 1)
s.add(count9 <= 1)
s.add(count10 <= 1)
s.add(count11 <= 1)
s.add(count12 <= 1)
s.add(count13 <= 1)
s.add(count14 <= 1)
s.add(count15 <= 1)
s.add(count16 <= 1)
s.add(count17 <= 1)
s.add(count18 <= 1)
s.add(count19 <= 1)
s.add(count20 <= 1)
s.add(count21 <= 1)
s.add(count22 <= 1)
s.add(count23 <= 1)
s.add(count24 <= 1)
s.add(count25 <= 1)
s.add(count26 <= 1)
s.add(count27 <= 1)
s.add(count28 <= 1)
s.add(count29 <= 1)
s.add(count30 <= 1)
s.add(count31 <= 1)
s.add(count32 <= 1)
s.add(count33 <= 1)
s.add(count34 <= 1)
s.add(count35 <= 1)
s.add(count36 <= 1)
s.add(count37 <= 1)
s.add(count38 <= 1)
s.add(count39 <= 1)
s.add(count40 <= 1)
s.add(count41 <= 1)
s.add(count42 <= 1)
s.add(count43 <= 1)
s.add(count44 <= 1)
s.add(count45 <= 1)
s.add(count46 <= 1)
s.add(count47 <= 1)
s.add(count48 <= 1)
s.add(count49 <= 1)
s.add(count50 <= 1)
s.add(count51 <= 1)
s.add(count52 <= 1)
s.add(count53 <= 1)
s.add(count54 <= 1)
s.add(count55 <= 1)
s.add(count56 <= 1)
s.add(count57 <= 1)
s.add(count58 <= 1)
s.add(count59 <= 1)
s.add(count60 <= 1)
s.add(count61 <= 1)
s.add(count62 <= 1)
s.add(count63 <= 1)
s.add(count64 <= 1)
s.add(count65 <= 1)
s.add(count66 <= 1)
s.add(count67 <= 1)
s.add(count68 <= 1)
s.add(count69 <= 1)
s.add(count70 <= 1)
s.add(count71 <= 1)
s.add(count72 <= 1)
s.add(count73 <= 1)
s.add(count74 <= 1)
s.add(count75 <= 1)
s.add(count76 <= 1)
s.add(count77 <= 1)
s.add(count78 <= 1)
s.add(count79 <= 1)
s.add(count80 <= 1)
s.add(count81 <= 1)
s.add(count82 <= 1)
s.add(count83 <= 1)
s.add(count84 <= 1)
s.add(count85 <= 1)
s.add(count86 <= 1)
s.add(count87 <= 1)
s.add(count88 <= 1)
s.add(count89 <= 1)
s.add(count90 <= 1)
s.add(count91 <= 1)
s.add(count92 <= 1)
s.add(count93 <= 1)
s.add(count94 <= 1)
s.add(count95 <= 1)
s.add(count96 <= 1)
s.add(count97 <= 1)
s.add(count98 <= 1)
s.add(count99 <= 1)
s.add(count100 <= 1)

s.add( count1 + count2 + count3 + count4 + count5 + count6 + count7 + count8 + count9 + count10 + count11 + count12 + count13 + count14 + count15 + count16 + count17 + count18 + count19 + count20 + count21 + count22 + count23 + count24 + count25 + count26 + count27 + count28 + count29 + count30 + count31 + count32 + count33 + count34 + count35 + count36 + count37 + count38 + count39 + count40 + count41 + count42 + count43 + count44 + count45 + count46 + count47 + count48 + count49 + count50 + count51 + count52 + count53 + count54 + count55 + count56 + count57 + count58 + count59 + count60 + count61 + count62 + count63 + count64 + count65 + count66 + count67 + count68 + count69 + count70 + count71 + count72 + count73 + count74 + count75 + count76 + count77 + count78 + count79 + count80 + count81 + count82 + count83 + count84 + count85 + count86 + count87 + count88 + count89 + count90 + count91 + count92 + count93 + count94 + count95 + count96 + count97 + count98 + count99 + count100 == 75)

x=s.check()
if(x == z3.sat):
	m = s.model()
	print m
else:
	print unsat

