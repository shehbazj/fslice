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
negcount1=Int('negcount1')
s.add(count1 <= 1)
s.add(count1 >= 0)
s.add(negcount1 <= 1)
s.add(negcount1 >= 0)
count2=Int('count2')
negcount2=Int('negcount2')
s.add(count2 <= 1)
s.add(count2 >= 0)
s.add(negcount2 <= 1)
s.add(negcount2 >= 0)
count3=Int('count3')
negcount3=Int('negcount3')
s.add(count3 <= 1)
s.add(count3 >= 0)
s.add(negcount3 <= 1)
s.add(negcount3 >= 0)
count4=Int('count4')
negcount4=Int('negcount4')
s.add(count4 <= 1)
s.add(count4 >= 0)
s.add(negcount4 <= 1)
s.add(negcount4 >= 0)
count5=Int('count5')
negcount5=Int('negcount5')
s.add(count5 <= 1)
s.add(count5 >= 0)
s.add(negcount5 <= 1)
s.add(negcount5 >= 0)
count6=Int('count6')
negcount6=Int('negcount6')
s.add(count6 <= 1)
s.add(count6 >= 0)
s.add(negcount6 <= 1)
s.add(negcount6 >= 0)
count7=Int('count7')
negcount7=Int('negcount7')
s.add(count7 <= 1)
s.add(count7 >= 0)
s.add(negcount7 <= 1)
s.add(negcount7 >= 0)
count8=Int('count8')
negcount8=Int('negcount8')
s.add(count8 <= 1)
s.add(count8 >= 0)
s.add(negcount8 <= 1)
s.add(negcount8 >= 0)
count9=Int('count9')
negcount9=Int('negcount9')
s.add(count9 <= 1)
s.add(count9 >= 0)
s.add(negcount9 <= 1)
s.add(negcount9 >= 0)
count10=Int('count10')
negcount10=Int('negcount10')
s.add(count10 <= 1)
s.add(count10 >= 0)
s.add(negcount10 <= 1)
s.add(negcount10 >= 0)
count11=Int('count11')
negcount11=Int('negcount11')
s.add(count11 <= 1)
s.add(count11 >= 0)
s.add(negcount11 <= 1)
s.add(negcount11 >= 0)
count12=Int('count12')
negcount12=Int('negcount12')
s.add(count12 <= 1)
s.add(count12 >= 0)
s.add(negcount12 <= 1)
s.add(negcount12 >= 0)
count13=Int('count13')
negcount13=Int('negcount13')
s.add(count13 <= 1)
s.add(count13 >= 0)
s.add(negcount13 <= 1)
s.add(negcount13 >= 0)
count14=Int('count14')
negcount14=Int('negcount14')
s.add(count14 <= 1)
s.add(count14 >= 0)
s.add(negcount14 <= 1)
s.add(negcount14 >= 0)
count15=Int('count15')
negcount15=Int('negcount15')
s.add(count15 <= 1)
s.add(count15 >= 0)
s.add(negcount15 <= 1)
s.add(negcount15 >= 0)
count16=Int('count16')
negcount16=Int('negcount16')
s.add(count16 <= 1)
s.add(count16 >= 0)
s.add(negcount16 <= 1)
s.add(negcount16 >= 0)
count17=Int('count17')
negcount17=Int('negcount17')
s.add(count17 <= 1)
s.add(count17 >= 0)
s.add(negcount17 <= 1)
s.add(negcount17 >= 0)
count18=Int('count18')
negcount18=Int('negcount18')
s.add(count18 <= 1)
s.add(count18 >= 0)
s.add(negcount18 <= 1)
s.add(negcount18 >= 0)
count19=Int('count19')
negcount19=Int('negcount19')
s.add(count19 <= 1)
s.add(count19 >= 0)
s.add(negcount19 <= 1)
s.add(negcount19 >= 0)
count20=Int('count20')
negcount20=Int('negcount20')
s.add(count20 <= 1)
s.add(count20 >= 0)
s.add(negcount20 <= 1)
s.add(negcount20 >= 0)
count21=Int('count21')
negcount21=Int('negcount21')
s.add(count21 <= 1)
s.add(count21 >= 0)
s.add(negcount21 <= 1)
s.add(negcount21 >= 0)
count22=Int('count22')
negcount22=Int('negcount22')
s.add(count22 <= 1)
s.add(count22 >= 0)
s.add(negcount22 <= 1)
s.add(negcount22 >= 0)
count23=Int('count23')
negcount23=Int('negcount23')
s.add(count23 <= 1)
s.add(count23 >= 0)
s.add(negcount23 <= 1)
s.add(negcount23 >= 0)
count24=Int('count24')
negcount24=Int('negcount24')
s.add(count24 <= 1)
s.add(count24 >= 0)
s.add(negcount24 <= 1)
s.add(negcount24 >= 0)
count25=Int('count25')
negcount25=Int('negcount25')
s.add(count25 <= 1)
s.add(count25 >= 0)
s.add(negcount25 <= 1)
s.add(negcount25 >= 0)
count26=Int('count26')
negcount26=Int('negcount26')
s.add(count26 <= 1)
s.add(count26 >= 0)
s.add(negcount26 <= 1)
s.add(negcount26 >= 0)
count27=Int('count27')
negcount27=Int('negcount27')
s.add(count27 <= 1)
s.add(count27 >= 0)
s.add(negcount27 <= 1)
s.add(negcount27 >= 0)
count28=Int('count28')
negcount28=Int('negcount28')
s.add(count28 <= 1)
s.add(count28 >= 0)
s.add(negcount28 <= 1)
s.add(negcount28 >= 0)
count29=Int('count29')
negcount29=Int('negcount29')
s.add(count29 <= 1)
s.add(count29 >= 0)
s.add(negcount29 <= 1)
s.add(negcount29 >= 0)
count30=Int('count30')
negcount30=Int('negcount30')
s.add(count30 <= 1)
s.add(count30 >= 0)
s.add(negcount30 <= 1)
s.add(negcount30 >= 0)
count31=Int('count31')
negcount31=Int('negcount31')
s.add(count31 <= 1)
s.add(count31 >= 0)
s.add(negcount31 <= 1)
s.add(negcount31 >= 0)
count32=Int('count32')
negcount32=Int('negcount32')
s.add(count32 <= 1)
s.add(count32 >= 0)
s.add(negcount32 <= 1)
s.add(negcount32 >= 0)
count33=Int('count33')
negcount33=Int('negcount33')
s.add(count33 <= 1)
s.add(count33 >= 0)
s.add(negcount33 <= 1)
s.add(negcount33 >= 0)
count34=Int('count34')
negcount34=Int('negcount34')
s.add(count34 <= 1)
s.add(count34 >= 0)
s.add(negcount34 <= 1)
s.add(negcount34 >= 0)
count35=Int('count35')
negcount35=Int('negcount35')
s.add(count35 <= 1)
s.add(count35 >= 0)
s.add(negcount35 <= 1)
s.add(negcount35 >= 0)
count36=Int('count36')
negcount36=Int('negcount36')
s.add(count36 <= 1)
s.add(count36 >= 0)
s.add(negcount36 <= 1)
s.add(negcount36 >= 0)
count37=Int('count37')
negcount37=Int('negcount37')
s.add(count37 <= 1)
s.add(count37 >= 0)
s.add(negcount37 <= 1)
s.add(negcount37 >= 0)
count38=Int('count38')
negcount38=Int('negcount38')
s.add(count38 <= 1)
s.add(count38 >= 0)
s.add(negcount38 <= 1)
s.add(negcount38 >= 0)
count39=Int('count39')
negcount39=Int('negcount39')
s.add(count39 <= 1)
s.add(count39 >= 0)
s.add(negcount39 <= 1)
s.add(negcount39 >= 0)
count40=Int('count40')
negcount40=Int('negcount40')
s.add(count40 <= 1)
s.add(count40 >= 0)
s.add(negcount40 <= 1)
s.add(negcount40 >= 0)
count41=Int('count41')
negcount41=Int('negcount41')
s.add(count41 <= 1)
s.add(count41 >= 0)
s.add(negcount41 <= 1)
s.add(negcount41 >= 0)
count42=Int('count42')
negcount42=Int('negcount42')
s.add(count42 <= 1)
s.add(count42 >= 0)
s.add(negcount42 <= 1)
s.add(negcount42 >= 0)
count43=Int('count43')
negcount43=Int('negcount43')
s.add(count43 <= 1)
s.add(count43 >= 0)
s.add(negcount43 <= 1)
s.add(negcount43 >= 0)
count44=Int('count44')
negcount44=Int('negcount44')
s.add(count44 <= 1)
s.add(count44 >= 0)
s.add(negcount44 <= 1)
s.add(negcount44 >= 0)
count45=Int('count45')
negcount45=Int('negcount45')
s.add(count45 <= 1)
s.add(count45 >= 0)
s.add(negcount45 <= 1)
s.add(negcount45 >= 0)
count46=Int('count46')
negcount46=Int('negcount46')
s.add(count46 <= 1)
s.add(count46 >= 0)
s.add(negcount46 <= 1)
s.add(negcount46 >= 0)
count47=Int('count47')
negcount47=Int('negcount47')
s.add(count47 <= 1)
s.add(count47 >= 0)
s.add(negcount47 <= 1)
s.add(negcount47 >= 0)
count48=Int('count48')
negcount48=Int('negcount48')
s.add(count48 <= 1)
s.add(count48 >= 0)
s.add(negcount48 <= 1)
s.add(negcount48 >= 0)
count49=Int('count49')
negcount49=Int('negcount49')
s.add(count49 <= 1)
s.add(count49 >= 0)
s.add(negcount49 <= 1)
s.add(negcount49 >= 0)
count50=Int('count50')
negcount50=Int('negcount50')
s.add(count50 <= 1)
s.add(count50 >= 0)
s.add(negcount50 <= 1)
s.add(negcount50 >= 0)
count51=Int('count51')
negcount51=Int('negcount51')
s.add(count51 <= 1)
s.add(count51 >= 0)
s.add(negcount51 <= 1)
s.add(negcount51 >= 0)
count52=Int('count52')
negcount52=Int('negcount52')
s.add(count52 <= 1)
s.add(count52 >= 0)
s.add(negcount52 <= 1)
s.add(negcount52 >= 0)
count53=Int('count53')
negcount53=Int('negcount53')
s.add(count53 <= 1)
s.add(count53 >= 0)
s.add(negcount53 <= 1)
s.add(negcount53 >= 0)
count54=Int('count54')
negcount54=Int('negcount54')
s.add(count54 <= 1)
s.add(count54 >= 0)
s.add(negcount54 <= 1)
s.add(negcount54 >= 0)
count55=Int('count55')
negcount55=Int('negcount55')
s.add(count55 <= 1)
s.add(count55 >= 0)
s.add(negcount55 <= 1)
s.add(negcount55 >= 0)
count56=Int('count56')
negcount56=Int('negcount56')
s.add(count56 <= 1)
s.add(count56 >= 0)
s.add(negcount56 <= 1)
s.add(negcount56 >= 0)
count57=Int('count57')
negcount57=Int('negcount57')
s.add(count57 <= 1)
s.add(count57 >= 0)
s.add(negcount57 <= 1)
s.add(negcount57 >= 0)
count58=Int('count58')
negcount58=Int('negcount58')
s.add(count58 <= 1)
s.add(count58 >= 0)
s.add(negcount58 <= 1)
s.add(negcount58 >= 0)
count59=Int('count59')
negcount59=Int('negcount59')
s.add(count59 <= 1)
s.add(count59 >= 0)
s.add(negcount59 <= 1)
s.add(negcount59 >= 0)
count60=Int('count60')
negcount60=Int('negcount60')
s.add(count60 <= 1)
s.add(count60 >= 0)
s.add(negcount60 <= 1)
s.add(negcount60 >= 0)
count61=Int('count61')
negcount61=Int('negcount61')
s.add(count61 <= 1)
s.add(count61 >= 0)
s.add(negcount61 <= 1)
s.add(negcount61 >= 0)
count62=Int('count62')
negcount62=Int('negcount62')
s.add(count62 <= 1)
s.add(count62 >= 0)
s.add(negcount62 <= 1)
s.add(negcount62 >= 0)
count63=Int('count63')
negcount63=Int('negcount63')
s.add(count63 <= 1)
s.add(count63 >= 0)
s.add(negcount63 <= 1)
s.add(negcount63 >= 0)
count64=Int('count64')
negcount64=Int('negcount64')
s.add(count64 <= 1)
s.add(count64 >= 0)
s.add(negcount64 <= 1)
s.add(negcount64 >= 0)
count65=Int('count65')
negcount65=Int('negcount65')
s.add(count65 <= 1)
s.add(count65 >= 0)
s.add(negcount65 <= 1)
s.add(negcount65 >= 0)
count66=Int('count66')
negcount66=Int('negcount66')
s.add(count66 <= 1)
s.add(count66 >= 0)
s.add(negcount66 <= 1)
s.add(negcount66 >= 0)
count67=Int('count67')
negcount67=Int('negcount67')
s.add(count67 <= 1)
s.add(count67 >= 0)
s.add(negcount67 <= 1)
s.add(negcount67 >= 0)
count68=Int('count68')
negcount68=Int('negcount68')
s.add(count68 <= 1)
s.add(count68 >= 0)
s.add(negcount68 <= 1)
s.add(negcount68 >= 0)
count69=Int('count69')
negcount69=Int('negcount69')
s.add(count69 <= 1)
s.add(count69 >= 0)
s.add(negcount69 <= 1)
s.add(negcount69 >= 0)
count70=Int('count70')
negcount70=Int('negcount70')
s.add(count70 <= 1)
s.add(count70 >= 0)
s.add(negcount70 <= 1)
s.add(negcount70 >= 0)
count71=Int('count71')
negcount71=Int('negcount71')
s.add(count71 <= 1)
s.add(count71 >= 0)
s.add(negcount71 <= 1)
s.add(negcount71 >= 0)
count72=Int('count72')
negcount72=Int('negcount72')
s.add(count72 <= 1)
s.add(count72 >= 0)
s.add(negcount72 <= 1)
s.add(negcount72 >= 0)
count73=Int('count73')
negcount73=Int('negcount73')
s.add(count73 <= 1)
s.add(count73 >= 0)
s.add(negcount73 <= 1)
s.add(negcount73 >= 0)
count74=Int('count74')
negcount74=Int('negcount74')
s.add(count74 <= 1)
s.add(count74 >= 0)
s.add(negcount74 <= 1)
s.add(negcount74 >= 0)
count75=Int('count75')
negcount75=Int('negcount75')
s.add(count75 <= 1)
s.add(count75 >= 0)
s.add(negcount75 <= 1)
s.add(negcount75 >= 0)
count76=Int('count76')
negcount76=Int('negcount76')
s.add(count76 <= 1)
s.add(count76 >= 0)
s.add(negcount76 <= 1)
s.add(negcount76 >= 0)
count77=Int('count77')
negcount77=Int('negcount77')
s.add(count77 <= 1)
s.add(count77 >= 0)
s.add(negcount77 <= 1)
s.add(negcount77 >= 0)
count78=Int('count78')
negcount78=Int('negcount78')
s.add(count78 <= 1)
s.add(count78 >= 0)
s.add(negcount78 <= 1)
s.add(negcount78 >= 0)
count79=Int('count79')
negcount79=Int('negcount79')
s.add(count79 <= 1)
s.add(count79 >= 0)
s.add(negcount79 <= 1)
s.add(negcount79 >= 0)
count80=Int('count80')
negcount80=Int('negcount80')
s.add(count80 <= 1)
s.add(count80 >= 0)
s.add(negcount80 <= 1)
s.add(negcount80 >= 0)
count81=Int('count81')
negcount81=Int('negcount81')
s.add(count81 <= 1)
s.add(count81 >= 0)
s.add(negcount81 <= 1)
s.add(negcount81 >= 0)
count82=Int('count82')
negcount82=Int('negcount82')
s.add(count82 <= 1)
s.add(count82 >= 0)
s.add(negcount82 <= 1)
s.add(negcount82 >= 0)
count83=Int('count83')
negcount83=Int('negcount83')
s.add(count83 <= 1)
s.add(count83 >= 0)
s.add(negcount83 <= 1)
s.add(negcount83 >= 0)
count84=Int('count84')
negcount84=Int('negcount84')
s.add(count84 <= 1)
s.add(count84 >= 0)
s.add(negcount84 <= 1)
s.add(negcount84 >= 0)
count85=Int('count85')
negcount85=Int('negcount85')
s.add(count85 <= 1)
s.add(count85 >= 0)
s.add(negcount85 <= 1)
s.add(negcount85 >= 0)
count86=Int('count86')
negcount86=Int('negcount86')
s.add(count86 <= 1)
s.add(count86 >= 0)
s.add(negcount86 <= 1)
s.add(negcount86 >= 0)
count87=Int('count87')
negcount87=Int('negcount87')
s.add(count87 <= 1)
s.add(count87 >= 0)
s.add(negcount87 <= 1)
s.add(negcount87 >= 0)
count88=Int('count88')
negcount88=Int('negcount88')
s.add(count88 <= 1)
s.add(count88 >= 0)
s.add(negcount88 <= 1)
s.add(negcount88 >= 0)
count89=Int('count89')
negcount89=Int('negcount89')
s.add(count89 <= 1)
s.add(count89 >= 0)
s.add(negcount89 <= 1)
s.add(negcount89 >= 0)
count90=Int('count90')
negcount90=Int('negcount90')
s.add(count90 <= 1)
s.add(count90 >= 0)
s.add(negcount90 <= 1)
s.add(negcount90 >= 0)
count91=Int('count91')
negcount91=Int('negcount91')
s.add(count91 <= 1)
s.add(count91 >= 0)
s.add(negcount91 <= 1)
s.add(negcount91 >= 0)
count92=Int('count92')
negcount92=Int('negcount92')
s.add(count92 <= 1)
s.add(count92 >= 0)
s.add(negcount92 <= 1)
s.add(negcount92 >= 0)
count93=Int('count93')
negcount93=Int('negcount93')
s.add(count93 <= 1)
s.add(count93 >= 0)
s.add(negcount93 <= 1)
s.add(negcount93 >= 0)
count94=Int('count94')
negcount94=Int('negcount94')
s.add(count94 <= 1)
s.add(count94 >= 0)
s.add(negcount94 <= 1)
s.add(negcount94 >= 0)
count95=Int('count95')
negcount95=Int('negcount95')
s.add(count95 <= 1)
s.add(count95 >= 0)
s.add(negcount95 <= 1)
s.add(negcount95 >= 0)
count96=Int('count96')
negcount96=Int('negcount96')
s.add(count96 <= 1)
s.add(count96 >= 0)
s.add(negcount96 <= 1)
s.add(negcount96 >= 0)
count97=Int('count97')
negcount97=Int('negcount97')
s.add(count97 <= 1)
s.add(count97 >= 0)
s.add(negcount97 <= 1)
s.add(negcount97 >= 0)
count98=Int('count98')
negcount98=Int('negcount98')
s.add(count98 <= 1)
s.add(count98 >= 0)
s.add(negcount98 <= 1)
s.add(negcount98 >= 0)
count99=Int('count99')
negcount99=Int('negcount99')
s.add(count99 <= 1)
s.add(count99 >= 0)
s.add(negcount99 <= 1)
s.add(negcount99 >= 0)
count100=Int('count100')
negcount100=Int('negcount100')
s.add(count100 <= 1)
s.add(count100 >= 0)
s.add(negcount100 <= 1)
s.add(negcount100 >= 0)

s.add ((count1 * 1 + (negcount1 * -1)) + (count2 * 2 + (negcount2 * -2)) + (count3 * 3 + (negcount3 * -3)) + (count4 * 4 + (negcount4 * -4)) + (count5 * 5 + (negcount5 * -5)) + (count6 * 6 + (negcount6 * -6)) + (count7 * 7 + (negcount7 * -7)) + (count8 * 8 + (negcount8 * -8)) + (count9 * 9 + (negcount9 * -9)) + (count10 * 10 + (negcount10 * -10)) + (count11 * 11 + (negcount11 * -11)) + (count12 * 12 + (negcount12 * -12)) + (count13 * 13 + (negcount13 * -13)) + (count14 * 14 + (negcount14 * -14)) + (count15 * 15 + (negcount15 * -15)) + (count16 * 16 + (negcount16 * -16)) + (count17 * 17 + (negcount17 * -17)) + (count18 * 18 + (negcount18 * -18)) + (count19 * 19 + (negcount19 * -19)) + (count20 * 20 + (negcount20 * -20)) + (count21 * 21 + (negcount21 * -21)) + (count22 * 22 + (negcount22 * -22)) + (count23 * 23 + (negcount23 * -23)) + (count24 * 24 + (negcount24 * -24)) + (count25 * 25 + (negcount25 * -25)) + (count26 * 26 + (negcount26 * -26)) + (count27 * 27 + (negcount27 * -27)) + (count28 * 28 + (negcount28 * -28)) + (count29 * 29 + (negcount29 * -29)) + (count30 * 30 + (negcount30 * -30)) + (count31 * 31 + (negcount31 * -31)) + (count32 * 32 + (negcount32 * -32)) + (count33 * 33 + (negcount33 * -33)) + (count34 * 34 + (negcount34 * -34)) + (count35 * 35 + (negcount35 * -35)) + (count36 * 36 + (negcount36 * -36)) + (count37 * 37 + (negcount37 * -37)) + (count38 * 38 + (negcount38 * -38)) + (count39 * 39 + (negcount39 * -39)) + (count40 * 40 + (negcount40 * -40)) + (count41 * 41 + (negcount41 * -41)) + (count42 * 42 + (negcount42 * -42)) + (count43 * 43 + (negcount43 * -43)) + (count44 * 44 + (negcount44 * -44)) + (count45 * 45 + (negcount45 * -45)) + (count46 * 46 + (negcount46 * -46)) + (count47 * 47 + (negcount47 * -47)) + (count48 * 48 + (negcount48 * -48)) + (count49 * 49 + (negcount49 * -49)) + (count50 * 50 + (negcount50 * -50)) + (count51 * 51 + (negcount51 * -51)) + (count52 * 52 + (negcount52 * -52)) + (count53 * 53 + (negcount53 * -53)) + (count54 * 54 + (negcount54 * -54)) + (count55 * 55 + (negcount55 * -55)) + (count56 * 56 + (negcount56 * -56)) + (count57 * 57 + (negcount57 * -57)) + (count58 * 58 + (negcount58 * -58)) + (count59 * 59 + (negcount59 * -59)) + (count60 * 60 + (negcount60 * -60)) + (count61 * 61 + (negcount61 * -61)) + (count62 * 62 + (negcount62 * -62)) + (count63 * 63 + (negcount63 * -63)) + (count64 * 64 + (negcount64 * -64)) + (count65 * 65 + (negcount65 * -65)) + (count66 * 66 + (negcount66 * -66)) + (count67 * 67 + (negcount67 * -67)) + (count68 * 68 + (negcount68 * -68)) + (count69 * 69 + (negcount69 * -69)) + (count70 * 70 + (negcount70 * -70)) + (count71 * 71 + (negcount71 * -71)) + (count72 * 72 + (negcount72 * -72)) + (count73 * 73 + (negcount73 * -73)) + (count74 * 74 + (negcount74 * -74)) + (count75 * 75 + (negcount75 * -75)) + (count76 * 76 + (negcount76 * -76)) + (count77 * 77 + (negcount77 * -77)) + (count78 * 78 + (negcount78 * -78)) + (count79 * 79 + (negcount79 * -79)) + (count80 * 80 + (negcount80 * -80)) + (count81 * 81 + (negcount81 * -81)) + (count82 * 82 + (negcount82 * -82)) + (count83 * 83 + (negcount83 * -83)) + (count84 * 84 + (negcount84 * -84)) + (count85 * 85 + (negcount85 * -85)) + (count86 * 86 + (negcount86 * -86)) + (count87 * 87 + (negcount87 * -87)) + (count88 * 88 + (negcount88 * -88)) + (count89 * 89 + (negcount89 * -89)) + (count90 * 90 + (negcount90 * -90)) + (count91 * 91 + (negcount91 * -91)) + (count92 * 92 + (negcount92 * -92)) + (count93 * 93 + (negcount93 * -93)) + (count94 * 94 + (negcount94 * -94)) + (count95 * 95 + (negcount95 * -95)) + (count96 * 96 + (negcount96 * -96)) + (count97 * 97 + (negcount97 * -97)) + (count98 * 98 + (negcount98 * -98)) + (count99 * 99 + (negcount99 * -99)) + (count100 * 100 + (negcount100 * -100)) == 75 )



x=s.check()
if(x == z3.sat):
	m = s.model()
	print m
else:
	print unsat

