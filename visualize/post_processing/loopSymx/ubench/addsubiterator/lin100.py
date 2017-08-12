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
counter21=Int('counter21')
s.add(counter21==If(s20 == 50,counter20 + 21, counter20 - 21))
s21=Int('s21')
counter22=Int('counter22')
s.add(counter22==If(s21 == 50,counter21 + 22, counter21 - 22))
s22=Int('s22')
counter23=Int('counter23')
s.add(counter23==If(s22 == 50,counter22 + 23, counter22 - 23))
s23=Int('s23')
counter24=Int('counter24')
s.add(counter24==If(s23 == 50,counter23 + 24, counter23 - 24))
s24=Int('s24')
counter25=Int('counter25')
s.add(counter25==If(s24 == 50,counter24 + 25, counter24 - 25))
s25=Int('s25')
counter26=Int('counter26')
s.add(counter26==If(s25 == 50,counter25 + 26, counter25 - 26))
s26=Int('s26')
counter27=Int('counter27')
s.add(counter27==If(s26 == 50,counter26 + 27, counter26 - 27))
s27=Int('s27')
counter28=Int('counter28')
s.add(counter28==If(s27 == 50,counter27 + 28, counter27 - 28))
s28=Int('s28')
counter29=Int('counter29')
s.add(counter29==If(s28 == 50,counter28 + 29, counter28 - 29))
s29=Int('s29')
counter30=Int('counter30')
s.add(counter30==If(s29 == 50,counter29 + 30, counter29 - 30))
s30=Int('s30')
counter31=Int('counter31')
s.add(counter31==If(s30 == 50,counter30 + 31, counter30 - 31))
s31=Int('s31')
counter32=Int('counter32')
s.add(counter32==If(s31 == 50,counter31 + 32, counter31 - 32))
s32=Int('s32')
counter33=Int('counter33')
s.add(counter33==If(s32 == 50,counter32 + 33, counter32 - 33))
s33=Int('s33')
counter34=Int('counter34')
s.add(counter34==If(s33 == 50,counter33 + 34, counter33 - 34))
s34=Int('s34')
counter35=Int('counter35')
s.add(counter35==If(s34 == 50,counter34 + 35, counter34 - 35))
s35=Int('s35')
counter36=Int('counter36')
s.add(counter36==If(s35 == 50,counter35 + 36, counter35 - 36))
s36=Int('s36')
counter37=Int('counter37')
s.add(counter37==If(s36 == 50,counter36 + 37, counter36 - 37))
s37=Int('s37')
counter38=Int('counter38')
s.add(counter38==If(s37 == 50,counter37 + 38, counter37 - 38))
s38=Int('s38')
counter39=Int('counter39')
s.add(counter39==If(s38 == 50,counter38 + 39, counter38 - 39))
s39=Int('s39')
counter40=Int('counter40')
s.add(counter40==If(s39 == 50,counter39 + 40, counter39 - 40))
s40=Int('s40')
counter41=Int('counter41')
s.add(counter41==If(s40 == 50,counter40 + 41, counter40 - 41))
s41=Int('s41')
counter42=Int('counter42')
s.add(counter42==If(s41 == 50,counter41 + 42, counter41 - 42))
s42=Int('s42')
counter43=Int('counter43')
s.add(counter43==If(s42 == 50,counter42 + 43, counter42 - 43))
s43=Int('s43')
counter44=Int('counter44')
s.add(counter44==If(s43 == 50,counter43 + 44, counter43 - 44))
s44=Int('s44')
counter45=Int('counter45')
s.add(counter45==If(s44 == 50,counter44 + 45, counter44 - 45))
s45=Int('s45')
counter46=Int('counter46')
s.add(counter46==If(s45 == 50,counter45 + 46, counter45 - 46))
s46=Int('s46')
counter47=Int('counter47')
s.add(counter47==If(s46 == 50,counter46 + 47, counter46 - 47))
s47=Int('s47')
counter48=Int('counter48')
s.add(counter48==If(s47 == 50,counter47 + 48, counter47 - 48))
s48=Int('s48')
counter49=Int('counter49')
s.add(counter49==If(s48 == 50,counter48 + 49, counter48 - 49))
s49=Int('s49')
counter50=Int('counter50')
s.add(counter50==If(s49 == 50,counter49 + 50, counter49 - 50))
s50=Int('s50')
counter51=Int('counter51')
s.add(counter51==If(s50 == 50,counter50 + 51, counter50 - 51))
s51=Int('s51')
counter52=Int('counter52')
s.add(counter52==If(s51 == 50,counter51 + 52, counter51 - 52))
s52=Int('s52')
counter53=Int('counter53')
s.add(counter53==If(s52 == 50,counter52 + 53, counter52 - 53))
s53=Int('s53')
counter54=Int('counter54')
s.add(counter54==If(s53 == 50,counter53 + 54, counter53 - 54))
s54=Int('s54')
counter55=Int('counter55')
s.add(counter55==If(s54 == 50,counter54 + 55, counter54 - 55))
s55=Int('s55')
counter56=Int('counter56')
s.add(counter56==If(s55 == 50,counter55 + 56, counter55 - 56))
s56=Int('s56')
counter57=Int('counter57')
s.add(counter57==If(s56 == 50,counter56 + 57, counter56 - 57))
s57=Int('s57')
counter58=Int('counter58')
s.add(counter58==If(s57 == 50,counter57 + 58, counter57 - 58))
s58=Int('s58')
counter59=Int('counter59')
s.add(counter59==If(s58 == 50,counter58 + 59, counter58 - 59))
s59=Int('s59')
counter60=Int('counter60')
s.add(counter60==If(s59 == 50,counter59 + 60, counter59 - 60))
s60=Int('s60')
counter61=Int('counter61')
s.add(counter61==If(s60 == 50,counter60 + 61, counter60 - 61))
s61=Int('s61')
counter62=Int('counter62')
s.add(counter62==If(s61 == 50,counter61 + 62, counter61 - 62))
s62=Int('s62')
counter63=Int('counter63')
s.add(counter63==If(s62 == 50,counter62 + 63, counter62 - 63))
s63=Int('s63')
counter64=Int('counter64')
s.add(counter64==If(s63 == 50,counter63 + 64, counter63 - 64))
s64=Int('s64')
counter65=Int('counter65')
s.add(counter65==If(s64 == 50,counter64 + 65, counter64 - 65))
s65=Int('s65')
counter66=Int('counter66')
s.add(counter66==If(s65 == 50,counter65 + 66, counter65 - 66))
s66=Int('s66')
counter67=Int('counter67')
s.add(counter67==If(s66 == 50,counter66 + 67, counter66 - 67))
s67=Int('s67')
counter68=Int('counter68')
s.add(counter68==If(s67 == 50,counter67 + 68, counter67 - 68))
s68=Int('s68')
counter69=Int('counter69')
s.add(counter69==If(s68 == 50,counter68 + 69, counter68 - 69))
s69=Int('s69')
counter70=Int('counter70')
s.add(counter70==If(s69 == 50,counter69 + 70, counter69 - 70))
s70=Int('s70')
counter71=Int('counter71')
s.add(counter71==If(s70 == 50,counter70 + 71, counter70 - 71))
s71=Int('s71')
counter72=Int('counter72')
s.add(counter72==If(s71 == 50,counter71 + 72, counter71 - 72))
s72=Int('s72')
counter73=Int('counter73')
s.add(counter73==If(s72 == 50,counter72 + 73, counter72 - 73))
s73=Int('s73')
counter74=Int('counter74')
s.add(counter74==If(s73 == 50,counter73 + 74, counter73 - 74))
s74=Int('s74')
counter75=Int('counter75')
s.add(counter75==If(s74 == 50,counter74 + 75, counter74 - 75))
s75=Int('s75')
counter76=Int('counter76')
s.add(counter76==If(s75 == 50,counter75 + 76, counter75 - 76))
s76=Int('s76')
counter77=Int('counter77')
s.add(counter77==If(s76 == 50,counter76 + 77, counter76 - 77))
s77=Int('s77')
counter78=Int('counter78')
s.add(counter78==If(s77 == 50,counter77 + 78, counter77 - 78))
s78=Int('s78')
counter79=Int('counter79')
s.add(counter79==If(s78 == 50,counter78 + 79, counter78 - 79))
s79=Int('s79')
counter80=Int('counter80')
s.add(counter80==If(s79 == 50,counter79 + 80, counter79 - 80))
s80=Int('s80')
counter81=Int('counter81')
s.add(counter81==If(s80 == 50,counter80 + 81, counter80 - 81))
s81=Int('s81')
counter82=Int('counter82')
s.add(counter82==If(s81 == 50,counter81 + 82, counter81 - 82))
s82=Int('s82')
counter83=Int('counter83')
s.add(counter83==If(s82 == 50,counter82 + 83, counter82 - 83))
s83=Int('s83')
counter84=Int('counter84')
s.add(counter84==If(s83 == 50,counter83 + 84, counter83 - 84))
s84=Int('s84')
counter85=Int('counter85')
s.add(counter85==If(s84 == 50,counter84 + 85, counter84 - 85))
s85=Int('s85')
counter86=Int('counter86')
s.add(counter86==If(s85 == 50,counter85 + 86, counter85 - 86))
s86=Int('s86')
counter87=Int('counter87')
s.add(counter87==If(s86 == 50,counter86 + 87, counter86 - 87))
s87=Int('s87')
counter88=Int('counter88')
s.add(counter88==If(s87 == 50,counter87 + 88, counter87 - 88))
s88=Int('s88')
counter89=Int('counter89')
s.add(counter89==If(s88 == 50,counter88 + 89, counter88 - 89))
s89=Int('s89')
counter90=Int('counter90')
s.add(counter90==If(s89 == 50,counter89 + 90, counter89 - 90))
s90=Int('s90')
counter91=Int('counter91')
s.add(counter91==If(s90 == 50,counter90 + 91, counter90 - 91))
s91=Int('s91')
counter92=Int('counter92')
s.add(counter92==If(s91 == 50,counter91 + 92, counter91 - 92))
s92=Int('s92')
counter93=Int('counter93')
s.add(counter93==If(s92 == 50,counter92 + 93, counter92 - 93))
s93=Int('s93')
counter94=Int('counter94')
s.add(counter94==If(s93 == 50,counter93 + 94, counter93 - 94))
s94=Int('s94')
counter95=Int('counter95')
s.add(counter95==If(s94 == 50,counter94 + 95, counter94 - 95))
s95=Int('s95')
counter96=Int('counter96')
s.add(counter96==If(s95 == 50,counter95 + 96, counter95 - 96))
s96=Int('s96')
counter97=Int('counter97')
s.add(counter97==If(s96 == 50,counter96 + 97, counter96 - 97))
s97=Int('s97')
counter98=Int('counter98')
s.add(counter98==If(s97 == 50,counter97 + 98, counter97 - 98))
s98=Int('s98')
counter99=Int('counter99')
s.add(counter99==If(s98 == 50,counter98 + 99, counter98 - 99))
s99=Int('s99')
counter100=Int('counter100')
s.add(counter100==If(s99 == 50,counter99 + 100, counter99 - 100))
s100=Int('s100')

counter_final=Int('counter_final')
s.add(counter_final == 75)
s.add(counter_final == counter100)
x=s.check()
if(x == z3.sat):
	m = s.model()
	print m
else:
	print unsat
