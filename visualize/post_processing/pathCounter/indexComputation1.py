from z3 import *

def IntArr(prefix, sz, N):
  """Create a vector with N Bit-Vectors of size sz"""
  return [ BitVec('%s__%s' % (prefix, i), sz) for i in range(N) ]

def CharArr(prefix, sz, N):
  """Create a vector with N Bit-Vectors of size sz"""
  return [ BitVec('%s__%s' % (prefix, i), sz) for i in range(N) ]

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
  	return [ BitVec('%s__%s' % (var, i), 32) for i in range(size) ]

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
#!/usr/bin/python
#solve():PATH CONTEXT main-entry:main-if.else:main-if.then5:main-if.end:main-if.end8
t1=ConstIntArr('t1', 5)
t2=Int('t2')
t7=t1
t9=Int('t9')
#t9=t2
s.add(t9 == t2)
t3 = Int('t3')
t5 = Int('t5')
t18 = 0
t3 = t18
t4 = []
t1 = t4
t4 = t7
t2 = t5
t5 = t9
t11 = t9
t12 = t9
t13 = t7
if(s.check() == z3.sat):
    m=s.model()
    print m
    id1=m[t9]
t14 = t7[ id1.as_long() ]
t15 = t14
t19 = 4
s.add(( t14 ==  t19) == False )
t20 = t9
t30 = 1
t21 = Int('t21')
s.add(t21 == t9 + t30)
#t21 = t9 +  t30
t9 = t21
t23 = t21
t24 = t21
t25 = t7
if(s.check() == z3.sat):
    m = s.model()
    print m
    id2=m[t21]
t26 = t7[ id2.as_long() ]
t27 = t26
s.add( t26 ==  t19 )
t31 = t21
t32 = t21
t33 = t7
if(s.check() == z3.sat):
    m = s.model()
    print m
    id3 = m[t21]
t34 = t7[ id3.as_long() ]
t37 = 5
t34 = t37
x=s.check()
if(str(x) == "sat"):
        m=s.model()
	print s.model()
        print "sat"
else:
	print str(x)
        print "unsat"
# 1) identify indexes - t9, t21
# 2) declare them as symbolic integer values
# 3) add assertions wherever they have been assigned certain values
# 4) before index access, do index check, solve and return valid value
#   assign concrete index to access the array
# extend the array on demand
#
#t9=m[t2]
#print t9
#if t9 is None:
#    t9 = 0
#t14 = t7[ 0 ]
#t15 = t14
#s.add(( t14 ==  t19) == False )
#print s.check()
