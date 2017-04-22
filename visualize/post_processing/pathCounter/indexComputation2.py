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
#solve():PATH CONTEXT main-entry:main-if.else:main-if.then7:main-if.end:main-if.end12
l1=10
t1=ConstIntArr('t1', l1)
t2=Int('t2')
t8=t1
#t10=t2
t10=Int('t10')
s.add(t10 == t2)
t3 = Int('t3')
t5 = Int('t5')
t6 = Int('t6')
t19 = 0
t3 = t19
t4 = []
t1 = t4
t4 = t8
t2 = t5
t5 = t10
t12 = t10
t13 = t10
t14 = t8
#t15 = t8[ t10 ]
t15 = Int('t10Obj')
s.add(t10 < l1)
t16 = t15
t20 = 4
s.add(( t15 ==  t20) == False )
t21 = t10
t37 = 1
#t22 = t10 +  t37
t22 = Int('t22')
s.add(t22 == t10 + t37)
t10 = t22
t24 = t22
t25 = t22
t26 = t8
#t27 = t8[ t22 ]
s.add(t22 < l1)
t27 = Int('t22Obj')
t28 = t27
s.add(t6 == t27)
t30 = t27
t31 = t27
t32 = t8
#t33 = t8[ t27 ]
t33 = Int('t27Obj')
s.add(t27 < l1)
t34 = t33
t38 = 9
t33 ==  t38
t39 = t22
t40 = t22
# symbols t2, t8, t10, t5, t6, t4, t12, t13, t14, t15, t16, t21, t22, t24, t25, t27, t28, t30, t31, t32, t34, t39, t40, t41, t42, t43, t44, t45, t46, t47
t41 = t8
#t42 = t8[ t22 ]
t42 = Int('t22Obj')
t43 = t42
t44 = t27
t45 = t27
t46 = t8
#t47 = t8[ t27 ]
t47 = Int('t27Obj')
s.add(t47 == t42)
x=s.check()
if(str(x) == "sat"):
	print s.model()
else:
	print str(x)
# scan all indexes, make them symbolic int
# for all values at symbolic indexes marked above, mark the objects at those indexes symbolic.
# for all equalities, if LHS is symbolic, add s.solve(lhs == value)
# solve(). you will get index values, object values. using these, create minimal concrete array!!!!!
