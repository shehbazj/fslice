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

s = Solver()
#!/usr/bin/python
t1=IntArr('t1', 32, 1)
t100=CharArr('t100', 8 , 1)
t101= t100[0]
x = BitVecVal(ord('x'), 8)
s.add(t101 == x)
t2=Int('t2')
t7=t1
t9=t2
t3 = 0
t5 = 0
t23 = 0
t3 = t23
t4 = []  
t1 = t4
t4 = t7
t2 = t5
t5 = t9
t11 = t7
t24 = 10
extendList(t7,11, 't7')
t12 = BV2Int(t7[ 10 ])
t25 = 5
t12 = t25
t14 = t7
extendList(t7,11, 't7')
t15 = BV2Int(t7[ 10 ])
t16 = t15
t17 = t9
t18 = t15 + t9
t19 = t7
t26 = 11
extendList(t7,12, 't7')
t20 = t7[ 11 ]
t20 = t18
x=s.check()
if(str(x) == "sat"):
	print s.model()
else:
	print str(x)
