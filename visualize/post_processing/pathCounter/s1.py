from z3 import *

# Create a Bitvector of size 8
#a = BitVec('a', 8)

# Create a "vector" (list) with 16 Bit-vectors of size 8
#DomVect = [ BitVec('DomVect_%s' % i, 8) for i in range(16) ]
#print DomVect
#print DomVect[15]

def BV2Int(var):
     ctx = var.ctx
     return ArithRef(Z3_mk_bv2int(ctx.ref(), var.as_ast(), 0), ctx)

set_param('smt.bv.enable_int2bv',True)

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

# The function BitVecVector is similar to the functions IntVector and RealVector in Z3Py.

# Create a vector with 32 Bit-vectors of size 8. 
#print BitVecVector("A", 8, 32)

set_param('smt.bv.enable_int2bv',True) 
s = Solver()

#a = [] # alloca single ptr
t1 = IntArr("t1", 32, 1) # mark_var_int_arr
#extendList(a,1, 'a')
a = t1 # store call back to a
one = a # load a
extendList(one, 4, 'a')
arridx = one[3] # getelementptr one [3]
two = arridx # load value

print "two = ", two
s.add(two == 10)

print(s.check())
print(s.model())

##t2 = BitVecVector("t2", 32, 5)
#t2 = [n for n in t1*5]
#print (t2)
#t1.extend(t2)
#print (len(t1))
#num5 = 5
#t1off = BV2Int(t1[5])
