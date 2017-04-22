from z3 import *

def IntArr(prefix, sz, N):
  """Create a vector with N Bit-Vectors of size sz"""
  return [ BitVec('%s__%s' % (prefix, i), sz) for i in range(N) ]

#def CharArr(prefix, sz, N):
#  """Create a vector with N Bit-Vectors of size sz"""
#  return [ BitVec('%s__%s' % (prefix, i), sz) for i in range(N) ]
#
#def extendList(var, num, prefix):
#    listSize = len(var)
#    if num - listSize > 0:
#        incrementSize = num-listSize
#        for val in range(incrementSize):
#            var.append( BitVec('%s__%s' % (prefix, listSize + val), 32))
#
#def BitVectorToInt(var):
#    if type(var) is int:    # if already int dont do anything
#        return
#    elif is_bv(var) and var.size() == 32: # if bitvector is int of size
#        # 32, then return Integer equavalent
#        ctx = var.ctx
#        return ArithRef(Z3_mk_bv2int(ctx.ref(), var.as_ast(), 0), ctx)
#    else:       # if bitvector is that of char, return as is
#            # since all character operations happen on bitvector
#        return var

s = Solver()
#t1=IntArr('t1',32,1)
#incrementSize=Int('I')
#t1.resize(incrementSize)

#set_param('smt.bv.enable_int2bv',True)

t1 = Int('t1')

s.add(t1 == 2)
x=s.check()
y=s.model()
print y
