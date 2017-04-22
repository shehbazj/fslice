from z3 import *

def str2array(a):
    """
    Convert a string into a list of Z3 bit-vector values of size 8
    """
    return [ BitVecVal(int(a[x].encode('hex'), 16), 8) for x in range(len(a)) ]

a = str2array("\xff\x33\x01\x88\x02\x11\x03\x55")
# 'a' is a list of Z3 bitvector constants.
print "a:", a
print "a type " , type(a)
## The elements of 'a' may look like Python integers but they are Z3 expressions.
## We can use the method sexpr() to get these values in SMT 2.0 syntax.
#print [ a_i.sexpr() for a_i in a ]
#
## b is a Z3 symbolic variable.
#b = BitVec('b', 8)
#
## We compute a list 'c' of Z3 expressions from 'a' and 'b'.
## We use Python list comprehensions but we can also use a for-loop.
#c = [ a_i ^ b for a_i in a ] 
#
#print "c:", c
#
#second = '\x23\x23'
## We convert 'second' in a Z3 bit-vector value of size 16
#second = BitVecVal(int(second.encode('hex'), 16), 16)
#print "second:", second
#
## The Z3 operation Concat concatenates two or more bit-vector expressions.
#d = []
#x = 0
#while x < len(c):
#    # c[x] is a Bit-vector of size 8, second is a Bit-vector of size 16.
#    # In Z3, we have to do the "casting" ourselves.
#    # We use ZeroExt(8, c[x]) to convert c[x] into a Bit-vector of size 16,
#    # by adding 0-bits.
#    d.append(ZeroExt(8, c[x]) ^ second)
#    x += 2
#print "d:", d
#
#goal = str2array('\xbd\x23\x43\x23\x40\x23\x41\x23')
#print "goal:", goal
## Note that, len(goal) == 2*len(d)
## We can use Concat to concatenate adjacent elements.
#
## We want each element of d[i] == Concat(goal[2*i], goal[2*i+1])
## We can use Z3 to find the 'b' that will satisfy these constraints
#
#s = Solver()
## 's' is a Z3 solver object
#i = 0
#while i < len(d):
#    s.add(d[i] == Concat(goal[2*i+1], goal[2*i]))
#    i += 1
#print s
## Now, 's' contains a set of equational constraints.
#print s.check()
#print s.model()
