from z3 import *

x = Int('x')
y = Int('y')
#y = x + 1
s = Solver()
s.add(x == 10)
s.add(y == x + 1)
s.check()
m = s.model()
f = s.assertions()
for i in range(len(f)):
    print f[i]
for i in range(len(m)):
    print m[i]
print "x = ",m[x]
print "y = ",m[y]
