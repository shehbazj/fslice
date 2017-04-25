from z3 import *

x, y, z = Reals('x y z')
s = Solver()
s.add(x > 1, y > 1, x + y > 3, z - x < 10)
print s.check()

m = s.model()
print "x = %s" % m[x]

print "traversing model..."
for d in m.decls():
    print "%s = %s" % (d.name(), m[d])



x = Real('x')
y = Real('y')
s = Solver()
s.add(x > 1, y > 1, Or(x + y > 3, x - y < 2))
print "asserted constraints..."
for c in s.assertions():
    print c

print s.check()
print "statistics for the last check method..."
print s.statistics()
# Traversing statistics
for k, v in s.statistics():
    print "%s : %s" % (k, v)
