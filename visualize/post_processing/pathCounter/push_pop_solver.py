from z3 import *

t1 = 10
t2 = Int('t2')
s = Solver()
s.add(t2 < t1)
if(s.check() == z3.sat):
    print s.model()
    print "value =  ", s.model()[t2]
else:
    print "no model found for 1"
new = s
new.push()
new.add(t2 < 5)
if(new.check() == z3.sat):
    print new.model()
    print "value =  ", new.model()[t2]
else:
    print "no model found for 2"

new.pop()
new2 = s
new2.add(t2 > 5)
if(new2.check() == z3.sat):
    print new2.model()[t2]
    print "value =  ", new2.model()[t2]
else:
    print "no model found for 3"

