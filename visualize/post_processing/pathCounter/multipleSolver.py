from z3 import *
from get_vars import *

def get(s,varStr):
    ret = set()
    for items in s.assertions():
        ret = set(list(get_vars(items)) + list(ret))
    for k in ret:
        if str(k.n) == varStr:
            print "found k", k
            return k
#    m = s.model()
#    for c in m.decls():
#        if(c.name() == varStr):
#            print "returning ", c.name(), " = ", m[c]
#            return c


if __name__ == "__main__":
    """ Main Start """
    print "main"
    s = Solver()
    x = Int('x')
    y = Int('y')
    z = Int('z')
    s.add(x == 10)
    s.add(x > y)
    print "check x = 10, and x > y",s.check()
    print "MODEL"
    print s.model()
    s.add(y < z)
    print "y < z added ",s.check()
    print "MODEL"
    print s.model()
    p = get(s,'x')
    q = get(s,'y')
    print "SOLVER CONSTRAINTS_BEFORE"
    for c in s.assertions():
        print c
    s.add(q != 0)
    s1.add(q == y)
    print "SOLVER CONSTRAINTS_AFTER"
    for c in s1.assertions():
        print c
    print s1.check()
    
print s1.model()
