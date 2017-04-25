from z3 import *

# Wrapper for allowing Z3 ASTs to be stored into Python Hashtables. 
class AstRefKey:
    def __init__(self, n):
        self.n = n
    def __hash__(self):
        return self.n.hash()
    def __eq__(self, other):
        return self.n.eq(other.n)
    def __repr__(self):
        return str(self.n)

def askey(n):
    assert isinstance(n, AstRef)
    return AstRefKey(n)

def get_vars(f):
    r = set()
    def collect(f):
      if is_const(f): 
          if f.decl().kind() == Z3_OP_UNINTERPRETED and not askey(f) in r:
              r.add(askey(f))
      else:
          for c in f.children():
              collect(c)
    collect(f)
    return r

if __name__ == "__main__":
    """Main Function"""

    x,y = Ints('x y')
    a,b = Bools('a b')
    s = Solver()
    s.add(x == y, a == b, x != a, y != b)
    ret = set()
    for item in s.assertions():
        ret  = set(list(ret) + list(get_vars(item)))
    for k in ret:
        print k, type(k)
#    s.add(Implies(And(x + y == 0, x*2 == 10),Or(a, Implies(a, b == False))))
#    print s.check()
#    print s.model()
#    ret = get_vars(s.assertions())
#    
