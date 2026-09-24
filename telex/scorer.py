import sys
import math
from random import randint

if (sys.version_info > (3, 0)):
    from functools import singledispatch
else:
    from singledispatch import singledispatch

from telex.stl import *
import operator as op

@singledispatch
def qualitativescore(stl, x, t):
    raise NotImplementedError("No qualitativescore for {} of class {}".format(stl, stl.__class__))

@qualitativescore.register(Globally)
def _(stl, x, t):
    (left, right) = stl.interval
    left = float(left) 
    right = float(right)  
    if left>right:
        raise ValueError("Interval [{},{}] empty for {}".format(left, right, stl))
    (maxtime, rangetime) = gettime(x, t+left, t+right)
    return all(qualitativescore(stl.subformula, x, t1) for t1 in rangetime)


@qualitativescore.register(Future)
def _(stl, x, t):
    (left, right) = stl.interval
    left = float(left) 
    right = float(right) 
    if left>right:
        raise ValueError("Interval [{},{}] empty for {}".format(left, right, stl))    
    (maxtime, rangetime) = gettime(x, t+left, t+right)
    return any(qualitativescore(stl.subformula, x, t1) for t1 in rangetime)


@qualitativescore.register(Until)
def _(stl, x, t):
    (left, right) = stl.interval
    left = float(left) 
    right = float(right) 
    if left>right:
        raise ValueError("Interval [{},{}] empty for {}".format(left, right, stl))    
    (_, rangetime) = gettime(x, t+left, t+right)
    return (qualitativescore(stl.right, x, t) or any(  (qualitativescore(stl.right, x, t1) or  all (qualitativescore(stl.left, x, t2) for t2 in filter(lambda v: (v>= t) & (v<= t1) , rangetime) ) ) for t1 in rangetime) )



@qualitativescore.register(Or)
def _(stl, x, t):
    return qualitativescore(stl.left, x, t) or qualitativescore(stl.right, x, t) 

@qualitativescore.register(And)
def _(stl, x, t):
    return qualitativescore(stl.left, x, t) and qualitativescore(stl.right, x, t) 

@qualitativescore.register(Implies)
def _(stl, x, t):
    return (not  qualitativescore(stl.left, x, t) ) or qualitativescore(stl.right, x, t)

@qualitativescore.register(Not)
def _(stl, x, t):
    return not qualitativescore(stl.subformula, x, t)

optable = { "<" : op.lt, ">" : op.gt, "<=" : op.le, ">=" : op.ge, "==": op.eq, "+" : op.add, "-" : op.sub, "*" : op.mul, "/" : op.truediv }
 
@qualitativescore.register(Constraint)
def _(stl, x, t):
    return optable[stl.relop](getval(stl.term, x, t), getval(stl.bound, x, t))

@qualitativescore.register(Atom)
def _(stl, x, t):
    return x[stl.name][t]


@singledispatch

def getval(term, x, t):
    raise NotImplementedError("No getval for {} of class {}".format(term, term.__class__))


@getval.register(Expr)
def _(term, x, t):
    return optable[term.arithop](getval(term.left, x, t), getval(term.right, x, t))

@getval.register(Var)
def _(term, x, t):
    return x[term.name].iloc[t]

@getval.register(Constant)
def _(term, x, t):
    return term 
    
@getval.register(Param)
def _(term, x, t):
    raise NotImplementedError("No getval for parameter {}".format(term))



@singledispatch
def quantitativescore(stl, x, t):
    raise NotImplementedError("No quantitativescore for {} of class {}".format(stl, stl.__class__))

@quantitativescore.register(Globally)
def _(stl, x, t):
    (left, right) = stl.interval
    (_, rangetime) = gettime(x, t+left, t+right)
    return  min([quantitativescore(stl.subformula, x, t1) for t1 in rangetime], default=1)

@quantitativescore.register(Future)
def _(stl, x, t):
    (left, right) = stl.interval
    (_, rangetime) = gettime(x, t+left, t+right)
    return max([quantitativescore(stl.subformula, x, t1) for t1 in rangetime], default=-1)

@quantitativescore.register(Until)
def _(stl, x, t):
    (left, right) = stl.interval
    left = float(left) 
    right = float(right) 
    if left>right:
        print(left, right, "until q score")
        raise ValueError("Interval [{},{}] empty for {}".format(left, right, stl))    
    (maxtime, rangetime) = gettime(x, t+left, t+right)
    #rangetime = filter(lambda v: (v<= right) & (v >= left), ts)
    #for t1 in rangetime:
    #    print(" t1 ", t1, quantitativescore(stl.right,x,t1))
    #    for t2 in filter(lambda v: (v>= t) & (v<= t+t1) , rangetime):
    #        print("   t2  ", t2, stl.left, quantitativescore(stl.left, x, t2) )
    #    print(filter(lambda v: (v>= t) & (v<= t1) , rangetime) )
    #    print(min (qualitativescore(stl.left, x, t2) for t2 in filter(lambda v: (v>= t) & (v< t1) , rangetime) ) )
    return max(quantitativescore(stl.right, x, t), 
               max( min (quantitativescore(stl.right, x, t1), 
                    min (quantitativescore(stl.left, x, t2) for t2 in filter(lambda v: (v>= t) & (v<= t1) , rangetime) ) ) for t1 in rangetime
                )
            )



@quantitativescore.register(Or)
def _(stl, x, t):
    return max(quantitativescore(stl.left, x, t), quantitativescore(stl.right, x, t))

@quantitativescore.register(And)
def _(stl, x, t):
    return min(quantitativescore(stl.left, x, t), quantitativescore(stl.right, x, t))

@quantitativescore.register(Implies)
def _(stl, x, t):
    return max( (-1*  quantitativescore(stl.left, x, t) ), quantitativescore(stl.right, x, t) )

@quantitativescore.register(Not)
def _(stl, x, t):
    return -1 * quantitativescore(stl.subformula, x, t)

#optable = { "<" : op.lt, ">" : op.gt, "<=" : op.le, ">=" : op.ge, "==": op.eq, "+" : op.add, "-" : op.sub, "*" : op.mul, "/" : op.truediv }

robusttable = { "<" : lambda x,y: y-x, "<=" : lambda x,y: y-x, ">" : lambda x,y: x-y , ">=": lambda x,y: x-y, "==" : lambda x,y: -abs(x-y) }

@quantitativescore.register(Constraint)
def _(stl, x, t):
    #print(stl,  robusttable[stl.relop](getval(stl.term, x, t), getval(stl.bound, x, t)) )
    return robusttable[stl.relop](getval(stl.term, x, t), getval(stl.bound, x, t))

@quantitativescore.register(Atom)
def _(stl, x, t):
    if x[stl.name][t]:
        return 1
    else:
        return 0





@singledispatch
def smartscore(stl, x, t):
    raise NotImplementedError("No smartscore for {} of class {}".format(stl, stl.__class__))

@smartscore.register(Globally)
def _(stl, x, t):
    (left, right) = stl.interval
    if left>right:
        raise ValueError("Interval [{},{}] empty for {}".format(left, right, stl))    
    intervalwidth = right - left + 1
    (maxtime, rangetime) = gettime(x, t+left, t+right)
    #rangetime =  x[(x['time'] <= right) & (x['time'] >= left)]["time"]
    return  2/(1 + math.exp(-0.01 * intervalwidth) ) * min(smartscore(stl.subformula, x, t1) for t1 in rangetime)

@smartscore.register(Future)
def _(stl, x, t):
    (left, right) = stl.interval
    if left>right:
        raise ValueError("Interval [{},{}] empty for {}".format(left, right, stl))    
    intervalwidth = right - left + 1
    (maxtime, rangetime) = gettime(x, t+left, t+right)
    return  2/(1 + math.exp(0.01 * intervalwidth) ) * max(smartscore(stl.subformula, x, t1) for t1 in rangetime)

@smartscore.register(Until)
def _(stl, x, t):
    (left, right) = stl.interval
    # left = float(left) 
    # right = float(right) 
    if left>right:
        raise ValueError("Interval [{},{}] empty for {}".format(left, right, stl))    
    intervalwidth = right - left + 1
    (maxtime, rangetime) = gettime(x, t+left, t+right)
    #rangetime = filter(lambda v: (v<= right) & (v >= left), ts)
    #rangetime = filter(lambda v: (v<= right) & (v >= left), ts)
    #for t1 in rangetime:
    #    print(" t1 ", t1, quantitativescore(stl.right,x,t1))
    #    for t2 in filter(lambda v: (v>= t) & (v<= t+t1) , rangetime):
    #        print("   t2  ", t2, stl.left, quantitativescore(stl.left, x, t2) )
    #    print(filter(lambda v: (v>= t) & (v<= t1) , rangetime) )
    #    print(min (qualitativescore(stl.left, x, t2) for t2 in filter(lambda v: (v>= t) & (v< t1) , rangetime) ) )
    return 2/(1 + math.exp(-0.01 * intervalwidth) ) * max(quantitativescore(stl.right, x, t), max( min (quantitativescore(stl.right, x, t1), min (quantitativescore(stl.left, x, t2) for t2 in filter(lambda v: (v>= t) & (v<= t1) , rangetime) ) ) for t1 in rangetime) )






@smartscore.register(Or)
def _(stl, x, t):
    return max(smartscore(stl.left, x, t), smartscore(stl.right, x, t))

@smartscore.register(And)
def _(stl, x, t):
    return min(smartscore(stl.left, x, t), smartscore(stl.right, x, t))

@smartscore.register(Implies)
def _(stl, x, t):
    return max( (-1*  smartscore(stl.left, x, t) ), smartscore(stl.right, x, t) )

@smartscore.register(Not)
def _(stl, x, t):
    return -1 * smartscore(stl.subformula, x, t)

robusttable = { "<" : lambda x,y: y-x, "<=" : lambda x,y: y-x, ">" : lambda x,y: x-y , ">=": lambda x,y: x-y, "==" : lambda x,y: -abs(x-y) }

@smartscore.register(Constraint)
def _(stl, x, t):
    alpha = 50 # scales the width and x-value of the peak
    beta = 4 # scales the height of the peak
    rawscore = (robusttable[stl.relop](getval(stl.term, x, t), getval(stl.bound, x, t)))
    return 1/(alpha*rawscore + math.exp(-beta*alpha*rawscore)) - math.exp(-alpha*rawscore) 

@smartscore.register(Atom)
def _(stl, x, t):
    if x[stl.name][t]:
        return 1
    else:
        return 0


def gettime(x, left, right):
    # ts = sorted(x['time'].keys())
    maxtime = x['time'].iloc[-1]#max(x['time'])#ts[-1]
    rangetime =  x.index[(x['time']<= right) & (x['time']>=left)]
    
    # rangetime = x['time'].between(left, right).index
    # rangetime = list(filter(lambda v: (v<= right) & (v >= left), ts))
    return maxtime, rangetime