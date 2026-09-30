#!/usr/bin/env python3
"""Longest P-good interval by SAT over the offsets (CaDiCaL through PySAT).

good_window(P, W) returns offsets s_p (the residue of the left end that makes s_p the position of
the first multiple of p) for which no position in [0, W) is covered by exactly one prime, or None.
One Boolean variable per prime p and residue r mod p, exactly one true per p; for every position
z and prime p the clause "if z is a multiple of p then z is a multiple of some other q".

Usage: python3 sat_interval.py LO HI K   (all K-subsets of primes in [LO, HI), best ratios)
"""
import sys, itertools
from sympy import primerange
from pysat.solvers import Cadical153
def good_window(P, W):
    """SAT: offsets s_p with no point in [0,W) covered exactly once. Returns offsets dict or None."""
    P=list(P); var={}
    n=0
    for p in P:
        for r in range(p):
            n+=1; var[(p,r)]=n
    s=Cadical153()
    for p in P:
        s.add_clause([var[(p,r)] for r in range(p)])
        for r1 in range(p):
            for r2 in range(r1+1,p): s.add_clause([-var[(p,r1)],-var[(p,r2)]])
    for x in range(W):
        for p in P:
            s.add_clause([-var[(p,x%p)]]+[var[(q,x%q)] for q in P if q!=p])
    if not s.solve(): return None
    m=set(v for v in s.get_model() if v>0)
    return {p:r for (p,r),v in var.items() if v in m}
def maxW(P, lo=None):
    W=lo or max(P)
    res=None
    while True:
        r=good_window(P,W+1)
        if r is None: return W,res
        W+=1; res=r
if __name__=="__main__":
    lo,hi,k=int(sys.argv[1]),int(sys.argv[2]),int(sys.argv[3])
    primes=list(primerange(lo,hi)); best=(0,)
    for P in itertools.combinations(primes,k):
        W,res=maxW(P, lo=int(1.5*max(P)))
        ratio=W/max(P)
        if ratio>best[0]: best=(ratio,P,W,res); print("%.3f"%ratio,P,W,res,flush=True)
