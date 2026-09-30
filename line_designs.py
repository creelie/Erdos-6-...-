#!/usr/bin/env python3
"""SAT search for m-level designs on u lines with integer intercepts in [0, S] and slopes in
[0, D]: for every line and every level a < m some other line passes through the same point.
Used to find the seven-prime pattern of two levels.

Usage: python3 line_designs.py U M S D
"""
import sys, itertools
from pysat.solvers import Cadical153
def find_design(u,m,S,D):
    cnt=[0]
    def new():
        cnt[0]+=1; return cnt[0]
    x={(i,s):new() for i in range(u) for s in range(S+1)}
    y={(i,d):new() for i in range(u) for d in range(D+1)}
    w={(i,s,d):new() for i in range(u) for s in range(S+1) for d in range(D+1)}
    V=S+(m-1)*D
    v={(i,a,val):new() for i in range(u) for a in range(m) for val in range(V+1)}
    sol=Cadical153()
    for i in range(u):
        sol.add_clause([x[(i,s)] for s in range(S+1)])
        for s1 in range(S+1):
            for s2 in range(s1+1,S+1): sol.add_clause([-x[(i,s1)],-x[(i,s2)]])
        sol.add_clause([y[(i,d)] for d in range(D+1)])
        for d1 in range(D+1):
            for d2 in range(d1+1,D+1): sol.add_clause([-y[(i,d1)],-y[(i,d2)]])
        for s in range(S+1):
            for d in range(D+1):
                sol.add_clause([-w[(i,s,d)],x[(i,s)]]); sol.add_clause([-w[(i,s,d)],y[(i,d)]]); sol.add_clause([w[(i,s,d)],-x[(i,s)],-y[(i,d)]])
        for a in range(m):
            for val in range(V+1):
                terms=[w[(i,s,d)] for s in range(S+1) for d in range(D+1) if s+a*d==val]
                # v <-> OR terms
                sol.add_clause([-v[(i,a,val)]]+terms)
                for t in terms: sol.add_clause([v[(i,a,val)],-t])
    # distinct slopes
    for i in range(u):
        for j in range(i+1,u):
            for d in range(D+1): sol.add_clause([-y[(i,d)],-y[(j,d)]])
    # symmetry: slopes increasing
    # coverage: each (i,a,val) true -> some other j has same val at a
    for i in range(u):
        for a in range(m):
            for val in range(V+1):
                sol.add_clause([-v[(i,a,val)]]+[v[(j,a,val)] for j in range(u) if j!=i])
    if not sol.solve(): return None
    M=set(t for t in sol.get_model() if t>0)
    sig=[s for i in range(u) for s in range(S+1) if x[(i,s)] in M]
    dd=[d for i in range(u) for d in range(D+1) if y[(i,d)] in M]
    return sig,dd
if __name__=="__main__":
    u,m,S,D=map(int,sys.argv[1:5])
    r=find_design(u,m,S,D); print(u,m,S,D,r)
