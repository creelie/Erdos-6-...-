#!/usr/bin/env python3
"""Given slopes, SAT search for intercepts in [0, S] forming an m-level design (used to find
eight-line grid designs, the pattern of two translated prime quadruplets).

Usage: python3 intercept_search.py M S
"""
import sys, itertools
from pysat.solvers import Cadical153
def find_sig(d,m,S):
    u=len(d); cnt=[0]
    def new():
        cnt[0]+=1; return cnt[0]
    x={(i,s):new() for i in range(u) for s in range(S+1)}
    lo=min(0,min(a*di for a in range(m) for di in d)); hi=S+max(a*di for a in range(m) for di in d)
    vals=range(lo,hi+1)
    v={(i,a,val):new() for i in range(u) for a in range(m) for val in vals}
    sol=Cadical153()
    for i in range(u):
        sol.add_clause([x[(i,s)] for s in range(S+1)])
        for s1 in range(S+1):
            for s2 in range(s1+1,S+1): sol.add_clause([-x[(i,s1)],-x[(i,s2)]])
        for a in range(m):
            for val in vals:
                s=val-a*d[i]
                if 0<=s<=S:
                    sol.add_clause([-v[(i,a,val)],x[(i,s)]]); sol.add_clause([v[(i,a,val)],-x[(i,s)]])
                else: sol.add_clause([-v[(i,a,val)]])
    for i in range(u):
        for a in range(m):
            for val in vals:
                sol.add_clause([-v[(i,a,val)]]+[v[(j,a,val)] for j in range(u) if j!=i])
    if not sol.solve(): return None
    M=set(t for t in sol.get_model() if t>0)
    return [s for i in range(u) for s in range(S+1) if x[(i,s)] in M]
if __name__=="__main__":
    m=int(sys.argv[1]); S=int(sys.argv[2])
    found=0
    for delta,dp,a,b in itertools.product(range(1,9),range(1,9),range(0,12),range(0,12)):
        d=[a,a+delta,a-dp,a-dp+delta,b,b+delta,b-dp,b-dp+delta]
        if len(set(d))<8: continue
        r=find_sig(d,m,S)
        if r: print("design m=%d: d=%s sigma=%s"%(m,d,r),flush=True); found+=1
        if found>=3: break
    print("found",found)
