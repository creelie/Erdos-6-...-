#!/usr/bin/env python3
"""Enumeration of m-level designs on u lines whose levels are pairwise disjoint perfect
matchings: for each choice of matchings the linear system is solved (null space) and the
program reports whether some solution has pairwise distinct slopes.

Usage: python3 matching_designs.py U M      e.g. 8 4 (none exist), 8 3, 6 3
"""
import itertools, numpy as np, sys, time
from scipy.linalg import null_space
def perfect_matchings(vs):
    if not vs: yield []; return
    a=vs[0]
    for b in vs[1:]:
        rest=[v for v in vs if v not in (a,b)]
        for m in perfect_matchings(rest): yield [(a,b)]+m
u=int(sys.argv[1]); m=int(sys.argv[2])
PM=[tuple(M) for M in perfect_matchings(list(range(u)))]
M0=PM[0]
def disjoint(A,B): return not (set(A)&set(B))
t=time.time(); found=0; best=None
def rec(chosen):
    global found,best
    if len(chosen)==m:
      for perm in itertools.permutations(range(1,m)):
        order=[chosen[0]]+[chosen[k] for k in perm]
        rows=[]
        for a,M in enumerate(order):
            for (i,j) in M:
                r=np.zeros(2*u); r[i]+=1; r[j]-=1; r[u+i]+=a; r[u+j]-=a; rows.append(r)
        A=np.array(rows); ns=null_space(A)
        if ns.shape[1]<2: continue
        D=ns[u:,:]
        if all(np.linalg.norm(D[i]-D[j])>1e-9 for i in range(u) for j in range(i+1,u)):
            found+=1
            if best is None or ns.shape[1]>best[0]: best=(ns.shape[1],order)
      return
    start=PM.index(chosen[-1])+1 if len(chosen)>1 else 1
    for k in range(start,len(PM)):
        M=PM[k]
        if all(disjoint(M,C) for C in chosen): rec(chosen+[M])
rec([M0])
print("u=%d m=%d designs with distinct slopes: %d, best nullspace dim %s, time %.0fs"%(u,m,found,best[0] if best else None,time.time()-t))
if best: print(best[1])
