#!/usr/bin/env python3
"""All K-subsets of primes in [LO, HI) through sat_interval.good_window, by binary search on W.
Used for the five-prime sweep over [30, 80] and the seven-prime run (logs/sweep_*.log).

Usage: python3 sweep_sat.py LO HI K
"""
import itertools, sys, time
from sympy import primerange
from sat_interval import good_window
def maxW(P,hi_ratio=4):
    lo=max(P); hi=int(hi_ratio*max(P)); best=None
    while lo<hi:
        mid=(lo+hi+1)//2; r=good_window(P,mid)
        if r: lo=mid; best=r
        else: hi=mid-1
    return lo,best
lo,hi,k=int(sys.argv[1]),int(sys.argv[2]),int(sys.argv[3])
primes=list(primerange(lo,hi)); best=(0,); n=0; t=time.time()
for P in itertools.combinations(primes,k):
    W,r=maxW(P); n+=1
    if W/max(P)>best[0]: best=(W/max(P),P,W,r); print("%.4f"%best[0],P,W,r,flush=True)
print("done",n,"sets, %.0fs"%(time.time()-t))
