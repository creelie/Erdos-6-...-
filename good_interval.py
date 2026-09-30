#!/usr/bin/env python3
"""Longest P-good interval for a set P of primes, by scanning one full period.

An integer is P-singular if exactly one prime of P divides it; an interval is P-good if it
contains no P-singular integer.  The pattern of multiples repeats with period prod(P), so for
small P the longest good interval is found exactly by marking the singular residues of one
period (read cyclically).

Usage: python3 good_interval.py 37 41 43 47            longest good interval and W/max(P)
       python3 good_interval.py --triples 13           all triples with largest prime <= 13
       python3 good_interval.py --sweep K LO HI MAXPROD all K-subsets of primes in [LO, HI)
                                                        with product <= MAXPROD, best ten
"""
import itertools
import sys
from math import prod

import numpy as np
from sympy import primerange


def longest_good(P):
    """Length of the longest run of consecutive integers containing no P-singular integer."""
    M = prod(P)
    cnt = np.zeros(M, dtype=np.int8)
    for p in P:
        cnt[::p] += 1
    singular = cnt == 1
    idx = np.flatnonzero(np.concatenate([singular, singular]))
    if len(idx) == 0:
        return M
    return int(min((np.diff(idx) - 1).max(), M))


if __name__ == "__main__":
    a = sys.argv[1:]
    if a and a[0] == "--triples":
        top = int(a[1])
        for P in itertools.combinations(list(primerange(2, top + 1)), 3):
            W = longest_good(P)
            print(P, W, "%.4f" % (W / P[2]))
    elif a and a[0] == "--sweep":
        k, lo, hi, maxprod = int(a[1]), int(a[2]), int(a[3]), float(a[4])
        best = []
        for P in itertools.combinations(list(primerange(lo, hi)), k):
            if prod(P) > maxprod:
                continue
            W = longest_good(P)
            best.append((W / max(P), W, P))
        best.sort(reverse=True)
        for r, W, P in best[:10]:
            print("%.4f" % r, W, P)
    else:
        P = tuple(int(x) for x in a)
        W = longest_good(P)
        print("P =", P, " longest good interval:", W, " W/max(P) = %.4f" % (W / max(P)))
