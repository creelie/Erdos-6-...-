#!/usr/bin/env python3
"""The finitely many sets excluded by the separation lemma, for u = 3, 4, 5.

The separation lemma of the paper applies when the second smallest prime satisfies
p_2 >= 2u - 1.  Otherwise p_1 < p_2 <= 2u - 3, and the counting inequality
    W (1 - sum_{q != p_1} 1/q) < u p_1
bounds W.  Using sum_{q != p_1} 1/q <= 1/p_2 + (reciprocals of the u - 2 primes after p_2),
this program computes, for each admissible pair (p_1, p_2), a bound W_max, so that a good
interval with W >= h max(P) forces max(P) <= W_max / h, and then computes the longest good
interval exactly for every set in that finite range.  The claim verified is that every such
set has all good intervals shorter than h max(P).

Usage: python3 small_cases.py
"""
import itertools
from fractions import Fraction
from math import floor

from sympy import nextprime, primerange

from good_interval import longest_good

TARGET = {3: 2, 4: 3, 5: 2}      # u -> h, the claim W < h max(P)


def check(u, h):
    worst, count = None, 0
    for p2 in primerange(3, 2 * u - 1):
        for p1 in primerange(2, p2):
            later, q = [], p2
            for _ in range(u - 2):
                q = nextprime(q)
                later.append(q)
            sigma = Fraction(1, p2) + sum(Fraction(1, r) for r in later)
            if sigma >= 1:
                raise ValueError("counting bound fails for", (p1, p2))
            wmax = floor(u * p1 / (1 - sigma))           # W < u p1 / (1 - sigma)
            top = wmax // h                              # max(P) <= W / h
            rest = [r for r in primerange(p2 + 1, top + 1)]
            for tail in itertools.combinations(rest, u - 2):
                P = (p1, p2) + tail
                W = longest_good(P)
                count += 1
                assert W < h * P[-1], (P, W)
                if worst is None or W / P[-1] > worst[0]:
                    worst = (W / P[-1], P, W)
            print(f"  u={u}: p1={p1}, p2={p2}: W < {u}p1/(1-sigma) gives W <= {wmax}, "
                  f"so max(P) <= {top}")
    print(f"u = {u}: {count} sets checked, all good intervals shorter than {h} max(P); "
          f"largest ratio {worst[0]:.4f} at P = {worst[1]} (W = {worst[2]})")


if __name__ == "__main__":
    for u, h in TARGET.items():
        check(u, h)
