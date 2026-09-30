#!/usr/bin/env python3
"""Reproduces the exhaustive sweeps reported in the computational section of the paper.

Exact period scans (good_interval.longest_good) for pairs, triples and quadruples of small
primes, and SAT searches (sat_interval.good_window) for a few larger sets.
"""
import itertools
from math import prod

from sympy import primerange

from good_interval import longest_good
from sat_interval import good_window


def sat_max(P, start):
    """Largest W for which a good interval of length W exists, by SAT, searching upward."""
    W, best = start, None
    while True:
        r = good_window(P, W + 1)
        if r is None:
            return W, best
        W, best = W + 1, r


def main():
    primes = list(primerange(2, 140))
    bad = [(p, q) for p, q in itertools.combinations(primes, 2) if longest_good((p, q)) != 2 * p - 1]
    print(f"pairs of primes below 140: {len(primes) * (len(primes) - 1) // 2}, "
          f"exceptions to W = 2 p_1 - 1: {bad}")

    best, n = [], 0
    for P in itertools.combinations(primes, 3):
        if prod(P) > 4 * 10**6:
            continue
        n += 1
        W = longest_good(P)
        best.append((W / P[2], W, P))
    best.sort(reverse=True)
    print(f"triples below 140 with product <= 4e6: {n}; top three:",
          [(f"{r:.4f}", W, P) for r, W, P in best[:3]])

    best, n = [], 0
    for P in itertools.combinations(list(primerange(2, 60)), 4):
        if prod(P) > 3 * 10**7:
            continue
        n += 1
        W = longest_good(P)
        best.append((W / P[3], W, P))
    best.sort(reverse=True)
    print(f"quadruples below 60 with product <= 3e7: {n}; top three:",
          [(f"{r:.4f}", W, P) for r, W, P in best[:3]])

    for P in [(101, 103, 107, 109), (191, 193, 197, 199), (101, 103, 107, 109, 113),
              (97, 101, 103, 107, 109, 113), (101, 103, 107, 109, 113, 127, 131)]:
        W, offs = sat_max(P, max(P))
        print(f"SAT: P = {P}: longest good interval {W}, ratio {W / max(P):.4f}")


if __name__ == "__main__":
    main()
