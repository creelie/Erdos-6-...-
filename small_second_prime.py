#!/usr/bin/env python3
"""The sets of u primes with a small second prime, 3 <= u <= 8.

This is the computation that the Lean function SweepCheck.smallOK carries out (and that the Lean
kernel evaluates in lean/SweepCheck/Upper.lean), written out in Python with a report.

Let P = {p_1 < ... < p_u} have a good interval of length L = h p_u.  The multiples of p_1 in it
include p_1 t for K = floor(h p_u / p_1) consecutive integers t, and each of these t is divisible
by a prime of P other than p_1, so the counting inequality

    K <= sum over q in P, q != p_1, of ceil(K / q)

holds.  The program lists all sets with p_2 <= 2u - 3 that satisfy it, by a search over the primes
in increasing order.  A partial set p_1 < ... < p_k is abandoned at the candidate c for the next
prime as soon as every completion by primes >= c is excluded: with D the product of p_2, ..., p_k
and c, and A = sum_{i=2..k} D / p_i + (u - k) D / c, this happens when A < D and
(floor(h c / p_1) - 1)(D - A) > (u - 2) D.  For each surviving set a search over the residues of
the start of the interval modulo the primes shows that no interval of length h p_u is good; a
branch of that search is cut when more positions are hit by exactly one of the residue classes
chosen so far than the remaining classes can reach.  Finally the longest good interval of each
surviving set is found by scanning one period.

The claim verified is: for (u, h) = (3, 2), (4, 3), (5, 2), (6, 4), (7, 3), (8, 4), no set of u
primes with p_2 <= 2u - 3 has a good interval of length h p_u.

Usage: python3 small_second_prime.py
"""
import time
from math import prod

import numpy as np

TARGET = {3: 2, 4: 3, 5: 2, 6: 4, 7: 3, 8: 4}     # u -> h, the claim W < h p_u


def is_prime(n):
    return n >= 2 and all(n % d for d in range(2, int(n ** 0.5) + 1))


def counting_ok(P, h):
    """The counting inequality for the complete set P and the length h p_u."""
    K = h * P[-1] // P[0]
    return K <= sum((K + q - 1) // q for q in P[1:])


def candidates(u, h):
    """All sets of u primes with p_2 <= 2u - 3 whose search is not cut before completion."""
    out = []

    def extend(pre, c):
        if len(pre) == u:
            out.append(tuple(pre))
            return
        while True:
            D = prod(pre[1:]) * c
            A = sum(D // q for q in pre[1:]) + (u - len(pre)) * (D // c)
            if A < D and (h * c // pre[0] - 1) * (D - A) > (u - 2) * D:
                return
            if is_prime(c):
                extend(pre + [c], c + 1)
            c += 1

    for p2 in range(3, 2 * u - 2):
        if is_prime(p2):
            for p1 in range(2, p2):
                if is_prime(p1):
                    extend([p1, p2], p2 + 1)
    return out


def residue_search(P, L):
    """True if no choice of residues makes the positions 0, ..., L-1 good (the Lean leafOK)."""
    def lone(cnt):
        return sum(1 for c in cnt if c == 1)

    def rec(k, cnt):
        rest = P[k:]
        if sum((L + q - 1) // q for q in rest) < lone(cnt):
            return True
        if k == len(P):
            return False
        q = P[k]
        for s in range(q):
            c2 = list(cnt)
            for j in range(s, L, q):
                c2[j] += 1
            if not rec(k + 1, c2):
                return False
        return True

    return rec(0, [0] * L)


def longest_good(P):
    """The longest good interval of P, by scanning one period of the pattern of multiples."""
    n = prod(P)
    count = np.zeros(n, dtype=np.int8)
    for p in P:
        count[::p] += 1
    singular = np.flatnonzero(count == 1)
    gaps = np.diff(np.concatenate([singular, [singular[0] + n]]))
    return int(gaps.max()) - 1


def main():
    for u, h in TARGET.items():
        t0 = time.time()
        sets = candidates(u, h)
        survivors = [P for P in sets if counting_ok(P, h)]
        for P in survivors:
            assert residue_search(P, h * P[-1]), P
        print(f"u = {u}, h = {h}: the search reaches {len(sets)} complete sets, "
              f"{len(survivors)} satisfy the counting inequality, none has a good interval "
              f"of length {h} p_u ({time.time() - t0:.1f}s)", flush=True)
        for P in survivors:
            W = longest_good(P)
            print(f"    P = {P}: longest good interval {W}, target {h * P[-1]}", flush=True)
    print("claim verified")


if __name__ == "__main__":
    main()
