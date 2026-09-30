#!/usr/bin/env python3
"""Feed the good intervals of the paper through the search of sweep_search.py.

A check that the rules and linear systems of the sweep do not exclude genuine good intervals.
For each explicit example (four, six, eight and sixteen primes) the interval is built from its
offsets, the primes are sorted, and the sequence of blocks (the sets of primes dividing the points
of the interval, from left to right) is read off.  The search of sweep_search.py is then run with
h = floor(W / max(P)), restricted to the one branch that follows this sequence of blocks; the
example passes if that branch survives every combinatorial rule and every linear system and ends
as a survivor.

Usage: python3 sweep_replay.py
"""
import sys

from sweep_search import Search
from verify_examples import EXAMPLES

sys.setrecursionlimit(20000)          # the sixteen-prime example has 32 blocks of 17 decisions each


class Replay(Search):
    """The search of sweep_search.py, confined to one prescribed sequence of blocks."""

    def __init__(self, u, h, target):
        super().__init__(u, h)
        self.target = target

    def member(self, i, v, S, c, partners, uf, blocks):
        if i >= len(self.target) or S != [w for w in self.target[i] if w < v]:
            return
        super().member(i, v, S, c, partners, uf, blocks)


def blocks_of(P, sigma, k):
    """Sorted primes, length W and blocks of the interval built as in verify_examples.py."""
    L = max(s - p for p, s in zip(P, sigma)) + 1
    R = min(s + (k + 1) * p for p, s in zip(P, sigma)) - 1
    W = R - L + 1
    primes = sorted(P)
    first = {p: (s - L) % p for p, s in zip(P, sigma)}
    points = {}
    for v, p in enumerate(primes):
        for x in range(first[p], W, p):
            points.setdefault(x, []).append(v)
    return primes, W, [tuple(points[x]) for x in sorted(points)]


if __name__ == "__main__":
    ok = True
    for name, (P, sigma, k) in EXAMPLES.items():
        primes, W, target = blocks_of(list(P), list(sigma), k)
        u, h = len(primes), W // primes[-1]
        s = Replay(u, h, target)
        st = s.run()
        passed = st['survivors'] == 1 and st['uncertified'] == 0
        ok &= passed
        print(f"{name}: u = {u}, W = {W}, h = {h}, {len(target)} blocks; "
              f"{st['nodes']} LP tests along the branch, "
              f"{'survives' if passed else 'DOES NOT SURVIVE'}", flush=True)
    print("all examples pass" if ok else "SOME EXAMPLE FAILS")
