#!/usr/bin/env python3
"""Exhaustive verification of the configuration lemma behind h(3)=2, h(4)=3 and h(5)=2.

Setting (see the paper).  Let P be a set of u primes whose two smallest elements satisfy the
size condition of the paper, so that two distinct primes of P share at most one multiple in a
good interval I.  Suppose I is P-good and has length W >= h * max(P).  For each point x of I that
is a multiple of some prime of P, let S(x) be the set of primes of P dividing x; goodness says
|S(x)| >= 2.  The sets S(x) form a linear hypergraph ("blocks") on the u primes in which every
prime lies in at least h blocks, and for each prime v the blocks containing v, read from left to
right, are its consecutive multiples t, t+p_v, t+2p_v, ...  With positions measured from the
left end of I, a configuration gives a solution of the linear system

    t_B' - t_B = p_v              for consecutive blocks B, B' of v,
    0 <= t_first(v) <= p_v - 1,   W - p_v <= t_last(v) <= W - 1,
    W >= h p_v,   p_0 >= 2,   p_v >= p_{v-1} + 1   (primes labelled in increasing order).

This program enumerates every labelled linear hypergraph with minimum degree >= h and every
ordering of the blocks at every vertex, depth first.  At each node the partial system is tested
for real solutions with a floating-point LP; whenever the LP reports infeasibility, a Farkas
certificate (y >= 0 on the inequalities, z free on the equalities, y.A_ub + z.A_eq = 0,
y.b_ub < 0) is computed, converted to exact rationals and checked in exact arithmetic, so that no
floating-point decision is trusted.  Nodes whose system has real solutions are kept; for the
full configurations that survive, the program checks the parity condition: consecutive
multiples of an odd prime alternate in parity, so the positions t_B mod 2 must admit a solution
with every p_v odd.  The claim verified is that no configuration survives both tests.

Usage: python3 configurations.py U H       e.g.  python3 configurations.py 5 2
"""
import itertools
import sys
import time
from fractions import Fraction

import numpy as np
from scipy.optimize import linprog


def linear_hypergraphs(u, h):
    """All families of subsets of {0..u-1} of size >= 2, pairwise meeting in <= 1 point,
    in which every point lies in at least h members."""
    subsets = [frozenset(c) for k in range(2, u + 1)
               for c in itertools.combinations(range(u), k)]
    out = []

    def grow(i, chosen):
        if i == len(subsets):
            if all(sum(v in B for B in chosen) >= h for v in range(u)):
                out.append(list(chosen))
            return
        grow(i + 1, chosen)
        if all(len(subsets[i] & B) <= 1 for B in chosen):
            grow(i + 1, chosen + [subsets[i]])

    grow(0, [])
    return out


def build_system(u, h, nblocks, orders):
    """Integer data (A_eq, A_ub, b_ub) of the system for the given partial orders."""
    nvar = nblocks + u + 1
    P = lambda v: nblocks + v
    Wi = nblocks + u
    A_eq, A_ub, b_ub = [], [], []

    def ineq(coefs, b):
        row = [0] * nvar
        for k, c in coefs:
            row[k] += c
        A_ub.append(row)
        b_ub.append(b)

    for v in range(u):
        ineq([(Wi, -1), (P(v), h)], 0)                 # h p_v <= W
        if v > 0:
            ineq([(P(v - 1), 1), (P(v), -1)], -1)      # p_{v-1} + 1 <= p_v
    ineq([(P(0), -1)], -2)                             # p_0 >= 2
    for v, order in orders.items():
        for a, b in zip(order, order[1:]):
            row = [0] * nvar
            row[b], row[a], row[P(v)] = 1, -1, -1      # t_b - t_a - p_v = 0
            A_eq.append(row)
        first, last = order[0], order[-1]
        ineq([(first, -1)], 0)                         # t_first >= 0
        ineq([(first, 1), (P(v), -1)], -1)             # t_first <= p_v - 1
        ineq([(last, -1), (Wi, 1), (P(v), -1)], 0)     # t_last >= W - p_v
        ineq([(last, 1), (Wi, -1)], -1)                # t_last <= W - 1
    return nvar, A_eq, A_ub, b_ub


def lp_feasible(nvar, A_eq, A_ub, b_ub):
    res = linprog(np.zeros(nvar), A_ub=np.array(A_ub, float), b_ub=b_ub,
                  A_eq=np.array(A_eq, float) if A_eq else None,
                  b_eq=[0] * len(A_eq) if A_eq else None,
                  bounds=[(None, None)] * nvar, method="highs")
    return res.status == 0


def farkas_certificate(nvar, A_eq, A_ub, b_ub):
    """Exact rational certificate of infeasibility, or None."""
    m1, m2 = len(A_ub), len(A_eq)
    M = np.zeros((nvar + 1, m1 + m2))
    for i, row in enumerate(A_ub):
        M[:nvar, i] = row
        M[nvar, i] = b_ub[i]
    for i, row in enumerate(A_eq):
        M[:nvar, m1 + i] = row
    rhs = np.zeros(nvar + 1)
    rhs[nvar] = -1
    res = linprog(np.r_[np.ones(m1), np.zeros(m2)], A_eq=M, b_eq=rhs,
                  bounds=[(0, None)] * m1 + [(None, None)] * m2, method="highs")
    if res.status != 0:
        return None
    for den in (10**3, 10**5, 10**7):
        y = [Fraction(x).limit_denominator(den) for x in res.x]
        if check_certificate(nvar, A_eq, A_ub, b_ub, y):
            return y
    return None


def check_certificate(nvar, A_eq, A_ub, b_ub, y):
    m1 = len(A_ub)
    if any(c < 0 for c in y[:m1]):
        return False
    for k in range(nvar):
        s = sum(y[i] * A_ub[i][k] for i in range(m1) if A_ub[i][k])
        s += sum(y[m1 + i] * A_eq[i][k] for i in range(len(A_eq)) if A_eq[i][k])
        if s != 0:
            return False
    return sum(y[i] * b_ub[i] for i in range(m1)) < 0


def parity_possible(u, nblocks, orders):
    """Is there t in (Z/2)^blocks with t_b = t_a + 1 for consecutive blocks of every vertex?"""
    colour = {}
    edges = [(a, b) for order in orders.values() for a, b in zip(order, order[1:])]
    adj = {}
    for a, b in edges:
        adj.setdefault(a, []).append(b)
        adj.setdefault(b, []).append(a)
    for start in range(nblocks):
        if start in colour:
            continue
        colour[start] = 0
        stack = [start]
        while stack:
            a = stack.pop()
            for b in adj.get(a, []):
                if b not in colour:
                    colour[b] = 1 - colour[a]
                    stack.append(b)
                elif colour[b] == colour[a]:
                    return False
    return True


def run(u, h):
    t0 = time.time()
    fams = linear_hypergraphs(u, h)
    stats = dict(nodes=0, certified=0, failed=0)
    survivors = []
    for blocks in fams:
        incident = {v: [i for i, B in enumerate(blocks) if v in B] for v in range(u)}

        def dfs(k, orders):
            stats["nodes"] += 1
            system = build_system(u, h, len(blocks), orders)
            if not lp_feasible(*system):
                if farkas_certificate(*system) is None:
                    stats["failed"] += 1
                    print("no exact certificate:", blocks, orders)
                else:
                    stats["certified"] += 1
                return
            if k == u:
                survivors.append((blocks, dict(orders)))
                return
            for perm in itertools.permutations(incident[k]):
                orders[k] = perm
                dfs(k + 1, orders)
                del orders[k]

        dfs(0, {})
    print(f"u = {u}, h = {h}")
    print(f"  linear hypergraphs with minimum degree >= {h}: {len(fams)}")
    print(f"  search nodes: {stats['nodes']}, closed by exact Farkas certificates: "
          f"{stats['certified']}, certificates not found: {stats['failed']}")
    print(f"  configurations with real solutions: {len(survivors)}")
    bad = 0
    for blocks, orders in survivors:
        ok = parity_possible(u, len(blocks), orders)
        bad += ok
        print("   ", [sorted(B) for B in blocks],
              {v: [sorted(blocks[i]) for i in o] for v, o in orders.items()},
              "parity:", "possible" if ok else "impossible")
    print(f"  configurations surviving both tests: {bad}")
    print(f"  time {time.time() - t0:.0f}s")
    return bad == 0 and stats["failed"] == 0


if __name__ == "__main__":
    u, h = int(sys.argv[1]), int(sys.argv[2])
    sys.exit(0 if run(u, h) else 1)
