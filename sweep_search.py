#!/usr/bin/env python3
"""Certified left-to-right search behind the upper bounds h(5) <= 2, h(6) <= 4, h(7) <= 3, h(8) <= 4.

Setting (see the paper).  P = {p_0 < ... < p_{u-1}} is a set of u odd primes whose second
smallest element satisfies p_1 >= 2u - 1, so that two primes of P share at most one multiple in
a good interval and every prime has at most u - 1 multiples there.  Suppose the positions
0, ..., W-1 form a P-good interval with W >= h p_{u-1}.  The points divisible by some prime of P
are x_0 < x_1 < ... < x_{n-1}; each is divisible by at least two primes, and the set of primes
dividing x_i is the i-th block.  If t_v is the position of the first multiple of p_v and c_v
blocks before the i-th contain v, then the next multiple of p_v is pi_v = t_v + c_v p_v, and

    pi_v = x_i  if v is in the i-th block,      pi_v >= x_i + 1  otherwise;

after the last block pi_v >= W for every v.  Together with

    p_0 >= 3,  p_v >= p_{v-1} + 2,  p_1 >= 2u - 1,  0 <= t_v <= p_v - 1,
    t_v + (u-1) p_v >= W,  W >= h p_{u-1},  x_0 >= 0,  x_i >= x_{i-1} + 1,  x_i <= W - 1,

this is a system of linear equations and inequalities with integer coefficients in the unknowns
p_v, t_v, W, x_i.  The program builds the blocks one at a time, deciding for each prime in turn
whether it belongs to the current block, and tests the partial system for real solutions after
every decision.  Combinatorial rules are applied as well: every block has at least two primes;
two primes lie together in at most one block (so no block can start once every pair has met);
a prime has at most u - 1 blocks, and each of its later blocks needs a partner it has not met
yet; and, the primes being odd, consecutive multiples of a prime have opposite parities, so the
primes in a block must satisfy s_v + c_v = s_w + c_w (mod 2), where s_v is the parity of t_v.

Whenever the floating-point LP (HiGHS) reports that a partial system has no real solution, a
Farkas certificate is taken from the solver's dual ray, converted to exact rationals and checked
in exact arithmetic: multipliers y_i with sum_i y_i a_i = 0 and
sum_{y_i > 0} y_i lo_i + sum_{y_i < 0} y_i hi_i > 0 for the rows lo_i <= a_i.x <= hi_i.  No branch
is closed on the word of the floating-point solver alone; the run reports any certificate that
could not be confirmed.  A "survivor" is a complete sequence of blocks whose system has a real
solution.  The claim verified is that there are no survivors and no unconfirmed certificates.

With --emit FILE the whole search is written to FILE as a proof log for the Lean checker in
lean/: one tag per node of the search tree, in the order the search visits them, and every
certificate with integer multipliers.  The format is described in lean/SweepCheck/Checker.lean.

Usage: python3 sweep_search.py U H [--no-parity] [--emit FILE]      e.g.  python3 sweep_search.py 8 4
"""
import sys
import time
from fractions import Fraction
from math import lcm

import highspy
import numpy as np

INF = highspy.kHighsInf

CERT, CAP, BND, ELM, SURV = 0, 1, 2, 3, 4          # tags of the proof log


class Log:
    """The proof log: tags and integers as unsigned LEB128 varints (integers zigzag-encoded)."""

    def __init__(self, path):
        self.f = open(path, 'wb') if path else None
        self.buf = bytearray()

    def nat(self, n):
        if self.f is None:
            return
        while True:
            b = n & 0x7f
            n >>= 7
            if n:
                self.buf.append(b | 0x80)
            else:
                self.buf.append(b)
                break
        if len(self.buf) > 1 << 20:
            self.flush()

    def int(self, z):
        self.nat(2 * z if z >= 0 else -2 * z - 1)

    def flush(self):
        if self.f is not None:
            self.f.write(self.buf)
            self.buf.clear()

    def close(self):
        if self.f is not None:
            self.flush()
            self.f.close()


class Search:
    def __init__(self, u, h, parity=True, emit=None):
        self.u, self.h, self.parity = u, h, parity
        self.log = Log(emit)
        self.maxb = u * (u - 1) // 2                  # every block uses a pair of its own
        nv = 2 * u + 1 + self.maxb
        hs = highspy.Highs()
        hs.setOptionValue('output_flag', False)
        hs.setOptionValue('presolve', 'off')
        hs.addVars(nv, np.full(nv, -INF), np.full(nv, INF))
        self.hs = hs
        self.rows = []                                # exact copies: (coefficients, lo, hi)
        P, T, W = self.P, self.T, self.W
        self.add({P(0): 1}, 3, INF)
        for v in range(1, u):
            self.add({P(v): 1, P(v - 1): -1}, 2, INF)
        self.add({P(1): 1}, 2 * u - 1, INF)
        for v in range(u):
            self.add({T(v): 1}, 0, INF)
            self.add({P(v): 1, T(v): -1}, 1, INF)
            self.add({T(v): 1, P(v): u - 1, W: -1}, 0, INF)
        self.add({W: 1, P(u - 1): -h}, 0, INF)
        self.stats = dict(nodes=0, closed_by_lp=0, certified=0, uncertified=0,
                          closed_by_counting=0, survivors=0)

    def P(self, v):
        return v

    def T(self, v):
        return self.u + v

    @property
    def W(self):
        return 2 * self.u

    def X(self, i):
        return 2 * self.u + 1 + i

    def add(self, coef, lo, hi):
        keys = sorted(coef)
        self.hs.addRow(lo, hi, len(keys), np.array(keys, dtype=np.int32),
                       np.array([float(coef[k]) for k in keys]))
        self.rows.append((dict(coef), lo, hi))

    def pop_to(self, n):
        m = len(self.rows)
        if m > n:
            self.hs.deleteRows(m - n, np.arange(n, m, dtype=np.int32))
            del self.rows[n:]

    # ------------------------------------------------------------------ LP and certificates
    def feasible(self):
        """Test the current rows; if they have no real solution, log a certificate."""
        self.stats['nodes'] += 1
        self.hs.run()
        st = self.hs.getModelStatus()
        if st not in (highspy.HighsModelStatus.kOptimal, highspy.HighsModelStatus.kInfeasible):
            self.hs.clearSolver()
            self.hs.run()
            st = self.hs.getModelStatus()
        if st == highspy.HighsModelStatus.kOptimal:
            return True
        if st != highspy.HighsModelStatus.kInfeasible:
            raise RuntimeError(f"unexpected LP status {st}")
        self.stats['closed_by_lp'] += 1
        y = self.certificate()
        if y is not None:
            self.stats['certified'] += 1
            self.write_certificate(y)
        else:
            self.stats['uncertified'] += 1
            self.log.nat(SURV)                        # the Lean checker rejects this node
            print("UNCERTIFIED", self.rows, flush=True)
        return False

    def certificate(self):
        for attempt in range(2):
            _, has, ray = self.hs.getDualRay()
            if has:
                for den in (10**4, 10**6, 10**9, 10**12):
                    y = [Fraction(float(r)).limit_denominator(den) for r in ray]
                    if self.check(y):
                        return y
                    y = [-a for a in y]
                    if self.check(y):
                        return y
            self.hs.clearSolver()
            self.hs.run()
        return None

    def check(self, y):
        total, bound = {}, Fraction(0)
        for yi, (coef, lo, hi) in zip(y, self.rows):
            if yi == 0:
                continue
            if yi > 0:
                if lo == -INF:
                    return False
                bound += yi * lo
            else:
                if hi == INF:
                    return False
                bound += yi * hi
            for k, c in coef.items():
                total[k] = total.get(k, 0) + yi * c
        return bound > 0 and all(s == 0 for s in total.values())

    def write_certificate(self, y):
        """Log the certificate with integer multipliers; rows are counted from the newest."""
        if self.log.f is None:
            return
        scale = lcm(*[a.denominator for a in y if a != 0])
        entries = [(len(self.rows) - 1 - k, int(a * scale)) for k, a in enumerate(y) if a != 0]
        self.log.nat(CERT)
        self.log.nat(len(entries))
        for k, z in entries:
            self.log.nat(k)
            self.log.int(z)

    # ------------------------------------------------------------------ parity (union-find)
    @staticmethod
    def find(uf, v):
        par, off = uf
        o = 0
        while par[v] != v:
            o ^= off[v]
            v = par[v]
        return v, o

    def join(self, uf, a, b, rel):
        """Impose s_a + s_b = rel (mod 2); None on contradiction."""
        ra, oa = self.find(uf, a)
        rb, ob = self.find(uf, b)
        if ra == rb:
            return uf if (oa ^ ob) == rel else None
        par, off = list(uf[0]), list(uf[1])
        par[rb], off[rb] = ra, oa ^ ob ^ rel
        return par, off

    # ------------------------------------------------------------------ the search
    def run(self):
        u = self.u
        self.t0 = time.time()
        self.step(0, [0] * u, [frozenset()] * u, (list(range(u)), [0] * u), [])
        self.log.close()
        return self.stats

    def step(self, i, c, partners, uf, blocks):
        """Before the i-th block: end the interval here, or start another block."""
        u, h = self.u, self.h
        for v in range(u):
            if c[v] + (u - 1 - len(partners[v])) < h:
                self.stats['closed_by_counting'] += 1
                self.log.nat(CAP)
                self.log.nat(v)
                return
        self.log.nat(BND)
        base = len(self.rows)
        if min(c) >= h:                               # try to end the interval here
            for v in range(u):
                self.add({self.T(v): 1, self.P(v): c[v], self.W: -1}, 0, INF)
            if self.feasible():
                self.stats['survivors'] += 1
                self.log.nat(SURV)
                print("SURVIVOR", blocks, flush=True)
            self.pop_to(base)
        if all(len(partners[v]) == u - 1 for v in range(u)):
            return                                    # every pair has met: no further block
        X = self.X(i)
        self.add({X: 1, self.X(i - 1): -1} if i else {X: 1}, 1 if i else 0, INF)
        self.add({self.W: 1, X: -1}, 1, INF)
        if self.feasible():
            self.member(i, 0, [], c, partners, uf, blocks)
        self.pop_to(base)

    def member(self, i, v, S, c, partners, uf, blocks):
        """Decide whether the prime of rank v belongs to the i-th block."""
        u = self.u
        if v == u:
            c2 = [c[w] + (w in S) for w in range(u)]
            p2 = [partners[w] | frozenset(S) - {w} if w in S else partners[w]
                  for w in range(u)]
            self.step(i + 1, c2, p2, uf, blocks + [tuple(S)])
            return
        self.log.nat(ELM)
        base = len(self.rows)
        pi = {self.T(v): 1, self.X(i): -1}
        if c[v]:
            pi[self.P(v)] = c[v]
        can_join = c[v] < u - 1 and not (partners[v] & set(S))
        uf2 = uf
        if can_join and S and self.parity:
            uf2 = self.join(uf, v, S[0], (c[v] + c[S[0]]) & 1)
            can_join = uf2 is not None
        if can_join:
            self.add(pi, 0, 0)                        # v divides x_i
            self.child(i, v, S + [v], c, partners, uf2, blocks)
            self.pop_to(base)
        self.add(pi, 1, INF)                          # the next multiple of v comes later
        self.child(i, v, S, c, partners, uf, blocks)
        self.pop_to(base)

    def child(self, i, v, S, c, partners, uf, blocks):
        """After the decision on v: a block with fewer than two primes is dropped untested."""
        if v + 1 == self.u and len(S) < 2:
            return
        if self.feasible():
            self.member(i, v + 1, S, c, partners, uf, blocks)


if __name__ == "__main__":
    sys.setrecursionlimit(10000)
    u, h = int(sys.argv[1]), int(sys.argv[2])
    emit = sys.argv[sys.argv.index('--emit') + 1] if '--emit' in sys.argv else None
    s = Search(u, h, parity='--no-parity' not in sys.argv, emit=emit)
    st = s.run()
    print(f"u = {u}, h = {h}{'' if s.parity else ', parity rule off'}: "
          f"{st['nodes']} LP tests, {st['closed_by_lp']} branches closed by the LP "
          f"({st['certified']} exact certificates confirmed, {st['uncertified']} not), "
          f"{st['closed_by_counting']} closed by counting, {st['survivors']} survivors, "
          f"{time.time() - s.t0:.0f}s")
    ok = st['survivors'] == 0 and st['uncertified'] == 0
    print("claim verified" if ok else "CLAIM NOT VERIFIED")
