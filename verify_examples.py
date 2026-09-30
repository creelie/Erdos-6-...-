#!/usr/bin/env python3
"""Direct verification of the explicit good intervals quoted in the paper.

For a set P of primes and offsets sigma_p (the position of the first multiple of p relative to a
common reference point N+1), the Chinese remainder theorem realises the offsets, and the pattern
of multiples near N depends only on the offsets.  The interval of the paper is
    L = max_p (sigma_p - p) + 1,   R = min_p (sigma_p + k p + p) - 1,
where k + 1 is the number of multiples of each prime inside it.  For every integer of [L, R]
the number of primes of P dividing it is counted directly; the interval is good exactly when
the count 1 never occurs.  The program also constructs one integer N realising the offsets and
re-checks the first example with genuine integers.
"""
import numpy as np
from sympy import isprime
from sympy.ntheory.modular import crt


def check(P, sigma, k):
    y0 = np.array(sigma)
    Pa = np.array(P)
    L = int(max(y0 - Pa)) + 1
    R = int(min(y0 + k * Pa + Pa)) - 1
    W = R - L + 1
    cnt = np.zeros(W, dtype=np.int32)
    for p, s in zip(P, sigma):
        cnt[(s - L) % p::p] += 1
    return W, W / max(P), sorted(set(cnt.tolist()))


EXAMPLES = {
    "four primes 37, 41, 43, 47": ((37, 41, 43, 47), (36, 36, 30, 30), 1),
    "four primes 191, 193, 197, 199": ((191, 193, 197, 199), (190, 188, 190, 188), 1),
    "eight primes, quadruplets at 1006301 and 1006331":
        ([1006301, 1006303, 1006307, 1006309, 1006331, 1006333, 1006337, 1006339],
         [14, 12, 2, 0] * 2, 2),
    "eight primes, quadruplets at 10531061 and 10531091":
        ([10531061, 10531063, 10531067, 10531069, 10531091, 10531093, 10531097, 10531099],
         [14, 12, 2, 0] * 2, 2),
    "sixteen primes, two cubes at 128538791 and 128570171":
        ([e + a * 2 + b * 6 + c * 1260 for e in (128538791, 128570171)
          for c in (0, 1) for b in (0, 1) for a in (0, 1)],
         [3794 - a * 2 - 2 * b * 6 - 3 * c * 1260 for e in (0, 1)
          for c in (0, 1) for b in (0, 1) for a in (0, 1)], 3),
    "six primes at 29340119": ([29340119, 29340121, 29340139, 29340131, 29340137, 29340127],
                               [16, 16, -4, -4, 0, 0], 2),
    "six primes at 5639": ([5639, 5641, 5659, 5651, 5657, 5647], [16, 16, -4, -4, 0, 0], 2),
    "six primes at 45119": ([45119, 45121, 45139, 45131, 45137, 45127], [16, 16, -4, -4, 0, 0], 2),
    "six primes at 229751": ([229751, 229753, 229771, 229763, 229769, 229759],
                             [16, 16, -4, -4, 0, 0], 2),
}

if __name__ == "__main__":
    for name, (P, sigma, k) in EXAMPLES.items():
        assert all(isprime(p) for p in P) and len(set(P)) == len(P)
        W, r, mult = check(list(P), list(sigma), k)
        print(f"{name}: W = {W}, W/max(P) = {r:.6f}, divisor counts occurring = {mult}")
    # genuine integers for the first example
    P, sigma, k = EXAMPLES["four primes 37, 41, 43, 47"]
    N1, _ = crt(list(P), [(-s) % p for p, s in zip(P, sigma)])
    N1 = int(N1)                                     # N1 = N + 1, with N1 + sigma_p = 0 mod p
    L = N1 + max(s - p for p, s in zip(P, sigma)) + 1
    R = N1 + min(s + (k + 1) * p for p, s in zip(P, sigma)) - 1
    counts = {sum(x % p == 0 for p in P) for x in range(L, R + 1)}
    print(f"four primes 37, 41, 43, 47 realised as the integers {L}..{R} "
          f"(length {R - L + 1}); divisor counts occurring = {sorted(counts)}")
