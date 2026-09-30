# Exact values of Erdős's interval function up to eight primes: code, proof logs and Lean formalisation

Code, proof logs and a Lean 4 formalisation for the paper

> D. Bhattacharjee, P. Mandal, U. Bhattacharya,
> *Exact values of Erdős's interval function up to eight primes*.

For a set P of u primes with largest element p_u, call an integer P-singular if exactly one prime
of P divides it. Erdős (1978) asked for the least h(u) such that every interval of length
h(u)·p_u contains a P-singular integer, whatever the u primes are. The paper proves

    h(1), ..., h(8) = 1, 2, 2, 3, 2, 4, 3, 4

and gives lower and upper bounds for larger u.

## What is checked, and how

**Upper bounds, formally.** The directory `lean/` contains a Lean 4 project (core library only, no
Mathlib) whose main theorem `SweepCheck.upper_bounds` (in `lean/SweepCheck/Upper.lean`) states: for
1 ≤ u ≤ 8, every strictly increasing list P of u primes with largest element m, and all N, W such
that none of N+1, ..., N+W is divisible by exactly one element of P, we have W < h(u)·m. The proof
uses only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`) and has one hypothesis,
that the verified checker `SweepCheck.checkLog` accepts the proof log for each u = 2, ..., 8. The
executable `sweepcheck` evaluates exactly that function on the logs in `logs/proofs/`.

- The sets whose second prime is small (p_2 ≤ 2u − 3) are handled by a search that the Lean kernel
  evaluates itself (`small_ok` in `Upper.lean`); `small_second_prime.py` is the same computation in
  Python with a readable report.
- All other sets are handled by the certified search of `sweep_search.py`. Every branch it closes
  is closed either by a combinatorial rule or by a Farkas certificate with integer multipliers,
  and `--emit FILE` writes the whole search tree with all certificates as a proof log. The Lean
  checker rebuilds every linear system itself and checks every certificate in exact arithmetic,
  and its soundness theorem `SweepCheck.checkLog_sound` is part of the formal proof.

**Everything else** (the explicit good intervals behind the lower bounds, the tables of the
computational section) is checked by the Python programs listed below, with recorded output in
`logs/`.

## Reproducing the formal proof

Install Lean 4.28.0 (for example with [elan](https://github.com/leanprover/elan); the file
`lean/lean-toolchain` pins the version), then

    xz -dk logs/proofs/sweep_8_4.bin.xz      # the eight-prime log is stored compressed
    cd lean
    lake build                               # builds and checks the formal proof
    ./.lake/build/bin/sweepcheck ../logs/proofs

The last command prints one line per log and ends with
`all logs accepted: the hypothesis of SweepCheck.upper_bounds holds`. Checking all seven logs takes
under two minutes on one core. `#print axioms SweepCheck.upper_bounds` lists the axioms used.

## Regenerating the proof logs

    pip install -r requirements.txt
    python3 sweep_search.py 8 4 --emit logs/proofs/sweep_8_4.bin

and likewise for `(u, h)` = `(2, 2)`, `(3, 2)`, `(4, 3)`, `(5, 2)`, `(6, 4)`, `(7, 3)`. The search is
deterministic: with the same versions of Python and HiGHS it reproduces the logs byte for byte. The runs for u ≤ 6 take seconds, u = 7 about
six minutes and u = 8 about an hour and three quarters on one core. `--no-parity` runs the search without the parity
rule.

## Files

| file | purpose |
|---|---|
| `lean/` | Lean 4 formalisation of the upper bounds and the proof-log checker `sweepcheck` |
| `logs/proofs/sweep_U_H.bin` | proof logs for (u, h) = (2, 2), ..., (8, 4); the last one as `.xz` |
| `logs/proofs/SHA256SUMS` | SHA-256 checksums of the uncompressed proof logs |
| `sweep_search.py` | the certified search for sets with p_2 ≥ 2u − 1, writes the proof logs |
| `small_second_prime.py` | the sets with p_2 ≤ 2u − 3 (the computation that the Lean kernel evaluates) |
| `sweep_replay.py` | runs the explicit good intervals of the paper through the search; each must survive |
| `verify_examples.py` | rebuilds the explicit good intervals (four, six, eight, sixteen primes) and checks every integer |
| `good_interval.py` | exact longest good interval of a set, by scanning one period |
| `sat_interval.py`, `sweep_sat.py` | longest good interval by satisfiability over the offsets |
| `sweeps.py` | the tables for pairs, triples and quadruples and the values for a few larger sets |
| `line_designs.py`, `intercept_search.py` | searches for designs of lines (how the constructions were found) |
| `matching_designs.py` | designs whose levels are perfect matchings |
| `logs/*.log` | recorded output of the programs |

Run the Python programs from the repository root, for example `python3 small_second_prime.py`.
They need Python 3.8 or later with `numpy`, `scipy`, `sympy`, `highspy` (the HiGHS LP solver, used
only to find certificates, which are then checked exactly) and `python-sat` (for the
satisfiability programs); see `requirements.txt`.

## Authors

Deep Bhattacharjee, Priyabrata Mandal, Ushashi Bhattacharya.
The code was written by the authors with the assistance of Claude (Anthropic).

## Licence

MIT, see `LICENSE`.
