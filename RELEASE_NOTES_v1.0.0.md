# v1.0.0

Code, proof logs and Lean formalisation for the paper
*Exact values of Erdős's interval function up to eight primes* by Deep Bhattacharjee,
Priyabrata Mandal and Ushashi Bhattacharya.

## What is in it

- A Lean 4 formalisation (core library only) of the upper bounds h(u) ≤ 1, 2, 2, 3, 2, 4, 3, 4 for
  u = 1, ..., 8. The main theorem `SweepCheck.upper_bounds` uses only the standard axioms. Its one
  hypothesis, that the verified checker accepts the proof logs, is discharged by running the
  compiled checker `sweepcheck` on `logs/proofs/`.
- The certified search `sweep_search.py`, which writes the proof logs: every closed branch carries
  a combinatorial reason or a Farkas certificate with integer multipliers.
- The treatment of the sets with a small second prime (`small_second_prime.py`), which the Lean
  kernel also evaluates directly.
- Direct verification of every explicit good interval quoted in the paper (four, six, eight and
  sixteen primes), and a replay of these intervals through the search.
- The tables of the computational section and the searches for designs of lines.
- Recorded output of every program in `logs/`.

## Running it

    xz -dk logs/proofs/sweep_8_4.bin.xz
    cd lean && lake build && ./.lake/build/bin/sweepcheck ../logs/proofs

See `README.md` for the Python programs and for regenerating the proof logs.

The code was written by the authors with the assistance of Claude (Anthropic).
