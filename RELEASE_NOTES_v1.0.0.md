# v1.0.0

First public release of the code and data behind the paper
*An interval problem of Erdős for four and five primes* by Deep Bhattacharjee,
Priyabrata Mandal and Ushashi Bhattacharya.

## What is in it

- The certified search over configurations of five primes. Every node of the search that has no
  real solution is closed by a Farkas certificate checked in exact rational arithmetic, and the
  eight configurations that do have real solutions are excluded by the parity condition. Together
  with the finite check for small primes this gives h(5) = 2.
- The same search for three and four primes, which confirms the hand proofs of h(3) = 2 and h(4) = 3.
- An exact scan of one period for the sets whose second prime is small (u = 3, 4, 5).
- Direct verification of every explicit good interval quoted in the paper, for four, six, eight
  and sixteen primes, including the sixteen-prime interval of ratio 4.9987.
- The exhaustive tables for pairs, triples and quadruples of primes and the SAT values for a few
  larger sets.
- The SAT searches for designs of lines that led to the constructions.
- Recorded output of every program in `logs/`.

## Running it

    pip install -r requirements.txt
    python3 configurations.py 5 2

The five-prime search takes about eight minutes on one core; everything else runs in seconds or
a few minutes.

The code was written by the authors with the assistance of Claude (Anthropic).
