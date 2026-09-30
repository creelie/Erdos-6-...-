# An interval problem of Erdős for four and five primes: code and data

Code and recorded output for the paper

> D. Bhattacharjee, P. Mandal, U. Bhattacharya,
> *An interval problem of Erdős for four and five primes*.

For a set P of u primes with largest element p_u, call an integer P-singular if exactly one prime
of P divides it. Erdős (1978) asked for the least h(u) such that every interval of length
h(u)·p_u contains a P-singular integer, whatever the u primes are. The paper proves
h(1) = 1, h(2) = h(3) = 2, h(4) = 3 and h(5) = 2, and gives general lower and upper bounds.

What the programs establish:

1. **Five primes** (`configurations.py 5 2`). Every labelled linear hypergraph on five vertices with
   minimum degree two, with every ordering of the blocks at every vertex, is examined. For
   114 626 of the 133 057 search nodes the linear system of the paper has no real solution, and each
   of these is closed by a Farkas certificate verified in exact rational arithmetic. The eight
   complete configurations with real solutions all violate the parity condition for odd primes.
2. **Three and four primes** (`configurations.py 3 2`, `configurations.py 4 3`): the same search leaves
   nothing (these cases also have short proofs by hand in the paper).
3. **Small primes** (`small_cases.py`): the finitely many sets that the separation lemma does not cover
   (u = 3, 4, 5) are checked by an exact scan of one period.
4. **Examples** (`verify_examples.py`): the good intervals quoted in the paper (four, six, eight and sixteen
   primes) are rebuilt and every integer in them is checked to be divisible by none or at least two of the primes.
5. **Sweeps** (`sweeps.py`, `sweep_sat.py`, `good_interval.py`): the exhaustive tables for pairs, triples,
   quadruples and a few larger sets.

## Requirements

Python 3.8 or later with `numpy`, `scipy` (LP solver HiGHS, used only to *find* certificates),
`sympy` and `python-sat` (CaDiCaL, for the SAT programs). Tested with numpy 2.4, scipy 1.17,
sympy 1.14, python-sat 1.9.

    pip install -r requirements.txt

## Files

| file | purpose | runtime (one core) |
|---|---|---|
| `configurations.py` | the certified search of Section 4 (`5 2`), and the analogues `3 2`, `4 3` | ~8 min for `5 2`, seconds otherwise |
| `small_cases.py` | the sets with a small second prime, u = 3, 4, 5 | seconds |
| `good_interval.py` | exact longest good interval by scanning one period; `--triples`, `--sweep` | seconds |
| `sat_interval.py` | longest good interval by SAT over the offsets | – |
| `sweep_sat.py` | all K-subsets of primes in a range through the SAT program | minutes |
| `sweeps.py` | the pair, triple and quadruple tables and the SAT values quoted in Section 7 | ~2 min |
| `verify_examples.py` | direct verification of the explicit good intervals | ~1 min |
| `line_designs.py`, `intercept_search.py` | SAT searches for designs of lines (how the constructions were found) | – |
| `matching_designs.py` | designs whose levels are perfect matchings | seconds |
| `logs/` | recorded output of every program | |

Run any program from the repository root, for example `python3 configurations.py 5 2`.

## Authors

Deep Bhattacharjee, Priyabrata Mandal, Ushashi Bhattacharya.
The code was written by the authors with the assistance of Claude (Anthropic).

## Licence

MIT, see `LICENSE`.
