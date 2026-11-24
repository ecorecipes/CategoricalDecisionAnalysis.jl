# Validation against other software

For this package the main oracles are other Julia packages: every number it shares with
DecisionAnalysis.jl must be equal (the test suite compares them on random problems), and the
evaluation and optimisation of pipelines are held to `interpret` and `contextual_optimize` of
CategoricalInfluenceDiagrams.jl. Those comparisons need nothing from this directory.

An external tool is used where one really exists for the quantity: the compiled programmes
and backward induction.

| Quantity | Reference | Script | Fixture |
|:--|:--|:--|:--|
| Optimum of the one-decision programme, with and without a budget on the expected use of an action | `scipy.optimize.linprog` (HiGHS), from a formulation written independently of `src/compile.jl` | `programs_reference.py` | `test/fixtures/validation/programs_reference.json` |
| The same over deterministic policies | `scipy.optimize.milp`, and exact enumeration with `fractions.Fraction` | `programs_reference.py` | the same file |
| Value of a three-stage decision tree (chance, decision, chance) under the expectation and under the worst case | brute-force backward induction and enumeration of every policy, with `fractions.Fraction` (exact) | `programs_reference.py` | the same file |

The script writes 25 random instances of each kind (seed 20261123) with rational data and their
provenance. `test/test_validation.jl` only reads the fixture, so the suite needs no Python. Never
edit the fixture by hand: re-run the script and report any number that moved.

## Versions used

Python 3.9.6, `numpy` 2.0.2, `scipy` 1.13.1 (`requirements.txt`).

## How to run

From the package root:

```sh
python3 -m venv validation/.venv
validation/.venv/bin/pip install -r validation/requirements.txt
validation/.venv/bin/python validation/programs_reference.py
```

`validation/.venv/` is ignored by git.

## Findings

- All 25 programmes agree: the exact optimum equals `linprog`'s to 1e-7 without the budget and
  with it, and the deterministic optimum under the budget equals `milp`'s and the exact
  enumeration.
- All 25 trees agree exactly for the expectation and for the worst case.
- No R comparison is made: no R package was found that computes these quantities for a decision
  diagram. The value-of-information estimators of the core are validated against R `voi` in
  `DecisionAnalysis.jl/validation`.
