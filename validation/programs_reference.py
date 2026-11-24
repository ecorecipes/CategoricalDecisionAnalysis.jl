"""Reference values for CategoricalDecisionAnalysis.jl, computed independently in Python.

Writes test/fixtures/validation/programs_reference.json. Run from the package root:

    validation/.venv/bin/python validation/programs_reference.py

Three kinds of check, on random instances (seed 20261123) with rational data:

1. The one-decision programme of a pipeline belief -> channel -> policy -> utility, with
   and without a budget on the expected use of the second action: scipy.optimize.linprog
   (HiGHS), from a formulation written here, not read from src/compile.jl.
2. The same under deterministic policies: scipy.optimize.milp, and exhaustive enumeration
   with fractions.Fraction (exact).
3. A three-stage decision tree (chance, decision, chance) solved by brute-force backward
   induction and by enumeration of every policy, with fractions.Fraction (exact), for
   the expectation and for the worst case.

Utilities are counts of individuals; every number is illustrative.
"""
import itertools
import json
import platform
import random
from fractions import Fraction

import numpy as np
import scipy
from scipy.optimize import LinearConstraint, Bounds, linprog, milp

SEED = 20261123
rng = random.Random(SEED)


def frac(x):
    return str(x.numerator) if x.denominator == 1 else f"{x.numerator}/{x.denominator}"


def probabilities(n):
    w = [rng.randint(1, 9) for _ in range(n)]
    return [Fraction(x, sum(w)) for x in w]


def policy_instance():
    n_states, n_signals, n_actions = 3, 2, 2
    prior = probabilities(n_states)
    columns = [probabilities(n_signals) for _ in range(n_states)]
    likelihood = [[columns[t][z] for t in range(n_states)] for z in range(n_signals)]
    payoff = [[Fraction(rng.randint(0, 60)) for _ in range(n_states)] for _ in range(n_actions)]
    budget = Fraction(rng.randint(1, 9), 10)
    # objective and use by cell (a, z)
    J = [[sum(prior[t] * likelihood[z][t] * payoff[a][t] for t in range(n_states))
          for z in range(n_signals)] for a in range(n_actions)]
    G = [[(sum(prior[t] * likelihood[z][t] for t in range(n_states)) if a == 1 else Fraction(0))
          for z in range(n_signals)] for a in range(n_actions)]
    cells = [(a, z) for a in range(n_actions) for z in range(n_signals)]
    c = np.array([-float(J[a][z]) for a, z in cells])
    A_eq = np.array([[1.0 if z == zz else 0.0 for a, z in cells] for zz in range(n_signals)])
    b_eq = np.ones(n_signals)
    use = np.array([[float(G[a][z]) for a, z in cells]])
    free = linprog(c, A_eq=A_eq, b_eq=b_eq, bounds=(0, 1), method="highs")
    capped = linprog(c, A_ub=use, b_ub=[float(budget)], A_eq=A_eq, b_eq=b_eq, bounds=(0, 1),
                     method="highs")
    constraints = [LinearConstraint(A_eq, b_eq, b_eq), LinearConstraint(use, -np.inf, float(budget))]
    integer = milp(c, constraints=constraints, integrality=np.ones(len(cells)), bounds=Bounds(0, 1))
    # exact enumeration of deterministic policies
    best_free, best_capped = None, None
    for policy in itertools.product(range(n_actions), repeat=n_signals):
        value = sum(J[policy[z]][z] for z in range(n_signals))
        used = sum(G[policy[z]][z] for z in range(n_signals))
        best_free = value if best_free is None else max(best_free, value)
        if used <= budget:
            best_capped = value if best_capped is None else max(best_capped, value)
    assert abs(-free.fun - float(best_free)) < 1e-9
    assert abs(-integer.fun - float(best_capped)) < 1e-7
    return {
        "prior": [frac(x) for x in prior],
        "likelihood": [[frac(x) for x in row] for row in likelihood],
        "payoff": [[frac(x) for x in row] for row in payoff],
        "budget": frac(budget),
        "optimum": frac(best_free),
        "optimum_linprog": -free.fun,
        "budget_optimum_linprog": -capped.fun,
        "budget_deterministic_optimum": frac(best_capped),
        "budget_optimum_milp": -integer.fun,
    }


def tree_instance():
    first, actions, second = ["x", "y"], ["l", "r"], ["u", "v"]
    p1, p2 = probabilities(2), probabilities(2)
    payoff = {(a, b, c): Fraction(rng.randint(0, 12)) for a in first for b in actions for c in second}

    def expectation(weights, values):
        return sum(w * v for w, v in zip(weights, values))

    def backward(aggregate1, aggregate2):
        return aggregate1(p1, [max(aggregate2(p2, [payoff[(a, b, c)] for c in second])
                                   for b in actions) for a in first])

    def exhaustive(aggregate):
        best = None
        for policy in itertools.product(actions, repeat=len(first)):
            outcomes = [(p1[i] * p2[j], payoff[(a, policy[i], c)])
                        for i, a in enumerate(first) for j, c in enumerate(second)]
            value = aggregate(outcomes)
            best = value if best is None else max(best, value)
        return best

    worst = lambda _w, values: min(values)
    eu_backward = backward(expectation, expectation)
    eu_exhaustive = exhaustive(lambda o: sum(w * v for w, v in o))
    wc_backward = backward(worst, worst)
    wc_exhaustive = exhaustive(lambda o: min(v for _, v in o))
    assert eu_backward == eu_exhaustive and wc_backward == wc_exhaustive
    return {
        "first": [frac(x) for x in p1],
        "second": [frac(x) for x in p2],
        "payoff": [[[frac(payoff[(a, b, c)]) for c in second] for b in actions] for a in first],
        "expectation": frac(eu_exhaustive),
        "worst_case": frac(wc_exhaustive),
    }


fixture = {
    "provenance": {
        "script": "validation/programs_reference.py",
        "seed": SEED,
        "python": platform.python_version(),
        "numpy": np.__version__,
        "scipy": scipy.__version__,
        "note": "Illustrative random instances; utilities are counts of individuals.",
    },
    "policy_programs": [policy_instance() for _ in range(25)],
    "trees": [tree_instance() for _ in range(25)],
}
with open("test/fixtures/validation/programs_reference.json", "w") as io:
    json.dump(fixture, io, indent=1)
    io.write("\n")
print("wrote test/fixtures/validation/programs_reference.json")
