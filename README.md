# CategoricalDecisionAnalysis.jl

[![Docs](https://img.shields.io/badge/docs-dev-blue.svg)](https://ecorecipes.github.io/CategoricalDecisionAnalysis.jl/dev/)
[![Build Status](https://github.com/ecorecipes/CategoricalDecisionAnalysis.jl/actions/workflows/CI.yml/badge.svg)](https://github.com/ecorecipes/CategoricalDecisionAnalysis.jl/actions/workflows/CI.yml)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)

The applied-category-theory layer over
[DecisionAnalysis.jl](https://github.com/ecorecipes/DecisionAnalysis.jl). It re-exports every name of that
package and gives the same numbers. What it adds is the structure of a decision analysis, made explicit
enough to compose, to check and to prove things about: a decision analysis as a typed diagram, the kinds of
uncertainty and the ways of summarising them as interchangeable parts, and decision rules as data.

No category theory is needed to use it: the [first vignette](vignettes/01_first_pipeline/01_first_pipeline.md)
builds a decision analysis as a diagram of five kinds of box and reads the usual answers off it.

## Features

- **Decision pipelines.** A `DecisionPipeline` is a diagram of named wires and boxes of five kinds: Belief,
  Channel (an observation process), Policy, Consequence (an outcome model) and Utility. Boxes are joined by
  wire name (`decision_pipeline`) or with Catlab's `compose` and `otimes`; the shape is an ACSet and the
  tables are kept beside it. An action can be an input wire, and `intervene` substitutes a value on a wire.
- **Interpreters into the core.** `evaluate` gives the kernel and expected utility of a pipeline for fixed
  policies, compositionally and exactly for rational tables; `decision_problem` and
  `observation_experiment` read a one-decision pipeline as a payoff table, a belief and an experiment, on
  which `decide`, `regret_table`, `evpi`, `evsi` and `value_with_information` are forwarded;
  `value_of_information` summarises them; `box_provenance` lists what a number depends on.
- **Uncertainty monads and algebras.** No uncertainty, finite distributions, non-empty sets and credal sets
  (`IdentityMonad`, `DistributionMonad`, `PowersetMonad`, `CredalMonad`), their structure maps on the reals
  (expectation, minimum and maximum, lower and upper expectation, certainty equivalents; and CVaR, quantile,
  Hurwicz, α-maxmin, which are not algebras), and the monad morphisms between them. A belief and an
  aggregator must match or be connected by a morphism.
- **Value pullback**, implemented once for every monad and algebra (`value_pullback`), with the matrix fast
  path for stochastic kernels and agreement with `RewardKernel` of CategoricalInfluenceDiagrams. The values
  of information are one function, `interchange_gap`.
- **Conditionals.** `bayesian_inverse` goes through a sub-stochastic kernel and a normaliser, so evidence of
  probability zero is a value (a zero column), and the inverse of a composite is the composite of the
  inverses at every evidence value.
- **Selection functions.** `SelectionFunction` with its quantifier, the product of selection functions, and
  every rule of the core exhibited as one (`rule_selection`), reproducing `decide`. A rule is an algebra box
  and a selection box that can be swapped independently.
- **Sequential problems.** `backward_induction` as the iterated product, tested against `policy_search`
  (every policy). Each criterion is classified (`backward_induction_class`): backward induction is used for
  expectation, worst case, best case and lower expectation; for CVaR and other monotone non-algebras it is
  refused unless the nested rule is asked for, and labelled; for minimax regret it is a labelled heuristic.
- **Information preorders.** Experiments under garbling and partitions under refinement, with value
  monotone on both; an experiment as a distribution over posteriors; the deficiency bound on value; the
  regret transform under coarsening, whose gap is the conditional EVPI (`regret_coarsening`).
- **Compositional fidelity.** Each box may state a total-variation error; `fidelity_bound` adds the errors
  of the boxes upstream of a utility and returns the bound `2 B Σ ε` on the expected utility lost by
  deciding with the approximate diagram.
- **Diagrams compiled to programmes.** `policy_program` compiles a one-decision pipeline to a linear
  programme (a `DecisionProgram` of the core, solved exactly by default or by any JuMP optimiser);
  `strategy_program` compiles several decisions to a mixed-integer programme whose parts compose along
  shared interface variables. Budgets and chance constraints are side constraints
  (`expectation_constraint`, `chance_constraint`), which the influence-diagram solvers cannot express.
- **A structural value-of-information test.** `observation_can_matter` decides from the graph alone whether
  an observation can have positive value.
- **Certificates.** `export_policy_certificate` and `export_fidelity_chain_certificate` write JSON
  documents that the Lean checker in `proofs/` decides.
- **Kernel bridges.** `finite_kernel` for stochastic matrices in either orientation and for
  `ResilienceCore.MarkovKernel`.

## What it does not claim

- Optimisation does not compose in general. Evaluation composes, and compiled programmes compose; the
  composite programme is still solved as one. The package offers no operation that optimises parts
  separately and composes the results.
- There are no string diagrams for credal kernels: the credal monad is not commutative. Credal kernels
  compose in sequence only, soundly and loosely.
- The constructions are known ones; [`docs/src/scope.md`](docs/src/scope.md) lists the prior art and what
  the literature search did not find.

## Installation

The ecosystem packages are not registered; they are found through `[sources]` URLs, so one command
installs the package:

```julia
using Pkg
Pkg.add(url="https://github.com/ecorecipes/CategoricalDecisionAnalysis.jl")
```

To work on the package, clone it and run the suite. Only the Lean project in `proofs/` needs
`DecisionAnalysis.jl` and `FiniteKernels.jl` cloned beside it:

```sh
git clone https://github.com/ecorecipes/FiniteKernels.jl
git clone https://github.com/ecorecipes/DecisionAnalysis.jl
git clone https://github.com/ecorecipes/CategoricalDecisionAnalysis.jl
cd CategoricalDecisionAnalysis.jl
julia --project -e 'using Pkg; Pkg.instantiate(); Pkg.test()'
```

## Quick start

All numbers are illustrative; counts are of water voles.

```julia
using CategoricalDecisionAnalysis

mink = :mink_pressure => [:low, :high]
action = :action => [:no_intervention, :trap_mink, :restore_banks]
raft = :raft => [:no_tracks, :tracks]

reach = decision_pipeline(belief_box(:prior, mink, [3 // 5, 2 // 5]),
                          channel_box(:footprint_raft, mink, raft, [9//10 1//4; 1//10 3//4]),
                          policy_box(:manager, raft, action),
                          utility_box(:voles, (action, mink), [84 20; 92 64; 104 36]))

problem = decision_problem(reach; baseline=:no_intervention)
decide(problem, MaxExpectedUtility()).chosen          # [:trap_mink]
expected_gain_over_baseline(problem)                  # [0, 112//5, 92//5]
value_of_information(reach)                           # (act_now = 404//5, informed = 2112//25, evsi = 92//25, ...)

# The same rule from its two boxes, and another by swapping the algebra box
select(rule_selection(; algebra=ExpectationAlgebra()), reach)   # [:trap_mink]
select(rule_selection(; algebra=SupremumAlgebra()), reach)      # [:restore_banks]

# Compiled to a linear programme, with a limit on the expected use of an action
cap = expectation_constraint(:trapping_effort, action, [0, 1, 0]; at_most=1 // 4)
solve_policy_program(reach; constraints=[cap]).value

# A fixed policy, evaluated; and what an emulator of the raft's accuracy could cost
pipeline_value(reach; policies=(:manager => Dict(:no_tracks => :restore_banks, :tracks => :trap_mink)))
fidelity_bound(with_error(reach, :footprint_raft => 1 // 100))
```

## Vignettes

Seven vignettes in [`vignettes/`](vignettes/), basic to advanced, on ecological examples whose outcomes are
counted in individuals and always compared with no intervention (all numbers illustrative). Each is
rendered to Markdown, HTML and PDF beside its `.qmd`, with the code run once:
`julia scripts/render_vignettes.jl` (see [`vignettes/README.md`](vignettes/README.md)).

| | Vignette | Topics |
|---|---|---|
| 1 | [A decision as a diagram](vignettes/01_first_pipeline/01_first_pipeline.md) | Wires and the five kinds of box, the payoff table read off the diagram, an observation, a fixed policy, intervention, provenance |
| 2 | [Five rules from one pipeline](vignettes/02_five_rules_one_pipeline/02_five_rules_one_pipeline.md) | Kinds of uncertainty, the algebra box and the selection box, beliefs and rules that must match, the value of information as an interchange gap, regret under coarsening |
| 3 | [Chains of observation](vignettes/03_observation_chains/03_observation_chains.md) | Sampling, assay and reporting as boxes in a row, value falling along the chain, garbling, Bayesian inversion with evidence of probability zero, deficiency, the structural test |
| 4 | [Replacing a submodel by an emulator](vignettes/04_emulators_and_fidelity/04_emulators_and_fidelity.md) | Two submodels, compositional evaluation, kernel distance, the decision-loss bound read off the diagram beside the actual loss, a kernel bridge, a fidelity certificate |
| 5 | [Selection functions and backward induction](vignettes/05_selection_functions_and_backward_induction/05_selection_functions_and_backward_induction.md) | Selection functions and their product, a two-season problem, which rules can be solved backwards, the refusals for CVaR and minimax regret with their counterexamples |
| 6 | [Compiling a diagram to an optimisation programme](vignettes/06_compiling_to_a_programme/06_compiling_to_a_programme.md) | The linear programme of one decision by three solver routes, a budget, a chance constraint, several decisions as a mixed-integer programme, programmes that compose, a policy certificate |
| 7 | [Bd epizootic response as a pipeline](vignettes/07_bd_epizootic_response_as_a_pipeline/07_bd_epizootic_response_as_a_pipeline.md) | The Drawert et al. (2017) analysis of the core's vignette 14 as a pipeline with the same numbers, then a survey as a chain, a handling limit, and the cost of an error in the weights |

## Proofs

`proofs/` holds a Lean 4 / Mathlib development that backs the code: the definitions are the finite
functions the Julia functions compute, and the theorems are the properties the tests assert, the reasons
for the refusals and labels, and the soundness of the certificate checkers. `docs/src/theorems.md` maps
each theorem to its Julia function and test and lists where the two sides differ.

## Conventions

- Everything of DecisionAnalysis holds: payoffs are utilities, `Q[a, θ]` has rows = actions, `L[z, θ]` has
  rows = signals, total variation is half the ℓ¹ distance.
- A kernel is column-stochastic, `K[y, x] = P(y | x)`, output first. The table of a box has the output axis
  first and then one axis per input wire.
- Composition is diagrammatic: `compose(p, q)` is first `p`, then `q`.
- Exact in, exact out. Ties are never broken at random.

## Licence

MIT. See [LICENSE](LICENSE).
