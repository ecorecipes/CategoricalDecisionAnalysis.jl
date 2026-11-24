# CategoricalDecisionAnalysis.jl

The applied-category-theory layer over
[DecisionAnalysis.jl](https://github.com/ecorecipes/DecisionAnalysis.jl). It re-exports
every name of that package and gives the same numbers; what it adds is the structure of a
decision analysis, made explicit enough to compose, to check and to prove things about.

A reader who does not know category theory can start with the first tutorial, which builds
a decision analysis as a diagram of five kinds of box and reads the usual answers off it.

```@docs
CategoricalDecisionAnalysis
```

## What is in the package

| Piece | What it is for | Main names |
|:--|:--|:--|
| Uncertainty monads and algebras | One vocabulary for "a state", "a distribution over states", "a set of possible states" and "a set of candidate distributions", and for the ways of summarising an uncertain payoff | [`DistributionMonad`](@ref), [`PowersetMonad`](@ref), [`CredalMonad`](@ref), [`StructureMap`](@ref), [`is_algebra`](@ref), [`monad_morphism`](@ref) |
| Value pullback | The expected (or worst-case, or lower-expected) utility at the input of a model, computed once for every kind of uncertainty | [`value_pullback`](@ref), [`interchange_gap`](@ref) |
| Conditionals | Bayes' rule in which evidence of probability zero is a value | [`bayesian_inverse`](@ref), [`inverse_compose`](@ref) |
| Selection functions | Decision rules as data, their product, and sequential problems | [`rule_selection`](@ref), [`selection_product`](@ref), [`backward_induction`](@ref), [`policy_search`](@ref) |
| Information | Experiments and partitions as preorders, with value monotone on both | [`is_garbling`](@ref), [`refines`](@ref), [`information_value`](@ref), [`regret_coarsening`](@ref) |
| Decision pipelines | A decision analysis as a typed diagram, and its interpreters | [`DecisionPipeline`](@ref), [`decision_pipeline`](@ref), [`evaluate`](@ref evaluate(::DecisionPipeline)), [`decision_problem`](@ref), [`value_of_information`](@ref) |
| Fidelity | The loss from deciding with an approximate model, read off the diagram | [`kernel_distance`](@ref), [`fidelity_bound`](@ref) |
| Programmes | A diagram compiled to a JuMP model, with budget and chance constraints | [`policy_program`](@ref), [`strategy_program`](@ref) |
| Certificates | Documents that the Lean checker decides | [`export_policy_certificate`](@ref), [`export_fidelity_chain_certificate`](@ref) |

## Conventions

- Everything of DecisionAnalysis holds: payoffs are utilities (higher is better), a payoff
  table is `Q[a, θ]` (rows = actions), a likelihood is `L[z, θ]` (rows = signals, columns
  sum to one), total variation is half the ℓ¹ distance.
- A kernel is column-stochastic, `K[y, x] = P(y | x)`, output first, as in FiniteKernels.
  The table of a pipeline box has the output axis first and then one axis per input wire.
- Composition is in diagrammatic order: `compose(p, q)` and `kleisli_compose(f, g)` are
  "first `p`, then `q`".
- Exact in, exact out: integer and rational inputs give rational results.
- Ties are never broken at random: a selection function returns the first best point, or
  all of them.
- Utilities in the examples are counts of individuals of the focal species, every example
  has a no-intervention action as its baseline, and every number is illustrative.

## Installation

The ecosystem packages are not registered. Clone this package beside `DecisionAnalysis.jl`
and `FiniteKernels.jl`, which it finds through `[sources]` paths; the other ecosystem
packages are fetched from GitHub.

```sh
git clone https://github.com/ecorecipes/FiniteKernels.jl
git clone https://github.com/ecorecipes/DecisionAnalysis.jl
git clone https://github.com/ecorecipes/CategoricalDecisionAnalysis.jl
cd CategoricalDecisionAnalysis.jl
julia --project -e 'using Pkg; Pkg.instantiate(); Pkg.test()'
```
