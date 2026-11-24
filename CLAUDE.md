# CategoricalDecisionAnalysis.jl

The applied-category-theory layer over DecisionAnalysis.jl: uncertainty monads and their algebras, value
pullback, conditionals, selection functions, information preorders, typed decision pipelines with their
interpreters, compositional fidelity, and pipelines compiled to JuMP models. It re-exports the core and
must give the same numbers.

## Place in the ecosystem

The core/categorical split is ADR 0009 of the organisation: `DecisionAnalysis.jl` is Catlab-free, and this
package is where Catlab enters. It imports the Catlab generics `compose`, `otimes`, `dom`, `codom` (from
`Catlab.Theories`) and `evaluate` (MarkovCategories', which is Catlab's), gives them methods, forwards to
the core, and re-exports every name of the core (a loop over `names(DecisionAnalysis)` in the module).

Dependencies: `DecisionAnalysis` and `FiniteKernels` by `[sources]` path to sibling directories
(`../DecisionAnalysis.jl`, `../FiniteKernels.jl`); `MarkovCategories`, `CategoricalInfluenceDiagrams`,
`InfluenceDiagrams`, `ResilienceCore` and the transitive siblings `CategoricalBayesianNetworks`,
`BayesianNetworks`, `BayesianNetworkInference`, `BayesianNetworkFormats` by GitHub URL (none is
registered, so every transitive sibling is listed in `[deps]` for its `[sources]` entry to apply; Aqua's
stale-dependency check is told so in `test/test_aqua.jl`); `Catlab` 0.17.6 and `ACSets` 0.2.29 at the
organisation's pins; `JuMP` to state programmes, never a solver (CDDLib and HiGHS are test extras and in
the vignette environment). Nothing depends on this package. Do not edit the siblings from here, with one
exception: a small, tested addition to the core when the categorical layer truly needs it, recorded in
the report of the change (none has been needed so far).

Do not `using Catlab` or `using CategoricalInfluenceDiagrams` wholesale in the module: CategoricalInfluenceDiagrams
re-exports InfluenceDiagrams, whose `FunctionUtility`, `AbstractUtility` and `optimize` clash with the
core's names, and it exports `regrets` (a best-response gap), which this package must never export.
Names are imported one by one; `InfluenceDiagrams` is reached as `IDs.`.

## Invariants that must not be broken

- **Same numbers as the core.** Anything expressible in both packages is equal in both: every rule
  through `rule_selection` (`test/test_selection.jl`), every value of information through
  `interchange_gap` and through pipelines, `bayesian_inverse` against `bayes_invert`. The comparison
  code shares nothing with the core beyond the linear-programme solver.
- **Definitions are a contract with the Lean development** (`proofs/`, read-only from the Julia side)
  and are written as a comment at the top of the source file that implements them: value pullback
  `(f* u)(x) = α(T u (f x))` (`src/effects.jl`); the monads' unit and bind and the structure maps
  (`src/monads.jl`); the joint inverse, the evidence and the zero column for evidence of probability zero
  (`src/conditionals.jl`); the product of selection functions (`src/selection.jl`); the regret
  coarsening in joint form (`src/information.jl`); kernel distance as the largest total variation over
  inputs and the bound `2 B Σ ε` (`src/fidelity.jl`); the two programmes (`src/compile.jl`).
  `docs/src/theorems.md` maps each Lean theorem to its Julia function and test, and lists where the
  Julia definition differs from the Lean one. Change neither side alone.
- **The schemas `policy-certificate/1` and `fidelity-chain-certificate/1`** (`docs/src/certificates.md`)
  are the same kind of contract. A certificate is verified in exact arithmetic before it is written; a
  change of meaning needs a new schema string. `test/test_certificates.jl` compares the exported
  documents with the hand-written fixtures in `proofs/certificate-fixtures/` and, with
  `CATEGORICALDECISIONANALYSIS_LEAN=1`, runs `lake exe check_certificate` on them.
- **Layouts.** A kernel is column-stochastic, `K[y, x] = P(y | x)`, output first. The table of a
  pipeline box has the output axis first and then one axis per input wire, in the order the inputs were
  listed; a utility box has one axis per input. `interchange_gap(weights, objectives)` takes
  `objectives[i, a]` (the Lean layout, the transpose of a payoff table); the three-argument method
  takes `Q[a, θ]`. Composition is diagrammatic everywhere.
- **Exact in, exact out.** Integer and rational inputs give rational results, through pipelines, the
  linear programme (`Rational{BigInt}` model, the core's exact simplex by default) and strategy
  enumeration. `ValuedKernel` exists because `RewardKernel` of CategoricalInfluenceDiagrams is
  `Float64` only.
- **Backward induction is classified, never silently applied.** `backward_induction_class` is `:flat`
  (algebra and monotone: expectation, worst case, best case, lower and upper expectation, certainty
  equivalents), `:nested` (monotone, not an algebra: CVaR, quantile, Hurwicz, Laplace, α-maxmin) or
  `:none` (minimax regret). `backward_induction` solves `:flat` criteria, throws
  `BackwardInductionError` for the others unless `nested = true` (label `:nested`: optimal for the
  nested rule, which is a different rule) or `heuristic = true` (label `:heuristic`, minimax regret).
  The two counterexamples of the Lean development are test fixtures (values 14/3 against 5; 9 against
  6). For a criterion that is not an algebra the quantifier of the monadic product is the *flat* value
  of the selected play, so the nested value is computed by `_recursive_policy`, not read off the
  product.
- **Set-valued products** are offered for deterministic problems only (`optimal_plays`), where they
  were tested against exhaustive search; a test shows the set is too small with chance stages.
- **Credal kernels compose in sequence only.** There is no tensor for the `CredalMonad` and no
  pipeline box holds a credal kernel; a belief box may hold a `CredalSet`, which interpreters that
  need a single distribution refuse (`MonadMismatchError`). The monad laws hold up to `same_hull`.
- **Laplace is not a function of the set of payoffs.** A set forgets multiplicities, so the Laplace
  rule is exhibited as the expectation under the uniform distribution on the states
  (`RuleSelection.uniform`), and `LaplaceMap` (the mean of the distinct values) is a different thing,
  kept only as a criterion for sequential problems over sets. Likewise a `FiniteBelief` read as a set
  is the set of **all** its states, the core's convention, not its support.
- **Optimisation does not compose, and nothing here says it does.** `evaluate` is compositional (a
  test for `compose`, `otimes` and identities); compiled strategy programmes compose
  (`compose(::StrategyProgram, ::StrategyProgram)`); the composite is still solved as one model.
- **The normal form of a pipeline is checked, not assumed.** `observation_experiment` throws when
  the observation carries payoff-relevant information beyond the belief wires; `policy_program` does
  not use the normal form and is right in that case too.
- **Fidelity.** Per-box errors are total-variation distances (`kernel_distance`), added over the boxes
  upstream of a utility. Every box table is checked to be column-stochastic when a pipeline is
  assembled, which is what the bound needs of approximate boxes (a truncated emulator is refused).
  The constant is the range of the total utility, which is valid and can be looser than the core's
  `largest_action_range`. Kullback-Leibler is not offered; the reason is that it is not a metric and
  gives no linear loss bound, **not** that it fails to compose (in the supremum form it is
  sub-additive along composition, and a test says so).
- **No export shadows a name** of Catlab, ACSets, MarkovCategories, the core, FiniteKernels,
  CategoricalInfluenceDiagrams, InfluenceDiagrams, CategoricalBayesianNetworks, JuMP or Base
  (`test/test_docstrings.jl`). `pipeline` is Base's; the constructor is `decision_pipeline`. Never
  export `regret` or `regrets`.
- Types are immutable. Ties are never broken at random. Every random number in a test is a seeded
  `Xoshiro`.

## Layout

- `src/errors.jl`: the root `CategoricalDecisionAnalysisError` and every exception under it.
- `src/monads.jl`: the five monads, their values (`FiniteDistribution`, `FiniteSubset`, `CredalHull`),
  unit, bind, map, join; hull membership by linear programme; structure maps and the algebra traits;
  monad morphisms; the core's aggregators and beliefs as structure maps and monad values;
  `KleisliMap`.
- `src/effects.jl`: `value_pullback` (generic, and the matrix, `FiniteKernel` and `RewardKernel` fast
  paths), `reward_kernel`, `interchange_gap`, `expectation_rewrite`.
- `src/conditionals.jl`: `normalize_mass`, `bayesian_inverse`, `posterior`, `inverse_compose`.
- `src/selection.jl`: `SelectionFunction`, `selection_product`, `RuleSelection` and `rule_selection`
  (every core rule), `pareto_selection`, the backward-induction classification, `SequentialProblem`,
  `policy_search`, `backward_induction`, `nested_value`, `optimal_plays`.
- `src/information.jl`: the garbling and refinement preorders, `information_value`, experiments as
  distributions over posteriors, the deficiency-enriched form, and `regret_coarsening`.
- `src/pipelines.jl`: the ACSet schema `SchDecisionPipeline` and `PipelineGraph`, `DecisionPipeline`
  (shape as an ACSet, tables beside it), the box constructors, `decision_pipeline`, `compose`,
  `otimes`, `intervene`, `ValuedKernel`, `evaluate`, `decision_problem`, `observation_experiment`,
  the forwarded core functions, `box_provenance`, `open_influence_diagram`. Everything numerical goes
  through one enumeration, `_accumulate`.
- `src/fidelity.jl`: `kernel_distance`, `jensen_shannon_distance`, `utility_range`, `total_error`,
  `fidelity_bound`.
- `src/compile.jl`: `ExpectationConstraint`, `policy_program` (a `DecisionProgram` of the core, solved
  by its `solve_program`), `strategy_program` (path formulation, open, composable) and
  `solve_strategy_program` (exact enumeration, or a mixed-integer optimiser whose strategy is then
  evaluated exactly).
- `src/structural.jl`: `with_observation`, `observation_can_matter` (d-separation).
- `src/certificates.jl`: the two exporters and their hand-written JSON.
- `src/bridges.jl`: `finite_kernel` for stochastic matrices in either orientation and for
  `ResilienceCore.MarkovKernel`.
- `test/helpers.jl`: random rational inputs and the slow oracles; `test/test_*.jl`: the suite;
  `test/fixtures/validation/`: the cross-language fixture, written by `validation/programs_reference.py`
  (Python, scipy) and only read by the tests.
- `docs/`: Documenter manual (`index.md`, `scope.md` with the non-claims and the prior art,
  `theorems.md`, `certificates.md`, the API split over `api/*.md` by source file with `@autodocs`, and
  `tutorials/`, the synced vignettes).
- `vignettes/NN_name/NN_name.qmd`: seven Quarto vignettes (Julia engine), basic to advanced, each
  rendered to `.md`, `.html` and `.pdf` beside it. Vignette 07 reads the cached Drawert et al. 2017
  table of `../Chytridiomycosis.jl`.
- `scripts/render_vignettes.jl` (run-once render) and `scripts/sync_vignettes.jl` (copy to
  `docs/src/tutorials`).
- `proofs/`: the Lean 4 / Mathlib project `CategoricalDecisionAnalysisProofs` and its
  `check_certificate` executable; see `proofs/README.md`.

## Commands

```sh
julia --project -e 'using Pkg; Pkg.instantiate(); Pkg.test()'   # the test suite; the only run that counts
CATEGORICALDECISIONANALYSIS_LEAN=1 julia --project -e 'using Pkg; Pkg.test()'   # also run exported certificates through the Lean checker (needs lake and a built proofs/)
julia --project=docs docs/make.jl --no-deploy                    # build the docs locally
validation/.venv/bin/python validation/programs_reference.py     # rewrite the Python fixture (see validation/README.md)
julia scripts/render_vignettes.jl [NN ...] [--no-execute]         # vignettes: code runs once (quarto to gfm), then pandoc makes HTML and PDF from the .md
julia scripts/sync_vignettes.jl [--check]                         # copy the rendered Markdown into docs/src/tutorials
```

## Files not to edit by hand

- `Manifest.toml` is generated and ignored; `docs/build/` is generated.
- `docs/src/tutorials/` is generated by `scripts/sync_vignettes.jl`.
- `vignettes/*/*.md`, `*.html`, `*.pdf` and `*_files/` are rendered output; edit the `.qmd` and
  re-render. Never add `html` or `pdf` to `vignettes/_quarto.yml` or a vignette's front matter (Quarto
  would re-run the code per format).
- `test/fixtures/validation/` is written by the script of `validation/`.
- `proofs/` belongs to the Lean development. Its `certificate-fixtures/` are read by the tests.

## Style

JuliaFormatter `yas`; `snake_case` functions, `CamelCase` types, a leading underscore for internals;
British spelling in prose and American in identifiers; no emojis. A docstring on every exported name,
enforced by `test/test_docstrings.jl`. Typed exceptions in `src/errors.jl` under
`CategoricalDecisionAnalysisError` (ADR 0013); invalid arguments and keywords raise `ArgumentError`;
never a bare `error()`; typed errors of the core and of FiniteKernels pass through unchanged; another
package's name in a docstring is a code span, never `@ref`. Every fast path is tested against a slow
oracle that shares no code with it. Vignette rules: counts of individuals where no valuation exists
(money only where an example naturally has a published one, never invented), a no-intervention
baseline in every vignette with gains over it, ecological examples, every number labelled
illustrative, and the first vignette readable without category theory. Scope rules: never claim that
optimisation composes in general, never offer string diagrams for credal kernels, never present a
known construction as new (`docs/src/scope.md` lists the prior art).
