# Contributing to CategoricalDecisionAnalysis.jl

## Local setup

The ecosystem packages are not registered. This package finds `DecisionAnalysis.jl` and
`FiniteKernels.jl` through `[sources]` paths to sibling directories, and the other ecosystem packages
(MarkovCategories, CategoricalInfluenceDiagrams and the packages under it, ResilienceCore) by GitHub URL:

```sh
git clone https://github.com/ecorecipes/FiniteKernels.jl
git clone https://github.com/ecorecipes/DecisionAnalysis.jl
git clone https://github.com/ecorecipes/CategoricalDecisionAnalysis.jl
cd CategoricalDecisionAnalysis.jl
julia --project -e 'using Pkg; Pkg.instantiate(); Pkg.test()'
```

`Pkg.test()` is the only run that counts as "the suite passes".

## Style

- Julia ≥ 1.12. Every dependency, including stdlibs and test-only extras, has a `[compat]` entry; Catlab,
  GATlab and ACSets are pinned as in the rest of the organisation.
- Format with JuliaFormatter using the repository `.JuliaFormatter.toml` (`style = "yas"`).
- `snake_case` for functions and variables, `CamelCase` for types, a leading underscore for internal
  helpers. British spelling in prose, American in identifiers. No emojis.
- Public names have docstrings with a signature line, a one-sentence summary, the conventions that fix the
  meaning (layouts, which way a composition runs), and an example where practical. A test enforces a
  docstring on every export.
- Errors follow ADR 0013. Exceptions are typed, carry the offending names, and live in `src/errors.jl`
  under `CategoricalDecisionAnalysisError`; library code never calls a bare `error("...")`. Invalid
  arguments and keywords raise `ArgumentError`. A typed error from DecisionAnalysis, FiniteKernels or
  CategoricalInfluenceDiagrams passes through unchanged.
- Types are immutable; constructors copy and check their arrays.
- No new export may have the name of something that Catlab, DecisionAnalysis, FiniteKernels,
  MarkovCategories, CategoricalInfluenceDiagrams, JuMP or Base exports, unless it is that binding with a
  new method (`compose`, `otimes`, `dom`, `codom`, `evaluate`). A test checks this. Never export `regret`
  or `regrets`.

## Tests

- One `@testset` in `test/runtests.jl` including `test_*.jl`. Random tests use a seeded `Random.Xoshiro`.
- Every fast path is checked against a slow oracle written from the definition, in `test/helpers.jl` or
  beside the test, sharing no code with the package. The main oracles are DecisionAnalysis (every number
  the two packages share must be equal) and CategoricalInfluenceDiagrams (`interpret`,
  `contextual_optimize`).
- Exact arithmetic first: a property is asserted with `==` on rational problems, then approximately in
  `Float64`.
- A law stated in a docstring (a functor law, a monad law, a monotonicity) has a test on random finite
  inputs; a refusal has a test that it refuses and a counterexample that shows why.
- Do not weaken a failing test. Fix the code, or record the failure.

## Contracts with the Lean development

The definitions written at the top of `src/monads.jl`, `src/effects.jl`, `src/conditionals.jl`,
`src/selection.jl`, `src/information.jl`, `src/fidelity.jl` and `src/compile.jl`, the certificate schemas
(`docs/src/certificates.md`) and the theorem map (`docs/src/theorems.md`) are shared with the proofs in
`proofs/`. Change them only together with that side; a change of meaning in a certificate needs a new
schema string.

## Vignettes

Edit the `.qmd`, then `julia scripts/render_vignettes.jl NN` and `julia scripts/sync_vignettes.jl`. Rendered
files are committed. Utilities are counts of individuals where no valuation exists (money only where an
example naturally has a published one, never invented); every vignette has a no-intervention baseline and
reports gains over it; examples are ecological and every number is labelled illustrative.

## Pull requests

Branch from `main`, keep pull requests focused, and make sure CI is green (tests on Julia 1.12 and latest,
formatter check, vignette-sync check, docs build).
