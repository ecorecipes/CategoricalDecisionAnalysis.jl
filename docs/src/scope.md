# Scope and prior art

## What the package does not claim

- **Optimisation does not compose in general.** Evaluation composes: the kernel and
  expected utility of a composite pipeline are the composite of those of its parts
  ([`evaluate`](@ref evaluate(::DecisionPipeline))). Compiled programmes compose: the
  programme of a chain is the programmes of its parts with shared interface variables
  ([`strategy_program`](@ref)). The **solution** does not: the best policy of a part depends
  on what the rest of the diagram does with its outputs, and there is no operation here that
  optimises parts separately and composes the results. CategoricalInfluenceDiagrams
  documents the obstruction and offers `contextual_optimize`, which optimises a part in an
  explicit context; this package reuses it in its tests and does not assert a valuation
  functor.
- **No string diagrams for credal kernels.** The credal monad is not commutative, so its
  Kleisli category has no tensor product. Credal kernels compose in sequence only
  ([`kleisli_compose`](@ref), [`CredalMonad`](@ref)). Sequential composition is exactly
  functorial for the lower pullback; it is loose relative to a model in which one unknown
  kernel acts at every intermediate value, because the composite lets the second step choose
  again after every outcome of the first. A [`DecisionPipeline`](@ref) takes a credal belief
  at a belief box (and hands it to the robust rules of DecisionAnalysis); its channel and
  consequence boxes are ordinary stochastic kernels.
- **Backward induction is not offered for every rule.** It is optimal for the criterion
  applied to the whole problem only when the criterion is an Eilenberg-Moore algebra and
  monotone. For a monotone criterion that is not an algebra (CVaR) it solves the nested
  rule, a different rule, and says so; for minimax regret it is a labelled heuristic
  ([`backward_induction_class`](@ref)).
- **Set-valued products of selection functions** are offered for deterministic problems
  only ([`optimal_plays`](@ref)), where they were tested against exhaustive search.
- **Optics and open games** are not in this package; CategoricalInfluenceDiagrams has an
  open-game layer.
- **The fidelity bound is usually far from tight.** It is a guarantee, not an estimate.
- Nothing here makes a value of information cheaper to compute or validates a model's causal
  or calibration claims.

## Prior art

The constructions are known ones. The package implements them, tests them against the core
and each other, and backs them with the Lean development in `proofs/`.

| Construction | Source |
|:--|:--|
| Markov categories, copy and discard; the free Markov category and its evaluation functor | Fritz (2020); Fritz and Liang (2023); MarkovCategories.jl |
| Reward kernels in the expectation semiring; valuation algebras for decision problems | Shenoy; Pralet, Verfaillie and Schiex; Li and Eisner; CategoricalInfluenceDiagrams.jl (`RewardKernel`) |
| Value pullback as the weakest pre-expectation fixed by an Eilenberg-Moore algebra | State-and-effect triangles: Jacobs; Hasuo |
| Convex and concave maps as oplax and lax algebra morphisms (Jensen as structure) | Fritz and Perrone (ordered Kantorovich monad) |
| Conditioning through sub-stochastic kernels and normalisation | Di Lavore and Román; Di Lavore, Román and Sobociński (partial Markov categories) |
| The credal monad is not commutative; graded credal kernels | Liell-Cock and Staton (2025) |
| Selection functions and their product | Escardó and Oliva (2010, 2011) |
| Selection functions over a monad; decision rules as selection functions | Hedges (2014); Hedges et al. |
| Choice with probability and reward; three semantics | Abadi and Plotkin (2020) |
| When monadic backward induction is correct | Brede and Botta (2021) |
| Set-valued (multi-valued) selection functions fail for games | Bolt, Hedges and Zahn |
| Comparison of experiments in Markov categories; distributions over posteriors | Blackwell; Fritz, Gonda, Perrone and Rischel (2023) |
| Deficiency | Le Cam; van Rooyen |
| Divergences on Markov categories, sub-additive under composition and tensor | Perrone; Rischel and Weichwald |
| Open causal models with actions as input wires; intervention as substitution | Jacobs, Kissinger and Zanasi; Lorenz and Tull |
| Structural criterion for value of information | van Merwijk, Carey and Everitt (2022); Lauritzen and Nilsson (2001) |
| Influence diagrams as mixed-integer programmes (path formulation) | Salo, Andelmin and Oliveira (2022); DecisionProgramming.jl |
| Open optimisation problems composed along shared variables | Hanks, Klawonn, Patterson, Hale and Fairbanks (2024); AlgebraicOptimization.jl |
| Optimisation composes at the level of Pareto fronts | Watanabe et al. (2023, 2024); Censi (co-design) |

Neither DecisionProgramming.jl nor AlgebraicOptimization.jl is a dependency: the path
formulation and the gluing of programmes along interface variables are written here for
decision pipelines, following those sources.

## Not found by the literature search

Stated as "not found", not "does not exist" (the search of 2025 and 2026 preprints was
limited): a categorical or machine-checked treatment of EVPI, EVPPI and EVSI as interchange
gaps; a categorical treatment of Savage regret under coarsening
([`regret_coarsening`](@ref)); a classified list of which decision rules admit backward
induction ([`backward_induction_class`](@ref)); a finite machine-checked additive fidelity
bound including tensor.

## Not implemented

- **Pareto-front composition of open pipelines** (the one setting in which optimisation is
  known to compose). A two-component finite statement would be: each open component
  exports the Pareto front of its vectors of boundary values (one coordinate per joint
  value of its output interface, for each of its policies), and the front of a serial
  composite is computed from the fronts of the parts. Not attempted here or in Lean.
- **A Wasserstein variant of the fidelity bound** for Lipschitz utilities on a metric state
  space.
- **Graded credal kernels**, which would restore a tensor for imprecise kernels.
- **A fidelity certificate for a general pipeline**: the schema covers chains on one state
  space.
