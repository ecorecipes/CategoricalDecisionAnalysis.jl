import CategoricalDecisionAnalysisProofs.Basic

/-!
# Roadmap

Prose only: what is not proved, where a statement of the plan was corrected, and what the
proved results ask of the package. This module has no declarations and no `sorry`; it is not
part of the default target.

## Status of the plan's inventory

| Item | Status |
|:--|:--|
| C1 | Imported (`FiniteKernelsProofs.FinStoch.instMarkovCategory`). Nothing reproved. |
| C2 | Proved: generic laws, instances `Id`, `D`, `P⁺` (min and max), agreement with the core. |
| C3 | Proved, in joint form and in normalised form with zero rows off the support. |
| C4 | Proved in part: affine maps are exactly the maps commuting with expectation. The clause "certainty equivalent is the transported structure" is not formalised. |
| C4b | Proved: `max` over actions is oplax (convex); EVPI, EVSI, EVPPI are interchange gaps. |
| C5 | Proved for lower expectations over generators; looseness and non-commutativity by instance. The convex-semilattice presentation and its "unique base" are not formalised. |
| C6 | Proved for expected regret, with the gap and the equality case. Nothing for maximum regret. |
| C7a | Proved for two stages (product of selection functions) and, for any horizon, in nested form. |
| C7b | Proved for two stages generically; expectation, worst case and best case instantiated. |
| C7c | Proved by explicit instances for CVaR (level 3/4) and minimax regret. |
| C8 | Proved (`Monotone` on both preorders; Lipschitz in two-sided deficiency). |
| C9 | Not attempted. See below. |
| T11 | Proved for composition, tensor and chains on one type, with the loss bounds. |
| S1a | Proved for feasibility (`IsDeficientWithin`), payoffs in `[0, 1]`. |
| S3 | Not attempted. See below. |
| Compiler correctness | Proved for one decision with a finite observation (linear case). |

## Statements of the plan that were corrected or sharpened

* **C7b: the conditions are sufficient for the *flat* criterion; one of them alone gives the
  nested one.** Backward induction is always optimal for the *nested* value as soon as the
  aggregator is monotone (`TwoStage.nestedValue_le_backwardValue`,
  `horizonPolicyValue_le_backwardValue`); the algebra law and reward-additivity are what make
  the nested value equal the value of the rule applied to the whole problem
  (`TwoStage.flatValue_eq_nestedValue`). So "CVaR fails backward induction" means: backward
  induction with CVaR optimises nested CVaR, which is a different rule. The package's flag
  should say that, and a nested-CVaR solve labelled as such is correct.
* **C7b: where the conditions are needed.** Monotonicity is needed at the first-stage
  outcomes and additivity at the second-stage outcomes only. For expectation this is
  nonnegative first-stage weights and *normalised* second-stage weights
  (`TwoStage.backwardInduction_optimal_expectation`): with a sub-stochastic second stage
  (a stopping or failure probability) reward-additivity fails and backward induction must
  carry the mass explicitly.
* **C6 is about expected regret.** "Regret under coarsening is lax" holds for the
  prior-weighted regret table cell by cell (`coarseRegret_le`) and for expected regret
  (`coarseExpectedRegret_le_expectedRegret`); the gap `evpi − evppi f` is the same for every
  action. No statement is made for maximum regret, and the plan's wording does not imply one.
* **C5: sequential composition of credal kernels is *exactly* functorial for the lower
  pullback** (`lowerPullback_credalComp`); the looseness is relative to the model in which one
  unknown kernel acts at every intermediate value (`credal_composition_loose`), not a failure
  of composition.
* **T11: which kernels must be stochastic.** In `f ; g` against `f' ; g'` the bound needs the
  exact second kernel `g` and the approximate first kernel `f'` stochastic (or, by symmetry of
  total variation, `g'` and `f`). If the approximate kernel in the *first* position is not
  normalised (a truncated emulator), the additive bound is not the one proved:
  `totalVariation_push_le` gives `ε · Σ p'` in place of `ε`.
* **C3 holds at every evidence value**, not only on the support, provided the inverse of
  evidence of probability zero is the zero row (`posterior_garble`). The support condition is
  where nonnegativity of the prior and of the first kernel is used.
* **S1a** is stated with payoffs in `[0, 1]` (range `B = 1`), actions the signals of `e'`, and
  both experiments normalised. It characterises feasibility of a tolerance `ε`, not the
  attained minimum.

## Not proved

* **C9** (`evaluate` as the unique structure-preserving functor out of the free Markov
  category on a signature). Not attempted: it needs the free Markov category on a signature,
  which Mathlib at the pin does not have, and the Julia interpreter can be tested as a
  structure-preserving map without it. What is proved towards it: the three laws `evaluate`
  must satisfy on effects (`effectPullback_id`, `effectPullback_comp`,
  `effectPullback_tensor`), assembled as `effectFunctor : FinStochᵒᵖ ⥤ Type`.
* **S3** (optimisation composes at the level of Pareto fronts of open diagrams). Not
  attempted; no definition of an open decision diagram is formalised here.
* **Backward induction beyond two stages, flat form.** `horizonPolicyValue_le_backwardValue`
  is for the nested value and Markov decision rules. The equality of nested and flat values
  over trajectories of length `n > 2`, and history-dependent policies, are not proved (the
  two-stage proof iterates, but the trajectory type has not been set up).
* **CVaR.** `cvar` is the Rockafellar-Uryasev objective maximised over the atoms. Not proved:
  that the maximum over all thresholds is attained at an atom, that it equals the sorted-tail
  value computed by `DecisionAnalysis.jl`, or anything at levels other than `3/4`. The
  numbers of the counterexample are easily confirmed in Julia.
* **The credal instance `C` as an `UncertaintyAlgebra`.** `lowerPullback_credalComp` is its
  composition law for a fixed index type; the generator index of a composite grows
  (`I × (Y → J)`), so it is not an instance of the structure as stated, and the monad (S4) is
  not formalised.
* **The compiler beyond one decision**: several decisions, imperfect recall, added
  constraints, and "compiling a composite equals composing the compiled parts".
* **The fidelity read-off for a general wiring diagram**: only composition, tensor and
  homogeneous chains; the certificate covers chains.
* **Attainment of the deficiency** and of `kernelDistance` as a programme: both are stated
  for feasible points or as a finite maximum.

## Consequences for the package

Each line names a proved result and what it asks of `CategoricalDecisionAnalysis.jl`.

* `UncertaintyAlgebra.pullback_kleisli`: one generic `pullback` with three method instances
  suffices; the property test for the functor laws can be written once over the instances.
  Monotonicity and preservation of constants are *not* laws of the generic structure; test
  them only for nonnegative, respectively normalised, kernels.
* `expectedUtility_push`: `evaluate` may either push the belief forward or pull the utility
  back; the two must agree to rounding, which is a cheap internal consistency test.
* `pullbackMin_le_pullbackD`: converting an expectation box to a worst-case box is a bound.
  The morphism `D → P⁺` (support) should be exposed as lax, with the direction stated.
* `commutesWithMix_iff_affine`, `isOplax_iff_convexOn`: a utility transformation may be moved
  through an expectation box only if it is affine; for a convex or concave transformation the
  rewrite is an inequality whose direction is known. A pipeline rewriter should carry one of
  three labels (`=`, `≤`, `≥`) and refuse otherwise.
* `evsi_eq_interchangeGap_posterior`, `evpi_eq_interchangeGap`: the VOI interpreter can be
  one function, `interchange_gap(weights, objectives)`, tested against the core's `evpi`,
  `evsi` and `evppi`.
* `posterior_garble`, `posterior_eq_zero`, `jointInverse_garble`: return the joint
  (sub-stochastic) inverse together with the normaliser; if a normalised matrix is returned,
  use a zero column for evidence of probability zero. With that convention the composition
  test needs no special case; with `nothing` or `NaN` it does.
* `TwoStage.IsBackwardPolicy.flatValue_optimal`, `cvar_backward_induction_suboptimal`,
  `minimaxRegret_backward_induction_suboptimal`: the flag "admits backward induction" is
  `true` for expectation, worst case and best case and `false` for CVaR and minimax regret;
  the two instances are ready-made fixtures (expected values `14/3` against `5`, and maximum
  regret `9` against `6`). A third label is justified: "nested" (the result is optimal for
  the nested rule) for monotone aggregators that are not algebras.
* `quantifier_selProd_maximin`: `Maximin` is literally a product of two selection functions
  (argmax over actions, argmin over states), a usable first example for the documentation.
* `coarseExpectedRegret_eq_expectedRegret_iff`: "coarsening the states loses nothing for
  this decision" is decidable without computing any regret: check for a common best action on
  each cell. `expectedRegret_sub_coarseExpectedRegret`: the regret transform should report
  the gap `evpi − evppi`, which does not depend on the action, so coarsening never reorders
  actions by expected regret.
* `totalVariation_garble_le`, `totalVariation_tensorKernel_le`: the fidelity read-off is a
  fold with `+` over both composition and tensor; it should check that approximate boxes are
  normalised (see above). `decision_loss_chain_le` gives the constant `2 B` with `B` the
  largest row range of the payoff table, as in the core.
* `isDeficientWithin_iff_forall_valueWithInformation_le`: a deficiency value is certified from
  below by a decision problem with payoffs in `[0, 1]` and one action per signal of `e'`; a
  "not within ε" witness could be exported in the same way as the core's
  `"not-garbling-witness/1"`.
* `Labelling.toExperiment_monotone`: the partition preorder embeds monotonically in the
  experiment preorder, so one implementation of "is at least as informative" (garbling)
  serves both, and a refinement test is a cheap sufficient check before the linear programme.
* `policyProgramme_optimum`, `isBinaryPolicy_iff_exists_deterministic`: for one decision the
  linear relaxation is exact; binary variables are needed only when constraints couple the
  columns of the policy. `policy_certificate_sound`: the column maxima of the objective
  coefficients are an optimal dual, so the certificate can be written without asking the
  solver for duals.
* `credal_tensor_not_commutative`: offering no tensor for credal kernels is forced, not a
  limitation of the implementation; the error message can cite the instance.
* `smoothAmbiguityMap_mono`, `smoothAmbiguityMap_depends_on_generators`,
  `smoothAmbiguityMap_credalComp_ne_nested`: `SmoothAmbiguityMap(η)` is monotone and concave
  but fails both hull invariance and the credal-monad multiplication law, so
  `is_algebra(::SmoothAmbiguityMap)` is `false` and `backward_induction_class` is `:nested`.
* `prune_redundant_lowerExpectation`, `stochasticDominance_order2_subset_order1`,
  `stochasticDominance_order1_nonempty`, `stochasticDominance_order2_nonempty`: backs
  `prune_generators(::CredalHull)` and `rule_selection(::StochasticDominance)`.
-/
