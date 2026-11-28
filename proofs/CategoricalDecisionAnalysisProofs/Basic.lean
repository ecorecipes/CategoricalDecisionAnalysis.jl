import DecisionAnalysisProofs.Finite.Problem

/-!
# CategoricalDecisionAnalysisProofs

Lean 4 / Mathlib formalisation accompanying `CategoricalDecisionAnalysis.jl` (toolchain
`leanprover/lean4:v4.30.0`, Mathlib tag `v4.30.0`, the pins of every sibling project).

**Purpose.** These proofs back the Julia code of the categorical layer and shape it. Each
definition is the finite function a Julia function computes; each theorem is the property a
Julia test asserts, the reason for a refusal or a label, or the soundness of a checker for
something Julia exports. They are not a development of category theory or of decision theory:
Mathlib's category theory is used once, to say what the value pullback is in the Markov
category that `FiniteKernels.jl/proofs` already provides.

The package was being written from the same plan while these proofs were written, so the
Julia names below are the **planned components** of the design page
(`design/categorical-decision-analysis-jl.md`), not checked function names.

Every library module is built by `lake build --wfail`; `Audit.lean` prints the axioms of every
theorem (only `propext`, `Classical.choice`, `Quot.sound`). `Roadmap.lean` lists what remains
and has no unproved declarations.

## Dependencies

The project depends by path on `DecisionAnalysis.jl/proofs` (Lake package
`decision_analysis_proofs`) and on `FiniteKernels.jl/proofs` (`finite_kernels_proofs`).
Nothing of the core is redefined: `expectedUtility`, `valueWithInformation`, `signalValue`,
`signalProbability`, `posterior`, `garble`, `IsGarblingOf`, `deterministic`, `evpi`, `evsi`,
`evppi`, `partialValue`, `regret`, `expectedRegret`, `maxRegret`, `totalVariation`,
`IsDeficientWithin`, `lowerExpectedUtility`, `mixture`, `firstArgmax`, `maxOver`, `minOver`
and Ville's alternative are the sibling's. **C1** (finite stochastic kernels form a Mathlib
`MarkovCategory`) is `FiniteKernelsProofs.FinStoch.instMarkovCategory`, imported.

## The model

Finite types; a kernel is `f : X → Y → K` with `f x y = P(y | x)`; composition is
diagrammatic (`garble f g` is `f` then `g`). `K` is any linearly ordered field: theorems are
used at `ℝ`, examples and the certificate checker run the same definitions at `ℚ`.
Nonnegativity and normalisation are separate hypotheses, assumed only where needed.

## By planned Julia component

| Component of `CategoricalDecisionAnalysis.jl` | Lean definitions | Lean results | Module |
|:--|:--|:--|:--|
| 1. Effects and value pullback (generic in the monad and algebra) | `UncertaintyAlgebra`, `pullback`, `kleisli`, `pullbackD`, `push`, `pullbackMin`, `pullbackMax`, `relComp` | `UncertaintyAlgebra.pullback_pure`, `UncertaintyAlgebra.pullback_kleisli`, `pullbackD_garble`, `pullbackD_mono`, `expectedUtility_eq_pullbackD`, `expectedUtility_push`, `pullbackMin_relComp`, `worstCase_eq_pullbackMin`, `effectFunctor` | `Finite/Pullback.lean`, `Theory/FinStoch.lean` |
| 2. Conditionals (Bayesian inversion, support explicit) | `jointInverse`, the core's `posterior` | `jointInverse_garble`, `posterior_garble`, `posterior_eq_zero`, `signalProbability_mul_posterior` | `Finite/Inversion.lean` |
| 3. Uncertainty monads `Id`, `D`, `P⁺`, `C` and their algebras; which maps commute | `idAlgebra`, `distAlgebra`, `minAlgebra`, `maxAlgebra`, `lowerExpectation`, `lowerPullback`, `credalComp`, `CommutesWithMix`, `IsOplax`, `IsLax`, `expSmoothAmbiguity` | `pullbackMin_le_pullbackD`, `commutesWithMix_iff_affine`, `lowerExpectation_le_mixture`, `lowerPullback_credalComp`, `credal_composition_loose`, `credal_tensor_not_commutative`, `smoothAmbiguityMap_bounds`, `smoothAmbiguityMap_concave`, `smoothAmbiguityMap_depends_on_generators`, `smoothAmbiguityMap_credalComp_ne_nested`, `prune_redundant_lowerExpectation` | `Finite/Pullback.lean`, `Finite/Interchange.lean`, `Finite/CredalKernel.lean`, `Finite/SmoothAmbiguity.lean` |
| 4. Selection functions, their product, and the flag "admits backward induction" | `quantifier`, `selProd`, `IsArgmax`, `TwoStage`, `flatValue`, `nestedValue`, `backwardValue`, `IsBackwardPolicy`, `horizonBackwardValue`, `cvar` | `quantifier_selProd`, `IsArgmax.product`, `TwoStage.IsBackwardPolicy.flatValue_optimal`, `TwoStage.backwardInduction_optimal_expectation`, `TwoStage.backwardInduction_optimal_worstCase`, `horizonPolicyValue_le_backwardValue`, `cvar_backward_induction_suboptimal`, `minimaxRegret_backward_induction_suboptimal`, `stochasticDominance_order2_subset_order1`, `stochasticDominance_order1_nonempty`, `stochasticDominance_order2_nonempty` | `Finite/Sequential.lean`, `Finite/BackwardInductionFails.lean`, `Finite/SmoothAmbiguity.lean` |
| 5. Information preorders | `Experiment`, `Labelling`, their `Preorder` instances | `valueWithInformation_monotone`, `evppi_monotone`, `Labelling.toExperiment_monotone`, `abs_valueWithInformation_sub_le`, `isDeficientWithin_iff_forall_valueWithInformation_le` | `Finite/InformationOrder.lean` |
| 6. Pipelines: the VOI interpreter | `interchangeGap` | `evpi_eq_interchangeGap`, `evsi_eq_interchangeGap`, `evsi_eq_interchangeGap_posterior`, `interchangeGap_nonneg` | `Finite/Interchange.lean` |
| 6. Pipelines: the diagram-to-JuMP interpreter (one decision) | `policyValue`, `DualFeasible` | `policyValue_eq_expectedUtility`, `policyProgramme_optimum`, `isBinaryPolicy_iff_exists_deterministic`, `policy_certificate_sound` | `Finite/PolicyProgramme.lean` |
| 7. Regret transform | `coarsePayoff`, `coarseRegret`, `coarseExpectedRegret`, `coarsePrior`, `coarseMeanPayoff` | `expectedRegret_sub_coarseExpectedRegret`, `coarseExpectedRegret_le_expectedRegret`, `coarseExpectedRegret_eq_expectedRegret_iff`, `expectedRegret_coarseMeanPayoff` | `Finite/RegretCoarsening.lean` |
| 8. Compositional fidelity | `kernelDistance`, `tensorKernel`, `tensorVec`, `chain` | `totalVariation_garble_le`, `totalVariation_tensorKernel_le`, `totalVariation_chain_le`, `decision_loss_comp_le`, `decision_loss_chain_le`, `decision_loss_tensor_le` | `Finite/KernelFidelity.lean` |
| Certificates (proposed schemas) | `Certificate.RawPolicy`, `Certificate.RawFidelity` | `Certificate.RawPolicy.accepts_sound`, `Certificate.RawFidelity.accepts_sound` | `Certificate/` |

## Scope

Exact finite-model results, not a verification of Julia's floating-point arrays. The Lean and
Julia definitions are separate hand-written texts; no theorem says that the Julia code
executes these definitions. The Julia tests mirror them on fixtures and random instances, and
exported certificates are checked by `check_certificate`.
-/

namespace CategoricalDecisionAnalysisProofs

/-- Smoke theorem so that the axiom audit always has a first line. -/
theorem smoke : (1 : Nat) + 1 = 2 := rfl

end CategoricalDecisionAnalysisProofs
