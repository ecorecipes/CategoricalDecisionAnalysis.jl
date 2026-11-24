# Theorem map

The Lean 4 / Mathlib development in `proofs/` (`CategoricalDecisionAnalysisProofs`) backs
the Julia code: a definition there is the finite function a Julia function computes, and a
theorem is the property a Julia test asserts, the reason for a refusal or a label, or the
soundness of a checker for something Julia exports. The two are separate hand-written
texts; no theorem says that the Julia code executes the Lean definitions. What holds them
together is this table: the Lean statement, the Julia function it is about, and the test
that asserts the same property on random finite inputs.

| Lean | Julia | Test |
|:--|:--|:--|
| `UncertaintyAlgebra.pullback_pure`, `UncertaintyAlgebra.pullback_kleisli` | [`value_pullback`](@ref) with [`kleisli_identity`](@ref) and [`kleisli_compose`](@ref), any algebra | `test_effects.jl`, "functor laws" |
| `pullbackD_identity`, `pullbackD_garble` | `value_pullback(K, u)`, the matrix fast path | `test_effects.jl`, "the matrix fast path against the generic pullback" |
| `pullbackD_mono`, `pullbackD_const` | the same, for stochastic kernels only | `test_effects.jl`, "monotone and constant-preserving for stochastic kernels" |
| `expectedUtility_push` | push the belief forward = pull the utility back | `test_effects.jl`, "push the belief forward = pull the utility back" |
| `pullbackMin_relComp`, `pullbackMax_relComp`, `worstCase_eq_pullbackMin` | `value_pullback` with [`InfimumAlgebra`](@ref) and [`SupremumAlgebra`](@ref) | `test_effects.jl`, "functor laws"; `test_monads.jl`, "structure maps agree with the core's aggregators" |
| `pullbackMin_le_pullbackD` | the support morphism is lax ([`MonadMorphism`](@ref)) | `test_effects.jl`, "the support is lax" |
| `commutesWithMix_iff_affine`, `isOplax_iff_convexOn` | [`expectation_rewrite`](@ref), [`interchange_gap`](@ref) with `h` | `test_effects.jl`, "interchange gap" |
| `evpi_eq_interchangeGap`, `evsi_eq_interchangeGap`, `evppi_eq_interchangeGap`, `evsi_eq_interchangeGap_posterior`, `interchangeGap_nonneg` | `interchange_gap(weights, objectives)`, [`posterior_payoff`](@ref) | `test_effects.jl`, "interchange gap = the values of information" |
| `jointInverse_garble`, `posterior_garble`, `posterior_eq_zero`, `signalProbability_mul_posterior` | [`bayesian_inverse`](@ref), [`inverse_compose`](@ref) | `test_conditionals.jl`, "inversion of a composite" and "agreement with the core's bayes_invert" |
| `lowerExpectation_le_mixture`, `lowerPullback_credalComp` | [`LowerExpectationAlgebra`](@ref), `value_pullback` for the [`CredalMonad`](@ref) | `test_monads.jl`, "algebra laws"; `test_effects.jl`, "functor laws: LowerExpectationAlgebra" |
| `credal_composition_loose`, `credal_tensor_not_commutative` | [`CredalMonad`](@ref): sequence only | `test_monads.jl`, "credal kernels: sequence only" and "the credal monad is not commutative" |
| `quantifier_selProd`, `IsArgmax.product`, `quantifier_selProd_maximin` | [`selection_product`](@ref), [`quantifier`](@ref) | `test_selection.jl`, "product of selection functions" |
| `TwoStage.IsBackwardPolicy.flatValue_optimal`, `TwoStage.backwardInduction_optimal_expectation`, `TwoStage.backwardInduction_optimal_worstCase` | [`backward_induction`](@ref) for criteria of class `:flat` | `test_sequential.jl`, "expectation: product = exhaustive search", "worst and best case" |
| `TwoStage.nestedValue_le_backwardValue`, `horizonPolicyValue_le_backwardValue` | `backward_induction(...; nested = true)`, [`nested_value`](@ref) | `test_sequential.jl`, "nested rules" |
| `cvar_backward_induction_suboptimal`, `cvar_two_step_ne_one_step` | the refusal for CVaR ([`backward_induction_class`](@ref)) | `test_sequential.jl`, "CVaR: the Lean counterexample" (values 14/3 and 5) |
| `minimaxRegret_backward_induction_suboptimal` | the refusal for minimax regret | `test_sequential.jl`, "minimax regret: the Lean counterexample" (values 9 and 6) |
| `cvar` (Rockafellar-Uryasev over the atoms) | [`CVaRMap`](@ref), the sorted tail of DecisionAnalysis | `test_sequential.jl`, "Rockafellar-Uryasev over the atoms = the sorted tail" |
| `valueWithInformation_monotone`, `evsi_monotone`, `evppi_monotone`, `Labelling.toExperiment_monotone` | [`information_value`](@ref), [`is_garbling`](@ref), [`refines`](@ref), [`partition_experiment`](@ref) | `test_information.jl`, the two "preorder" test sets |
| `abs_valueWithInformation_sub_le` | [`value_gap_bound`](@ref), [`information_distance`](@ref) | `test_information.jl`, "deficiency" |
| `expectedRegret_sub_coarseExpectedRegret`, `coarseRegret_le`, `coarseExpectedRegret_le_expectedRegret`, `coarseExpectedRegret_eq_expectedRegret_iff` | [`regret_coarsening`](@ref), [`coarsening_is_lossless`](@ref) | `test_information.jl`, "regret under coarsening (C6)" |
| `totalVariation_garble_le`, `totalVariation_tensorKernel_le`, `totalVariation_chain_le` | [`kernel_distance`](@ref) | `test_fidelity.jl`, "sub-additive under composition and tensor" |
| `decision_loss_comp_le`, `decision_loss_chain_le`, `decision_loss_tensor_le` | [`fidelity_bound`](@ref) | `test_fidelity.jl`, "the bound read off a diagram" |
| `policyValue_eq_expectedUtility`, `policyProgramme_optimum`, `isBinaryPolicy_iff_exists_deterministic` | [`policy_program`](@ref), [`solve_policy_program`](@ref) | `test_compile.jl`, "one decision: the linear programme is exact" |
| `policyValue_le_dual`, `policy_certificate_sound`, `Certificate.RawPolicy.accepts_sound` | [`export_policy_certificate`](@ref) | `test_certificates.jl`, "policy certificate" and the Lean round trip |
| `Certificate.RawFidelity.accepts_sound` | [`export_fidelity_chain_certificate`](@ref) | `test_certificates.jl`, "fidelity-chain certificate" and the Lean round trip |
| `effectPullback_id`, `effectPullback_comp`, `effectPullback_tensor` | [`evaluate`](@ref evaluate(::DecisionPipeline)) with `compose`, `otimes` and [`identity_pipeline`](@ref) | `test_pipelines.jl`, "evaluation is compositional" |

## Where the Julia definitions differ from the Lean ones

- **CVaR.** Lean defines `cvar` as Rockafellar and Uryasev's objective maximised over the
  atoms; Julia computes the mean of the sorted lower tail. The two were not proved equal in
  Lean; a test holds them equal on random finite distributions with rational data.
- **The interchange gap.** Lean's `interchangeGap w W` takes `W[i, a]` (index first, action
  second); the two-argument Julia method has that layout. The three-argument method takes
  the payoff table `Q[a, θ]` of DecisionAnalysis and a value of a monad, and reduces to the
  Lean form for the distribution monad.
- **The fidelity constant.** The Lean chain theorem uses the largest range of one action's
  payoffs across the states. [`fidelity_bound`](@ref) reads a general pipeline, where the
  payoff table is not given but computed, and uses the range of the total utility
  ([`utility_range`](@ref)), which is at least as large: the bound is valid and can be
  looser. The chain certificate takes the range as an argument, and DecisionAnalysis's
  `largest_action_range` gives the sharper one.
- **Sequential problems.** The Lean theorems are for two stages (and, in nested form, for
  any horizon with Markov decision rules). The Julia functions take any number of stages and
  history-dependent policies; beyond two stages the agreement of backward induction with
  exhaustive search is tested, not proved.
- **The credal monad.** Lean has the composition law of the lower pullback for a fixed
  index type, not the monad. Julia implements the monad on generator lists, with its laws
  holding up to equality of hulls ([`same_hull`](@ref)), which is tested.
- **Not formalised**: the strategy programme for several decisions and its composition, the
  fidelity read-off for a general wiring diagram, the structural value-of-information test,
  and `evaluate` as the unique functor out of a free Markov category.
