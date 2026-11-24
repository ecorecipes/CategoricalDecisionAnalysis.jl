# CategoricalDecisionAnalysisProofs

Lean 4 / Mathlib formalisation for `CategoricalDecisionAnalysis.jl` (toolchain v4.30.0, Mathlib
v4.30.0).

**Purpose.** These proofs back the Julia code of the categorical layer and shape it. Each
definition is the finite function a Julia function computes; each theorem is the property a
Julia test asserts, the reason for a refusal or a label, or the soundness of a checker for
something Julia exports. They are not a development of category theory or of decision theory.

**Status of the Julia side.** The package was written from the same plan while these proofs were
written. The Julia names below are the *planned components* of the design; `docs/src/theorems.md`
maps theorems to the functions as built. The Julia tests mirror the definitions here (the two
backward-induction counterexamples, the regret-coarsening identity, CVaR in both forms) and
exported certificates go through `check_certificate`. No theorem says that the Julia code executes
these definitions.

```sh
cd proofs
make build            # lake build --wfail: the default target, sorry-free
make audit            # #print axioms for every theorem, and a source scan
make check-fixtures   # check_certificate on certificate-fixtures/, exit codes as in EXPECTED.md
make roadmap          # builds the remaining-work module (prose only)
```

The dependency checkout is shared with the other ecosystem `proofs/` projects via `packagesDir`
(`../../.lake-packages`), at the same Lean and Mathlib pins, so nothing is downloaded when a
sibling project has been built (`lake exe cache get` otherwise). The project depends by path on
`../../DecisionAnalysis.jl/proofs` (`decision_analysis_proofs`) and
`../../FiniteKernels.jl/proofs` (`finite_kernels_proofs`); building it also builds those two
libraries in their own `.lake` directories. `Roadmap.lean` is not imported by the default
target. No CI workflow is included yet.

## What is reused

Nothing of the core is redefined. `expectedUtility`, `valueWithInformation`, `signalValue`,
`signalProbability`, `posterior`, `garble`, `IsGarblingOf`, `deterministic`, `evpi`, `evsi`,
`evppi`, `partialValue`, `regret`, `expectedRegret`, `maxRegret`, `totalVariation`,
`IsDeficientWithin`, `lowerExpectedUtility`, `mixture`, `firstArgmax`, `maxOver`, `minOver`,
the T6, T6a and T10 theorems and Ville's alternative come from `DecisionAnalysisProofs`. The
Markov category of finite stochastic kernels (C1) is `FiniteKernelsProofs.FinStoch`.

## What is formalised

Finite types; a kernel is `f : X → Y → K` with `f x y = P(y | x)`; composition is diagrammatic
(`garble f g` is `f` then `g`). `K` is any linearly ordered field: the theorems are used at
`ℝ`, the counterexamples and the certificate checker run the same definitions at `ℚ`.

### By planned Julia component

| Component (design page) | What the proofs back | Lean | Module |
|:--|:--|:--|:--|
| 1. Effects and value pullback | The generic `pullback(algebra, f, u)` and its instances; the test "functor laws for value pullback on random kernels"; agreement with the core | `UncertaintyAlgebra.pullback_pure`, `UncertaintyAlgebra.pullback_kleisli`, `pullbackD_identity`, `pullbackD_garble`, `pullbackD_mono`, `pullbackD_const`, `pullbackMin_relComp`, `pullbackMax_relComp`, `expectedUtility_eq_pullbackD`, `expectedUtility_push`, `worstCase_eq_pullbackMin`, `pullbackD_tensorKernel`, `effectFunctor` | `Finite/Pullback.lean`, `Theory/FinStoch.lean` |
| 2. Conditionals | Bayesian inversion through a sub-stochastic kernel and a normaliser; inversion of a composite; evidence of probability zero as a value | `jointInverse_garble`, `posterior_garble`, `posterior_eq_zero`, `signalProbability_mul_posterior`, `posterior_garble_normalised` | `Finite/Inversion.lean` |
| 3. Uncertainty monads and their algebras | Which maps may be moved through an expectation (`=` for affine, `≤` for convex, `≥` for concave); `D → P⁺` is lax; lower expectation is computed over generators; credal kernels compose in sequence only | `commutesWithMix_iff_affine`, `isOplax_iff_convexOn`, `pullbackMin_le_pullbackD`, `lowerExpectation_le_mixture`, `lowerExpectation_concave`, `lowerPullback_credalComp`, `credal_composition_loose`, `credal_tensor_not_commutative` | `Finite/Interchange.lean`, `Finite/Pullback.lean`, `Finite/CredalKernel.lean` |
| 4. Selection functions | The product of selection functions against exhaustive search; the per-rule flag "admits backward induction" and the refusal for CVaR and minimax regret | `quantifier_selProd`, `IsArgmax.product`, `selProd_firstArgmax_spec`, `TwoStage.IsBackwardPolicy.flatValue_optimal`, `TwoStage.backwardInduction_optimal_expectation`, `TwoStage.backwardInduction_optimal_worstCase`, `horizonPolicyValue_le_backwardValue`, `cvar_backward_induction_suboptimal`, `minimaxRegret_backward_induction_suboptimal` | `Finite/Sequential.lean`, `Finite/BackwardInductionFails.lean` |
| 5. Information preorders | Value as a monotone map out of the garbling and refinement preorders; Lipschitz in deficiency; a deficiency value read as a uniform value gap | `valueWithInformation_monotone`, `evsi_monotone`, `evppi_monotone`, `Labelling.toExperiment_monotone`, `abs_valueWithInformation_sub_le`, `isDeficientWithin_iff_forall_valueWithInformation_le` | `Finite/InformationOrder.lean` |
| 6. Pipelines, VOI interpreter | VOI as "maximise then average minus average then maximise", equal to the core's EVPI, EVSI, EVPPI | `evpi_eq_interchangeGap`, `evsi_eq_interchangeGap`, `evppi_eq_interchangeGap`, `evsi_eq_interchangeGap_posterior`, `interchangeGap_nonneg` | `Finite/Interchange.lean` |
| 6. Pipelines, diagram-to-JuMP interpreter | One decision: the objective is expected utility, the feasible set is the set of strategies, the optimum is the core's value and is attained deterministically | `policyValue_eq_expectedUtility`, `policyProgramme_optimum`, `isBinaryPolicy_iff_exists_deterministic`, `policyValue_le_dual`, `policy_certificate_sound` | `Finite/PolicyProgramme.lean` |
| 7. Regret transform | The coarsening inequality, its gap `evpi − evppi`, and the equality case | `expectedRegret_sub_coarseExpectedRegret`, `coarseExpectedRegret_le_expectedRegret`, `coarseRegret_le`, `coarseExpectedRegret_eq_expectedRegret_iff`, `expectedRegret_coarseMeanPayoff` | `Finite/RegretCoarsening.lean` |
| 8. Compositional fidelity | Errors add along composition and tensor; the loss bound `2 B Σ ε` read off a chain or a tensor | `totalVariation_garble_le`, `totalVariation_tensorKernel_le`, `totalVariation_chain_le`, `decision_loss_comp_le`, `decision_loss_chain_le`, `decision_loss_tensor_le` | `Finite/KernelFidelity.lean` |

### By plan item

| Item | Headline theorems | Proved |
|:--|:--|:--|
| C1 | `FiniteKernelsProofs.FinStoch.instMarkovCategory` (imported) | upstream |
| C2 | `UncertaintyAlgebra.pullback_kleisli`, `pullbackD_garble`, `pullbackMin_relComp` | yes |
| C3 | `posterior_garble` | yes |
| C4 | `commutesWithMix_iff_affine` | yes, without the certainty-equivalent clause |
| C4b | `convexOn_maxOver`, `evsi_eq_interchangeGap_posterior` | yes |
| C5 | `lowerExpectation_le_mixture`, `lowerPullback_credalComp`, `credal_composition_loose`, `credal_tensor_not_commutative` | yes, without the convex-semilattice presentation |
| C6 | `expectedRegret_sub_coarseExpectedRegret`, `coarseExpectedRegret_eq_expectedRegret_iff` | yes, for expected regret |
| C7a | `IsArgmax.product`, `horizonPolicyValue_le_backwardValue_deterministic` | yes |
| C7b | `TwoStage.IsBackwardPolicy.flatValue_optimal` | yes, two stages |
| C7c | `cvar_backward_induction_suboptimal`, `minimaxRegret_backward_induction_suboptimal` | yes, by instance |
| C8 | `valueWithInformation_monotone`, `evppi_monotone`, `abs_valueWithInformation_sub_le` | yes |
| T11 | `totalVariation_garble_le`, `totalVariation_tensorKernel_le`, `decision_loss_chain_le` | yes |
| S1a | `isDeficientWithin_of_forall_valueWithInformation_le` | yes, payoffs in `[0, 1]` |
| Compiler | `policyProgramme_optimum` | yes, one decision |
| C9, S3 | none | no; see `Roadmap.lean` |

### By certificate

Both schemas are documented in `docs/src/certificates.md` and written by `export_policy_certificate`
and `export_fidelity_chain_certificate`; the fixtures here are written by hand.

| Schema | Checker | Soundness theorem |
|:--|:--|:--|
| `"policy-certificate/1"`: problem, policy, dual vector, value | `Certificate.checkPolicy` | `Certificate.RawPolicy.accepts_sound`: the value is `valueWithInformation` and the policy is optimal |
| `"fidelity-chain-certificate/1"`: boxes with exact and approximate kernels and errors, range, bound | `Certificate.checkFidelity` | `Certificate.RawFidelity.accepts_sound`: the decision loss is at most the bound |

`lake exe check_certificate FILE.json` exits 0 when the proved checker accepts, 1 when it
rejects, 2 when the document is malformed. The JSON parser and the decoding are trusted.

### Modules

| Module | Content |
|:--|:--|
| `Basic.lean` | Introduction, the component table, the smoke theorem |
| `Finite/Pullback.lean` | C2 |
| `Finite/Sequential.lean` | C7a, C7b |
| `Finite/BackwardInductionFails.lean` | C7c |
| `Finite/RegretCoarsening.lean` | C6 |
| `Finite/KernelFidelity.lean` | T11 |
| `Finite/InformationOrder.lean` | C8, S1a |
| `Finite/Interchange.lean` | C4, C4b |
| `Finite/Inversion.lean` | C3 |
| `Finite/CredalKernel.lean` | C5 |
| `Finite/PolicyProgramme.lean` | The one-decision programme |
| `Theory/FinStoch.lean` | Value pullback as a functor on the imported Markov category |
| `Certificate/Policy.lean`, `Certificate/Fidelity.lean` | The two proved checkers |
| `Roadmap.lean` | What is not proved, what was corrected, what the package should do |
| `Audit.lean` | `#print axioms` for every theorem of the library |
| `CheckCertificate.lean` | The `check_certificate` executable |

## Corrections to the plan, and consequences for the package

Both are in `Roadmap.lean`. The three that change the design:

* Backward induction is optimal for the *nested* value of any monotone aggregator; the algebra
  law and reward-additivity are what make the nested value equal the rule applied to the
  whole problem. "CVaR does not admit backward induction" means that backward induction
  computes nested CVaR, a different rule (`cvar_two_step_ne_one_step`).
* The Bayesian inverse of a composite is the composite of the inverses at *every* evidence
  value if evidence of probability zero is given the zero row; use that convention.
* In the fidelity bound the approximate first kernel and the exact second kernel must be
  stochastic; the read-off should check that approximate boxes are normalised.

## Scope

Exact finite-model results, not a verification of Julia's floating-point arrays. The Lean and
Julia definitions are separate hand-written texts; no theorem says that the Julia code
executes these definitions.
