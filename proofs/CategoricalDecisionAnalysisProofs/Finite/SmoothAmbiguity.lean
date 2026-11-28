import CategoricalDecisionAnalysisProofs.Finite.CredalKernel
import DecisionAnalysisProofs.Finite.CertaintyEquivalentVOI
import DecisionAnalysisProofs.Finite.StochasticDominance
import DecisionAnalysisProofs.Finite.ImplementationAndModel
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum

/-!
# CategoricalDecisionAnalysisProofs.Finite.SmoothAmbiguity

Smooth ambiguity structure maps (`SmoothAmbiguityMap` in `src/monads.jl`), generator pruning on
`CredalHull` (`prune_generators` in `src/monads.jl`), and stochastic dominance rule selection
(`rule_selection(::StochasticDominance)` in `src/selection.jl`).

## What each result backs or shapes

* **`smoothAmbiguityMap_bounds`**, **`smoothAmbiguityMap_mono`**,
  **`smoothAmbiguityMap_add_const`**, **`smoothAmbiguityMap_const`**,
  **`smoothAmbiguityMap_concave`**: for `η > 0`, `SmoothAmbiguityMap(η)` lies between
  `LowerExpectationAlgebra` and the second-order mixture expectation (and below
  `UpperExpectationAlgebra`), is monotone (justifying `backward_induction_class = :nested`),
  translation-equivariant, constant-preserving (satisfying the unit law `α(η_C x) = x`), and
  concave (ambiguity-averse).
* **`smoothAmbiguityMap_depends_on_generators`**: unlike `LowerExpectationAlgebra`, uniform
  `SmoothAmbiguityMap(η)` depends on the generator list, not just the convex hull — adding a
  redundant midpoint generator strictly changes the score.
* **`smoothAmbiguityMap_credalComp_ne_nested`**: `SmoothAmbiguityMap(η)` fails the credal-monad
  multiplication law (`α(μ_C M) ≠ α(C α M)`), strictly separating flat evaluation on
  `credalComp` from two-stage nested evaluation; backs `is_algebra(::SmoothAmbiguityMap) = false`
  and `admits_backward_induction(::SmoothAmbiguityMap) = false`.
* **`prune_redundant_lowerExpectation`**: removing a generator in the convex hull of the others
  preserves `lowerExpectation`, backing `prune_generators(::CredalHull)`.
* **`stochasticDominance_order2_subset_order1`**, **`stochasticDominance_order1_nonempty`**,
  **`stochasticDominance_order2_nonempty`**: backs `rule_selection(StochasticDominance(; order))`.

Not claimed: floating-point log-sum-exp rounding or tolerance handling in `SmoothAmbiguityMap`
and `select`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CategoricalDecisionAnalysisProofs

open DecisionAnalysisProofs Finset

/-! ### `SmoothAmbiguityMap` on finitely generated credal sets -/

section SmoothAmbiguityLaws

variable {Θ I : Type} [Fintype Θ] [Nonempty Θ] [Fintype I] [Nonempty I]

/-- For `η > 0`, `SmoothAmbiguityMap(η)` is sandwiched between `lowerExpectation` and the
second-order mixture expectation. -/
theorem smoothAmbiguityMap_bounds {η : ℝ} (hη : 0 < η) {μ : I → ℝ} (hμ : NonnegPrior μ)
    (hμ1 : NormalisedPrior μ) (P : I → Θ → ℝ) (x : Θ → ℝ) :
    lowerExpectation P x ≤ expSmoothAmbiguity η μ P x ∧
      expSmoothAmbiguity η μ P x ≤ ∑ θ, mixture μ P θ * x θ :=
  ⟨minOver_le_caraCE hη hμ hμ1 (fun i => ∑ θ, P i θ * x θ),
    expSmoothAmbiguity_le_mixture hη hμ hμ1 P x⟩

/-- `SmoothAmbiguityMap(η)` is monotone in the gamble `x` (`backward_induction_class = :nested`
rather than `:none`). -/
theorem smoothAmbiguityMap_mono {η : ℝ} (hη : 0 < η) {μ : I → ℝ} (hμ : NonnegPrior μ)
    (hμ1 : NormalisedPrior μ) {P : I → Θ → ℝ} (hP : ∀ i, NonnegPrior (P i))
    {x y : Θ → ℝ} (hxy : ∀ θ, x θ ≤ y θ) :
    expSmoothAmbiguity η μ P x ≤ expSmoothAmbiguity η μ P y :=
  expSmoothAmbiguity_mono hη hμ hμ1 hP hxy

/-- `SmoothAmbiguityMap(η)` commutes with adding a constant to every outcome. -/
theorem smoothAmbiguityMap_add_const {η : ℝ} (hη : η ≠ 0) {μ : I → ℝ} (hμ : NonnegPrior μ)
    (hμ1 : NormalisedPrior μ) {P : I → Θ → ℝ} (hP : ∀ i, NormalisedPrior (P i))
    (x : Θ → ℝ) (c : ℝ) :
    expSmoothAmbiguity η μ P (fun θ => x θ + c) = expSmoothAmbiguity η μ P x + c :=
  expSmoothAmbiguity_add_const hη hμ hμ1 hP x c

/-- `SmoothAmbiguityMap(η)` preserves constants (satisfies the monad unit law `α(η x) = x`). -/
theorem smoothAmbiguityMap_const {η : ℝ} (hη : η ≠ 0) {μ : I → ℝ} (hμ1 : NormalisedPrior μ)
    {P : I → Θ → ℝ} (hP : ∀ i, NormalisedPrior (P i)) (c : ℝ) :
    expSmoothAmbiguity η μ P (fun _ => c) = c :=
  expSmoothAmbiguity_const hη hμ1 hP c

/-- `SmoothAmbiguityMap(η)` is concave in the gamble (ambiguity aversion). -/
theorem smoothAmbiguityMap_concave {η : ℝ} (hη : 0 < η) {μ : I → ℝ} (hμ : NonnegPrior μ)
    (hμ1 : NormalisedPrior μ) (P : I → Θ → ℝ) (x y : Θ → ℝ)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) * expSmoothAmbiguity η μ P x + t * expSmoothAmbiguity η μ P y ≤
      expSmoothAmbiguity η μ P (fun θ => (1 - t) * x θ + t * y θ) :=
  expSmoothAmbiguity_concave hη hμ hμ1 P x y ht0 ht1

end SmoothAmbiguityLaws

/-! ### Non-invariance under redundant generators and failure of the algebra law -/

/-- Two-point credal generators `{δ_0, δ_1}` on `Fin 2`. -/
def twoPointGens : Fin 2 → Fin 2 → ℝ
  | 0, 0 => 1 | 0, 1 => 0
  | 1, 0 => 0 | 1, 1 => 1

/-- The same convex hull with the redundant midpoint `(δ_0 + δ_1) / 2` added as a third
generator. -/
noncomputable def threePointGens : Fin 3 → Fin 2 → ℝ
  | 0, 0 => 1   | 0, 1 => 0
  | 1, 0 => 0   | 1, 1 => 1
  | 2, 0 => 1/2 | 2, 1 => 1/2

/-- Gamble paying `0` on state `0` and `2` on state `1`. -/
def zeroTwoGamble : Fin 2 → ℝ
  | 0 => 0 | 1 => 2

/-- Adding a redundant interior generator leaves `lowerExpectation` unchanged but strictly raises
the uniform `SmoothAmbiguityMap(1)` score. -/
theorem smoothAmbiguityMap_depends_on_generators :
    lowerExpectation twoPointGens zeroTwoGamble = lowerExpectation threePointGens zeroTwoGamble ∧
      expSmoothAmbiguity 1 (fun _ : Fin 2 => (1 : ℝ) / 2) twoPointGens zeroTwoGamble <
        expSmoothAmbiguity 1 (fun _ : Fin 3 => (1 : ℝ) / 3) threePointGens zeroTwoGamble := by
  constructor
  · have h2 : lowerExpectation twoPointGens zeroTwoGamble = 0 := by
      unfold lowerExpectation
      rw [minOver_fin_two]
      norm_num [Fin.sum_univ_two, twoPointGens, zeroTwoGamble]
    have h3 : lowerExpectation threePointGens zeroTwoGamble = 0 := by
      unfold lowerExpectation
      rw [minOver_fin_three]
      norm_num [Fin.sum_univ_two, threePointGens, zeroTwoGamble]
    rw [h2, h3]
  · unfold expSmoothAmbiguity caraCE
    have hs2 : ∑ i : Fin 2, ((1 : ℝ) / 2) * Real.exp (-1 * ∑ θ : Fin 2, twoPointGens i θ * zeroTwoGamble θ) =
        (1 + Real.exp (-2)) / 2 := by
      simp [Fin.sum_univ_two, twoPointGens, zeroTwoGamble]
      ring
    have hs3 : ∑ i : Fin 3, ((1 : ℝ) / 3) * Real.exp (-1 * ∑ θ : Fin 2, threePointGens i θ * zeroTwoGamble θ) =
        (1 + Real.exp (-2) + Real.exp (-1)) / 3 := by
      simp [Fin.sum_univ_three, Fin.sum_univ_two, threePointGens, zeroTwoGamble]
      ring
    rw [hs2, hs3]
    have he1_lt : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    have he2 : Real.exp (-2) = Real.exp (-1) * Real.exp (-1) := by
      rw [← Real.exp_add]; norm_num
    have hpos3 : 0 < (1 + Real.exp (-2) + Real.exp (-1)) / 3 := by
      have := Real.exp_pos (-2)
      have := Real.exp_pos (-1)
      linarith
    have hlt : (1 + Real.exp (-2) + Real.exp (-1)) / 3 < (1 + Real.exp (-2)) / 2 := by
      have hsq : 0 < (1 - Real.exp (-1)) * (1 - Real.exp (-1)) :=
        mul_pos (by linarith) (by linarith)
      rw [he2]
      linarith
    have hlog := Real.log_lt_log hpos3 hlt
    norm_num
    linarith

/-- First-stage credal kernel: a single fair coin on `Fin 2`. -/
noncomputable def smoothStageOne : Unit → Unit → Fin 2 → ℝ := fun _ _ _ => 1 / 2

/-- Second-stage credal kernel: at `y = 0` always `δ_0`; at `y = 1`, `{δ_0, δ_1}`. -/
def smoothStageTwo : Fin 2 → Fin 2 → Fin 2 → ℝ
  | 0, _, 0 => 1 | 0, _, 1 => 0
  | 1, 0, 0 => 1 | 1, 0, 1 => 0
  | 1, 1, 0 => 0 | 1, 1, 1 => 1

/-- **Failure of the credal-monad algebra law for `SmoothAmbiguityMap`**: for `η = 1` on the
two-stage problem `(smoothStageOne, smoothStageTwo)` with payoff `zeroTwoGamble`, two-stage
nested evaluation is strictly below flat evaluation on `credalComp`. Backs
`is_algebra(::SmoothAmbiguityMap) = false` and `admits_backward_induction = false`. -/
theorem smoothAmbiguityMap_credalComp_ne_nested :
    expSmoothAmbiguity 1 (fun _ : Unit => (1 : ℝ)) (smoothStageOne ())
        (fun y => expSmoothAmbiguity 1 (fun _ : Fin 2 => (1 : ℝ) / 2) (smoothStageTwo y)
          zeroTwoGamble) <
      expSmoothAmbiguity 1 (fun _ : Unit × (Fin 2 → Fin 2) => (1 : ℝ) / 4)
        (credalComp smoothStageOne smoothStageTwo ()) zeroTwoGamble := by
  have hy0 : expSmoothAmbiguity 1 (fun _ : Fin 2 => (1 : ℝ) / 2) (smoothStageTwo 0)
      zeroTwoGamble = 0 := by
    unfold expSmoothAmbiguity caraCE
    simp [Fin.sum_univ_two, smoothStageTwo, zeroTwoGamble]
  have hy1 : expSmoothAmbiguity 1 (fun _ : Fin 2 => (1 : ℝ) / 2) (smoothStageTwo 1)
      zeroTwoGamble = -Real.log ((1 + Real.exp (-2)) / 2) := by
    unfold expSmoothAmbiguity caraCE
    have hsum : ∑ i : Fin 2, ((1 : ℝ) / 2) *
        Real.exp (-1 * ∑ θ : Fin 2, smoothStageTwo 1 i θ * zeroTwoGamble θ) =
        (1 + Real.exp (-2)) / 2 := by
      simp [Fin.sum_univ_two, smoothStageTwo, zeroTwoGamble]
      ring
    rw [hsum]
    ring
  have hinner : (fun y => expSmoothAmbiguity 1 (fun _ : Fin 2 => (1 : ℝ) / 2) (smoothStageTwo y)
      zeroTwoGamble) = fun y => if y = 0 then 0 else -Real.log ((1 + Real.exp (-2)) / 2) :=
    funext fun y => by fin_cases y <;> [simpa using hy0; simpa using hy1]
  have hnested : expSmoothAmbiguity 1 (fun _ : Unit => (1 : ℝ)) (smoothStageOne ())
      (fun y => expSmoothAmbiguity 1 (fun _ : Fin 2 => (1 : ℝ) / 2) (smoothStageTwo y)
        zeroTwoGamble) = -(1 / 2) * Real.log ((1 + Real.exp (-2)) / 2) := by
    rw [hinner]
    unfold expSmoothAmbiguity caraCE
    simp [smoothStageOne, Fin.sum_univ_two]
  have hflat : expSmoothAmbiguity 1 (fun _ : Unit × (Fin 2 → Fin 2) => (1 : ℝ) / 4)
      (credalComp smoothStageOne smoothStageTwo ()) zeroTwoGamble =
      -Real.log ((1 + Real.exp (-1)) / 2) := by
    unfold expSmoothAmbiguity caraCE
    have hrow : ∀ s : Unit × (Fin 2 → Fin 2),
        ∑ z : Fin 2, credalComp smoothStageOne smoothStageTwo () s z * zeroTwoGamble z =
          if s.2 1 = 0 then 0 else 1 := by
      rintro ⟨⟨⟩, f⟩
      have h0 : f 0 = 0 ∨ f 0 = 1 := by generalize f 0 = a; fin_cases a <;> simp
      have h1 : f 1 = 0 ∨ f 1 = 1 := by generalize f 1 = b; fin_cases b <;> simp
      rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;>
        simp [credalComp, smoothStageOne, smoothStageTwo, zeroTwoGamble, Fin.sum_univ_two, h0, h1]
    have hsum : ∑ s : Unit × (Fin 2 → Fin 2), ((1 : ℝ) / 4) *
        Real.exp (-1 * ∑ z : Fin 2, credalComp smoothStageOne smoothStageTwo () s z *
          zeroTwoGamble z) = (1 + Real.exp (-1)) / 2 := by
      simp_rw [hrow]
      rw [Fintype.sum_prod_type]
      simp only [Finset.univ_unique, PUnit.default_eq_unit, Finset.sum_singleton]
      let e : (Fin 2 → Fin 2) ≃ Fin 2 × Fin 2 :=
        { toFun := fun f => (f 0, f 1)
          invFun := fun p i => if i = 0 then p.1 else p.2
          left_inv := fun f => funext fun i => by fin_cases i <;> rfl
          right_inv := fun ⟨_, _⟩ => rfl }
      rw [← Equiv.sum_comp e.symm]
      rw [Fintype.sum_prod_type]
      simp [e, Fin.sum_univ_two]
      ring
    rw [hsum]
    ring
  rw [hnested, hflat]
  have he1_lt : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have he2 : Real.exp (-2) = Real.exp (-1) * Real.exp (-1) := by
    rw [← Real.exp_add]; norm_num
  have hpos1 : 0 < (1 + Real.exp (-1)) / 2 := by linarith [Real.exp_pos (-1)]
  have hsq_lt : ((1 + Real.exp (-1)) / 2) * ((1 + Real.exp (-1)) / 2) <
      (1 + Real.exp (-2)) / 2 := by
    have hsq : 0 < (1 - Real.exp (-1)) * (1 - Real.exp (-1)) :=
      mul_pos (by linarith) (by linarith)
    rw [he2]
    linarith
  have hlog := Real.log_lt_log (mul_pos hpos1 hpos1) hsq_lt
  rw [Real.log_mul (ne_of_gt hpos1) (ne_of_gt hpos1)] at hlog
  linarith

/-! ### `prune_generators` and `rule_selection(::StochasticDominance)` -/

section CredalPruningAndDominance

variable {A Θ I : Type} [Fintype A] [Nonempty A] [Fintype Θ] [Fintype I] [DecidableEq I]
  {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Pruning a redundant generator of a `CredalHull` preserves `lowerExpectation`. Backs
`prune_generators` in `src/monads.jl`. -/
theorem prune_redundant_lowerExpectation [Nonempty I] {P : I → Θ → K} {k : I}
    (hk : IsRedundantGenerator P k) [Nonempty {i : I // i ≠ k}] (x : Θ → K) :
    lowerExpectation (fun j : {i : I // i ≠ k} => P j.1) x = lowerExpectation P x :=
  prune_redundant_lowerExpectedUtility hk (fun (_ : Unit) => x) ()

/-- `rule_selection(StochasticDominance(; order=2))` selects a subset of
`rule_selection(StochasticDominance(; order=1))`. -/
theorem stochasticDominance_order2_subset_order1 {u : A → Θ → K} {p : Θ → K}
    (hp1 : NormalisedPrior p) {a : A} (h : IsSSDUndominated u p a) :
    IsFSDUndominated u p a :=
  h.isFSDUndominated hp1

/-- `rule_selection(StochasticDominance(; order=1))` is always nonempty on finite action sets. -/
theorem stochasticDominance_order1_nonempty (u : A → Θ → K) (p : Θ → K) :
    ∃ a, IsFSDUndominated u p a :=
  exists_isFSDUndominated u p

/-- `rule_selection(StochasticDominance(; order=2))` is always nonempty on finite action sets. -/
theorem stochasticDominance_order2_nonempty (u : A → Θ → K) (p : Θ → K) :
    ∃ a, IsSSDUndominated u p a :=
  exists_isSSDUndominated u p

end CredalPruningAndDominance

end CategoricalDecisionAnalysisProofs
