import CategoricalDecisionAnalysisProofs.Finite.Pullback
import DecisionAnalysisProofs.Finite.Credal
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum

/-!
# CategoricalDecisionAnalysisProofs.Finite.CredalKernel

**C5: lower expectations and credal kernels.** Backs the instance `C` (finitely generated
credal sets, algebra "lower expectation") of component 3 of `CategoricalDecisionAnalysis.jl`,
and three decisions the plan takes about it: lower expectation is computed over the
**generators** only; credal kernels are composed in sequence with a documented looseness; and
no tensor of credal kernels is offered.

## Conventions

* A finitely generated credal set is a family of generators `P : I → Θ → K`, as in the core
  (`lowerExpectedUtility`, `mixture`). `lowerExpectation P x = min_i Σ_θ P i θ · x θ` is the
  lower expectation of the gamble `x`.
* A credal kernel is `F : X → I → Y → K`: at each input `x`, generators `F x i`. Its lower
  pullback is `lowerPullback F u x = lowerExpectation (F x) u`.
* `credalComp F G` is the Kleisli composite: a generator of the composite at `x` is a choice
  of generator `i` of `F x` **and of a generator of `G y` for each intermediate `y`
  separately** (a selector `Y → J`). This is what makes it a composition, and what makes it
  loose: a model in which the *same* unknown kernel `G · j` acts at every `y` only allows
  constant selectors.
* `credalTensorLeft P Q` lets the generator of `Q` depend on the outcome of `P`;
  `credalTensorRight` the reverse. A tensor needs them to agree.

## Results

* **`lowerExpectation_le_mixture`**, **`exists_generator_eq_lowerExpectation`**: the lower
  expectation over the convex hull is the minimum over the generators (it is below the
  expectation under every mixture, and attained at a generator).
* **`lowerExpectation_superadditive`**, **`lowerExpectation_smul`**,
  **`lowerExpectation_concave`**, **`lowerExpectation_mono`**,
  **`lowerExpectation_add_const`**: concave, positively homogeneous, monotone (nonnegative
  generators) and constant-additive (normalised generators): a coherent lower prevision.
* **`lowerPullback_credalComp`**: the lower pullback is functorial for `credalComp`
  (nonnegative `F`), so sequential composition is well defined for backward evaluation.
* **`lowerPullback_credalComp_le`** (soundness): the composite's lower value is below the
  value of every composite of fixed generators `F · i ; G · j`.
* **`credal_composition_loose`**: an instance where every fixed composite has value `1/2` and
  the credal composite has lower value `0`.
* **`credal_tensor_not_commutative`**: an instance where the two candidate tensors have lower
  expectations `0` and `1/2`; the credal construction has no tensor compatible with both
  orders of evaluation.

Not claimed: the credal monad or its laws (S4); upper expectations (dual); that the looseness
is bounded; graded credal kernels, which remove it.
-/

set_option autoImplicit false
-- One ordered-field context is declared per file; not every theorem uses every instance.
set_option linter.unusedSectionVars false

namespace CategoricalDecisionAnalysisProofs

open DecisionAnalysisProofs Finset

variable {A Θ I J X Y Z : Type} [Fintype A] [Fintype Θ] [Fintype I] [Nonempty I] [Fintype J]
  [Nonempty J] [Fintype X] [Fintype Y] [Fintype Z]
  {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-! ### Lower expectation over generators -/

/-- The lower expectation of the gamble `x` over the generators `P`. -/
def lowerExpectation (P : I → Θ → K) (x : Θ → K) : K := minOver fun i => ∑ θ, P i θ * x θ

/-- The core's lower expected utility of an action is the lower expectation of its payoff
row. -/
theorem lowerExpectedUtility_eq_lowerExpectation (u : A → Θ → K) (P : I → Θ → K) (a : A) :
    lowerExpectedUtility u P a = lowerExpectation P (u a) := rfl

/-- A nonnegative rescaling commutes with the minimum. -/
theorem minOver_mul_left (f : I → K) {s : K} (hs : 0 ≤ s) :
    minOver (fun i => s * f i) = s * minOver f := by
  obtain ⟨i, hi⟩ := exists_eq_minOver f
  exact minOver_eq_of i (by rw [hi]) fun j => mul_le_mul_of_nonneg_left (hi ▸ minOver_le f j) hs

/-- **C5.** The lower expectation is below the expectation under every prior in the convex
hull of the generators. -/
theorem lowerExpectation_le_mixture (P : I → Θ → K) (x : Θ → K) {w : I → K}
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) :
    lowerExpectation P x ≤ ∑ θ, mixture w P θ * x θ := by
  have hmix : ∑ θ, mixture w P θ * x θ = ∑ i, w i * ∑ θ, P i θ * x θ := by
    simp only [mixture, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun θ _ => by ring
  rw [hmix]
  calc lowerExpectation P x = ∑ i, w i * lowerExpectation P x := by
        rw [← Finset.sum_mul, hw1, one_mul]
    _ ≤ ∑ i, w i * ∑ θ, P i θ * x θ := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (minOver_le (fun i => ∑ θ, P i θ * x θ) i) (hw i)

/-- **C5.** The lower expectation is attained at a generator: with
`lowerExpectation_le_mixture`, the minimum over the hull is the minimum over the generators. -/
theorem exists_generator_eq_lowerExpectation (P : I → Θ → K) (x : Θ → K) :
    ∃ i, lowerExpectation P x = ∑ θ, P i θ * x θ :=
  exists_eq_minOver fun i => ∑ θ, P i θ * x θ

/-- **C5.** Superadditivity. -/
theorem lowerExpectation_superadditive (P : I → Θ → K) (x y : Θ → K) :
    lowerExpectation P x + lowerExpectation P y ≤ lowerExpectation P fun θ => x θ + y θ :=
  le_minOver fun i => by
    have hx := minOver_le (fun i => ∑ θ, P i θ * x θ) i
    have hy := minOver_le (fun i => ∑ θ, P i θ * y θ) i
    simp only [mul_add, Finset.sum_add_distrib]
    exact add_le_add hx hy

/-- **C5.** Positive homogeneity. -/
theorem lowerExpectation_smul (P : I → Θ → K) (x : Θ → K) {s : K} (hs : 0 ≤ s) :
    lowerExpectation P (fun θ => s * x θ) = s * lowerExpectation P x := by
  unfold lowerExpectation
  rw [← minOver_mul_left _ hs]
  refine congrArg minOver (funext fun i => ?_)
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun θ _ => by ring

/-- **C5.** Concavity: the lower expectation of a mixture of gambles is at least the mixture
of the lower expectations (the algebra map is lax for convex combination). -/
theorem lowerExpectation_concave (P : I → Θ → K) (x y : Θ → K) {t : K} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    (1 - t) * lowerExpectation P x + t * lowerExpectation P y ≤
      lowerExpectation P fun θ => (1 - t) * x θ + t * y θ := by
  rw [← lowerExpectation_smul P x (sub_nonneg.mpr ht1), ← lowerExpectation_smul P y ht0]
  exact lowerExpectation_superadditive P _ _

/-- **C5.** Monotonicity, for generators with nonnegative entries. -/
theorem lowerExpectation_mono {P : I → Θ → K} (hP : ∀ i θ, 0 ≤ P i θ) {x y : Θ → K}
    (h : ∀ θ, x θ ≤ y θ) : lowerExpectation P x ≤ lowerExpectation P y :=
  le_minOver fun i => (minOver_le (fun i => ∑ θ, P i θ * x θ) i).trans
    (Finset.sum_le_sum fun θ _ => mul_le_mul_of_nonneg_left (h θ) (hP i θ))

/-- **C5.** Constants add, for normalised generators. -/
theorem lowerExpectation_add_const {P : I → Θ → K} (hP : ∀ i, ∑ θ, P i θ = 1) (x : Θ → K)
    (c : K) : lowerExpectation P (fun θ => x θ + c) = lowerExpectation P x + c := by
  obtain ⟨i, hi⟩ := exists_eq_minOver fun i => ∑ θ, P i θ * x θ
  have hrow : ∀ j, ∑ θ, P j θ * (x θ + c) = ∑ θ, P j θ * x θ + c := fun j => by
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hP j, one_mul]
  refine minOver_eq_of i ?_ fun j => ?_
  · rw [hrow, ← hi]
    rfl
  · rw [hrow]
    exact add_le_add_left (minOver_le (fun i => ∑ θ, P i θ * x θ) j) c

/-! ### Credal kernels in sequence -/

/-- The lower pullback of an effect along a credal kernel:
`(F* u)(x) = min_i Σ_y F x i y · u y`. -/
def lowerPullback (F : X → I → Y → K) (u : Y → K) : X → K := fun x => lowerExpectation (F x) u

/-- Sequential (Kleisli) composition of credal kernels: a generator at `x` is a generator of
`F x` and, for each intermediate `y`, a generator of `G y`. -/
def credalComp (F : X → I → Y → K) (G : Y → J → Z → K) : X → I × (Y → J) → Z → K :=
  fun x s z => ∑ y, F x s.1 y * G y (s.2 y) z

/-- **C5.** The lower pullback is functorial for sequential composition of credal kernels
with nonnegative entries: `(F ; G)* u = F* (G* u)`. -/
theorem lowerPullback_credalComp [DecidableEq Y] {F : X → I → Y → K}
    (hF : ∀ x i y, 0 ≤ F x i y) (G : Y → J → Z → K) (u : Z → K) :
    lowerPullback (credalComp F G) u = lowerPullback F (lowerPullback G u) := by
  funext x
  have hrow : ∀ s : I × (Y → J), ∑ z, credalComp F G x s z * u z =
      ∑ y, F x s.1 y * ∑ z, G y (s.2 y) z * u z := fun s => by
    simp only [credalComp, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => by ring
  apply le_antisymm
  · refine le_minOver fun i => ?_
    choose sel hsel using fun y => exists_eq_minOver fun j => ∑ z, G y j z * u z
    refine (minOver_le (fun s : I × (Y → J) => ∑ z, credalComp F G x s z * u z)
      (i, sel)).trans (le_of_eq ?_)
    rw [hrow]
    exact Finset.sum_congr rfl fun y _ => by
      rw [← hsel y]
      rfl
  · refine le_minOver fun s => ?_
    rw [hrow]
    exact (minOver_le (fun i => ∑ y, F x i y * lowerPullback G u y) s.1).trans
      (Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left
        (minOver_le (fun j => ∑ z, G y j z * u z) (s.2 y)) (hF x s.1 y))

/-- **C5**, soundness. The lower value of the credal composite is below the value of every
composite of fixed generators: it is a valid lower bound for the model in which one unknown
kernel `F · i` is followed by one unknown kernel `G · j`. -/
theorem lowerPullback_credalComp_le [DecidableEq Y] (F : X → I → Y → K) (G : Y → J → Z → K)
    (u : Z → K) (i : I) (j : J) (x : X) :
    lowerPullback (credalComp F G) u x ≤
      pullbackD (garble (fun x => F x i) fun y => G y j) u x :=
  minOver_le (fun s : I × (Y → J) => ∑ z, credalComp F G x s z * u z) (i, fun _ => j)

/-! ### The looseness, and the failure of commutativity -/

/-- One generator: the fair coin on `Fin 2`. -/
def coinKernel : Unit → Unit → Fin 2 → ℚ := fun _ _ _ => 1/2

/-- Two generators at each `y`: keep `y` (`j = 0`) or flip it (`j = 1`). -/
def keepOrFlip : Fin 2 → Fin 2 → Fin 2 → ℚ := fun y j z => if z = y + j then 1 else 0

/-- The effect that pays `1` on the outcome `1`. -/
def payOne : Fin 2 → ℚ := fun z => if z = 1 then 1 else 0

/-- **C5**, looseness. A fair coin followed by "keep or flip": each fixed second kernel gives
a fair coin again and value `1/2`, but the credal composite, which may keep after one outcome
and flip after the other, has lower value `0`. -/
theorem credal_composition_loose :
    (∀ j, pullbackD (garble (fun x => coinKernel x ()) fun y => keepOrFlip y j) payOne () = 1/2) ∧
      lowerPullback (credalComp coinKernel keepOrFlip) payOne () = 0 := by
  constructor
  · intro j
    fin_cases j <;>
      simp [pullbackD, garble, coinKernel, keepOrFlip, payOne, Fin.sum_univ_two]
  · apply le_antisymm
    · refine (minOver_le (fun s : Unit × (Fin 2 → Fin 2) =>
        ∑ z, credalComp coinKernel keepOrFlip () s z * payOne z) ((), fun y => y)).trans
        (le_of_eq ?_)
      simp [credalComp, coinKernel, keepOrFlip, payOne, Fin.sum_univ_two]
    · have hnn : ∀ s : Unit × (Fin 2 → Fin 2),
          0 ≤ ∑ z, credalComp coinKernel keepOrFlip () s z * payOne z := by
        intro s
        unfold credalComp
        refine Finset.sum_nonneg fun z _ => mul_nonneg ?_ ?_
        · refine Finset.sum_nonneg fun y _ => mul_nonneg ?_ ?_
          · norm_num [coinKernel]
          · unfold keepOrFlip
            split_ifs <;> norm_num
        · unfold payOne
          split_ifs <;> norm_num
      exact le_minOver hnn

/-- The candidate tensor in which the generator of `Q` may depend on the outcome of `P`. -/
def credalTensorLeft (P : I → X → K) (Q : J → Y → K) : I × (X → J) → X × Y → K :=
  fun s t => P s.1 t.1 * Q (s.2 t.1) t.2

/-- The candidate tensor in which the generator of `P` may depend on the outcome of `Q`. -/
def credalTensorRight (P : I → X → K) (Q : J → Y → K) : J × (Y → I) → X × Y → K :=
  fun s t => P (s.2 t.2) t.1 * Q s.1 t.2

/-- One generator: the fair coin. -/
def coinSet : Unit → Fin 2 → ℚ := fun _ _ => 1/2

/-- Two generators: the point masses on `Fin 2`. -/
def pointSet : Fin 2 → Fin 2 → ℚ := fun j y => if y = j then 1 else 0

/-- The gamble that pays `1` when the two outcomes agree. -/
def agree : Fin 2 × Fin 2 → ℚ := fun t => if t.1 = t.2 then 1 else 0

/-- **C5**, no tensor. For the fair coin and the two point masses, the two orders of forming
a joint credal set give lower expectations `0` and `1/2` to the same gamble: the construction
is not commutative, so it has no tensor that both orders of evaluation respect. -/
theorem credal_tensor_not_commutative :
    lowerExpectation (credalTensorLeft coinSet pointSet) agree = 0 ∧
      lowerExpectation (credalTensorRight coinSet pointSet) agree = 1/2 := by
  constructor
  · apply le_antisymm
    · refine (minOver_le (fun s : Unit × (Fin 2 → Fin 2) =>
        ∑ t, credalTensorLeft coinSet pointSet s t * agree t) ((), fun x => x + 1)).trans
        (le_of_eq ?_)
      simp [credalTensorLeft, coinSet, pointSet, agree, Fintype.sum_prod_type, Fin.sum_univ_two]
    · have hnn : ∀ s : Unit × (Fin 2 → Fin 2),
          0 ≤ ∑ t, credalTensorLeft coinSet pointSet s t * agree t := by
        intro s
        unfold credalTensorLeft
        refine Finset.sum_nonneg fun t _ => mul_nonneg (mul_nonneg ?_ ?_) ?_
        · norm_num [coinSet]
        · unfold pointSet
          split_ifs <;> norm_num
        · unfold agree
          split_ifs <;> norm_num
      exact le_minOver hnn
  · have hrow : ∀ s : Fin 2 × (Fin 2 → Unit),
        ∑ t, credalTensorRight coinSet pointSet s t * agree t = 1/2 := by
      rintro ⟨j, r⟩
      fin_cases j <;>
        simp [credalTensorRight, coinSet, pointSet, agree, Fintype.sum_prod_type]
    exact minOver_eq_of ((0 : Fin 2), fun _ => ()) (hrow _) fun s => (hrow s).ge

end CategoricalDecisionAnalysisProofs
