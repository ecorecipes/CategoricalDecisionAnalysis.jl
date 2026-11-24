import CategoricalDecisionAnalysisProofs.Finite.Pullback
import DecisionAnalysisProofs.Finite.Fidelity
import DecisionAnalysisProofs.Finite.Posterior
import DecisionAnalysisProofs.Finite.Affine
import FiniteKernelsProofs.Finite.Kernel

/-!
# CategoricalDecisionAnalysisProofs.Finite.KernelFidelity

**T11: compositional fidelity.** Backs component 8 ("each box may carry a total-variation
error; errors add along composition and tensor; the decision-loss bound is read off the
diagram") of `CategoricalDecisionAnalysis.jl`, and the fidelity certificate of the plan (per-box
errors and the diagram; the bound is recomputed by these theorems).

## Conventions

* The distance between two kernels is the **largest total variation between corresponding
  rows**: `kernelDistance f f' = max_x totalVariation (f x) (f' x)`, with the core's
  `totalVariation` (half the ℓ¹ distance). Most statements are in the form
  `∀ x, totalVariation (f x) (f' x) ≤ ε`, which needs no nonempty input type and is what a
  per-box error bound asserts.
* `garble f g` (`f` first) and `push p f` are the core's; `tensorKernel f g` is the parallel
  product `(f ⊗ g)((x₁, x₂), (y₁, y₂)) = f x₁ y₁ · g x₂ y₂` (the sibling `Kernel.tensor` at
  `K = ℝ`, `tensorKernel_eq_tensor`), and `tensorVec p q` the product belief.
* **Which kernels must be stochastic.** In a composite `f ; g` against `f' ; g'` the bound
  uses that the *exact second* kernel `g` and the *approximate first* kernel `f'` are
  stochastic; nothing is asked of `f` and `g'` beyond the error bounds. In a tensor the same
  holds with `g` and `f'`. In a chain every kernel is assumed stochastic.
* The payoff range `B` is the core's row range, `∀ a θ θ', u a θ - u a θ' ≤ B`, together
  with `0 ≤ B`.

## Results

* **`totalVariation_push_le`**: the one inequality behind the others,
  `TV(p ; g, p' ; g') ≤ TV(p, p') + ε · Σ p'`.
* **T11**, **`totalVariation_garble_le`**, **`kernelDistance_garble_le`**: sub-additivity
  under sequential composition.
* **T11**, **`totalVariation_tensorVec_le`**, **`totalVariation_tensorKernel_le`**,
  **`kernelDistance_tensorKernel_le`**: sub-additivity under the parallel product.
* **`totalVariation_chain_le`**: along a chain of `n` boxes the errors add.
* **`decision_loss_comp_le`**, **`decision_loss_chain_le`**, **`decision_loss_tensor_le`**:
  an action that is Bayes for the approximate model loses at most `2 · B · Σ ε_i` under the
  exact one, over a two-box pipeline, a chain and a tensor of beliefs.

Not claimed: tightness of the additive bound; any divergence other than total variation
(Kullback-Leibler does not compose additively and is not offered); chains of boxes with
different types (compose `totalVariation_garble_le` box by box); the read-off for an arbitrary
wiring diagram, which is a recursion on these two cases in Julia and is not modelled here.
-/

set_option autoImplicit false
-- One ordered-field context is declared per file; not every theorem uses every instance.
set_option linter.unusedSectionVars false

namespace CategoricalDecisionAnalysisProofs

open DecisionAnalysisProofs Finset

variable {A X Y Z X₁ X₂ Y₁ Y₂ : Type} [Fintype A] [Nonempty A] [Fintype X] [Fintype Y]
  [Fintype Z] [Fintype X₁] [Fintype X₂] [Fintype Y₁] [Fintype Y₂]
  {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-! ### The divergence -/

/-- `kernel_distance(f, f′)`: the largest total variation between corresponding rows. -/
def kernelDistance [Nonempty X] (f f' : X → Y → K) : K :=
  maxOver fun x => totalVariation (f x) (f' x)

/-- The parallel product of two kernels (`tensor_kernel`). -/
def tensorKernel (f : X₁ → Y₁ → K) (g : X₂ → Y₂ → K) : X₁ × X₂ → Y₁ × Y₂ → K :=
  fun x y => f x.1 y.1 * g x.2 y.2

/-- The product of two beliefs. -/
def tensorVec (p : X → K) (q : Y → K) : X × Y → K := fun t => p t.1 * q t.2

/-- At `K = ℝ` the parallel product is the sibling project's `Kernel.tensor`. -/
theorem tensorKernel_eq_tensor (f : FiniteKernelsProofs.Finite.Kernel X₁ Y₁)
    (g : FiniteKernelsProofs.Finite.Kernel X₂ Y₂) :
    tensorKernel f g = FiniteKernelsProofs.Finite.Kernel.tensor f g := rfl

theorem totalVariation_le_kernelDistance [Nonempty X] (f f' : X → Y → K) (x : X) :
    totalVariation (f x) (f' x) ≤ kernelDistance f f' :=
  le_maxOver (fun x => totalVariation (f x) (f' x)) x

theorem kernelDistance_le_iff [Nonempty X] (f f' : X → Y → K) (ε : K) :
    kernelDistance f f' ≤ ε ↔ ∀ x, totalVariation (f x) (f' x) ≤ ε :=
  ⟨fun h x => (totalVariation_le_kernelDistance f f' x).trans h, fun h => maxOver_le h⟩

theorem kernelDistance_nonneg [Nonempty X] (f f' : X → Y → K) : 0 ≤ kernelDistance f f' :=
  (totalVariation_nonneg _ _).trans
    (totalVariation_le_kernelDistance f f' (Classical.arbitrary X))

/-- The kernel distance is zero exactly for equal kernels. -/
theorem kernelDistance_eq_zero_iff [Nonempty X] (f f' : X → Y → K) :
    kernelDistance f f' = 0 ↔ f = f' := by
  constructor
  · intro h
    funext x
    exact (totalVariation_eq_zero_iff _ _).mp
      (le_antisymm (h ▸ totalVariation_le_kernelDistance f f' x) (totalVariation_nonneg _ _))
  · rintro rfl
    exact le_antisymm (maxOver_le fun x => (totalVariation_self _).le) (kernelDistance_nonneg _ _)

/-! ### Sequential composition -/

/-- Pushing two weightings through two kernels: the total variation of the images is at most
that of the weightings plus the row error of the kernels, scaled by the mass of the second
weighting. `g` must be stochastic and `p'` nonnegative. -/
theorem totalVariation_push_le {p p' : X → K} {g g' : X → Y → K} (hg : StochasticKernel g)
    (hp' : NonnegPrior p') {ε : K} (hε : ∀ x, totalVariation (g x) (g' x) ≤ ε) :
    totalVariation (push p g) (push p' g') ≤ totalVariation p p' + ε * ∑ x, p' x := by
  have h1 : ∀ y, |push p g y - push p' g' y| ≤
      ∑ x, (|p x - p' x| * g x y + p' x * |g x y - g' x y|) := by
    intro y
    have hsplit : push p g y - push p' g' y =
        ∑ x, ((p x - p' x) * g x y + p' x * (g x y - g' x y)) := by
      simp only [push, signalProbability, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [hsplit]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg (hg.1 x y), abs_of_nonneg (hp' x)]
  have h2 : ∑ y, ∑ x, (|p x - p' x| * g x y + p' x * |g x y - g' x y|) =
      ∑ x, |p x - p' x| + ∑ x, p' x * ∑ y, |g x y - g' x y| := by
    rw [Finset.sum_comm, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hg.2 x, mul_one]
  have h3 : ∑ x, p' x * ∑ y, |g x y - g' x y| ≤ ∑ x, p' x * (2 * ε) :=
    Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (by
      have h := hε x
      unfold totalVariation at h
      linarith) (hp' x)
  have h4 := Finset.sum_le_sum fun y (_ : y ∈ (Finset.univ : Finset Y)) => h1 y
  rw [h2] at h4
  rw [← Finset.sum_mul] at h3
  unfold totalVariation
  linarith

/-- **T11**, sequential composition, row by row: errors add. The exact second kernel `g` and
the approximate first kernel `f'` are stochastic. -/
theorem totalVariation_garble_le {f f' : X → Y → K} {g g' : Y → Z → K}
    (hg : StochasticKernel g) (hf' : StochasticKernel f') {ε₁ ε₂ : K}
    (h₁ : ∀ x, totalVariation (f x) (f' x) ≤ ε₁) (h₂ : ∀ y, totalVariation (g y) (g' y) ≤ ε₂)
    (x : X) : totalVariation (garble f g x) (garble f' g' x) ≤ ε₁ + ε₂ := by
  have h := totalVariation_push_le (p := f x) (p' := f' x) hg (hf'.1 x) h₂
  rw [hf'.2 x, mul_one] at h
  exact h.trans (add_le_add_left (h₁ x) _)

/-- **T11**, sequential composition: the kernel distance is sub-additive. -/
theorem kernelDistance_garble_le [Nonempty X] [Nonempty Y] {f f' : X → Y → K}
    {g g' : Y → Z → K} (hg : StochasticKernel g) (hf' : StochasticKernel f') :
    kernelDistance (garble f g) (garble f' g') ≤ kernelDistance f f' + kernelDistance g g' :=
  maxOver_le fun x => totalVariation_garble_le hg hf'
    (totalVariation_le_kernelDistance f f') (totalVariation_le_kernelDistance g g') x

/-! ### Parallel product -/

/-- **T11**, tensor of beliefs: errors add. The exact second factor `q` and the approximate
first factor `p'` are probability vectors. -/
theorem totalVariation_tensorVec_le {p p' : X → K} {q q' : Y → K} (hq : NonnegPrior q)
    (hq1 : NormalisedPrior q) (hp' : NonnegPrior p') (hp'1 : NormalisedPrior p') :
    totalVariation (tensorVec p q) (tensorVec p' q') ≤ totalVariation p p' + totalVariation q q' := by
  have h1 : ∀ t : X × Y, |tensorVec p q t - tensorVec p' q' t| ≤
      |p t.1 - p' t.1| * q t.2 + p' t.1 * |q t.2 - q' t.2| := by
    intro t
    have hsplit : tensorVec p q t - tensorVec p' q' t =
        (p t.1 - p' t.1) * q t.2 + p' t.1 * (q t.2 - q' t.2) := by
      unfold tensorVec
      ring
    rw [hsplit]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg (hq t.2), abs_of_nonneg (hp' t.1)]
  have h2 : ∑ t : X × Y, (|p t.1 - p' t.1| * q t.2 + p' t.1 * |q t.2 - q' t.2|) =
      ∑ x, |p x - p' x| + ∑ y, |q y - q' y| := by
    rw [Fintype.sum_prod_type, Finset.sum_congr rfl fun x _ => Finset.sum_add_distrib]
    simp only [← Finset.mul_sum]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
    unfold NormalisedPrior at hq1 hp'1
    rw [hq1, hp'1, mul_one, one_mul]
  have h3 := Finset.sum_le_sum fun t (_ : t ∈ (Finset.univ : Finset (X × Y))) => h1 t
  rw [h2] at h3
  unfold totalVariation
  linarith

/-- **T11**, tensor of kernels, row by row: errors add. The exact second kernel `g` and the
approximate first kernel `f'` are stochastic. -/
theorem totalVariation_tensorKernel_le {f f' : X₁ → Y₁ → K} {g g' : X₂ → Y₂ → K}
    (hg : StochasticKernel g) (hf' : StochasticKernel f') {ε₁ ε₂ : K}
    (h₁ : ∀ x, totalVariation (f x) (f' x) ≤ ε₁) (h₂ : ∀ x, totalVariation (g x) (g' x) ≤ ε₂)
    (x : X₁ × X₂) :
    totalVariation (tensorKernel f g x) (tensorKernel f' g' x) ≤ ε₁ + ε₂ :=
  (totalVariation_tensorVec_le (p := f x.1) (p' := f' x.1) (q := g x.2) (q' := g' x.2)
    (hg.1 x.2) (hg.2 x.2) (hf'.1 x.1) (hf'.2 x.1)).trans (add_le_add (h₁ x.1) (h₂ x.2))

/-- **T11**, tensor: the kernel distance is sub-additive. -/
theorem kernelDistance_tensorKernel_le [Nonempty X₁] [Nonempty X₂] {f f' : X₁ → Y₁ → K}
    {g g' : X₂ → Y₂ → K} (hg : StochasticKernel g) (hf' : StochasticKernel f') :
    kernelDistance (tensorKernel f g) (tensorKernel f' g') ≤
      kernelDistance f f' + kernelDistance g g' :=
  maxOver_le fun x => totalVariation_tensorKernel_le hg hf'
    (totalVariation_le_kernelDistance f f') (totalVariation_le_kernelDistance g g') x

/-! ### Chains -/

section Chain

variable [DecidableEq X]

/-- The composite of a list of kernels on one type, first kernel first. -/
def chain : List (X → X → K) → X → X → K
  | [] => deterministic id
  | f :: fs => garble f (chain fs)

/-- A chain of stochastic kernels is stochastic. -/
theorem stochasticKernel_chain (fs : List (X → X → K)) (h : ∀ f ∈ fs, StochasticKernel f) :
    StochasticKernel (chain fs) := by
  induction fs with
  | nil => exact stochasticKernel_deterministic id
  | cons f fs ih =>
    exact (h f List.mem_cons_self).garble (ih fun g hg => h g (List.mem_cons_of_mem f hg))

/-- **T11** along a chain. Each box is a triple (exact kernel, approximate kernel, error
bound); the composite of the exact kernels is within the **sum** of the bounds of the
composite of the approximate ones, in every row. -/
theorem totalVariation_chain_le (boxes : List ((X → X → K) × (X → X → K) × K))
    (h : ∀ b ∈ boxes, StochasticKernel b.1 ∧ StochasticKernel b.2.1 ∧
      ∀ x, totalVariation (b.1 x) (b.2.1 x) ≤ b.2.2) (x : X) :
    totalVariation (chain (boxes.map fun b => b.1) x) (chain (boxes.map fun b => b.2.1) x) ≤
      (boxes.map fun b => b.2.2).sum := by
  induction boxes generalizing x with
  | nil => simp [chain, totalVariation_self]
  | cons b bs ih =>
    have hb := h b List.mem_cons_self
    have hbs : ∀ c ∈ bs, StochasticKernel c.1 ∧ StochasticKernel c.2.1 ∧
        ∀ x, totalVariation (c.1 x) (c.2.1 x) ≤ c.2.2 := fun c hc =>
      h c (List.mem_cons_of_mem b hc)
    have hg : StochasticKernel (chain (bs.map fun b => b.1)) :=
      stochasticKernel_chain _ fun f hf => by
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hf
        exact (hbs c hc).1
    simpa [chain] using totalVariation_garble_le hg hb.2.1 hb.2.2 (ih hbs) x

end Chain

/-! ### The decision-loss bound read off a diagram -/

/-- **T10** with a bound on the total variation in place of its value. -/
theorem decision_loss_le_of_totalVariation_le {u : A → X → K} {p q : X → K} {a : A}
    (h : IsBayes u q a) (hpq : ∑ x, p x = ∑ x, q x) {B ε : K} (hB0 : 0 ≤ B)
    (hB : ∀ a x x', u a x - u a x' ≤ B) (hε : totalVariation p q ≤ ε) :
    actNowValue u p - expectedUtility u p a ≤ 2 * B * ε :=
  (h.decision_loss_le hpq hB).trans
    (mul_le_mul_of_nonneg_left hε (mul_nonneg zero_le_two hB0))

/-- **T11**, the loss bound over a two-box pipeline `prior ; f ; g`. An action that is Bayes
for the approximate pipeline (`p₀'`, `f'`, `g'`) falls short of the best under the exact one
by at most `2 · B · (ε₀ + ε₁ + ε₂)`, with `ε₀` the error of the prior. -/
theorem decision_loss_comp_le {u : A → Z → K} {p₀ p₀' : X → K} {f f' : X → Y → K}
    {g g' : Y → Z → K} {a : A} (hp₀1 : NormalisedPrior p₀)
    (hp₀' : NonnegPrior p₀') (hp₀'1 : NormalisedPrior p₀')
    (hf : StochasticKernel f) (hf' : StochasticKernel f') (hg : StochasticKernel g)
    (hg' : NormalisedKernel g') {B ε₀ ε₁ ε₂ : K} (hB0 : 0 ≤ B)
    (hB : ∀ a z z', u a z - u a z' ≤ B) (h₀ : totalVariation p₀ p₀' ≤ ε₀)
    (h₁ : ∀ x, totalVariation (f x) (f' x) ≤ ε₁) (h₂ : ∀ y, totalVariation (g y) (g' y) ≤ ε₂)
    (h : IsBayes u (push p₀' (garble f' g')) a) :
    actNowValue u (push p₀ (garble f g)) - expectedUtility u (push p₀ (garble f g)) a ≤
      2 * B * (ε₀ + ε₁ + ε₂) := by
  have hmass : ∑ z, push p₀ (garble f g) z = ∑ z, push p₀' (garble f' g') z := by
    rw [sum_signalProbability p₀ (hf.2.garble hg.2),
      sum_signalProbability p₀' (hf'.2.garble hg')]
    exact hp₀1.trans hp₀'1.symm
  have htv := totalVariation_push_le (p := p₀) (p' := p₀') (hf.garble hg) hp₀'
    (totalVariation_garble_le hg hf' h₁ h₂)
  unfold NormalisedPrior at hp₀'1
  rw [hp₀'1, mul_one] at htv
  exact decision_loss_le_of_totalVariation_le h hmass hB0 hB (by linarith)

/-- **T11**, the loss bound along a chain of boxes on one type: at most
`2 · B · (ε₀ + Σ ε_i)`. -/
theorem decision_loss_chain_le [DecidableEq X] {u : A → X → K} {p₀ p₀' : X → K}
    (boxes : List ((X → X → K) × (X → X → K) × K)) {a : A} (hp₀1 : NormalisedPrior p₀)
    (hp₀' : NonnegPrior p₀') (hp₀'1 : NormalisedPrior p₀')
    (hboxes : ∀ b ∈ boxes, StochasticKernel b.1 ∧ StochasticKernel b.2.1 ∧
      ∀ x, totalVariation (b.1 x) (b.2.1 x) ≤ b.2.2)
    {B ε₀ : K} (hB0 : 0 ≤ B) (hB : ∀ a x x', u a x - u a x' ≤ B)
    (h₀ : totalVariation p₀ p₀' ≤ ε₀)
    (h : IsBayes u (push p₀' (chain (boxes.map fun b => b.2.1))) a) :
    actNowValue u (push p₀ (chain (boxes.map fun b => b.1))) -
        expectedUtility u (push p₀ (chain (boxes.map fun b => b.1))) a ≤
      2 * B * (ε₀ + (boxes.map fun b => b.2.2).sum) := by
  have hc : StochasticKernel (chain (boxes.map fun b => b.1)) :=
    stochasticKernel_chain _ fun f hf => by
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hf
      exact (hboxes c hc).1
  have hc' : StochasticKernel (chain (boxes.map fun b => b.2.1)) :=
    stochasticKernel_chain _ fun f hf => by
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hf
      exact (hboxes c hc).2.1
  have hmass : ∑ x, push p₀ (chain (boxes.map fun b => b.1)) x =
      ∑ x, push p₀' (chain (boxes.map fun b => b.2.1)) x := by
    rw [sum_signalProbability p₀ hc.2, sum_signalProbability p₀' hc'.2]
    exact hp₀1.trans hp₀'1.symm
  have htv := totalVariation_push_le (p := p₀) (p' := p₀') hc hp₀'
    (totalVariation_chain_le boxes hboxes)
  unfold NormalisedPrior at hp₀'1
  rw [hp₀'1, mul_one] at htv
  exact decision_loss_le_of_totalVariation_le h hmass hB0 hB (by linarith)

/-- **T11**, the loss bound over a tensor of two beliefs: an action that is Bayes for
`p' ⊗ q'` falls short of the best under `p ⊗ q` by at most `2 · B · (ε₁ + ε₂)`. -/
theorem decision_loss_tensor_le {u : A → X × Y → K} {p p' : X → K} {q q' : Y → K} {a : A}
    (hp1 : NormalisedPrior p) (hp' : NonnegPrior p') (hp'1 : NormalisedPrior p')
    (hq : NonnegPrior q) (hq1 : NormalisedPrior q) (hq'1 : NormalisedPrior q')
    {B ε₁ ε₂ : K} (hB0 : 0 ≤ B) (hB : ∀ a t t', u a t - u a t' ≤ B)
    (h₁ : totalVariation p p' ≤ ε₁) (h₂ : totalVariation q q' ≤ ε₂)
    (h : IsBayes u (tensorVec p' q') a) :
    actNowValue u (tensorVec p q) - expectedUtility u (tensorVec p q) a ≤
      2 * B * (ε₁ + ε₂) := by
  have hsum : ∀ (r : X → K) (s : Y → K), ∑ t, tensorVec r s t = (∑ x, r x) * ∑ y, s y := by
    intro r s
    rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
    rfl
  have hmass : ∑ t, tensorVec p q t = ∑ t, tensorVec p' q' t := by
    unfold NormalisedPrior at hp1 hp'1 hq1 hq'1
    rw [hsum, hsum, hp1, hp'1, hq1, hq'1]
  have htv := totalVariation_tensorVec_le (p := p) (p' := p') (q := q) (q' := q') hq hq1 hp' hp'1
  exact decision_loss_le_of_totalVariation_le h hmass hB0 hB (by linarith)

end CategoricalDecisionAnalysisProofs
