import CategoricalDecisionAnalysisProofs.Finite.Pullback
import DecisionAnalysisProofs.Finite.ValueOfInformation
import DecisionAnalysisProofs.Finite.Posterior
import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic.FieldSimp

/-!
# CategoricalDecisionAnalysisProofs.Finite.Interchange

**C4 and C4b: expectation, affine maps, and the value of information as an interchange gap.**
Backs two things in `CategoricalDecisionAnalysis.jl`:

* the rule that decides when a transformation of values may be moved through an expectation
  box of a pipeline (component 3, "a pipeline's belief type and aggregator must match or be
  connected by a morphism"): exactly the affine maps commute; a convex map moves through with
  `≤` (oplax) and a concave one with `≥` (lax), so the rewrite is labelled an equality or a
  one-sided bound accordingly;
* the VOI interpreter (component 6), which computes a value of information as "maximise then
  average" minus "average then maximise": `interchangeGap`. The theorems say this is the
  core's `evpi`, `evsi` and `evppi`, so the interpreter can be tested against the core
  entry by entry.

## Conventions

* `mix w x = Σ_i w i · x i` is the expectation of the values `x` under the weights `w`: the
  algebra of `D` on `K` (`distAlgebra`, `mix_eq_pullbackD`).
* Commutation with expectation is stated for two points,
  `φ((1 − t) x + t y) = (1 − t) φ x + t φ y` for `0 ≤ t ≤ 1` (`CommutesWithMix`), and derived
  for every finite expectation (`map_mix_of_affine`). `IsOplax` and `IsLax` are the same
  statement with `≤` and `≥`; they are Mathlib's `ConvexOn` and `ConcaveOn` on the whole
  line (`isOplax_iff_convexOn`, `isLax_iff_concaveOn`).
* `interchangeGap w W = Σ_i w i · max_a W i a − max_a Σ_i w i · W i a`, for weights `w` and a
  table `W` of objectives indexed by "what is learned" (`i`) and action (`a`).

## Results

* **C4**, **`commutesWithMix_iff_affine`**: the maps commuting with expectation are exactly
  `x ↦ s · x + b`; **`map_mix_of_affine`**: such a map commutes with every normalised finite
  expectation.
* **C4b**, **`maxOver_mix_le`** (the core's `maxOver_weighted_sum_le`, restated) and
  **`convexOn_maxOver`**: the maximum over actions is oplax, i.e. convex.
  **`interchangeGap_nonneg`**.
* **C4b**, **`evpi_eq_interchangeGap`**, **`evsi_eq_interchangeGap`**,
  **`evppi_eq_interchangeGap`**, **`evsi_eq_interchangeGap_posterior`**: each value of
  information of the core is an interchange gap; the last is the textbook form with the
  signal probabilities as weights and the posterior expected utilities as objectives.
* **`interchangeGap_affine`**: the gap scales with a nonnegative slope and ignores shifts
  that do not depend on the action.

Not claimed: the certainty equivalent as a transported algebra structure (C4, last clause; no
Julia function uses it yet); Jensen's inequality for a general convex map on a finite
expectation (Mathlib's `ConvexOn.map_sum_le` is the statement, reachable through
`isOplax_iff_convexOn`).
-/

set_option autoImplicit false
-- One ordered-field context is declared per file; not every theorem uses every instance.
set_option linter.unusedSectionVars false

namespace CategoricalDecisionAnalysisProofs

open DecisionAnalysisProofs Finset

variable {A Θ Z C I : Type} [Fintype A] [Nonempty A] [Fintype Θ] [Fintype Z] [Fintype C]
  [Fintype I] {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-! ### C4: expectation and the maps that commute with it -/

/-- The expectation of the values `x` under the weights `w`. -/
def mix (w x : I → K) : K := ∑ i, w i * x i

/-- `mix` is the algebra of `D` on `K`: the pullback of `x` along the weights. -/
theorem mix_eq_pullbackD (w x : I → K) : mix w x = pullbackD (fun _ : Unit => w) x () := rfl

/-- `φ` commutes with two-point expectations. -/
def CommutesWithMix (φ : K → K) : Prop :=
  ∀ t x y : K, 0 ≤ t → t ≤ 1 → φ ((1 - t) * x + t * y) = (1 - t) * φ x + t * φ y

/-- `φ` is oplax for expectation: the value of the average is at most the average value. -/
def IsOplax (φ : K → K) : Prop :=
  ∀ t x y : K, 0 ≤ t → t ≤ 1 → φ ((1 - t) * x + t * y) ≤ (1 - t) * φ x + t * φ y

/-- `φ` is lax for expectation: the value of the average is at least the average value. -/
def IsLax (φ : K → K) : Prop :=
  ∀ t x y : K, 0 ≤ t → t ≤ 1 → (1 - t) * φ x + t * φ y ≤ φ ((1 - t) * x + t * y)

/-- **C4.** The maps that commute with expectation are exactly the affine maps. -/
theorem commutesWithMix_iff_affine (φ : K → K) :
    CommutesWithMix φ ↔ ∃ s b : K, ∀ x, φ x = s * x + b := by
  constructor
  · intro h
    refine ⟨φ 1 - φ 0, φ 0, fun x => ?_⟩
    rcases lt_trichotomy x 0 with hx | hx | hx
    · -- `0` lies between `x` and `1`.
      have h1x : 0 < 1 - x := by linarith
      have key := h (-x / (1 - x)) x 1 (div_nonneg (by linarith) h1x.le)
        ((div_le_one h1x).mpr (by linarith))
      have harg : (1 - -x / (1 - x)) * x + -x / (1 - x) * 1 = 0 := by
        field_simp
        ring
      rw [harg] at key
      have hmul : (1 - x) * φ 0 = φ x - x * φ 1 := by
        rw [key]
        field_simp
        ring
      linarith
    · subst hx
      ring
    · rcases le_or_gt x 1 with hx1 | hx1
      · have key := h x 0 1 hx.le hx1
        have harg : (1 - x) * 0 + x * 1 = x := by ring
        rw [harg] at key
        rw [key]
        ring
      · -- `1` lies between `0` and `x`.
        have hx0 : 0 < x := hx
        have key := h (1 / x) 0 x (div_nonneg zero_le_one hx0.le)
          ((div_le_one hx0).mpr hx1.le)
        have harg : (1 - 1 / x) * 0 + 1 / x * x = 1 := by
          rw [mul_zero, zero_add, one_div, inv_mul_cancel₀ hx0.ne']
        rw [harg] at key
        have hmul : x * φ 1 = (x - 1) * φ 0 + φ x := by
          rw [key]
          field_simp
        linarith
  · rintro ⟨s, b, h⟩ t x y _ _
    rw [h, h, h]
    ring

/-- An affine map commutes with every finite expectation whose weights sum to one. -/
theorem map_mix_of_affine {φ : K → K} (hφ : ∃ s b : K, ∀ x, φ x = s * x + b) {w : I → K}
    (hw : ∑ i, w i = 1) (x : I → K) : φ (mix w x) = mix w fun i => φ (x i) := by
  obtain ⟨s, b, h⟩ := hφ
  unfold mix
  simp only [h, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hw, one_mul, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The oplax maps are Mathlib's convex functions on the line. -/
theorem isOplax_iff_convexOn (φ : K → K) : IsOplax φ ↔ ConvexOn K Set.univ φ := by
  constructor
  · intro h
    refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    have hb1 : b ≤ 1 := by linarith
    have ha' : a = 1 - b := by linarith
    simpa [ha', smul_eq_mul] using h b x y hb hb1
  · intro h t x y ht0 ht1
    have := h.2 (Set.mem_univ x) (Set.mem_univ y) (sub_nonneg.mpr ht1) ht0 (by ring)
    simpa [smul_eq_mul] using this

/-- The lax maps are Mathlib's concave functions on the line. -/
theorem isLax_iff_concaveOn (φ : K → K) : IsLax φ ↔ ConcaveOn K Set.univ φ := by
  constructor
  · intro h
    refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    have hb1 : b ≤ 1 := by linarith
    have ha' : a = 1 - b := by linarith
    simpa [ha', smul_eq_mul] using h b x y hb hb1
  · intro h t x y ht0 ht1
    have := h.2 (Set.mem_univ x) (Set.mem_univ y) (sub_nonneg.mpr ht1) ht0 (by ring)
    simpa [smul_eq_mul] using this

/-- A map is affine exactly when it is both lax and oplax. -/
theorem commutesWithMix_iff_isLax_and_isOplax (φ : K → K) :
    CommutesWithMix φ ↔ IsLax φ ∧ IsOplax φ :=
  ⟨fun h => ⟨fun t x y h0 h1 => (h t x y h0 h1).ge, fun t x y h0 h1 => (h t x y h0 h1).le⟩,
    fun h t x y h0 h1 => le_antisymm (h.2 t x y h0 h1) (h.1 t x y h0 h1)⟩

/-! ### C4b: the maximum over actions is oplax, and the gap is the value of information -/

/-- **C4b.** The maximum over actions is oplax for expectation: the best action against the
average objective is worth at most the average of the best values. -/
theorem maxOver_mix_le {w : I → K} (hw : ∀ i, 0 ≤ w i) (W : I → A → K) :
    maxOver (fun a => mix w fun i => W i a) ≤ mix w fun i => maxOver (W i) :=
  maxOver_weighted_sum_le w hw W

/-- **C4b.** The maximum over actions is a convex function of the payoff vector. -/
theorem convexOn_maxOver : ConvexOn K Set.univ (fun x : A → K => maxOver x) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb _ => ?_⟩
  refine maxOver_le fun i => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  exact add_le_add (mul_le_mul_of_nonneg_left (le_maxOver x i) ha)
    (mul_le_mul_of_nonneg_left (le_maxOver y i) hb)

/-- The interchange gap of `max` and expectation: maximise then average, minus average then
maximise. -/
def interchangeGap (w : I → K) (W : I → A → K) : K :=
  (∑ i, w i * maxOver (W i)) - maxOver fun a => ∑ i, w i * W i a

/-- **C4b.** The gap is nonnegative for nonnegative weights. -/
theorem interchangeGap_nonneg {w : I → K} (hw : ∀ i, 0 ≤ w i) (W : I → A → K) :
    0 ≤ interchangeGap w W :=
  sub_nonneg.mpr (maxOver_weighted_sum_le w hw W)

/-- The gap scales with a nonnegative slope and ignores shifts that do not depend on the
action. -/
theorem interchangeGap_affine (w : I → K) (W : I → A → K) {s : K} (hs : 0 ≤ s) (b : I → K) :
    interchangeGap w (fun i a => s * W i a + b i) = s * interchangeGap w W := by
  unfold interchangeGap
  have h1 : ∀ i, maxOver (fun a => s * W i a + b i) = s * maxOver (W i) + b i := fun i =>
    maxOver_mul_add (W i) hs (b i)
  have h2 : (fun a => ∑ i, w i * (s * W i a + b i)) =
      fun a => s * (∑ i, w i * W i a) + ∑ i, w i * b i := by
    funext a
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have h4 : ∑ i, w i * maxOver (fun a => s * W i a + b i) =
      s * (∑ i, w i * maxOver (W i)) + ∑ i, w i * b i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by
      rw [h1 i]
      ring
  rw [h2, maxOver_mul_add _ hs, h4]
  ring

/-- **C4b.** EVPI is the interchange gap with the prior as weights and the payoff columns as
objectives. -/
theorem evpi_eq_interchangeGap (u : A → Θ → K) (p : Θ → K) :
    evpi u p = interchangeGap p fun θ a => u a θ := rfl

/-- **C4b.** For a normalised experiment, EVSI is the interchange gap of the joint-form
objectives (one per signal, unit weights). -/
theorem evsi_eq_interchangeGap (u : A → Θ → K) (p : Θ → K) {e : Θ → Z → K}
    (he : NormalisedKernel e) :
    evsi u p e = interchangeGap (fun _ : Z => (1 : K)) (signalValue u p e) := by
  unfold evsi interchangeGap valueWithInformation actNowValue
  simp only [one_mul]
  rw [show (fun a => ∑ z, signalValue u p e z a) = expectedUtility u p from
    funext (sum_signalValue u p he)]

/-- **C4b.** EVPPI is the interchange gap of the cell objectives. -/
theorem evppi_eq_interchangeGap [DecidableEq C] (u : A → Θ → K) (p : Θ → K) (f : Θ → C) :
    evppi u p f =
      interchangeGap (fun _ : C => (1 : K)) (signalValue u p (deterministic f)) := by
  rw [evppi_eq_evsi]
  exact evsi_eq_interchangeGap u p (normalisedKernel_deterministic f)

/-- **C4b**, posterior form. EVSI is the interchange gap with the signal probabilities as
weights and the posterior expected utilities as objectives: `E_z[max_a E[u a | z]]` minus
`max_a E_z[E[u a | z]]`. -/
theorem evsi_eq_interchangeGap_posterior (u : A → Θ → K) {p : Θ → K} (hp : NonnegPrior p)
    {e : Θ → Z → K} (he : StochasticKernel e) :
    evsi u p e =
      interchangeGap (signalProbability p e) fun z a => expectedUtility u (posterior p e z) a := by
  have hrow : ∀ z a, signalProbability p e z * expectedUtility u (posterior p e z) a =
      signalValue u p e z a := fun z a => by
    by_cases hz : signalProbability p e z = 0
    · rw [hz, zero_mul, signalValue_eq_zero u hp he.1 hz]
    · exact (signalValue_eq_posterior u p e hz a).symm
  unfold evsi interchangeGap
  rw [valueWithInformation_eq_posterior_form u hp he.1]
  simp only [hrow]
  rw [show (fun a => ∑ z, signalValue u p e z a) = expectedUtility u p from
    funext (sum_signalValue u p he.2)]
  rfl

end CategoricalDecisionAnalysisProofs
