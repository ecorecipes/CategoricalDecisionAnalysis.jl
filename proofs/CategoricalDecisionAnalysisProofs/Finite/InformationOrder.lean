import DecisionAnalysisProofs.Finite.Deficiency
import DecisionAnalysisProofs.Finite.Alternative
import DecisionAnalysisProofs.Finite.ValueOfInformation
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.FieldSimp

/-!
# CategoricalDecisionAnalysisProofs.Finite.InformationOrder

**C8 and S1a: information preorders.** Backs component 5 ("experiments on Θ under garbling;
partitions of Θ under refinement; value of a fixed problem as a monotone map out of each") of
`CategoricalDecisionAnalysis.jl`, its property test "preorder monotonicity", the enrichment of
the preorder by deficiency ("value is Lipschitz, not only monotone"), and the two-sided
reading of a deficiency value.

## Conventions

* `Experiment Θ K` bundles an experiment on `Θ` with its own finite signal type, so that
  experiments with different signals can be compared. `e' ≤ e` means `e'` is a garbling of
  `e` (the core's `IsGarblingOf e'.kernel e.kernel`): **larger is more informative**.
* `Labelling Θ` bundles a labelling `Θ → Label` (a partition with named cells, as
  `evppi(problem, partition)` takes). `f' ≤ f` means `f'` factors through `f`
  (`Function.FactorsThrough`): `f` refines `f'`, so again larger is more informative.
* Both are preorders, not partial orders: equivalent experiments and relabelled partitions are
  different elements.
* In S1a payoffs lie in `[0, 1]`, so the payoff range is `B = 1` and the gap is `ε`. A table
  with range `B` is brought to this form by the core's `rescale`.

## Results

* **C8**, **`valueWithInformation_monotone`**, **`evsi_monotone`**: the value of a fixed
  problem is `Monotone` on the garbling preorder (T6 repackaged).
* **C8**, **`evppi_monotone`**, **`partialValue_monotone`**: EVPPI is `Monotone` on the
  refinement preorder (T4 repackaged); **`Labelling.toExperiment_monotone`**: revealing the
  label is a monotone map from labellings to experiments, and
  **`evppi_eq_evsi_toExperiment`** says the two value maps agree along it.
* **C8**, **`abs_valueWithInformation_sub_le`**: value is Lipschitz for the two-sided
  deficiency, `|value(e) − value(e')| ≤ B · δ` (T6a applied in both directions).
* **`totalVariation_eq_sum_pos`**: for vectors of equal mass the total variation is the mass
  by which the second exceeds the first where it does (the event form of total variation,
  for the optimal event).
* **S1a**, **`isDeficientWithin_of_forall_valueWithInformation_le`**: if for every payoff
  table with entries in `[0, 1]` (actions: the signals of `e'`) and every probability prior
  the value of `e'` exceeds that of `e` by at most `ε`, then `e` simulates `e'` to within
  deficiency `ε`. With T6a, **`isDeficientWithin_iff_forall_valueWithInformation_le`**: the
  uniform value gap characterises deficiency.

Not claimed: that the infimum of feasible `δ` is attained (S1a is stated for feasibility
`IsDeficientWithin e e' ε`, which is what the theorem delivers); antisymmetry up to
equivalence of experiments.
-/

set_option autoImplicit false
-- One ordered-field context is declared per file; not every theorem uses every instance.
set_option linter.unusedSectionVars false

namespace CategoricalDecisionAnalysisProofs

open DecisionAnalysisProofs Finset

variable {A Θ Z Z' : Type} [Fintype A] [Nonempty A] [Fintype Θ] [Fintype Z] [Fintype Z']
  {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-! ### The garbling preorder -/

/-- An experiment on `Θ` together with its finite signal type. -/
structure Experiment (Θ : Type) (K : Type) where
  /-- The signals. -/
  Signal : Type
  [fintype : Fintype Signal]
  /-- The likelihood `kernel θ z = P(z | θ)`. -/
  kernel : Θ → Signal → K

attribute [instance] Experiment.fintype

/-- The garbling preorder: `e' ≤ e` when `e'` is a garbling of `e`. -/
instance : Preorder (Experiment Θ K) where
  le e' e := IsGarblingOf e'.kernel e.kernel
  le_refl e := by
    classical
    exact IsGarblingOf.refl e.kernel
  le_trans _ _ _ h₁ h₂ := IsGarblingOf.trans h₁ h₂

theorem Experiment.le_iff (e' e : Experiment Θ K) :
    e' ≤ e ↔ IsGarblingOf e'.kernel e.kernel := Iff.rfl

/-- **C8.** The value of deciding after an experiment is monotone on the garbling preorder,
for every payoff table and prior. -/
theorem valueWithInformation_monotone (u : A → Θ → K) (p : Θ → K) :
    Monotone fun e : Experiment Θ K => valueWithInformation u p e.kernel :=
  fun _ _ h => IsGarblingOf.valueWithInformation_le h u p

/-- **C8.** EVSI is monotone on the garbling preorder. -/
theorem evsi_monotone (u : A → Θ → K) (p : Θ → K) :
    Monotone fun e : Experiment Θ K => evsi u p e.kernel :=
  fun _ _ h => IsGarblingOf.evsi_le h u p

/-! ### The refinement preorder -/

/-- A labelling of the states: a partition of `Θ` with named cells. -/
structure Labelling (Θ : Type) where
  /-- The names of the cells. -/
  Label : Type
  [fintype : Fintype Label]
  [decEq : DecidableEq Label]
  [nonempty : Nonempty Label]
  /-- The cell of each state. -/
  label : Θ → Label

attribute [instance] Labelling.fintype Labelling.decEq Labelling.nonempty

/-- The refinement preorder: `f' ≤ f` when `f'` is constant on the cells of `f`. -/
instance : Preorder (Labelling Θ) where
  le f' f := Function.FactorsThrough f'.label f.label
  le_refl _ := fun _ _ h => h
  le_trans _ _ _ h₁ h₂ := fun _ _ h => h₁ (h₂ h)

theorem Labelling.le_iff (f' f : Labelling Θ) :
    f' ≤ f ↔ Function.FactorsThrough f'.label f.label := Iff.rfl

/-- **C8.** EVPPI is monotone on the refinement preorder. -/
theorem evppi_monotone (u : A → Θ → K) (p : Θ → K) :
    Monotone fun f : Labelling Θ => evppi u p f.label :=
  fun _ _ h => evppi_mono_of_factorsThrough u p h

/-- **C8.** The value of deciding after the label is revealed is monotone on the refinement
preorder. -/
theorem partialValue_monotone (u : A → Θ → K) (p : Θ → K) :
    Monotone fun f : Labelling Θ => partialValue u p f.label := fun f' f h => by
  have := evppi_monotone u p h
  simp only [evppi] at this
  linarith

/-- Revealing the label, as an experiment. -/
def Labelling.toExperiment (f : Labelling Θ) : Experiment Θ K :=
  { Signal := f.Label, kernel := deterministic f.label }

/-- Refinement of labellings is garbling of the experiments that reveal them. -/
theorem Labelling.toExperiment_monotone :
    Monotone (Labelling.toExperiment : Labelling Θ → Experiment Θ K) := by
  intro f' f h
  obtain ⟨k, hk⟩ := (Function.factorsThrough_iff f'.label).mp h
  change IsGarblingOf (deterministic f'.label : Θ → f'.Label → K) (deterministic f.label)
  refine ⟨deterministic k, stochasticKernel_deterministic k, ?_⟩
  rw [hk, deterministic_comp]

/-- EVPPI of a labelling is EVSI of the experiment that reveals it: the two value maps agree
along `Labelling.toExperiment`. -/
theorem evppi_eq_evsi_toExperiment (u : A → Θ → K) (p : Θ → K) (f : Labelling Θ) :
    evppi u p f.label = evsi u p (f.toExperiment (K := K)).kernel :=
  evppi_eq_evsi u p f.label

/-! ### Lipschitz in deficiency -/

/-- **C8.** If each of two normalised experiments simulates the other to within deficiency
`δ`, their values differ by at most `B · δ`, with `B` the largest spread of payoffs within a
state. -/
theorem abs_valueWithInformation_sub_le {e : Θ → Z → K} {e' : Θ → Z' → K} {δ : K}
    (h : IsDeficientWithin e e' δ) (h' : IsDeficientWithin e' e δ) (he : NormalisedKernel e)
    (he' : NormalisedKernel e') (u : A → Θ → K) {p : Θ → K} (hp : NonnegPrior p)
    (hp1 : NormalisedPrior p) {B : K} (hB : ∀ θ a a', u a θ - u a' θ ≤ B) :
    |valueWithInformation u p e - valueWithInformation u p e'| ≤ B * δ := by
  have h1 := h.valueWithInformation_le he he' u hp hp1 hB
  have h2 := h'.valueWithInformation_le he' he u hp hp1 hB
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-! ### S1a: the converse -/

omit [Fintype A] [Nonempty A] [Fintype Z] [Fintype Z'] in
/-- For vectors of equal total mass, the total variation is the excess of the second over the
first, summed where it is positive. -/
theorem totalVariation_eq_sum_pos (a b : Θ → K) (h : ∑ i, a i = ∑ i, b i) :
    totalVariation a b = ∑ i, if a i < b i then b i - a i else 0 := by
  have habs : ∀ i, |a i - b i| =
      (if a i < b i then b i - a i else 0) + (if a i < b i then 0 else a i - b i) := by
    intro i
    split_ifs with hi
    · rw [abs_of_neg (by linarith)]
      ring
    · rw [abs_of_nonneg (by linarith [not_lt.mp hi])]
      ring
  have hdiff : ∀ i, b i - a i =
      (if a i < b i then b i - a i else 0) - (if a i < b i then 0 else a i - b i) := by
    intro i
    split_ifs <;> ring
  have hzero : ∑ i, (b i - a i) = 0 := by
    rw [Finset.sum_sub_distrib, h, sub_self]
  rw [Finset.sum_congr rfl fun i _ => hdiff i, Finset.sum_sub_distrib] at hzero
  unfold totalVariation
  rw [Finset.sum_congr rfl fun i _ => habs i, Finset.sum_add_distrib]
  linarith

/-- The indicator `1` or `0`. -/
def indicatorOf (b : Bool) : K := if b then 1 else 0

omit [Fintype A] [Nonempty A] in
/-- **S1a.** If, for every payoff table with entries in `[0, 1]` whose actions are the
signals of `e'` and for every probability prior, the value of `e'` exceeds the value of `e`
by at most `ε`, then `e` simulates `e'` to within deficiency `ε`. -/
theorem isDeficientWithin_of_forall_valueWithInformation_le [Nonempty Z'] {e : Θ → Z → K}
    {e' : Θ → Z' → K} (he : NormalisedKernel e) (he' : NormalisedKernel e') {ε : K}
    (h : ∀ (u : Z' → Θ → K) (p : Θ → K), (∀ a θ, 0 ≤ u a θ ∧ u a θ ≤ 1) → NonnegPrior p →
      NormalisedPrior p → valueWithInformation u p e' ≤ valueWithInformation u p e + ε) :
    IsDeficientWithin e e' ε := by
  classical
  -- The gap between `e'` and the deterministic garbling by `f`, at the pair `r = (θ, z')`.
  let D : (Z → Z') → Θ × Z' → K := fun f r => e' r.1 r.2 - garble e (deterministic f) r.1 r.2
  rcases exists_mixed_pos_or_exists_mixed_nonpos
    (fun (s : Θ × (Z' → Bool)) (f : Z → Z') =>
      (∑ z', indicatorOf (s.2 z') * D f (s.1, z')) - ε) with
    ⟨y, hy, hy1, hpos⟩ | ⟨x, hx, hx1, hle⟩
  · -- A problem on which `e'` beats `e` by more than `ε`: contradiction.
    exfalso
    let T : Θ × Z' → K := fun r => ∑ φ : Z' → Bool, y (r.1, φ) * indicatorOf (φ r.2)
    let p : Θ → K := fun θ => ∑ φ : Z' → Bool, y (θ, φ)
    have hp : NonnegPrior p := fun θ => Finset.sum_nonneg fun φ _ => hy (θ, φ)
    have hp1 : NormalisedPrior p := by
      unfold NormalisedPrior
      rw [← hy1, Fintype.sum_prod_type]
    have hT0 : ∀ r, 0 ≤ T r := fun r => Finset.sum_nonneg fun φ _ =>
      mul_nonneg (hy (r.1, φ)) (by unfold indicatorOf; split_ifs <;> norm_num)
    have hTp : ∀ r, T r ≤ p r.1 := fun r => Finset.sum_le_sum fun φ _ => by
      have h0 := hy (r.1, φ)
      unfold indicatorOf
      split_ifs <;> simp [h0]
    have hT : ∀ f, ε < ∑ r, T r * D f r := fun f => by
      have h1 := hpos f
      have e1 : ∑ s, y s * ((∑ z', indicatorOf (s.2 z') * D f (s.1, z')) - ε) =
          ∑ r, T r * D f r - ε := by
        simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hy1, one_mul]
        congr 1
        rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun θ _ => ?_
        simp only [T, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun z' _ => Finset.sum_congr rfl fun φ _ => by ring
      rw [e1] at h1
      linarith
    let u : Z' → Θ → K := fun a θ => T (θ, a) / p θ
    have hu : ∀ a θ, 0 ≤ u a θ ∧ u a θ ≤ 1 := fun a θ =>
      ⟨div_nonneg (hT0 (θ, a)) (hp θ), div_le_one_of_le₀ (hTp (θ, a)) (hp θ)⟩
    have hpu : ∀ a θ, p θ * u a θ = T (θ, a) := fun a θ => by
      rcases (hp θ).lt_or_eq with hpos | hzero
      · simp only [u]
        field_simp
      · have hT' : T (θ, a) = 0 := le_antisymm (hzero ▸ hTp (θ, a)) (hT0 (θ, a))
        rw [← hzero, zero_mul, hT']
    have hsv : ∀ {Y : Type} [Fintype Y] (e₀ : Θ → Y → K) (z : Y) (a : Z'),
        signalValue u p e₀ z a = ∑ θ, e₀ θ z * T (θ, a) := fun e₀ z a =>
      Finset.sum_congr rfl fun θ _ => by
        rw [← hpu a θ]
        ring
    choose f hf using fun z => exists_eq_maxOver (signalValue u p e z)
    have hval : valueWithInformation u p e = ∑ r, T r * garble e (deterministic f) r.1 r.2 := by
      unfold valueWithInformation
      rw [Finset.sum_congr rfl fun z _ => hf z, Fintype.sum_prod_type]
      simp only [hsv, garble, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun θ _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun z _ => ?_
      simp [deterministic, mul_comm]
    have hval' : ∑ r, T r * e' r.1 r.2 ≤ valueWithInformation u p e' := by
      have : ∑ r, T r * e' r.1 r.2 = ∑ z', signalValue u p e' z' z' := by
        rw [Fintype.sum_prod_type, Finset.sum_comm]
        simp only [hsv]
        exact Finset.sum_congr rfl fun z' _ => Finset.sum_congr rfl fun θ _ => mul_comm _ _
      rw [this]
      exact Finset.sum_le_sum fun z' _ => le_maxOver (signalValue u p e' z') z'
    have h2 := hT f
    simp only [D, mul_sub, Finset.sum_sub_distrib] at h2
    have h3 := h u p hu hp hp1
    linarith
  · -- A mixture of deterministic garblings is within `ε` of `e'` in every state.
    let g : Z → Z' → K := fun z z' => ∑ f, x f * deterministic f z z'
    have hg : StochasticKernel g := by
      refine ⟨fun z z' => Finset.sum_nonneg fun f _ => mul_nonneg (hx f) ?_, fun z => ?_⟩
      · exact (stochasticKernel_deterministic f).1 z z'
      · simp only [g]
        rw [Finset.sum_comm]
        calc ∑ f, ∑ z', x f * deterministic f z z'
            = ∑ f, x f := Finset.sum_congr rfl fun f _ => by
              rw [← Finset.mul_sum, (stochasticKernel_deterministic (K := K) f).2 z, mul_one]
          _ = 1 := hx1
    have hmix : ∀ (θ : Θ) (φ : Z' → Bool),
        ∑ z', indicatorOf (φ z') * (e' θ z' - garble e g θ z') ≤ ε := fun θ φ => by
      have h1 := hle (θ, φ)
      have e1 : ∑ f, ((∑ z', indicatorOf (φ z') * D f (θ, z')) - ε) * x f =
          ∑ z', indicatorOf (φ z') * (e' θ z' - garble e g θ z') - ε := by
        simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hx1, mul_one,
          Finset.sum_mul]
        congr 1
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun z' _ => ?_
        have e2 : ∑ f, x f * D f (θ, z') = e' θ z' - garble e g θ z' := by
          simp only [D, mul_sub, Finset.sum_sub_distrib]
          rw [← Finset.sum_mul, hx1, one_mul, sum_mul_garble_deterministic]
        rw [← e2, Finset.mul_sum]
        exact Finset.sum_congr rfl fun f _ => by ring
      rw [e1] at h1
      linarith
    refine ⟨g, hg, fun θ => ?_⟩
    have hmass : ∑ z', garble e g θ z' = ∑ z', e' θ z' := by
      rw [he.garble hg.2 θ, he' θ]
    rw [totalVariation_eq_sum_pos _ _ hmass]
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun z' _ => ?_))
      (hmix θ fun z' => decide (garble e g θ z' < e' θ z'))
    by_cases hz : garble e g θ z' < e' θ z' <;> simp [indicatorOf, hz]

omit [Fintype A] [Nonempty A] in
/-- **S1a**, both directions (with T6a). For normalised experiments, `e` simulates `e'` to
within deficiency `ε` exactly when, in every decision problem with payoffs in `[0, 1]` and
every probability prior, the value of `e'` exceeds that of `e` by at most `ε`. -/
theorem isDeficientWithin_iff_forall_valueWithInformation_le [Nonempty Z'] {e : Θ → Z → K}
    {e' : Θ → Z' → K} (he : NormalisedKernel e) (he' : NormalisedKernel e') (ε : K) :
    IsDeficientWithin e e' ε ↔
      ∀ (B : Type) [Fintype B] [Nonempty B] (u : B → Θ → K) (p : Θ → K),
        (∀ a θ, 0 ≤ u a θ ∧ u a θ ≤ 1) → NonnegPrior p → NormalisedPrior p →
          valueWithInformation u p e' ≤ valueWithInformation u p e + ε := by
  constructor
  · intro h B _ _ u p hu hp hp1
    have h1 := h.valueWithInformation_le he he' u hp hp1 (B := 1)
      fun θ a a' => by linarith [(hu a θ).2, (hu a' θ).1]
    linarith
  · intro h
    exact isDeficientWithin_of_forall_valueWithInformation_le he he' fun u p => h Z' u p

end CategoricalDecisionAnalysisProofs
