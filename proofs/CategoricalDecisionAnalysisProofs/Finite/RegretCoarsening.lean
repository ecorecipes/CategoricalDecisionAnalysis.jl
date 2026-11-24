import DecisionAnalysisProofs.Finite.ValueOfInformation
import DecisionAnalysisProofs.Finite.Regret

/-!
# CategoricalDecisionAnalysisProofs.Finite.RegretCoarsening

**C6: regret under coarsening of the states.** Backs component 7 ("regret transform ... with
the coarsening inequality and its gap") of `CategoricalDecisionAnalysis.jl`: the function that
recomputes a regret table after the states are merged along a labelling `f : Θ → C`, the
property test "coarse regret ≤ fine regret, gap = EVPI − EVPPI", and the check "coarsening
loses nothing" that the equality case makes cheap.

## Conventions

* The coarsening is a labelling `f : Θ → C` (the core's `evppi(problem, partition)` takes the
  same object). All sums over a cell are written `Σ_θ if f θ = c then … else 0`, as in the
  core's `partialValue`.
* Everything is in **joint form**, with no division: `coarsePayoff u p f a c` is
  `Σ_{θ ∈ f⁻¹ c} p θ · u a θ`, the payoff of `a` in the cell `c` *multiplied by the
  probability of the cell*. `coarseRegret` is the regret table of that array and
  `coarseExpectedRegret` its sum over cells. The normalised form (a genuine decision problem
  with prior `coarsePrior p f` and conditional-mean payoffs `coarseMeanPayoff u p f`) is
  related by **`expectedRegret_coarseMeanPayoff`**; a cell of probability zero has payoff
  `0/0 = 0` there and contributes nothing in either form.
* The "conditional EVPI of the refinement" is `evpi u p − evppi u p f`, the expected value of
  learning the state when its cell is already known.

## Results

* **`coarseExpectedRegret_eq`**: coarse expected regret is `partialValue u p f` minus the
  expected utility, as `expectedRegret_eq` says for the fine table.
* **C6**, **`expectedRegret_sub_coarseExpectedRegret`**: fine minus coarse expected regret is
  `evpi u p − evppi u p f`, for every action (the gap does not depend on the action, so
  coarsening never changes the ranking of actions by expected regret).
* **C6**, **`coarseExpectedRegret_le_expectedRegret`** and the cellwise form
  **`coarseRegret_le`**: coarsening cannot raise regret (the transform is lax), for a
  nonnegative prior.
* **C6**, **`coarseExpectedRegret_eq_expectedRegret_iff`**: equality holds exactly when every
  cell has an action that is best at each of its states of positive probability.
* **`coarseExpectedRegret_comp_le`**, **`coarseExpectedRegret_id`**,
  **`coarseExpectedRegret_const`**: monotone along further coarsening; the identity labelling
  gives the fine regret and the constant labelling gives the shortfall from the act-now value.

Not claimed: any statement for *maximum* regret (`MinimaxRegret`) under coarsening. The
cellwise inequality `coarseRegret_le` holds for weighted regrets; maximum regret of the
normalised coarse table is not ordered against the fine one by these results.
-/

set_option autoImplicit false
-- One ordered-field context is declared per file; not every theorem uses every instance.
set_option linter.unusedSectionVars false

namespace CategoricalDecisionAnalysisProofs

open DecisionAnalysisProofs Finset

variable {A Θ C C' : Type} [Fintype A] [Nonempty A] [Fintype Θ] [Fintype C] [DecidableEq C]
  [Fintype C'] [DecidableEq C'] {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The joint-form payoff of `a` in the cell `c`: `Σ_{θ : f θ = c} p θ · u a θ`. -/
def coarsePayoff (u : A → Θ → K) (p : Θ → K) (f : Θ → C) (a : A) (c : C) : K :=
  ∑ θ, if f θ = c then p θ * u a θ else 0

/-- The regret table of the coarsened problem, in joint form. -/
def coarseRegret (u : A → Θ → K) (p : Θ → K) (f : Θ → C) (a : A) (c : C) : K :=
  (maxOver fun a' => coarsePayoff u p f a' c) - coarsePayoff u p f a c

/-- The expected regret of `a` in the coarsened problem. -/
def coarseExpectedRegret (u : A → Θ → K) (p : Θ → K) (f : Θ → C) (a : A) : K :=
  ∑ c, coarseRegret u p f a c

/-- The probability of the cell `c`. -/
def coarsePrior (p : Θ → K) (f : Θ → C) (c : C) : K := ∑ θ, if f θ = c then p θ else 0

/-- The conditional mean payoff of `a` given the cell `c` (zero for a cell of probability
zero). -/
def coarseMeanPayoff (u : A → Θ → K) (p : Θ → K) (f : Θ → C) (a : A) (c : C) : K :=
  coarsePayoff u p f a c / coarsePrior p f c

omit [Nonempty A] in
/-- The cells partition the states: summing the joint-form payoffs over cells gives the
expected utility. -/
theorem sum_coarsePayoff (u : A → Θ → K) (p : Θ → K) (f : Θ → C) (a : A) :
    ∑ c, coarsePayoff u p f a c = expectedUtility u p a := by
  unfold coarsePayoff expectedUtility
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun θ _ => by simp

/-- Coarse expected regret is the partial-information value minus the expected utility. -/
theorem coarseExpectedRegret_eq (u : A → Θ → K) (p : Θ → K) (f : Θ → C) (a : A) :
    coarseExpectedRegret u p f a = partialValue u p f - expectedUtility u p a := by
  unfold coarseExpectedRegret coarseRegret
  rw [Finset.sum_sub_distrib, sum_coarsePayoff]
  rfl

/-- **C6.** The gap between fine and coarse expected regret is the conditional EVPI of the
refinement, `evpi − evppi f`, whatever the action. -/
theorem expectedRegret_sub_coarseExpectedRegret (u : A → Θ → K) (p : Θ → K) (f : Θ → C)
    (a : A) :
    expectedRegret u p a - coarseExpectedRegret u p f a = evpi u p - evppi u p f := by
  rw [expectedRegret_eq, coarseExpectedRegret_eq]
  unfold evpi evppi
  ring

/-- **C6.** Coarsening the states cannot raise expected regret. -/
theorem coarseExpectedRegret_le_expectedRegret (u : A → Θ → K) {p : Θ → K}
    (hp : NonnegPrior p) (f : Θ → C) (a : A) :
    coarseExpectedRegret u p f a ≤ expectedRegret u p a := by
  have h := expectedRegret_sub_coarseExpectedRegret u p f a
  have h' := evppi_le_evpi u hp f
  linarith

/-- **C6**, cell by cell: the coarse regret of a cell is at most the weighted fine regret
summed over the cell. -/
theorem coarseRegret_le (u : A → Θ → K) {p : Θ → K} (hp : NonnegPrior p) (f : Θ → C) (a : A)
    (c : C) : coarseRegret u p f a c ≤ ∑ θ, if f θ = c then p θ * regret u a θ else 0 := by
  have hmax : (maxOver fun a' => coarsePayoff u p f a' c) ≤
      ∑ θ, if f θ = c then p θ * maxOver (fun a' => u a' θ) else 0 :=
    maxOver_le fun a' => Finset.sum_le_sum fun θ _ => by
      split_ifs
      · exact mul_le_mul_of_nonneg_left (le_maxOver (fun a' => u a' θ) a') (hp θ)
      · exact le_refl _
  have hsplit : (∑ θ, if f θ = c then p θ * regret u a θ else 0) =
      (∑ θ, if f θ = c then p θ * maxOver (fun a' => u a' θ) else 0) -
        coarsePayoff u p f a c := by
    unfold coarsePayoff
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun θ _ => ?_
    split_ifs
    · unfold regret
      ring
    · ring
  rw [hsplit]
  unfold coarseRegret
  linarith

/-- The perfect-information value, cell by cell. -/
theorem perfectValue_eq_sum_cells (u : A → Θ → K) (p : Θ → K) (f : Θ → C) :
    perfectValue u p = ∑ c, ∑ θ, if f θ = c then p θ * maxOver (fun a' => u a' θ) else 0 := by
  unfold perfectValue
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun θ _ => by simp

/-- **C6**, the equality case. For a nonnegative prior, coarsening leaves expected regret
unchanged exactly when every cell has a common best action: one action that is optimal at
every state of positive probability in the cell. -/
theorem coarseExpectedRegret_eq_expectedRegret_iff (u : A → Θ → K) {p : Θ → K}
    (hp : NonnegPrior p) (f : Θ → C) (a : A) :
    coarseExpectedRegret u p f a = expectedRegret u p a ↔
      ∀ c, ∃ b, ∀ θ, f θ = c → 0 < p θ → ∀ a', u a' θ ≤ u b θ := by
  have hcell : ∀ c a', coarsePayoff u p f a' c ≤
      ∑ θ, if f θ = c then p θ * maxOver (fun a' => u a' θ) else 0 := fun c a' =>
    Finset.sum_le_sum fun θ _ => by
      split_ifs
      · exact mul_le_mul_of_nonneg_left (le_maxOver (fun a' => u a' θ) a') (hp θ)
      · exact le_refl _
  have hle : ∀ c ∈ (Finset.univ : Finset C), (maxOver fun a' => coarsePayoff u p f a' c) ≤
      ∑ θ, if f θ = c then p θ * maxOver (fun a' => u a' θ) else 0 := fun c _ =>
    maxOver_le (hcell c)
  have hiff : coarseExpectedRegret u p f a = expectedRegret u p a ↔
      ∀ c ∈ (Finset.univ : Finset C), (maxOver fun a' => coarsePayoff u p f a' c) =
        ∑ θ, if f θ = c then p θ * maxOver (fun a' => u a' θ) else 0 := by
    rw [← Finset.sum_eq_sum_iff_of_le hle, ← perfectValue_eq_sum_cells, coarseExpectedRegret_eq,
      expectedRegret_eq]
    constructor
    · intro h
      exact sub_left_injective h
    · intro h
      unfold partialValue
      exact congrArg (· - expectedUtility u p a) h
  rw [hiff]
  refine forall_congr' fun c => ?_
  simp only [Finset.mem_univ, forall_true_left]
  constructor
  · intro h
    obtain ⟨b, hb⟩ := exists_eq_maxOver fun a' => coarsePayoff u p f a' c
    refine ⟨b, fun θ hθ hpos a' => ?_⟩
    have hterm : ∀ θ ∈ (Finset.univ : Finset Θ),
        (if f θ = c then p θ * u b θ else 0) ≤
          if f θ = c then p θ * maxOver (fun a' => u a' θ) else 0 := fun θ _ => by
      split_ifs
      · exact mul_le_mul_of_nonneg_left (le_maxOver (fun a' => u a' θ) b) (hp θ)
      · exact le_refl _
    have heq := (Finset.sum_eq_sum_iff_of_le hterm).mp (hb.symm.trans h) θ (Finset.mem_univ θ)
    rw [if_pos hθ, if_pos hθ] at heq
    have hbmax : u b θ = maxOver fun a' => u a' θ := mul_left_cancel₀ hpos.ne' heq
    rw [hbmax]
    exact le_maxOver (fun a' => u a' θ) a'
  · rintro ⟨b, hb⟩
    apply le_antisymm (maxOver_le (hcell c))
    calc (∑ θ, if f θ = c then p θ * maxOver (fun a' => u a' θ) else 0)
        = coarsePayoff u p f b c := by
          unfold coarsePayoff
          refine Finset.sum_congr rfl fun θ _ => ?_
          split_ifs with hθ
          · rcases (hp θ).lt_or_eq with hpos | hzero
            · rw [maxOver_eq_of b rfl (hb θ hθ hpos)]
            · rw [← hzero, zero_mul, zero_mul]
          · rfl
      _ ≤ maxOver fun a' => coarsePayoff u p f a' c :=
          le_maxOver (fun a' => coarsePayoff u p f a' c) b

/-- Coarsening further lowers expected regret further. -/
theorem coarseExpectedRegret_comp_le (u : A → Θ → K) (p : Θ → K) (f : Θ → C) (h : C → C')
    (a : A) : coarseExpectedRegret u p (h ∘ f) a ≤ coarseExpectedRegret u p f a := by
  have hm := evppi_mono u p f h
  rw [coarseExpectedRegret_eq, coarseExpectedRegret_eq]
  unfold evppi at hm
  linarith

/-- The identity labelling gives the fine expected regret. -/
theorem coarseExpectedRegret_id [DecidableEq Θ] (u : A → Θ → K) {p : Θ → K}
    (hp : NonnegPrior p) (a : A) : coarseExpectedRegret u p id a = expectedRegret u p a := by
  have h := expectedRegret_sub_coarseExpectedRegret u p (id : Θ → Θ) a
  rw [evppi_id u hp] at h
  linarith

/-- The one-cell labelling gives the shortfall of `a` from the act-now value. -/
theorem coarseExpectedRegret_const (u : A → Θ → K) (p : Θ → K) (a : A) :
    coarseExpectedRegret u p (fun _ => ()) a = actNowValue u p - expectedUtility u p a := by
  have h := evppi_const u p
  rw [coarseExpectedRegret_eq]
  unfold evppi at h
  linarith

/-- The normalised coarse problem (prior `coarsePrior`, conditional-mean payoffs
`coarseMeanPayoff`) has the core's expected regret equal to the joint-form coarse expected
regret. Cells of probability zero contribute nothing in either. -/
theorem expectedRegret_coarseMeanPayoff (u : A → Θ → K) {p : Θ → K} (hp : NonnegPrior p)
    (f : Θ → C) (a : A) :
    expectedRegret (coarseMeanPayoff u p f) (coarsePrior p f) a =
      coarseExpectedRegret u p f a := by
  unfold expectedRegret coarseExpectedRegret
  refine Finset.sum_congr rfl fun c _ => ?_
  have hq : 0 ≤ coarsePrior p f c := Finset.sum_nonneg fun θ _ => by
    split_ifs
    · exact hp θ
    · exact le_refl _
  unfold regret coarseRegret
  rcases hq.lt_or_eq with hpos | hzero
  · rw [mul_sub, ← maxOver_mul_left _ hq]
    have hcancel : ∀ a', coarsePrior p f c * coarseMeanPayoff u p f a' c =
        coarsePayoff u p f a' c := fun a' => by
      unfold coarseMeanPayoff
      rw [mul_comm, div_mul_cancel₀ _ hpos.ne']
    simp only [hcancel]
  · have hzero' : ∀ θ ∈ (Finset.univ : Finset Θ), (if f θ = c then p θ else 0) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun θ _ => by
        split_ifs
        · exact hp θ
        · exact le_refl _).mp hzero.symm
    have hpay : ∀ a', coarsePayoff u p f a' c = 0 := fun a' =>
      Finset.sum_eq_zero fun θ hθ => by
        have h0 := hzero' θ hθ
        split_ifs with hc
        · rw [if_pos hc] at h0
          rw [h0, zero_mul]
        · rfl
    have hmax : (maxOver fun _ : A => (0 : K)) = 0 :=
      maxOver_eq_of (Classical.arbitrary A) rfl fun _ => le_refl _
    simp only [hpay, ← hzero, zero_mul, sub_zero, hmax]

end CategoricalDecisionAnalysisProofs
