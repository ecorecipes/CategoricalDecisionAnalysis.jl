import CategoricalDecisionAnalysisProofs.Finite.Pullback
import DecisionAnalysisProofs.Finite.Selection

/-!
# CategoricalDecisionAnalysisProofs.Finite.Sequential

**C7a, C7b: selection functions and backward induction.** Backs component 4 ("selection
functions ... the product of selection functions for multi-stage problems") of
`CategoricalDecisionAnalysis.jl`, and the per-rule flag "admits backward induction": the
conditions proved sufficient here are the ones the flag records, and the test "selection
function product against exhaustive backward induction" is the first theorem of each section.

## Conventions

* A selection function is `ε : (A → R) → A`; its quantifier is `quantifier ε p = p (ε p)`.
  `selProd ε δ` is the Escardó-Oliva product for two stages, the second stage's selection
  function being allowed to depend on the first move.
* A two-stage problem with chance (`TwoStage`) has a first action `a₁`, an uncertain
  intermediate state `x₁` drawn from `step₁ a₁ : T X₁`, a second action chosen **after seeing
  `x₁`**, and an uncertain final state from `step₂ x₁ a₂ : T X₂`; rewards `reward₁ a₁ x₁` and
  `reward₂ x₁ a₂ x₂` are added. A policy is a pair `(a₁, π)` with `π : X₁ → A₂`.
* Two values of a policy are distinguished, and the theorem is that they agree under the
  stated conditions:
  * `flatValue`: the aggregate of the **total reward over trajectories** (what a rule means
    when it is applied to the whole problem, and what exhaustive policy search evaluates);
  * `nestedValue`: the aggregate applied stage by stage (what backward induction evaluates).
* The three conditions of Brede and Botta, in the vocabulary of `Finite/Pullback.lean`: the
  aggregator is an algebra (the laws `expect_pure`, `expect_bind` of `UncertaintyAlgebra`),
  it is monotone (`MonotoneAt`, at the first-stage outcomes), and adding the stage reward
  commutes with it (`AdditiveAt`, at the second-stage outcomes).

## Results

* **C7a**, **`quantifier_selProd`**, **`IsArgmax.product`**, **`selProd_firstArgmax_spec`**:
  the product of selection functions has the product quantifier; a product of argmax
  selection functions is an argmax on pairs, so it attains the maximum over all plays.
  **`quantifier_selProd_maximin`**: argmax against argmin gives the core's maximin value.
* **`TwoStage.flatValue_eq_iterated`**: the flat value as an iterated aggregate (no
  hypothesis; for `D` this is the double sum Julia evaluates,
  **`TwoStage.flatValue_distAlgebra`**).
* **C7b**, **`TwoStage.flatValue_eq_nestedValue`** (needs `AdditiveAt`),
  **`TwoStage.nestedValue_le_backwardValue`** (needs `MonotoneAt`),
  **`TwoStage.IsBackwardPolicy.flatValue_optimal`** and
  **`TwoStage.backwardValue_eq_flatValue`**: a backward-induction policy maximises the flat
  value over all policies, and the backward-induction value is that maximum.
* **`TwoStage.backwardInduction_optimal_expectation`** (kernels with nonnegative first-stage
  weights and normalised second-stage weights), **`TwoStage.backwardInduction_optimal_worstCase`**,
  **`TwoStage.backwardInduction_optimal_bestCase`**: expectation, worst case and best case
  satisfy the conditions.
* **`horizonPolicyValue_le_backwardValue`**, **`horizonPolicyValue_backwardPolicy`**: for any
  horizon `n` and any monotone aggregator, backward induction maximises the **nested** value
  over sequences of `n` decision rules, and the first-argmax policy attains it. With the
  identity aggregator this is the deterministic `n`-stage case of C7a.

Not claimed: for horizon `n > 2` the equality of the nested value and the flat value over
trajectories (proved for two stages only); history-dependent policies beyond two stages;
set-valued selection functions; games with more than one player. The failures for CVaR and
minimax regret are in `Finite/BackwardInductionFails.lean`.
-/

set_option autoImplicit false
-- One ordered-field context is declared per file; not every theorem uses every instance.
set_option linter.unusedSectionVars false

namespace CategoricalDecisionAnalysisProofs

open DecisionAnalysisProofs Finset

/-! ### C7a: selection functions and their product -/

section Selection

variable {A B R : Type}

/-- The quantifier of a selection function: the value at the selected point. -/
def quantifier (ε : (A → R) → A) : (A → R) → R := fun p => p (ε p)

/-- The product of selection functions for two stages: the second stage answers the first
move `a` with `δ a`, and the first stage selects against that answer. -/
def selProd (ε : (A → R) → A) (δ : A → (B → R) → B) : (A × B → R) → A × B := fun p =>
  (ε fun x => p (x, δ x fun y => p (x, y)),
    δ (ε fun x => p (x, δ x fun y => p (x, y)))
      fun y => p (ε fun x => p (x, δ x fun y => p (x, y)), y))

/-- **C7a.** The quantifier of the product is the product of the quantifiers: the value of
the selected play is computed by backward induction. -/
theorem quantifier_selProd (ε : (A → R) → A) (δ : A → (B → R) → B) (p : A × B → R) :
    quantifier (selProd ε δ) p =
      quantifier ε fun a => quantifier (δ a) fun b => p (a, b) := rfl

/-- `ε` selects a maximiser of every objective. -/
def IsArgmax [LE R] (ε : (A → R) → A) : Prop := ∀ (p : A → R) (a : A), p a ≤ p (ε p)

/-- `ε` selects a minimiser of every objective. -/
def IsArgmin [LE R] (ε : (A → R) → A) : Prop := ∀ (p : A → R) (a : A), p (ε p) ≤ p a

/-- **C7a.** A product of argmax selection functions is an argmax on plays: backward
induction attains the maximum over all pairs of moves, hence over all strategies. -/
theorem IsArgmax.product [Preorder R] {ε : (A → R) → A} {δ : A → (B → R) → B}
    (hε : IsArgmax ε) (hδ : ∀ a, IsArgmax (δ a)) : IsArgmax (selProd ε δ) := by
  rintro p ⟨a, b⟩
  exact (hδ a (fun y => p (a, y)) b).trans (hε (fun x => p (x, δ x fun y => p (x, y))) a)

/-- A strategy `(a, σ)` of the deterministic two-stage problem never beats the play selected
by the product. -/
theorem IsArgmax.strategy_le_selProd [Preorder R] {ε : (A → R) → A} {δ : A → (B → R) → B}
    (hε : IsArgmax ε) (hδ : ∀ a, IsArgmax (δ a)) (p : A × B → R) (a : A) (σ : A → B) :
    p (a, σ a) ≤ p (selProd ε δ p) :=
  hε.product hδ p (a, σ a)

end Selection

section SelectionOrdered

variable {A B : Type} [Fintype A] [Nonempty A] [LinearOrder A] [Fintype B] [Nonempty B]
  [LinearOrder B] {K : Type} [LinearOrder K]

/-- The core's `firstArgmax` (`first_choice` of a maximising rule) is an argmax selection
function. -/
theorem isArgmax_firstArgmax : IsArgmax (firstArgmax : (A → K) → A) := fun p a =>
  le_firstArgmax_value p a

/-- The core's `firstArgmin` is an argmin selection function. -/
theorem isArgmin_firstArgmin : IsArgmin (firstArgmin : (A → K) → A) := fun p a =>
  firstArgmin_value_le p a

theorem quantifier_firstArgmax (p : A → K) : quantifier firstArgmax p = maxOver p :=
  firstArgmax_spec p

theorem quantifier_firstArgmin (p : A → K) : quantifier firstArgmin p = minOver p :=
  firstArgmin_spec p

/-- **C7a**, for the selection functions Julia uses: the product of first-argmax selections
attains the maximum over all plays. -/
theorem selProd_firstArgmax_spec (p : A × B → K) :
    p (selProd firstArgmax (fun _ => firstArgmax) p) = maxOver p :=
  (maxOver_eq_of _ rfl
    ((isArgmax_firstArgmax.product fun _ => isArgmax_firstArgmax) p)).symm

/-- The product of an argmax over actions and an argmin over states computes the maximin
value of the core (`Maximin`): the rule is a product of selection functions. -/
theorem quantifier_selProd_maximin (u : A → B → K) :
    quantifier (selProd firstArgmax fun _ => firstArgmin) (fun x : A × B => u x.1 x.2) =
      maxOver (worstCase u) := by
  rw [quantifier_selProd, quantifier_firstArgmax]
  exact congrArg maxOver (funext fun a => quantifier_firstArgmin (u a))

end SelectionOrdered

/-! ### C7b: two stages with chance -/

/-- A two-stage sequential problem with uncertainty of type `T`: act, observe `x₁`, act
again, observe `x₂`; stage rewards add. -/
structure TwoStage (T : Type → Type) (K : Type) (A₁ X₁ A₂ X₂ : Type) where
  /-- The uncertain intermediate state after the first action. -/
  step₁ : A₁ → T X₁
  /-- The first stage reward. -/
  reward₁ : A₁ → X₁ → K
  /-- The uncertain final state after the second action, taken at `x₁`. -/
  step₂ : X₁ → A₂ → T X₂
  /-- The second stage reward. -/
  reward₂ : X₁ → A₂ → X₂ → K

namespace TwoStage

variable {T : Type → Type} {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  (E : UncertaintyAlgebra T K)
  {A₁ X₁ A₂ X₂ : Type} [Fintype A₁] [Nonempty A₁] [Fintype X₁] [DecidableEq X₁] [Fintype A₂]
  [Nonempty A₂] [Fintype X₂] [DecidableEq X₂] (P : TwoStage T K A₁ X₁ A₂ X₂)

/-- The uncertain trajectory `(x₁, x₂)` under the policy `(a₁, π)`. -/
def trajectory (a₁ : A₁) (π : X₁ → A₂) : T (X₁ × X₂) :=
  E.bind (P.step₁ a₁) fun x₁ => E.bind (P.step₂ x₁ (π x₁)) fun x₂ => E.pure (x₁, x₂)

/-- The total reward along a trajectory. -/
def totalReward (a₁ : A₁) (π : X₁ → A₂) : X₁ × X₂ → K := fun t =>
  P.reward₁ a₁ t.1 + P.reward₂ t.1 (π t.1) t.2

/-- The value of a policy as the rule defines it: the aggregate of the total reward over
trajectories. Exhaustive policy search maximises this. -/
def flatValue (a₁ : A₁) (π : X₁ → A₂) : K :=
  E.expect (P.totalReward a₁ π) (P.trajectory E a₁ π)

/-- The aggregate second-stage reward of `a₂` at `x₁`. -/
def continuationValue (x₁ : X₁) (a₂ : A₂) : K := E.expect (P.reward₂ x₁ a₂) (P.step₂ x₁ a₂)

/-- The value of a policy computed stage by stage. -/
def nestedValue (a₁ : A₁) (π : X₁ → A₂) : K :=
  E.expect (fun x₁ => P.reward₁ a₁ x₁ + P.continuationValue E x₁ (π x₁)) (P.step₁ a₁)

/-- The optimal continuation value at `x₁` (the last step of backward induction). -/
def stageTwoValue (x₁ : X₁) : K := maxOver (P.continuationValue E x₁)

/-- The score backward induction gives the first action `a₁`. -/
def stageOneScore (a₁ : A₁) : K :=
  E.expect (fun x₁ => P.reward₁ a₁ x₁ + P.stageTwoValue E x₁) (P.step₁ a₁)

/-- The value computed by backward induction. -/
def backwardValue : K := maxOver (P.stageOneScore E)

/-- `(a₁, π)` is a policy returned by backward induction: `π` is optimal at every `x₁`, and
`a₁` is optimal against the optimal continuation values. -/
def IsBackwardPolicy (a₁ : A₁) (π : X₁ → A₂) : Prop :=
  (∀ x₁ a₂, P.continuationValue E x₁ a₂ ≤ P.continuationValue E x₁ (π x₁)) ∧
    ∀ a₁', P.stageOneScore E a₁' ≤ P.stageOneScore E a₁

/-- The flat value as an iterated aggregate; no condition on the aggregator is used. -/
theorem flatValue_eq_iterated (a₁ : A₁) (π : X₁ → A₂) :
    P.flatValue E a₁ π =
      E.expect (fun x₁ => E.expect (fun x₂ => P.reward₁ a₁ x₁ + P.reward₂ x₁ (π x₁) x₂)
        (P.step₂ x₁ (π x₁))) (P.step₁ a₁) := by
  unfold flatValue trajectory
  rw [E.expect_bind]
  refine congrArg (fun g => E.expect g (P.step₁ a₁)) (funext fun x₁ => ?_)
  rw [E.expect_bind]
  refine congrArg (fun g => E.expect g (P.step₂ x₁ (π x₁))) (funext fun x₂ => ?_)
  rw [E.expect_pure]
  rfl

/-- **C7b**, first half. When adding the stage reward commutes with the aggregate at every
second-stage outcome, the flat value of a policy is its nested value. -/
theorem flatValue_eq_nestedValue (hadd : ∀ x₁ a₂, E.AdditiveAt (P.step₂ x₁ a₂)) (a₁ : A₁)
    (π : X₁ → A₂) : P.flatValue E a₁ π = P.nestedValue E a₁ π := by
  rw [flatValue_eq_iterated]
  exact congrArg (fun g => E.expect g (P.step₁ a₁))
    (funext fun x₁ => hadd x₁ (π x₁) (P.reward₁ a₁ x₁) (P.reward₂ x₁ (π x₁)))

/-- **C7b**, second half. When the aggregate is monotone at every first-stage outcome, no
policy has a nested value above the backward-induction value. -/
theorem nestedValue_le_backwardValue (hmono : ∀ a₁, E.MonotoneAt (P.step₁ a₁)) (a₁ : A₁)
    (π : X₁ → A₂) : P.nestedValue E a₁ π ≤ P.backwardValue E :=
  (hmono a₁ _ _ fun x₁ =>
    add_le_add_right (le_maxOver (P.continuationValue E x₁) (π x₁)) _).trans
    (le_maxOver (P.stageOneScore E) a₁)

/-- A backward-induction policy has nested value equal to the backward-induction value. -/
theorem IsBackwardPolicy.nestedValue_eq {a₁ : A₁} {π : X₁ → A₂}
    (h : P.IsBackwardPolicy E a₁ π) : P.nestedValue E a₁ π = P.backwardValue E := by
  have h₂ : ∀ x₁, P.continuationValue E x₁ (π x₁) = P.stageTwoValue E x₁ := fun x₁ =>
    (maxOver_eq_of (π x₁) rfl (h.1 x₁)).symm
  have h₁ : P.nestedValue E a₁ π = P.stageOneScore E a₁ :=
    congrArg (fun g => E.expect g (P.step₁ a₁))
      (funext fun x₁ => congrArg (P.reward₁ a₁ x₁ + ·) (h₂ x₁))
  rw [h₁]
  exact (maxOver_eq_of a₁ rfl h.2).symm

/-- Backward induction returns a policy. -/
theorem exists_isBackwardPolicy : ∃ (a₁ : A₁) (π : X₁ → A₂), P.IsBackwardPolicy E a₁ π := by
  choose π hπ using fun x₁ => exists_eq_maxOver (P.continuationValue E x₁)
  obtain ⟨a₁, ha₁⟩ := exists_eq_maxOver (P.stageOneScore E)
  exact ⟨a₁, π, fun x₁ a₂ => (hπ x₁) ▸ le_maxOver (P.continuationValue E x₁) a₂,
    fun a₁' => ha₁ ▸ le_maxOver (P.stageOneScore E) a₁'⟩

/-- **C7b.** Under the three conditions (algebra, monotone, reward-additive), a
backward-induction policy maximises the flat value over all policies. -/
theorem IsBackwardPolicy.flatValue_optimal (hmono : ∀ a₁, E.MonotoneAt (P.step₁ a₁))
    (hadd : ∀ x₁ a₂, E.AdditiveAt (P.step₂ x₁ a₂)) {a₁ : A₁} {π : X₁ → A₂}
    (h : P.IsBackwardPolicy E a₁ π) (a₁' : A₁) (π' : X₁ → A₂) :
    P.flatValue E a₁' π' ≤ P.flatValue E a₁ π := by
  rw [P.flatValue_eq_nestedValue E hadd, P.flatValue_eq_nestedValue E hadd, h.nestedValue_eq]
  exact P.nestedValue_le_backwardValue E hmono a₁' π'

/-- **C7b.** Under the three conditions the backward-induction value is the flat value of a
backward-induction policy, hence the optimum of exhaustive policy search. -/
theorem backwardValue_eq_flatValue (hadd : ∀ x₁ a₂, E.AdditiveAt (P.step₂ x₁ a₂)) {a₁ : A₁}
    {π : X₁ → A₂} (h : P.IsBackwardPolicy E a₁ π) : P.backwardValue E = P.flatValue E a₁ π := by
  rw [P.flatValue_eq_nestedValue E hadd, h.nestedValue_eq]

/-- Every policy's flat value is at most the backward-induction value. -/
theorem flatValue_le_backwardValue (hmono : ∀ a₁, E.MonotoneAt (P.step₁ a₁))
    (hadd : ∀ x₁ a₂, E.AdditiveAt (P.step₂ x₁ a₂)) (a₁ : A₁) (π : X₁ → A₂) :
    P.flatValue E a₁ π ≤ P.backwardValue E := by
  rw [P.flatValue_eq_nestedValue E hadd]
  exact P.nestedValue_le_backwardValue E hmono a₁ π

end TwoStage

/-! ### The rules that satisfy the conditions -/

section Instances

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {A₁ X₁ A₂ X₂ : Type} [Fintype A₁] [Nonempty A₁] [Fintype X₁] [DecidableEq X₁] [Fintype A₂]
  [Nonempty A₂] [Fintype X₂] [DecidableEq X₂]

/-- For expectation the flat value is the double sum over trajectories that Julia evaluates. -/
theorem TwoStage.flatValue_distAlgebra (P : TwoStage (fun X => X → K) K A₁ X₁ A₂ X₂) (a₁ : A₁)
    (π : X₁ → A₂) :
    P.flatValue (distAlgebra K) a₁ π =
      ∑ x₁, P.step₁ a₁ x₁ *
        ∑ x₂, P.step₂ x₁ (π x₁) x₂ * (P.reward₁ a₁ x₁ + P.reward₂ x₁ (π x₁) x₂) :=
  P.flatValue_eq_iterated (distAlgebra K) a₁ π

/-- **C7b** for expectation: with nonnegative first-stage weights and normalised second-stage
weights, backward induction maximises expected total reward. -/
theorem TwoStage.backwardInduction_optimal_expectation
    (P : TwoStage (fun X => X → K) K A₁ X₁ A₂ X₂) (h₁ : ∀ a₁ x₁, 0 ≤ P.step₁ a₁ x₁)
    (h₂ : ∀ x₁ a₂, ∑ x₂, P.step₂ x₁ a₂ x₂ = 1) {a₁ : A₁} {π : X₁ → A₂}
    (h : P.IsBackwardPolicy (distAlgebra K) a₁ π) (a₁' : A₁) (π' : X₁ → A₂) :
    P.flatValue (distAlgebra K) a₁' π' ≤ P.flatValue (distAlgebra K) a₁ π :=
  TwoStage.IsBackwardPolicy.flatValue_optimal (distAlgebra K) P (fun a => distAlgebra_monotoneAt (h₁ a))
    (fun x₁ a₂ => distAlgebra_additiveAt (h₂ x₁ a₂)) h a₁' π'

/-- **C7b** for the worst case: backward induction maximises the worst total reward. -/
theorem TwoStage.backwardInduction_optimal_worstCase (P : TwoStage NonemptyFinset K A₁ X₁ A₂ X₂)
    {a₁ : A₁} {π : X₁ → A₂} (h : P.IsBackwardPolicy (minAlgebra K) a₁ π) (a₁' : A₁)
    (π' : X₁ → A₂) : P.flatValue (minAlgebra K) a₁' π' ≤ P.flatValue (minAlgebra K) a₁ π :=
  TwoStage.IsBackwardPolicy.flatValue_optimal (minAlgebra K) P (fun a => minAlgebra_monotoneAt (P.step₁ a))
    (fun x₁ a₂ => minAlgebra_additiveAt (P.step₂ x₁ a₂)) h a₁' π'

/-- **C7b** for the best case: backward induction maximises the best total reward. -/
theorem TwoStage.backwardInduction_optimal_bestCase (P : TwoStage NonemptyFinset K A₁ X₁ A₂ X₂)
    {a₁ : A₁} {π : X₁ → A₂} (h : P.IsBackwardPolicy (maxAlgebra K) a₁ π) (a₁' : A₁)
    (π' : X₁ → A₂) : P.flatValue (maxAlgebra K) a₁' π' ≤ P.flatValue (maxAlgebra K) a₁ π :=
  TwoStage.IsBackwardPolicy.flatValue_optimal (maxAlgebra K) P (fun a => maxAlgebra_monotoneAt (P.step₁ a))
    (fun x₁ a₂ => maxAlgebra_additiveAt (P.step₂ x₁ a₂)) h a₁' π'

end Instances

/-! ### Any horizon: the nested value -/

section Horizon

variable {S A M K : Type} [Fintype A] [Nonempty A] [Field K] [LinearOrder K]
  [IsStrictOrderedRing K] (agg : (S → K) → M → K) (step : S → A → M) (r : S → A → S → K)

/-- The nested value of a sequence of decision rules (first rule first) from state `s`:
`agg` applied to stage reward plus the value of the remaining rules. -/
def horizonPolicyValue : List (S → A) → S → K
  | [], _ => 0
  | π :: πs, s => agg (fun s' => r s (π s) s' + horizonPolicyValue πs s') (step s (π s))

/-- The backward-induction value with `n` stages to go. -/
def horizonBackwardValue : ℕ → S → K
  | 0, _ => 0
  | n + 1, s => maxOver fun a => agg (fun s' => r s a s' + horizonBackwardValue n s') (step s a)

/-- The policy backward induction returns, with ties broken to the first action
(`first_choice`). -/
def horizonBackwardPolicy [LinearOrder A] : ℕ → List (S → A)
  | 0 => []
  | n + 1 =>
    (fun s => firstArgmax fun a =>
      agg (fun s' => r s a s' + horizonBackwardValue agg step r n s') (step s a)) ::
      horizonBackwardPolicy n

theorem length_horizonBackwardPolicy [LinearOrder A] (n : ℕ) :
    (horizonBackwardPolicy agg step r n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [horizonBackwardPolicy, ih]

/-- For a monotone aggregator, no sequence of `n` decision rules has nested value above the
backward-induction value. -/
theorem horizonPolicyValue_le_backwardValue
    (hmono : ∀ s a (v w : S → K), (∀ s', v s' ≤ w s') → agg v (step s a) ≤ agg w (step s a))
    (πs : List (S → A)) (s : S) :
    horizonPolicyValue agg step r πs s ≤ horizonBackwardValue agg step r πs.length s := by
  induction πs generalizing s with
  | nil => exact le_refl _
  | cons π πs ih =>
    exact (hmono s (π s) _ _ fun s' => add_le_add_right (ih s') _).trans
      (le_maxOver (fun a => agg (fun s' => r s a s' +
        horizonBackwardValue agg step r πs.length s') (step s a)) (π s))

/-- The first-argmax policy attains the backward-induction value (no condition on `agg`). -/
theorem horizonPolicyValue_backwardPolicy [LinearOrder A] (n : ℕ) (s : S) :
    horizonPolicyValue agg step r (horizonBackwardPolicy agg step r n) s =
      horizonBackwardValue agg step r n s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    have hfun : (fun s' => horizonPolicyValue agg step r (horizonBackwardPolicy agg step r n) s')
        = horizonBackwardValue agg step r n := funext ih
    simp only [horizonBackwardPolicy, horizonPolicyValue, horizonBackwardValue, hfun]
    exact firstArgmax_spec fun a =>
      agg (fun s' => r s a s' + horizonBackwardValue agg step r n s') (step s a)

/-- **C7a**, any horizon: in a deterministic problem (`step s a` is the next state and the
aggregate is evaluation there) backward induction maximises total reward over sequences of
decision rules. -/
theorem horizonPolicyValue_le_backwardValue_deterministic (next : S → A → S)
    (r : S → A → S → K) (πs : List (S → A)) (s : S) :
    horizonPolicyValue (fun v s' => v s') next r πs s ≤
      horizonBackwardValue (fun v s' => v s') next r πs.length s :=
  horizonPolicyValue_le_backwardValue _ next r (fun _ _ _ _ h => h _) πs s

/-- Any horizon, expectation: for a transition kernel with nonnegative entries backward
induction maximises the nested expected reward. -/
theorem horizonPolicyValue_le_backwardValue_expectation [Fintype S] (step : S → A → S → K)
    (hstep : ∀ s a s', 0 ≤ step s a s') (r : S → A → S → K) (πs : List (S → A)) (s : S) :
    horizonPolicyValue (fun v m => ∑ s', m s' * v s') step r πs s ≤
      horizonBackwardValue (fun v m => ∑ s', m s' * v s') step r πs.length s :=
  horizonPolicyValue_le_backwardValue _ step r
    (by
      intro s a v w h
      exact Finset.sum_le_sum fun s' _ => mul_le_mul_of_nonneg_left (h s') (hstep s a s'))
    πs s

end Horizon

end CategoricalDecisionAnalysisProofs
