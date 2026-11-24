import CategoricalDecisionAnalysisProofs.Finite.Sequential
import DecisionAnalysisProofs.Finite.Problem
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum

/-!
# CategoricalDecisionAnalysisProofs.Finite.BackwardInductionFails

**C7c: rules for which backward induction is strictly suboptimal.** Backs the refusal of the
selection-function product of `CategoricalDecisionAnalysis.jl` for `CVaR` and
`MinimaxRegret` (the per-rule flag "admits backward induction" is `false` for both), and
supplies the two fixtures for the planned test "naive backward induction disagrees with
exhaustive policy search".

## Conventions

* `cvar α p x` is the tail mean of a **utility** at tail probability `α`, in the
  Rockafellar-Uryasev form restricted to the atoms:
  `max_i (x i − (Σ_j p j · max(x i − x j, 0)) / α)`. The docstring of `CVaR` in
  `DecisionAnalysis.jl` states that its sorted-tail value equals the Rockafellar-Uryasev
  optimum; that equality, and the fact that the optimum over all thresholds is attained at an
  atom, are **not** proved here. The numbers below (`1`, `4/3`, `14/3`, `5`) are the
  sorted-tail values as well, which the Julia fixture can confirm.
* The CVaR problem: a fair coin `x₁` decides the first reward (`0` or `10`); then the agent
  chooses `safe` (`1` for sure) or `risky` (`0` or `4` on a second fair coin `x₂`). Level
  `α = 3/4`. Backward induction scores the second-stage choice by the CVaR of the
  second-stage reward given `x₁`; the flat value of a policy is the CVaR of the total reward
  over the four trajectories.
* The minimax-regret problem: two states; the agent chooses `stop` or `continue`, and after
  `continue` chooses `b` or `c`. Regret is the core's `regret` (relative to the menu at
  hand). Backward induction applies the rule to the menu `{b, c}` and then to
  `{stop, winner}`; the flat rule applies it to the menu of all three plans.

## Results

* **`cvar_backward_induction_suboptimal`**: every policy that backward induction can return
  (it is unique: `risky` at both `x₁`) has flat CVaR `14/3`, strictly below the `5` of the
  policy "risky after the low reward, safe after the high one".
* **`cvar_stage_strict`**, **`cvar_flat_backward`**, **`cvar_flat_better`**: the three
  numbers.
* **`minimaxRegret_backward_induction_suboptimal`**: backward induction returns `b`
  (strictly, at both stages), whose maximum regret in the full menu is `9`; the minimax
  regret of the full menu is `6`, attained by `c`.

* **`cvar_two_step_ne_one_step`**: the condition CVaR fails is the algebra law
  (`expect_bind` of `UncertaintyAlgebra`): aggregating the better policy's reward in two
  steps gives `41/9`, in one step `5`.

CVaR is monotone and commutes with adding a constant; those two conditions are not the ones
that fail (this remark is not a theorem here). Minimax regret fails earlier: its score is not
a function of the action's own outcomes at all, since it depends on the menu (the core's
`minimaxRegret_violates_iia`).

Not claimed: that no reformulation makes these rules dynamically consistent (nested risk
measures do, and are a different rule); anything for other levels `α`.
-/

set_option autoImplicit false
-- One ordered-field context is declared per file; not every theorem uses every instance.
set_option linter.unusedSectionVars false

namespace CategoricalDecisionAnalysisProofs

open DecisionAnalysisProofs Finset

section Cvar

variable {ι κ K : Type} [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ] [Field K]
  [LinearOrder K] [IsStrictOrderedRing K]

/-- `CVaR(α)` of the utility `x` under the weights `p`, as the Rockafellar-Uryasev objective
maximised over the atoms of `x`. -/
def cvar (α : K) (p x : ι → K) : K :=
  maxOver fun i => x i - (∑ j, p j * max (x i - x j) 0) / α

/-- A maximum over a product is an iterated maximum. -/
theorem maxOver_prod (f : ι × κ → K) : maxOver f = maxOver fun i => maxOver fun j => f (i, j) := by
  apply le_antisymm
  · exact maxOver_le fun ⟨i, j⟩ =>
      (le_maxOver (fun j => f (i, j)) j).trans (le_maxOver (fun i => maxOver fun j => f (i, j)) i)
  · exact maxOver_le fun i => maxOver_le fun j => le_maxOver f (i, j)

end Cvar

/-! ### CVaR -/

/-- The first reward: `0` after `x₁ = 0`, `10` after `x₁ = 1`. -/
def cvarReward₁ : Fin 2 → ℚ
  | 0 => 0 | 1 => 10

/-- The second reward: action `0` (`safe`) pays `1`; action `1` (`risky`) pays `0` or `4`. -/
def cvarReward₂ : Fin 2 → Fin 2 → ℚ
  | 0, _ => 1
  | 1, 0 => 0 | 1, 1 => 4

/-- A fair coin. -/
def fairCoin : Fin 2 → ℚ := fun _ => 1/2

/-- The score backward induction gives the second-stage action `a₂` (the same at both `x₁`,
because CVaR commutes with adding the first reward). -/
def cvarStageScore (a₂ : Fin 2) : ℚ := cvar (3/4) fairCoin (cvarReward₂ a₂)

/-- The flat value of the policy `π`: the CVaR of the total reward over the four equally
likely trajectories `(x₁, x₂)`. -/
def cvarFlatValue (π : Fin 2 → Fin 2) : ℚ :=
  cvar (3/4) (fun t : Fin 2 × Fin 2 => fairCoin t.1 * fairCoin t.2)
    fun t => cvarReward₁ t.1 + cvarReward₂ (π t.1) t.2

/-- The policy backward induction returns: `risky` at both `x₁`. -/
def cvarBackwardPolicy : Fin 2 → Fin 2 := fun _ => 1

/-- A better policy: `risky` after the low reward, `safe` after the high one. -/
def cvarBetterPolicy : Fin 2 → Fin 2
  | 0 => 1 | 1 => 0

/-- At the second stage `risky` (`4/3`) strictly beats `safe` (`1`). -/
theorem cvar_stage_strict : cvarStageScore 0 = 1 ∧ cvarStageScore 1 = 4/3 := by
  constructor <;>
    norm_num [cvarStageScore, cvar, maxOver_fin_two, Fin.sum_univ_two, cvarReward₂, fairCoin]

theorem cvar_flat_backward : cvarFlatValue cvarBackwardPolicy = 14/3 := by
  norm_num [cvarFlatValue, cvar, maxOver_prod, Fintype.sum_prod_type, maxOver_fin_two,
    Fin.sum_univ_two, cvarReward₁, cvarReward₂, fairCoin, cvarBackwardPolicy]

theorem cvar_flat_better : cvarFlatValue cvarBetterPolicy = 5 := by
  norm_num [cvarFlatValue, cvar, maxOver_prod, Fintype.sum_prod_type, maxOver_fin_two,
    Fin.sum_univ_two, cvarReward₁, cvarReward₂, fairCoin, cvarBetterPolicy]

/-- **C7c**, CVaR. Every policy that is optimal at each second-stage decision (every policy
backward induction can return) has a strictly smaller CVaR of total reward than another
policy. -/
theorem cvar_backward_induction_suboptimal (π : Fin 2 → Fin 2)
    (hπ : ∀ x₁ a₂, cvarStageScore a₂ ≤ cvarStageScore (π x₁)) :
    cvarFlatValue π < cvarFlatValue cvarBetterPolicy := by
  have h : π = cvarBackwardPolicy := by
    funext x₁
    have h1 := hπ x₁ 1
    obtain h0 | h0 : π x₁ = 0 ∨ π x₁ = 1 := by
      generalize π x₁ = y
      fin_cases y <;> simp
    · rw [h0, cvar_stage_strict.1, cvar_stage_strict.2] at h1
      norm_num at h1
    · exact h0
  rw [h, cvar_flat_backward, cvar_flat_better]
  norm_num

/-- The algebra law fails for CVaR: for the better policy, aggregating in two steps (CVaR of
the first reward plus the second-stage CVaR) gives `41/9`, while aggregating the total reward
in one step gives `5`. Backward induction therefore values that policy below its own
(`41/9 < 14/3`) although its flat value is higher. -/
theorem cvar_two_step_ne_one_step :
    cvar (3/4) fairCoin (fun x₁ => cvarReward₁ x₁ + cvarStageScore (cvarBetterPolicy x₁)) = 41/9 ∧
      cvarFlatValue cvarBetterPolicy = 5 := by
  refine ⟨?_, cvar_flat_better⟩
  have h0 : cvarStageScore (cvarBetterPolicy 0) = 4/3 := cvar_stage_strict.2
  have h1 : cvarStageScore (cvarBetterPolicy 1) = 1 := cvar_stage_strict.1
  unfold cvar
  rw [maxOver_fin_two]
  simp only [Fin.sum_univ_two, h0, h1]
  norm_num [cvarReward₁, fairCoin]

/-! ### Minimax regret -/

/-- Payoffs of the three plans over two states: `0 = stop`, `1 = continue then b`,
`2 = continue then c`. -/
def regretPlans : Fin 3 → Fin 2 → ℚ
  | 0, 0 => 0  | 0, 1 => 9
  | 1, 0 => 10 | 1, 1 => 0
  | 2, 0 => 6  | 2, 1 => 3

/-- The second-stage menu `{b, c}`. -/
def regretStageTwo : Fin 2 → Fin 2 → ℚ
  | 0 => regretPlans 1 | 1 => regretPlans 2

/-- The first-stage menu `{stop, b}`, after the second stage has selected `b`. -/
def regretStageOne : Fin 2 → Fin 2 → ℚ
  | 0 => regretPlans 0 | 1 => regretPlans 1

/-- **C7c**, minimax regret. Backward induction selects `b` at the second stage (maximum
regret `3` against `4`) and again at the first (`9` against `10`); in the menu of all plans
`b` has maximum regret `9`, while the minimax regret is `6`. -/
theorem minimaxRegret_backward_induction_suboptimal :
    (maxRegret regretStageTwo 0 = 3 ∧ maxRegret regretStageTwo 1 = 4) ∧
    (maxRegret regretStageOne 0 = 10 ∧ maxRegret regretStageOne 1 = 9) ∧
    maxRegret regretPlans 1 = 9 ∧ minimaxRegretValue regretPlans = 6 ∧
    IsMinimaxRegret regretPlans 2 := by
  have h0 : maxRegret regretPlans 0 = 10 := by
    norm_num [maxRegret, regret, maxOver_fin_two, maxOver_fin_three, regretPlans]
  have h1 : maxRegret regretPlans 1 = 9 := by
    norm_num [maxRegret, regret, maxOver_fin_two, maxOver_fin_three, regretPlans]
  have h2 : maxRegret regretPlans 2 = 6 := by
    norm_num [maxRegret, regret, maxOver_fin_two, maxOver_fin_three, regretPlans]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, h1, ?_, ?_⟩
  · norm_num [maxRegret, regret, maxOver_fin_two, regretStageTwo, regretPlans]
  · norm_num [maxRegret, regret, maxOver_fin_two, regretStageTwo, regretPlans]
  · norm_num [maxRegret, regret, maxOver_fin_two, regretStageOne, regretPlans]
  · norm_num [maxRegret, regret, maxOver_fin_two, regretStageOne, regretPlans]
  · unfold minimaxRegretValue
    rw [minOver_fin_three, h0, h1, h2]
    norm_num
  · intro a'
    rw [h2]
    fin_cases a'
    · exact h0 ▸ (by norm_num)
    · exact h1 ▸ (by norm_num)
    · exact h2 ▸ le_refl _

end CategoricalDecisionAnalysisProofs
