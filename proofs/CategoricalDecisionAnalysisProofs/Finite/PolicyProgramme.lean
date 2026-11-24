import CategoricalDecisionAnalysisProofs.Finite.Pullback
import DecisionAnalysisProofs.Finite.Affine

/-!
# CategoricalDecisionAnalysisProofs.Finite.PolicyProgramme

**Compiler correctness for the diagram-to-JuMP interpreter, one decision.** Backs the planned
interpreter "compile a decision diagram to a JuMP model" of `CategoricalDecisionAnalysis.jl`
in its linear case (a single decision with a fixed information structure), and the plan's proof
obligation for it: *the compiled programme's feasible set is in bijection with the diagram's
strategies, and its objective equals expected utility*. It also backs the planned check "the
compiled model's optimum equals the core's exact answer", and proves sound the certificate
`"policy-certificate/1"` of `SCHEMAS-PROPOSED.md`.

## Conventions

* The diagram is `Belief ; Channel ; Policy ; Utility`: a prior `p` on `Θ`, an experiment
  `e : Θ → Z → K`, a decision box that sees `z`, and a payoff table `u : A → Θ → K`.
* The decision variables are a table `π : Z → A → K`, `π z a = P(a | z)`; the Julia variable
  is `policy[a, z]`, a **column-stochastic** matrix (columns are signals), as the likelihood
  is. The constraints are `π z a ≥ 0` and `Σ_a π z a = 1` for each `z`, that is
  `StochasticKernel π` (the core's predicate): the feasible set **is** the set of randomised
  strategies. The binary feasible points are the deterministic strategies
  (`isBinaryPolicy_iff_exists_deterministic`, `deterministic_policy_injective`).
* The objective is `policyValue u p e π = Σ_z Σ_a π z a · signalValue u p e z a`, linear in
  `π`, with coefficients the core's joint-form objectives `c[a, z] = Σ_θ p θ · e θ z · u a θ`.
* The dual programme has one variable `v z` per signal, constraints
  `v z ≥ signalValue u p e z a` for every action (`DualFeasible`), and objective `Σ_z v z`.

## Results

* **`policyValue_eq_expectedUtility`**: the objective is the expected utility of the
  strategy, `Σ_θ p θ · Σ_a (e ; π) θ a · u a θ`: what `evaluate` computes on the diagram.
  **`policyValue_deterministic`**: for a deterministic strategy `d` it is
  `Σ_z signalValue z (d z)`.
* **`policyValue_le_valueWithInformation`**, **`exists_deterministic_policyValue_eq`**,
  **`policyProgramme_optimum`**: the optimum of the programme is the core's
  `valueWithInformation`, and it is attained at a deterministic strategy (so the linear
  relaxation is exact and binary variables are not needed for one decision).
* **`policyValue_le_dual`** (weak duality), **`dualFeasible_maxOver`** and
  **`sum_maxOver_eq_valueWithInformation`** (strong duality, by exhibiting the optimal dual).
* **`policy_certificate_sound`**: a feasible `π` and a dual feasible `v` with equal objectives
  certify that both are optimal and that the common value is `valueWithInformation`.

Not claimed: several decisions, with or without perfect recall (the mixed-integer case);
extra constraints (budgets, chance constraints), under which a deterministic optimum need not
exist; gluing of open diagrams; anything about JuMP, the solver or floating point.
-/

set_option autoImplicit false
-- One ordered-field context is declared per file; not every theorem uses every instance.
set_option linter.unusedSectionVars false

namespace CategoricalDecisionAnalysisProofs

open DecisionAnalysisProofs Finset

variable {A Θ Z : Type} [Fintype A] [Nonempty A] [Fintype Θ] [Fintype Z]
  {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The objective of the compiled programme at the policy `π` (`π z a = P(a | z)`):
`Σ_z Σ_a π z a · c z a` with `c z a = signalValue u p e z a`. -/
def policyValue (u : A → Θ → K) (p : Θ → K) (e : Θ → Z → K) (π : Z → A → K) : K :=
  ∑ z, ∑ a, π z a * signalValue u p e z a

/-- A feasible point of the dual programme: `v z` bounds every action's objective after `z`. -/
def DualFeasible (u : A → Θ → K) (p : Θ → K) (e : Θ → Z → K) (v : Z → K) : Prop :=
  ∀ z a, signalValue u p e z a ≤ v z

omit [Nonempty A] in
/-- The objective of the programme is the expected utility of the strategy: the prior, then
the experiment, then the policy, against the payoff table. -/
theorem policyValue_eq_expectedUtility (u : A → Θ → K) (p : Θ → K) (e : Θ → Z → K)
    (π : Z → A → K) :
    policyValue u p e π = ∑ θ, p θ * ∑ a, garble e π θ a * u a θ := by
  unfold policyValue signalValue garble
  have h1 : ∀ z, ∑ a, π z a * ∑ θ, p θ * e θ z * u a θ =
      ∑ θ, ∑ a, p θ * (e θ z * π z a * u a θ) := by
    intro z
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun θ _ => by ring
  have h2 : ∀ θ, p θ * ∑ a, (∑ z, e θ z * π z a) * u a θ =
      ∑ z, ∑ a, p θ * (e θ z * π z a * u a θ) := by
    intro θ
    rw [Finset.sum_comm, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_congr rfl fun z _ => h1 z, Finset.sum_comm,
    Finset.sum_congr rfl fun θ _ => h2 θ]

omit [Nonempty A] in
/-- The objective at a deterministic strategy. -/
theorem policyValue_deterministic [DecidableEq A] (u : A → Θ → K) (p : Θ → K) (e : Θ → Z → K)
    (d : Z → A) : policyValue u p e (deterministic d) = ∑ z, signalValue u p e z (d z) := by
  unfold policyValue
  exact Finset.sum_congr rfl fun z _ => by simp [deterministic]

/-- Every feasible policy has objective at most the value with information. -/
theorem policyValue_le_valueWithInformation (u : A → Θ → K) (p : Θ → K) (e : Θ → Z → K)
    {π : Z → A → K} (hπ : StochasticKernel π) :
    policyValue u p e π ≤ valueWithInformation u p e :=
  Finset.sum_le_sum fun z _ =>
    calc ∑ a, π z a * signalValue u p e z a
        ≤ ∑ a, π z a * maxOver (signalValue u p e z) := Finset.sum_le_sum fun a _ =>
          mul_le_mul_of_nonneg_left (le_maxOver (signalValue u p e z) a) (hπ.1 z a)
      _ = maxOver (signalValue u p e z) := by rw [← Finset.sum_mul, hπ.2 z, one_mul]

/-- The value with information is attained by a deterministic strategy. -/
theorem exists_deterministic_policyValue_eq [DecidableEq A] (u : A → Θ → K) (p : Θ → K)
    (e : Θ → Z → K) :
    ∃ d : Z → A, policyValue u p e (deterministic d) = valueWithInformation u p e := by
  choose d hd using fun z => exists_eq_maxOver (signalValue u p e z)
  refine ⟨d, ?_⟩
  rw [policyValue_deterministic]
  exact Finset.sum_congr rfl fun z _ => (hd z).symm

/-- **Compiler correctness, one decision.** The linear programme over column-stochastic
policies has optimum `valueWithInformation u p e`: a feasible (deterministic) policy attains
it and no feasible policy exceeds it. -/
theorem policyProgramme_optimum [DecidableEq A] (u : A → Θ → K) (p : Θ → K) (e : Θ → Z → K) :
    (∃ d : Z → A, StochasticKernel (deterministic d : Z → A → K) ∧
        policyValue u p e (deterministic d) = valueWithInformation u p e) ∧
      ∀ π : Z → A → K, StochasticKernel π →
        policyValue u p e π ≤ valueWithInformation u p e := by
  obtain ⟨d, hd⟩ := exists_deterministic_policyValue_eq u p e
  exact ⟨⟨d, stochasticKernel_deterministic d, hd⟩,
    fun π hπ => policyValue_le_valueWithInformation u p e hπ⟩

/-! ### The dual programme and the certificate -/

/-- Weak duality: a feasible policy is worth at most any dual feasible objective. -/
theorem policyValue_le_dual (u : A → Θ → K) (p : Θ → K) (e : Θ → Z → K) {π : Z → A → K}
    (hπ : StochasticKernel π) {v : Z → K} (hv : DualFeasible u p e v) :
    policyValue u p e π ≤ ∑ z, v z :=
  Finset.sum_le_sum fun z _ =>
    calc ∑ a, π z a * signalValue u p e z a
        ≤ ∑ a, π z a * v z := Finset.sum_le_sum fun a _ =>
          mul_le_mul_of_nonneg_left (hv z a) (hπ.1 z a)
      _ = v z := by rw [← Finset.sum_mul, hπ.2 z, one_mul]

/-- The pointwise maxima are dual feasible. -/
theorem dualFeasible_maxOver (u : A → Θ → K) (p : Θ → K) (e : Θ → Z → K) :
    DualFeasible u p e fun z => maxOver (signalValue u p e z) :=
  fun z a => le_maxOver (signalValue u p e z) a

/-- Strong duality: the optimal dual objective is the value with information. -/
theorem sum_maxOver_eq_valueWithInformation (u : A → Θ → K) (p : Θ → K) (e : Θ → Z → K) :
    ∑ z, maxOver (signalValue u p e z) = valueWithInformation u p e := rfl

/-- Every dual feasible objective bounds the value with information from above. -/
theorem valueWithInformation_le_dual (u : A → Θ → K) (p : Θ → K) (e : Θ → Z → K) {v : Z → K}
    (hv : DualFeasible u p e v) : valueWithInformation u p e ≤ ∑ z, v z :=
  Finset.sum_le_sum fun z _ => maxOver_le (hv z)

/-- **Soundness of the policy certificate.** A feasible policy and a dual feasible vector with
equal objectives certify the optimum: the policy's value is the value with information, and
no feasible policy does better. -/
theorem policy_certificate_sound (u : A → Θ → K) (p : Θ → K) (e : Θ → Z → K) {π : Z → A → K}
    (hπ : StochasticKernel π) {v : Z → K} (hv : DualFeasible u p e v)
    (heq : policyValue u p e π = ∑ z, v z) :
    policyValue u p e π = valueWithInformation u p e ∧
      ∀ π' : Z → A → K, StochasticKernel π' → policyValue u p e π' ≤ policyValue u p e π :=
  have h : policyValue u p e π = valueWithInformation u p e :=
    le_antisymm (policyValue_le_valueWithInformation u p e hπ)
      (heq ▸ valueWithInformation_le_dual u p e hv)
  ⟨h, fun _ hπ' => h ▸ policyValue_le_valueWithInformation u p e hπ'⟩

/-! ### Deterministic strategies are the binary feasible points -/

omit [Nonempty A] [Fintype A] in
/-- Distinct deterministic strategies compile to distinct policies. -/
theorem deterministic_policy_injective [DecidableEq A] :
    Function.Injective fun d : Z → A => (deterministic d : Z → A → K) := by
  intro d d' h
  funext z
  have h1 : (deterministic d : Z → A → K) z (d z) = deterministic d' z (d z) :=
    congrFun (congrFun h z) (d z)
  simp only [deterministic, if_true] at h1
  by_contra hne
  rw [if_neg hne] at h1
  exact one_ne_zero h1

omit [Nonempty A] in
/-- **The feasible set and the strategies.** The feasible policies with entries in `{0, 1}`
(the feasible set of the binary formulation) are exactly the deterministic strategies. -/
theorem isBinaryPolicy_iff_exists_deterministic [DecidableEq A] (π : Z → A → K) :
    (StochasticKernel π ∧ ∀ z a, π z a = 0 ∨ π z a = 1) ↔
      ∃ d : Z → A, π = deterministic d := by
  constructor
  · rintro ⟨hπ, hbin⟩
    have hex : ∀ z, ∃ a, π z a = 1 := by
      intro z
      by_contra hno
      have hzero : ∀ a, π z a = 0 := fun a => (hbin z a).resolve_right fun h => hno ⟨a, h⟩
      have hsum := hπ.2 z
      rw [Finset.sum_congr rfl fun a _ => hzero a, Finset.sum_const_zero] at hsum
      exact zero_ne_one hsum
    choose d hd using hex
    refine ⟨d, funext fun z => funext fun a => ?_⟩
    unfold deterministic
    split_ifs with ha
    · rw [ha, hd z]
    · rcases hbin z a with h0 | h1
      · exact h0
      · exfalso
        have hpair : π z a + π z (d z) ≤ ∑ b, π z b := by
          have hsub : ({a, d z} : Finset A) ⊆ Finset.univ := Finset.subset_univ _
          have := Finset.sum_le_sum_of_subset_of_nonneg hsub fun b _ _ => hπ.1 z b
          rwa [Finset.sum_pair ha] at this
        rw [hπ.2 z, h1, hd z] at hpair
        linarith
  · rintro ⟨d, rfl⟩
    refine ⟨stochasticKernel_deterministic d, fun z a => ?_⟩
    unfold deterministic
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl

end CategoricalDecisionAnalysisProofs
