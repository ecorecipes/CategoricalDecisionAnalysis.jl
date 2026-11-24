import CategoricalDecisionAnalysisProofs.Finite.PolicyProgramme
import DecisionAnalysisProofs.Certificate.Check

/-!
# CategoricalDecisionAnalysisProofs.Certificate.Policy

The checker for `"policy-certificate/1"` (documented in `docs/src/certificates.md`): what the
diagram-to-JuMP interpreter of `CategoricalDecisionAnalysis.jl` can export after solving the
one-decision programme, so that the optimum is trusted without trusting the solver.

## The document

The payoff table (rows are actions, columns are states), the prior, the likelihood (rows are
signals, columns are states, as in the core's certificates), the policy matrix
`policy[a][z] = P(a | z)` (rows are actions, columns are signals: column-stochastic), the dual
vector (one entry per signal) and the claimed optimal value.

`RawPolicy.Accepts` checks the shapes, that there is at least one action, that the policy is
column-stochastic, that the dual vector is feasible (`dual[z] ≥ Σ_θ p θ · e θ z · u a θ` for
every action), and that the policy's objective and the dual objective both equal the claimed
value.

* **`RawPolicy.accepts_sound`**: an accepted document proves that the claimed value is the
  core's `valueWithInformation` and that no column-stochastic policy has a larger objective.

The check is sound and, for this programme, complete in the sense that an optimal pair always
exists (`policyProgramme_optimum`, `dualFeasible_maxOver`): a deterministic optimal policy
and the column maxima of the objective coefficients. It does not require the prior or the
likelihood to be normalised; the theorem holds without.

Not claimed: correctness of the JSON parser in `CheckCertificate.lean`, which is trusted.
-/

set_option autoImplicit false

namespace CategoricalDecisionAnalysisProofs.Certificate

open DecisionAnalysisProofs DecisionAnalysisProofs.Certificate CategoricalDecisionAnalysisProofs

/-- A decoded `"policy-certificate/1"` document. -/
structure RawPolicy where
  /-- The payoff table: rows are actions, columns are states. -/
  payoff : List (List ℚ)
  /-- The prior over states. -/
  prior : List ℚ
  /-- The likelihood: rows are signals, columns are states. -/
  likelihood : List (List ℚ)
  /-- The policy `policy[a][z] = P(a | z)`: rows are actions, columns are signals. -/
  policy : List (List ℚ)
  /-- The dual vector, one entry per signal. -/
  dual : List ℚ
  /-- The claimed optimal value. -/
  value : ℚ

/-- The payoff table `u a θ`. -/
def RawPolicy.u (r : RawPolicy) : Fin r.payoff.length → Fin r.prior.length → ℚ :=
  table r.payoff r.payoff.length r.prior.length

/-- The prior. -/
def RawPolicy.p (r : RawPolicy) : Fin r.prior.length → ℚ := vec r.prior r.prior.length

/-- The experiment `e θ z = likelihood[z][θ]`. -/
def RawPolicy.e (r : RawPolicy) : Fin r.prior.length → Fin r.likelihood.length → ℚ :=
  kernelOf r.likelihood r.prior.length r.likelihood.length

/-- The policy `π z a = policy[a][z]`. -/
def RawPolicy.π (r : RawPolicy) : Fin r.likelihood.length → Fin r.payoff.length → ℚ :=
  kernelOf r.policy r.likelihood.length r.payoff.length

/-- The dual vector. -/
def RawPolicy.v (r : RawPolicy) : Fin r.likelihood.length → ℚ :=
  vec r.dual r.likelihood.length

instance {A Θ Z : Type} [Fintype A] [Fintype Θ] [Fintype Z] (u : A → Θ → ℚ) (p : Θ → ℚ)
    (e : Θ → Z → ℚ) (v : Z → ℚ) : Decidable (DualFeasible u p e v) := by
  unfold DualFeasible; infer_instance

/-- What the policy-certificate checker decides. -/
def RawPolicy.Accepts (r : RawPolicy) : Prop :=
  0 < r.payoff.length ∧
  rect r.payoff r.payoff.length r.prior.length = true ∧
  rect r.likelihood r.likelihood.length r.prior.length = true ∧
  rect r.policy r.payoff.length r.likelihood.length = true ∧
  r.dual.length = r.likelihood.length ∧
  StochasticKernel r.π ∧ DualFeasible r.u r.p r.e r.v ∧
  policyValue r.u r.p r.e r.π = r.value ∧ ∑ z, r.v z = r.value

instance RawPolicy.instDecidableAccepts (r : RawPolicy) : Decidable r.Accepts := by
  unfold RawPolicy.Accepts; infer_instance

/-- The policy-certificate checker run by `lake exe check_certificate`. -/
def checkPolicy (r : RawPolicy) : Bool := decide r.Accepts

/-- An accepted document has at least one action. -/
theorem RawPolicy.nonempty_of_accepts {r : RawPolicy} (h : checkPolicy r = true) :
    Nonempty (Fin r.payoff.length) :=
  ⟨⟨0, (of_decide_eq_true h : r.Accepts).1⟩⟩

/-- **Soundness of the policy-certificate checker.** If it accepts, the claimed value is the
value with information of the problem, the policy attains it, and no column-stochastic policy
has a larger objective. -/
theorem RawPolicy.accepts_sound {r : RawPolicy} [Nonempty (Fin r.payoff.length)]
    (h : checkPolicy r = true) :
    r.value = valueWithInformation r.u r.p r.e ∧ policyValue r.u r.p r.e r.π = r.value ∧
      ∀ π' : Fin r.likelihood.length → Fin r.payoff.length → ℚ, StochasticKernel π' →
        policyValue r.u r.p r.e π' ≤ r.value := by
  have h' : r.Accepts := of_decide_eq_true h
  obtain ⟨-, -, -, -, -, hπ, hv, hval, hdual⟩ := h'
  have hs := policy_certificate_sound r.u r.p r.e hπ hv (hval.trans hdual.symm)
  exact ⟨hval.symm.trans hs.1, hval, fun π' hπ' => hval ▸ hs.2 π' hπ'⟩

end CategoricalDecisionAnalysisProofs.Certificate
