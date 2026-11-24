import CategoricalDecisionAnalysisProofs.Finite.KernelFidelity
import DecisionAnalysisProofs.Certificate.Check

/-!
# CategoricalDecisionAnalysisProofs.Certificate.Fidelity

The checker for `"fidelity-chain-certificate/1"` (documented in `docs/src/certificates.md`): the
fidelity read-off of `CategoricalDecisionAnalysis.jl` for a chain of boxes, each replaced by an
approximation (an emulator, a coarser model) with a stated total-variation error.

## The document

The number of states `n`; a list of boxes, each with the exact kernel, the approximate kernel
(both `n × n` matrices `M[y][x] = P(y | x)`, column-stochastic, as `kernel_matrix` in
FiniteKernels.jl) and the claimed error; the payoff range `B`; and the claimed loss bound.

`RawFidelity.Accepts` checks the shapes, that every kernel is column-stochastic, that each
claimed error bounds the total variation between corresponding columns of the two kernels,
that `B ≥ 0`, and that the bound is `2 · B · Σ errors`.

* **`RawFidelity.accepts_sound`**: for an accepted document, every payoff table on the `n`
  states whose rows have range at most `B`, every probability prior and every action that is
  Bayes for the approximate chain: that action falls short of the best under the exact chain
  by at most the claimed bound (T11 with T10).

The check is sound and not tight: the claimed errors may exceed the true total variations,
and the additive bound may exceed the true loss.

Not claimed: diagrams other than a chain on one state space; correctness of the JSON parser
in `CheckCertificate.lean`, which is trusted.
-/

set_option autoImplicit false

namespace CategoricalDecisionAnalysisProofs.Certificate

open DecisionAnalysisProofs DecisionAnalysisProofs.Certificate CategoricalDecisionAnalysisProofs

/-- One box of a decoded `"fidelity-chain-certificate/1"` document. -/
structure RawBox where
  /-- The exact kernel, `exact[y][x] = P(y | x)`. -/
  exact : List (List ℚ)
  /-- The approximate kernel, in the same layout. -/
  approx : List (List ℚ)
  /-- The claimed bound on the total variation between corresponding columns. -/
  error : ℚ

/-- A decoded `"fidelity-chain-certificate/1"` document. -/
structure RawFidelity where
  /-- The number of states of every box. -/
  nStates : ℕ
  /-- The boxes, first box first. -/
  boxes : List RawBox
  /-- The payoff range `B`. -/
  range : ℚ
  /-- The claimed bound on the decision loss. -/
  bound : ℚ

/-- A box as a triple (exact kernel, approximate kernel, error). -/
def RawBox.triple (n : ℕ) (b : RawBox) :
    (Fin n → Fin n → ℚ) × (Fin n → Fin n → ℚ) × ℚ :=
  (kernelOf b.exact n n, kernelOf b.approx n n, b.error)

/-- The boxes as triples. -/
def RawFidelity.triples (r : RawFidelity) :
    List ((Fin r.nStates → Fin r.nStates → ℚ) × (Fin r.nStates → Fin r.nStates → ℚ) × ℚ) :=
  r.boxes.map (RawBox.triple r.nStates)

/-- What the fidelity-chain checker decides. -/
def RawFidelity.Accepts (r : RawFidelity) : Prop :=
  (∀ b ∈ r.boxes, rect b.exact r.nStates r.nStates = true ∧
    rect b.approx r.nStates r.nStates = true) ∧
  (∀ t ∈ r.triples, StochasticKernel t.1 ∧ StochasticKernel t.2.1 ∧
    ∀ x, totalVariation (t.1 x) (t.2.1 x) ≤ t.2.2) ∧
  0 ≤ r.range ∧ r.bound = 2 * r.range * (r.triples.map fun t => t.2.2).sum

instance RawFidelity.instDecidableAccepts (r : RawFidelity) : Decidable r.Accepts := by
  unfold RawFidelity.Accepts; infer_instance

/-- The fidelity-chain checker run by `lake exe check_certificate`. -/
def checkFidelity (r : RawFidelity) : Bool := decide r.Accepts

/-- **Soundness of the fidelity-chain checker.** If it accepts, then for every payoff table
whose rows have range at most `B`, every probability prior and every action that is Bayes for
the approximate chain, the loss under the exact chain is at most the claimed bound. -/
theorem RawFidelity.accepts_sound {r : RawFidelity} (h : checkFidelity r = true) (m : ℕ)
    (u : Fin (m + 1) → Fin r.nStates → ℚ) (hB : ∀ a x x', u a x - u a x' ≤ r.range)
    (p₀ : Fin r.nStates → ℚ) (hp₀ : NonnegPrior p₀) (hp₀1 : NormalisedPrior p₀)
    (a : Fin (m + 1))
    (ha : IsBayes u (push p₀ (chain (r.triples.map fun t => t.2.1))) a) :
    actNowValue u (push p₀ (chain (r.triples.map fun t => t.1))) -
        expectedUtility u (push p₀ (chain (r.triples.map fun t => t.1))) a ≤ r.bound := by
  have h' : r.Accepts := of_decide_eq_true h
  obtain ⟨-, hboxes, hB0, hbound⟩ := h'
  have hloss := decision_loss_chain_le (p₀ := p₀) (p₀' := p₀) r.triples hp₀1 hp₀ hp₀1 hboxes
    hB0 hB (ε₀ := 0) (totalVariation_self p₀).le ha
  rw [zero_add] at hloss
  rw [hbound]
  exact hloss

end CategoricalDecisionAnalysisProofs.Certificate
