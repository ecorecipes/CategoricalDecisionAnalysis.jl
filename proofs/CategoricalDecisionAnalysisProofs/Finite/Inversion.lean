import CategoricalDecisionAnalysisProofs.Finite.Pullback
import DecisionAnalysisProofs.Finite.Posterior

/-!
# CategoricalDecisionAnalysisProofs.Finite.Inversion

**C3: Bayesian inversion composes on the support.** Backs component 2 ("conditionals:
Bayesian inversion of a channel against a prior, with the support condition explicit;
inversion of a composite is the composite of inversions") of `CategoricalDecisionAnalysis.jl`,
in the form its revision asks for: conditioning through a sub-stochastic kernel and a
normaliser, "so evidence of probability zero is a value, not an exception".

## Conventions

* `jointInverse p f y x = p x · f x y` is the **unnormalised** inverse of `f` against `p`: a
  sub-stochastic kernel from evidence `y` to hypotheses `x`, whose row sums are the evidence
  probabilities `push p f y` (`sum_jointInverse`). Nothing is divided.
* The normalised inverse is the core's `posterior p f y x = p x · f x y / push p f y`
  (`bayes_invert`). For evidence of probability zero Lean's `x / 0 = 0` makes the row
  **identically zero** (`posterior_eq_zero`); this is the convention under which the
  composition law below holds for every evidence value, and it is the one a Julia
  implementation should use if it returns a matrix rather than `nothing` (a zero column, with
  the normaliser reported beside it).
* Composition is diagrammatic: `garble f g` is `f` then `g`; the inverse of the composite is
  the inverse of `g` (against the pushed prior) followed by the inverse of `f`.

## Results

* **`jointInverse_garble`**: the unnormalised inverse of a composite, with no division:
  `jointInverse p (f ; g) z x = Σ_y g y z · jointInverse p f y x`.
* **`signalProbability_mul_posterior`**: normaliser times posterior is the joint inverse,
  including at evidence of probability zero (for a nonnegative prior and kernel).
* **C3**, **`posterior_garble`**: for a nonnegative prior and a nonnegative first kernel,
  `posterior p (f ; g) = posterior (push p f) g ; posterior p f` as kernels, at **every**
  evidence value. The intermediate values `y` of probability zero drop out of the sum; that
  is the content of "on the support", and it is where nonnegativity is used.
* **`posterior_garble_normalised`**: at evidence of positive probability the composite
  inverse is a probability vector.

Not claimed: uniqueness of the inverse off the support (any row would do there; the zero row
is chosen); inversion for kernels with negative entries, where the support argument fails.
-/

set_option autoImplicit false
-- One ordered-field context is declared per file; not every theorem uses every instance.
set_option linter.unusedSectionVars false

namespace CategoricalDecisionAnalysisProofs

open DecisionAnalysisProofs Finset

variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
  {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The unnormalised Bayesian inverse of `f` against `p` (the joint, read from evidence to
hypothesis): `jointInverse p f y x = p x · f x y`. -/
def jointInverse (p : X → K) (f : X → Y → K) : Y → X → K := fun y x => p x * f x y

/-- The row sums of the unnormalised inverse are the evidence probabilities. -/
theorem sum_jointInverse (p : X → K) (f : X → Y → K) (y : Y) :
    ∑ x, jointInverse p f y x = push p f y := rfl

/-- The core's posterior is the unnormalised inverse divided by the evidence probability. -/
theorem posterior_eq_jointInverse_div (p : X → K) (f : X → Y → K) (y : Y) (x : X) :
    posterior p f y x = jointInverse p f y x / push p f y := rfl

/-- The unnormalised inverse of a composite: no division, no support condition. -/
theorem jointInverse_garble (p : X → K) (f : X → Y → K) (g : Y → Z → K) (z : Z) (x : X) :
    jointInverse p (garble f g) z x = ∑ y, g y z * jointInverse p f y x := by
  simp only [jointInverse, garble, Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => by ring

/-- Evidence of probability zero has a zero joint row, for a nonnegative prior and kernel. -/
theorem jointInverse_eq_zero {p : X → K} (hp : NonnegPrior p) {f : X → Y → K}
    (hf : NonnegKernel f) {y : Y} (h : push p f y = 0) (x : X) : jointInverse p f y x = 0 :=
  (Finset.sum_eq_zero_iff_of_nonneg fun x _ => mul_nonneg (hp x) (hf x y)).mp h x
    (Finset.mem_univ x)

/-- Evidence of probability zero has a zero posterior row: the value returned instead of an
error. -/
theorem posterior_eq_zero (p : X → K) (f : X → Y → K) {y : Y} (h : push p f y = 0) (x : X) :
    posterior p f y x = 0 := by
  unfold posterior
  rw [show signalProbability p f y = 0 from h, div_zero]

/-- Normaliser times posterior is the joint inverse, at every evidence value. -/
theorem signalProbability_mul_posterior {p : X → K} (hp : NonnegPrior p) {f : X → Y → K}
    (hf : NonnegKernel f) (y : Y) (x : X) :
    push p f y * posterior p f y x = jointInverse p f y x := by
  by_cases h : push p f y = 0
  · rw [h, zero_mul, jointInverse_eq_zero hp hf h]
  · unfold posterior jointInverse
    rw [mul_div_cancel₀ _ h]

/-- **C3.** Bayesian inversion composes: the posterior of a composite `f ; g` is the posterior
of `g` against the pushed prior, followed by the posterior of `f`. It holds at every evidence
value, with zero rows at evidence of probability zero. -/
theorem posterior_garble {p : X → K} (hp : NonnegPrior p) {f : X → Y → K} (hf : NonnegKernel f)
    (g : Y → Z → K) :
    posterior p (garble f g) = garble (posterior (push p f) g) (posterior p f) := by
  funext z x
  have hm : signalProbability (push p f) g z = signalProbability p (garble f g) z :=
    (congrFun (push_garble p f g) z).symm
  have hterm : ∀ y, posterior (push p f) g z y * posterior p f y x =
      p x * (f x y * g y z) / signalProbability p (garble f g) z := by
    intro y
    unfold posterior
    rw [hm]
    by_cases hy : signalProbability p f y = 0
    · have h0 : p x * f x y = 0 := jointInverse_eq_zero hp hf hy x
      rw [hy, div_zero, mul_zero, ← mul_assoc, h0, zero_mul, zero_div]
    · rw [div_mul_div_comm,
        show signalProbability p f y * g y z * (p x * f x y) =
          p x * (f x y * g y z) * signalProbability p f y by ring,
        mul_div_mul_right _ _ hy]
  change p x * garble f g x z / signalProbability p (garble f g) z =
    ∑ y, posterior (push p f) g z y * posterior p f y x
  rw [Finset.sum_congr rfl fun y _ => hterm y]
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  rfl

/-- At evidence of positive probability the composite inverse is normalised. -/
theorem posterior_garble_normalised {p : X → K} (hp : NonnegPrior p) {f : X → Y → K}
    (hf : NonnegKernel f) (g : Y → Z → K) {z : Z} (h : push p (garble f g) z ≠ 0) :
    ∑ x, garble (posterior (push p f) g) (posterior p f) z x = 1 := by
  rw [← posterior_garble hp hf g]
  exact posterior_normalised p (garble f g) h

end CategoricalDecisionAnalysisProofs
