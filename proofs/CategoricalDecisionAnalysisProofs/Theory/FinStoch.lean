import CategoricalDecisionAnalysisProofs.Finite.KernelFidelity
import FiniteKernelsProofs.Theory.FinStoch

/-!
# CategoricalDecisionAnalysisProofs.Theory.FinStoch

**C1 is imported, and C2 is stated against it.** `FiniteKernelsProofs.FinStoch` is the Mathlib
`MarkovCategory` of finite stochastic kernels (proved in `FiniteKernels.jl/proofs`; nothing of
it is reproved here). This module says what the value pullback of
`CategoricalDecisionAnalysis.jl` (component 1) is in that category: a contravariant functor
from `FinStoch` to types, which sends an object to its effects and respects the tensor on
product effects. It is the link between the concrete theorems of `Finite/Pullback.lean`,
which the Julia tests mirror, and the categorical vocabulary of the package's documentation.

## Conventions

* `Effect X` is `X.carrier → ℝ`; `effectPullback f u` is `pullbackD f.val u`.
* `tensorKernel` (`Finite/KernelFidelity.lean`) is `Kernel.tensor` at `K = ℝ`, which is the
  tensor of `FinStoch` on morphisms.

## Results

* **`pullbackD_tensorKernel`** (any ordered field): pulling a product effect `u ⊗ v` back
  along `f ⊗ g` gives the product of the pullbacks. This backs evaluating a tensor of
  pipelines box by box.
* **`effectPullback_id`**, **`effectPullback_comp`**, **`effectPullback_tensor`**,
  **`effectPullback_const`**, **`effectPullback_mono`**: the same facts for morphisms of
  `FinStoch`; the constant law is discard naturality (the Markov axiom) in effect form.
* **`effectFunctor`**: the functor `FinStochᵒᵖ ⥤ Type` they assemble into.

Not claimed: that effects that are not products are respected by the tensor (they are not
determined by their marginals); a functor for `P⁺` or for credal kernels.
-/

set_option autoImplicit false
-- One ordered-field context is declared per file; not every theorem uses every instance.
set_option linter.unusedSectionVars false

namespace CategoricalDecisionAnalysisProofs

open DecisionAnalysisProofs Finset

section Tensor

variable {X₁ X₂ Y₁ Y₂ : Type} [Fintype Y₁] [Fintype Y₂]
  {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The pullback of a product effect along a tensor of kernels is the product of the
pullbacks. -/
theorem pullbackD_tensorKernel (f : X₁ → Y₁ → K) (g : X₂ → Y₂ → K) (u : Y₁ → K) (v : Y₂ → K) :
    pullbackD (tensorKernel f g) (fun t => u t.1 * v t.2) =
      fun s => pullbackD f u s.1 * pullbackD g v s.2 := by
  funext s
  simp only [pullbackD, tensorKernel]
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun y₁ _ => Finset.sum_congr rfl fun y₂ _ => by ring

end Tensor

open CategoryTheory MonoidalCategory FiniteKernelsProofs

variable {X Y Z W : FinStoch}

/-- The effects on an object of `FinStoch`. -/
abbrev Effect (X : FinStoch) : Type := X.carrier → ℝ

/-- Value pullback along a morphism of `FinStoch`. -/
noncomputable def effectPullback (f : X ⟶ Y) (u : Effect Y) : Effect X := pullbackD f.val u

/-- Identity law. -/
theorem effectPullback_id (u : Effect X) : effectPullback (𝟙 X) u = u :=
  pullbackD_identity u

/-- Composition law (contravariant). -/
theorem effectPullback_comp (f : X ⟶ Y) (g : Y ⟶ Z) (u : Effect Z) :
    effectPullback (f ≫ g) u = effectPullback f (effectPullback g u) :=
  pullbackD_garble f.val g.val u

/-- The tensor of `FinStoch` is respected on product effects. -/
theorem effectPullback_tensor (f : X ⟶ Y) (g : Z ⟶ W) (u : Effect Y) (v : Effect W) :
    effectPullback (f ⊗ₘ g) (fun t : Y.carrier × W.carrier => u t.1 * v t.2) =
      fun s : X.carrier × Z.carrier => effectPullback f u s.1 * effectPullback g v s.2 :=
  pullbackD_tensorKernel f.val g.val u v

/-- Constants pull back to constants: discard naturality, in effect form. -/
theorem effectPullback_const (f : X ⟶ Y) (c : ℝ) :
    effectPullback f (fun _ => c) = fun _ => c :=
  pullbackD_const f.2.2 c

/-- Monotonicity. -/
theorem effectPullback_mono (f : X ⟶ Y) {u v : Effect Y} (h : ∀ y, u y ≤ v y)
    (x : X.carrier) : effectPullback f u x ≤ effectPullback f v x :=
  pullbackD_mono f.2.1 h x

/-- **C2**, as a functor on the Markov category of finite stochastic kernels: effects, with
value pullback, form a functor `FinStochᵒᵖ ⥤ Type`. -/
noncomputable def effectFunctor : FinStochᵒᵖ ⥤ Type where
  obj X := Effect X.unop
  map f := ↾(effectPullback f.unop)
  map_id X := by
    ext u x
    exact congrFun (effectPullback_id u) x
  map_comp f g := by
    ext u x
    exact congrFun (effectPullback_comp g.unop f.unop u) x

/-- The functor acts on morphisms by value pullback. -/
theorem effectFunctor_map (f : X ⟶ Y) (u : Effect Y) :
    effectFunctor.map f.op u = effectPullback f u := rfl

end CategoricalDecisionAnalysisProofs
