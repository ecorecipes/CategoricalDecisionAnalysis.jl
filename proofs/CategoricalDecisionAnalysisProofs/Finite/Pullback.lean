import DecisionAnalysisProofs.Finite.Garbling
import Mathlib.Data.Finset.Union
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.Order.Monoid.Unbundled.MinMax

/-!
# CategoricalDecisionAnalysisProofs.Finite.Pullback

**C2, value pullback.** Backs component 1 ("effects and value pullback") and component 3
("uncertainty monads, each with its algebra on ℝ") of `CategoricalDecisionAnalysis.jl`: the
generic function that pulls a utility back along a box of a pipeline, and its three planned
instances `Id`, `D` and `P⁺`.

## Conventions

* An **effect** on a finite type `Y` is a function `u : Y → K` (a utility, a payoff column).
* `UncertaintyAlgebra T R` is the data the generic Julia function needs and nothing more: a
  unit `pure`, a Kleisli extension `bind`, and `expect u m`, the algebra applied to the image
  of `m` under `u`, with the two laws `expect_pure` and `expect_bind`. No monad law is
  assumed, because functoriality of the pullback does not need one. The carrier types are
  finite with decidable equality, as every Julia object is.
* `pullback f u = fun x => expect u (f x)` and `kleisli f g = fun x => bind (f x) g`.
  Composition is in diagrammatic order (`f` first), as `garble` and `Kernel.comp` are.
* The instances: `idAlgebra` (functions; pullback is composition), `distAlgebra`
  (`T X = X → K`, weights; pullback is `pullbackD f u x = Σ_y f x y · u y`, composition is the
  sibling project's `garble`), `minAlgebra` and `maxAlgebra` (`T X` = non-empty finite sets;
  pullback is the minimum or maximum of `u` over the set).
* Nonnegativity and normalisation are **not** part of `distAlgebra`: the functor laws are
  linear algebra and hold for every weight table. Monotonicity needs nonnegative weights and
  preservation of constants needs normalised ones; both are stated as hypotheses.

## Results

* **`UncertaintyAlgebra.pullback_pure`**, **`UncertaintyAlgebra.pullback_kleisli`**: the
  generic contravariant functor laws. They back the property test "functor laws for value
  pullback on random kernels" for every instance at once.
* **`pullbackD_identity`**, **`pullbackD_garble`**, **`pullbackD_mono`**,
  **`pullbackD_const`**, **`pullbackD_deterministic`**: the instance `D` in the form Julia
  computes (a matrix-vector product).
* **`expectedUtility_eq_pullbackD`**, **`expectedUtility_push`**: agreement with the core's
  `expectedUtility`; pulling the payoff back along a kernel is pushing the belief forward.
* **`pullbackMin_identity`**, **`pullbackMin_relComp`**, **`pullbackMin_mono`** and the `Max`
  duals; **`worstCase_eq_pullbackMin`**: the instance `P⁺`, and agreement with the core's
  `worstCase` (the score of `Maximin`).
* **`pullbackMin_le_pullbackD`**: the support map `D → P⁺` is *lax*, not an algebra morphism:
  the worst case over a set containing the support is below the expectation. A pipeline may
  therefore replace an expectation box by a worst-case box as a bound, not as an equality.

Not claimed: the monad laws of `D` or `P⁺`; the credal instance `C` (see `Finite/CredalKernel.lean`
for what holds of it); anything about `RewardKernel` evaluation in CategoricalInfluenceDiagrams.
-/

set_option autoImplicit false
-- One ordered-field context is declared per file; not every theorem uses every instance.
set_option linter.unusedSectionVars false

namespace CategoricalDecisionAnalysisProofs

open DecisionAnalysisProofs Finset

/-! ### The generic statement -/

/-- An uncertainty type constructor `T` with a unit, a Kleisli extension and an algebra on the
value type `R`, presented by `expect u m` ("aggregate the values `u` over the uncertain
outcome `m`"). The Julia generic `pullback(algebra, f, u)` needs exactly this. -/
structure UncertaintyAlgebra (T : Type → Type) (R : Type) where
  /-- The certain outcome. -/
  pure : {X : Type} → [Fintype X] → [DecidableEq X] → X → T X
  /-- Kleisli extension: run `f` at an uncertain input. -/
  bind : {X Y : Type} → [Fintype X] → [DecidableEq X] → [Fintype Y] → [DecidableEq Y] →
    T X → (X → T Y) → T Y
  /-- The algebra, applied after mapping `u`: the aggregate value of `u` over `m`. -/
  expect : {X : Type} → [Fintype X] → [DecidableEq X] → (X → R) → T X → R
  /-- Unit law of the algebra. -/
  expect_pure : ∀ {X : Type} [Fintype X] [DecidableEq X] (u : X → R) (x : X),
    expect u (pure x) = u x
  /-- Multiplication law of the algebra: aggregating in one step or in two agrees. -/
  expect_bind : ∀ {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (u : Y → R) (m : T X) (f : X → T Y),
    expect u (bind m f) = expect (fun x => expect u (f x)) m

namespace UncertaintyAlgebra

variable {T : Type → Type} {R : Type} (E : UncertaintyAlgebra T R)
  {X Y Z : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Fintype Z]
  [DecidableEq Z]

/-- Value pullback (weakest pre-expectation): `(f* u)(x) = expect u (f x)`. -/
def pullback (f : X → T Y) (u : Y → R) : X → R := fun x => E.expect u (f x)

/-- Kleisli composition, `f` first. -/
def kleisli (f : X → T Y) (g : Y → T Z) : X → T Z := fun x => E.bind (f x) g

/-- **C2**, identity law: pulling back along the unit changes nothing. -/
theorem pullback_pure (u : X → R) : E.pullback E.pure u = u :=
  funext fun x => E.expect_pure u x

/-- **C2**, composition law (contravariant): `(f ; g)* u = f* (g* u)`. -/
theorem pullback_kleisli (f : X → T Y) (g : Y → T Z) (u : Z → R) :
    E.pullback (E.kleisli f g) u = E.pullback f (E.pullback g u) :=
  funext fun x => E.expect_bind u (f x) g

/-- The aggregate is monotone in the values at the uncertain outcome `m`. -/
def MonotoneAt [LE R] (m : T X) : Prop :=
  ∀ u v : X → R, (∀ x, u x ≤ v x) → E.expect u m ≤ E.expect v m

/-- Adding a constant commutes with the aggregate at `m` ("stage reward addition is an
algebra map"). -/
def AdditiveAt [Add R] (m : T X) : Prop :=
  ∀ (c : R) (u : X → R), E.expect (fun x => c + u x) m = c + E.expect u m

/-- **C2**, monotonicity: a pointwise larger effect pulls back to a pointwise larger one. -/
theorem pullback_mono [LE R] {f : X → T Y} (hf : ∀ x, E.MonotoneAt (f x)) {u v : Y → R}
    (h : ∀ y, u y ≤ v y) (x : X) : E.pullback f u x ≤ E.pullback f v x :=
  hf x u v h

end UncertaintyAlgebra

/-! ### `Id`: functions -/

/-- The instance `Id`: no uncertainty; the aggregate of `u` at `x` is `u x`. -/
def idAlgebra (R : Type) : UncertaintyAlgebra (fun X => X) R where
  pure x := x
  bind m f := f m
  expect u m := u m
  expect_pure _ _ := rfl
  expect_bind _ _ _ := rfl

section Id

variable {R : Type} {X Y Z : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Z] [DecidableEq Z]

/-- For `Id` the pullback is precomposition. -/
theorem idAlgebra_pullback (f : X → Y) (u : Y → R) : (idAlgebra R).pullback f u = u ∘ f := rfl

/-- For `Id` Kleisli composition is function composition. -/
theorem idAlgebra_kleisli (f : X → Y) (g : Y → Z) : (idAlgebra R).kleisli f g = g ∘ f := rfl

theorem idAlgebra_monotoneAt [LE R] (x : X) : (idAlgebra R).MonotoneAt x := fun _ _ h => h x

theorem idAlgebra_additiveAt [Add R] (x : X) : (idAlgebra R).AdditiveAt x := fun _ _ => rfl

end Id

/-! ### `D`: finite kernels -/

section Dist

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {A Θ X Y Z : Type} [Fintype A] [Fintype Θ] [Fintype X] [Fintype Y] [Fintype Z]

/-- The instance `D`: a weight table on `X`, with the weighted sum as aggregate. -/
def distAlgebra (K : Type) [Field K] : UncertaintyAlgebra (fun X => X → K) K where
  pure x := fun y => if y = x then 1 else 0
  bind m f := fun y => ∑ x, m x * f x y
  expect u m := ∑ x, m x * u x
  expect_pure u x := by simp
  expect_bind u m f := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring

/-- `pullback(f, u)` for a finite kernel: `(f* u)(x) = Σ_y f x y · u y`, the matrix-vector
product `transpose(kernel_matrix(f)) * u`. -/
def pullbackD (f : X → Y → K) (u : Y → K) : X → K := fun x => ∑ y, f x y * u y

/-- `pushforward(p, f)`: the image of the weights `p` under the kernel `f`. It is the core's
`signalProbability` (the marginal of the signal), used here for any kernel. -/
abbrev push (p : X → K) (f : X → Y → K) : Y → K := signalProbability p f

theorem distAlgebra_pullback [DecidableEq X] [DecidableEq Y] (f : X → Y → K) (u : Y → K) :
    (distAlgebra K).pullback f u = pullbackD f u := rfl

/-- For `D` Kleisli composition is the core's `garble` (`compose_kernel`). -/
theorem distAlgebra_kleisli [DecidableEq X] [DecidableEq Y] [DecidableEq Z] (f : X → Y → K)
    (g : Y → Z → K) : (distAlgebra K).kleisli f g = garble f g := rfl

/-- The unit of `D` is the identity kernel. -/
theorem distAlgebra_pure [DecidableEq X] :
    ((distAlgebra K).pure : X → X → K) = deterministic id := rfl

/-- **C2** for `D`, identity law. -/
theorem pullbackD_identity [DecidableEq X] (u : X → K) : pullbackD (deterministic id) u = u :=
  (distAlgebra K).pullback_pure u

/-- **C2** for `D`, composition law: `(f ; g)* u = f* (g* u)`. -/
theorem pullbackD_garble (f : X → Y → K) (g : Y → Z → K) (u : Z → K) :
    pullbackD (garble f g) u = pullbackD f (pullbackD g u) := by
  classical
  exact (distAlgebra K).pullback_kleisli f g u

/-- Along a deterministic kernel the pullback is precomposition: `Id` embeds in `D`. -/
theorem pullbackD_deterministic [DecidableEq Y] (h : X → Y) (u : Y → K) :
    pullbackD (deterministic h) u = u ∘ h := by
  funext x
  simp [pullbackD, deterministic]

/-- **C2** for `D`, monotonicity, for a kernel with nonnegative entries. -/
theorem pullbackD_mono {f : X → Y → K} (hf : NonnegKernel f) {u v : Y → K}
    (h : ∀ y, u y ≤ v y) (x : X) : pullbackD f u x ≤ pullbackD f v x :=
  Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (h y) (hf x y)

/-- A normalised kernel pulls a constant back to the same constant. -/
theorem pullbackD_const {f : X → Y → K} (hf : NormalisedKernel f) (c : K) :
    pullbackD f (fun _ => c) = fun _ => c := by
  funext x
  unfold pullbackD
  rw [← Finset.sum_mul, hf x, one_mul]

/-- The pullback is linear in the effect. -/
theorem pullbackD_add_const_mul (f : X → Y → K) (c s : K) (u : Y → K) (x : X) :
    pullbackD f (fun y => c + s * u y) x = c * ∑ y, f x y + s * pullbackD f u x := by
  simp only [pullbackD, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1 <;> exact Finset.sum_congr rfl fun y _ => by ring

theorem distAlgebra_monotoneAt [DecidableEq X] {m : X → K} (hm : ∀ x, 0 ≤ m x) :
    (distAlgebra K).MonotoneAt m := fun _ _ h =>
  Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (h x) (hm x)

theorem distAlgebra_additiveAt [DecidableEq X] {m : X → K} (hm : ∑ x, m x = 1) :
    (distAlgebra K).AdditiveAt m := fun c u => by
  change ∑ x, m x * (c + u x) = c + ∑ x, m x * u x
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hm, one_mul]

/-- The core's expected utility is the pullback of the payoff row along the belief, seen as a
kernel out of the one-point type. -/
theorem expectedUtility_eq_pullbackD (u : A → Θ → K) (p : Θ → K) (a : A) :
    expectedUtility u p a = pullbackD (fun _ : Unit => p) (u a) () := rfl

/-- Pulling the payoff back along a kernel is pushing the belief forward along it:
`E_{f_* p}[u a] = E_p[f* (u a)]`. -/
theorem expectedUtility_push (u : A → Y → K) (p : X → K) (f : X → Y → K) (a : A) :
    expectedUtility u (push p f) a = expectedUtility (fun a => pullbackD f (u a)) p a := by
  simp only [expectedUtility, signalProbability, pullbackD, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring

/-- Pushing forward along a composite is pushing forward twice. -/
theorem push_garble (p : X → K) (f : X → Y → K) (g : Y → Z → K) :
    push p (garble f g) = push (push p f) g := by
  funext z
  simp only [signalProbability, garble, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => by ring

end Dist

/-! ### `P⁺`: non-empty finite sets, with `min` and with `max` -/

/-- A non-empty finite set of outcomes (`P⁺ X`). -/
abbrev NonemptyFinset (X : Type) : Type := {s : Finset X // s.Nonempty}

section Possibility

variable {K : Type} [LinearOrder K] {A Θ X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]

/-- The instance `P⁺` with the worst case as aggregate. -/
def minAlgebra (K : Type) [LinearOrder K] : UncertaintyAlgebra NonemptyFinset K where
  pure x := ⟨{x}, Finset.singleton_nonempty x⟩
  bind m f := ⟨m.1.biUnion fun x => (f x).1, m.2.biUnion fun x _ => (f x).2⟩
  expect u m := m.1.inf' m.2 u
  expect_pure _ _ := Finset.inf'_singleton _
  expect_bind _ m f := Finset.inf'_biUnion _ m.2 fun x => (f x).2

/-- The instance `P⁺` with the best case as aggregate. -/
def maxAlgebra (K : Type) [LinearOrder K] : UncertaintyAlgebra NonemptyFinset K where
  pure x := ⟨{x}, Finset.singleton_nonempty x⟩
  bind m f := ⟨m.1.biUnion fun x => (f x).1, m.2.biUnion fun x _ => (f x).2⟩
  expect u m := m.1.sup' m.2 u
  expect_pure _ _ := Finset.sup'_singleton _
  expect_bind _ m f := Finset.sup'_biUnion _ m.2 fun x => (f x).2

/-- `pullback(f, u)` for a total multivalued map with the worst case:
`(f* u)(x) = min_{y ∈ f x} u y`. -/
def pullbackMin (f : X → Finset Y) (hf : ∀ x, (f x).Nonempty) (u : Y → K) : X → K :=
  fun x => (f x).inf' (hf x) u

/-- `pullback(f, u)` for a total multivalued map with the best case:
`(f* u)(x) = max_{y ∈ f x} u y`. -/
def pullbackMax (f : X → Finset Y) (hf : ∀ x, (f x).Nonempty) (u : Y → K) : X → K :=
  fun x => (f x).sup' (hf x) u

/-- Composition of multivalued maps, `f` first: `z` is reachable from `x` through some `y`. -/
def relComp [DecidableEq Z] (f : X → Finset Y) (g : Y → Finset Z) : X → Finset Z :=
  fun x => (f x).biUnion g

theorem relComp_nonempty [DecidableEq Z] {f : X → Finset Y} {g : Y → Finset Z}
    (hf : ∀ x, (f x).Nonempty) (hg : ∀ y, (g y).Nonempty) (x : X) : (relComp f g x).Nonempty :=
  (hf x).biUnion fun y _ => hg y

theorem minAlgebra_pullback [DecidableEq X] [DecidableEq Y] (f : X → NonemptyFinset Y)
    (u : Y → K) :
    (minAlgebra K).pullback f u = pullbackMin (fun x => (f x).1) (fun x => (f x).2) u := rfl

theorem maxAlgebra_pullback [DecidableEq X] [DecidableEq Y] (f : X → NonemptyFinset Y)
    (u : Y → K) :
    (maxAlgebra K).pullback f u = pullbackMax (fun x => (f x).1) (fun x => (f x).2) u := rfl

/-- **C2** for `P⁺` with `min`, identity law. -/
theorem pullbackMin_identity (u : X → K) :
    pullbackMin (fun x : X => ({x} : Finset X)) (fun x => Finset.singleton_nonempty x) u = u :=
  funext fun _ => Finset.inf'_singleton _

/-- **C2** for `P⁺` with `min`, composition law. -/
theorem pullbackMin_relComp [DecidableEq Z] (f : X → Finset Y) (hf : ∀ x, (f x).Nonempty)
    (g : Y → Finset Z) (hg : ∀ y, (g y).Nonempty) (u : Z → K) :
    pullbackMin (relComp f g) (relComp_nonempty hf hg) u =
      pullbackMin f hf (pullbackMin g hg u) :=
  funext fun x => Finset.inf'_biUnion _ (hf x) hg

/-- **C2** for `P⁺` with `min`, monotonicity. -/
theorem pullbackMin_mono (f : X → Finset Y) (hf : ∀ x, (f x).Nonempty) {u v : Y → K}
    (h : ∀ y, u y ≤ v y) (x : X) : pullbackMin f hf u x ≤ pullbackMin f hf v x :=
  Finset.inf'_mono_fun fun y _ => h y

/-- **C2** for `P⁺` with `max`, identity law. -/
theorem pullbackMax_identity (u : X → K) :
    pullbackMax (fun x : X => ({x} : Finset X)) (fun x => Finset.singleton_nonempty x) u = u :=
  funext fun _ => Finset.sup'_singleton _

/-- **C2** for `P⁺` with `max`, composition law. -/
theorem pullbackMax_relComp [DecidableEq Z] (f : X → Finset Y) (hf : ∀ x, (f x).Nonempty)
    (g : Y → Finset Z) (hg : ∀ y, (g y).Nonempty) (u : Z → K) :
    pullbackMax (relComp f g) (relComp_nonempty hf hg) u =
      pullbackMax f hf (pullbackMax g hg u) :=
  funext fun x => Finset.sup'_biUnion _ (hf x) hg

/-- **C2** for `P⁺` with `max`, monotonicity. -/
theorem pullbackMax_mono (f : X → Finset Y) (hf : ∀ x, (f x).Nonempty) {u v : Y → K}
    (h : ∀ y, u y ≤ v y) (x : X) : pullbackMax f hf u x ≤ pullbackMax f hf v x :=
  Finset.sup'_mono_fun fun y _ => h y

theorem minAlgebra_monotoneAt [DecidableEq X] (m : NonemptyFinset X) :
    (minAlgebra K).MonotoneAt m := fun _ _ h =>
  Finset.inf'_mono_fun (hs := m.2) fun x _ => h x

theorem maxAlgebra_monotoneAt [DecidableEq X] (m : NonemptyFinset X) :
    (maxAlgebra K).MonotoneAt m := fun _ _ h =>
  Finset.sup'_mono_fun (hs := m.2) fun x _ => h x

/-- The core's worst-case score of an action (`Maximin`) is the `min` pullback of its payoff
row along the multivalued map that allows every state. -/
theorem worstCase_eq_pullbackMin [Fintype Θ] [Nonempty Θ] (u : A → Θ → K) (a : A) :
    worstCase u a =
      pullbackMin (fun _ : Unit => (Finset.univ : Finset Θ)) (fun _ => Finset.univ_nonempty)
        (u a) () := rfl

end Possibility

section Additive

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {X Y : Type} [Fintype X] [Fintype Y]

theorem minAlgebra_additiveAt [DecidableEq X] (m : NonemptyFinset X) :
    (minAlgebra K).AdditiveAt m := fun c u => by
  change m.1.inf' m.2 (fun x => c + u x) = c + m.1.inf' m.2 u
  exact (Finset.comp_inf'_eq_inf'_comp m.2 (fun t => c + t)
    (fun a b => (min_add_add_left c a b).symm)).symm

theorem maxAlgebra_additiveAt [DecidableEq X] (m : NonemptyFinset X) :
    (maxAlgebra K).AdditiveAt m := fun c u => by
  change m.1.sup' m.2 (fun x => c + u x) = c + m.1.sup' m.2 u
  exact (Finset.comp_sup'_eq_sup'_comp m.2 (fun t => c + t)
    (fun a b => (max_add_add_left c a b).symm)).symm

/-- The support map `D → P⁺` is lax: for a stochastic kernel `f` and sets `s x` that contain
its support, the worst case over `s x` is at most the expectation. Equality fails in general,
so replacing an expectation by a worst case is a bound, not a change of presentation. -/
theorem pullbackMin_le_pullbackD {f : X → Y → K} (hf : StochasticKernel f) (s : X → Finset Y)
    (hs : ∀ x, (s x).Nonempty) (hsupp : ∀ x y, f x y ≠ 0 → y ∈ s x) (u : Y → K) (x : X) :
    pullbackMin s hs u x ≤ pullbackD f u x := by
  unfold pullbackMin pullbackD
  calc (s x).inf' (hs x) u = ∑ y, f x y * (s x).inf' (hs x) u := by
        rw [← Finset.sum_mul, hf.2 x, one_mul]
    _ ≤ ∑ y, f x y * u y := Finset.sum_le_sum fun y _ => by
        by_cases hy : f x y = 0
        · simp [hy]
        · exact mul_le_mul_of_nonneg_left (Finset.inf'_le u (hsupp x y hy)) (hf.1 x y)

end Additive

end CategoricalDecisionAnalysisProofs
