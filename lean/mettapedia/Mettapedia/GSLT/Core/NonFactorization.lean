import Mathlib.Logic.Function.Basic

/-!
# Factorization through a projection

Every obstruction compiled in this development so far has one shape.  A
projection forgets something, an invariant depends on what was forgotten, and
the invariant therefore cannot be computed from the projection's output.
Derivation cost against provability, the coinductive discharge licence
against a checker's verdict, a translated term against the source judgment,
bisimilarity against forward simulation — all the same statement, each
proved separately on its own fixture.

This module states it once.

The content is elementary and deliberately so.  Its value is not depth but
*organization*: it turns a pile of independent negative results into
instances of one criterion, and — more usefully — it turns the discovery of
new obstructions into a routine.  To show an invariant is unreachable from a
projection, exhibit two ambient points with the same shadow and different
value.  Nothing else is ever required.

The positive direction matters just as much.  When the fibres *are* trivial
the invariant does factor, and that is the precise sense in which a
projection loses nothing.  Both signs live here so that a development can say
which one it is claiming.

Nothing in this file mentions proofs, presentations, or any particular
semantics; the instances live where their fixtures live.
-/

namespace Mettapedia.GSLT.Core.NonFactorization

universe uA uS uV

/-- `invariant` **factors through** `shadow` when some function of the shadow
recovers it.  This is what it means for a projection to retain everything the
invariant depends on. -/
def Factors {A : Sort uA} {S : Sort uS} {V : Sort uV}
    (shadow : A → S) (invariant : A → V) : Prop :=
  ∃ recover : S → V, ∀ a, recover (shadow a) = invariant a

/-- `invariant` is **constant on fibres** of `shadow` when points with equal
shadows have equal values. -/
def ConstantOnFibers {A : Sort uA} {S : Sort uS} {V : Sort uV}
    (shadow : A → S) (invariant : A → V) : Prop :=
  ∀ a b, shadow a = shadow b → invariant a = invariant b

/-- Anything recoverable from the shadow is constant on fibres. -/
theorem Factors.constantOnFibers {A : Sort uA} {S : Sort uS} {V : Sort uV}
    {shadow : A → S} {invariant : A → V} (factors : Factors shadow invariant) :
    ConstantOnFibers shadow invariant := by
  obtain ⟨recover, recovers⟩ := factors
  intro a b sameShadow
  rw [← recovers a, ← recovers b, sameShadow]

/-- **The witness.**  Two ambient points sharing a shadow but differing in
value.  Producing one of these is the whole method for refuting
factorization, and every negative result in this development is one. -/
structure NonTrivialFiber {A : Sort uA} {S : Sort uS} {V : Sort uV}
    (shadow : A → S) (invariant : A → V) where
  /-- One ambient point. -/
  left : A
  /-- Another ambient point with the same shadow. -/
  right : A
  /-- The projection cannot tell them apart. -/
  sameShadow : shadow left = shadow right
  /-- The invariant can. -/
  differentValue : invariant left ≠ invariant right

/-- **The criterion.**  A non-trivial fibre refutes factorization. -/
theorem NonTrivialFiber.not_factors {A : Sort uA} {S : Sort uS} {V : Sort uV}
    {shadow : A → S} {invariant : A → V}
    (fiber : NonTrivialFiber shadow invariant) :
    ¬ Factors shadow invariant := fun factors =>
  fiber.differentValue (factors.constantOnFibers _ _ fiber.sameShadow)

/-- A non-trivial fibre is exactly the failure of fibre-constancy. -/
theorem NonTrivialFiber.not_constantOnFibers {A : Sort uA} {S : Sort uS}
    {V : Sort uV} {shadow : A → S} {invariant : A → V}
    (fiber : NonTrivialFiber shadow invariant) :
    ¬ ConstantOnFibers shadow invariant := fun constant =>
  fiber.differentValue (constant _ _ fiber.sameShadow)

/-- Conversely, failure of fibre-constancy produces a witness. -/
theorem nonTrivialFiber_of_not_constantOnFibers {A : Sort uA} {S : Sort uS}
    {V : Sort uV} {shadow : A → S} {invariant : A → V}
    (notConstant : ¬ ConstantOnFibers shadow invariant) :
    Nonempty (NonTrivialFiber shadow invariant) := by
  by_contra empty
  exact notConstant fun a b sameShadow => by
    by_contra differentValue
    exact empty ⟨⟨a, b, sameShadow, differentValue⟩⟩

/-- **Propositional form.**  When the invariant is a proposition, a fibre is
non-trivial as soon as it holds at one end and fails at the other. -/
def NonTrivialFiber.ofProp {A : Sort uA} {S : Sort uS} {shadow : A → S}
    {invariant : A → Prop} {a b : A} (sameShadow : shadow a = shadow b)
    (holds : invariant a) (fails : ¬ invariant b) :
    NonTrivialFiber shadow invariant where
  left := a
  right := b
  sameShadow := sameShadow
  differentValue := fun equalValues => fails (equalValues ▸ holds)

/-- **The characterization**, for a projection that reaches every shadow.
Surjectivity is what lets fibre-constancy be assembled into a function; the
criterion above needs no such hypothesis, which is why it is the form the
instances use. -/
theorem factors_iff_constantOnFibers {A S V : Type*} {shadow : A → S}
    (surjective : Function.Surjective shadow) (invariant : A → V) :
    Factors shadow invariant ↔ ConstantOnFibers shadow invariant := by
  refine ⟨Factors.constantOnFibers, fun constant => ?_⟩
  refine ⟨fun s => invariant (Function.surjInv surjective s), fun a => ?_⟩
  exact constant _ _ (Function.surjInv_eq surjective (shadow a))

/-! ## Coarsening

A projection that factors through a finer one cannot recover more than the
finer one does.  This is what makes a single obstruction propagate: an
invariant unreachable from a derivation's erasure is unreachable from
anything that erasure passes through. -/

/-- If `shadow` is `fine` followed by a further forgetting step, then
anything recoverable from `shadow` was already recoverable from `fine`. -/
theorem Factors.of_coarsening {A : Sort uA} {S : Sort uS} {S' : Sort*}
    {V : Sort uV} {shadow : A → S} {fine : A → S'} {coarsen : S' → S}
    (coarsens : ∀ a, shadow a = coarsen (fine a)) {invariant : A → V}
    (factors : Factors shadow invariant) : Factors fine invariant := by
  obtain ⟨recover, recovers⟩ := factors
  refine ⟨fun s => recover (coarsen s), fun a => ?_⟩
  show recover (coarsen (fine a)) = invariant a
  rw [← coarsens a]
  exact recovers a

/-- **Obstructions propagate outward.**  Failing to factor through a finer
projection implies failing to factor through any coarsening of it. -/
theorem not_factors_of_coarsening {A : Sort uA} {S : Sort uS} {S' : Sort*}
    {V : Sort uV} {shadow : A → S} {fine : A → S'} {coarsen : S' → S}
    (coarsens : ∀ a, shadow a = coarsen (fine a)) {invariant : A → V}
    (fineFails : ¬ Factors fine invariant) : ¬ Factors shadow invariant :=
  fun factors => fineFails (factors.of_coarsening coarsens)

/-- A fibre of a finer projection is a fibre of any coarsening. -/
def NonTrivialFiber.coarsen {A : Sort uA} {S : Sort uS} {S' : Sort*}
    {V : Sort uV} {shadow : A → S} {fine : A → S'} {coarsen : S' → S}
    (coarsens : ∀ a, shadow a = coarsen (fine a)) {invariant : A → V}
    (fiber : NonTrivialFiber fine invariant) :
    NonTrivialFiber shadow invariant where
  left := fiber.left
  right := fiber.right
  sameShadow := by simp only [coarsens, fiber.sameShadow]
  differentValue := fiber.differentValue

/-! ## Subsingleton shadows

The sharpest case, and the one proof irrelevance puts us in.  When the
shadow type has at most one inhabitant it separates nothing, so *every*
non-constant invariant fails to factor.  A projection into a proposition is
of this kind, which is why truncating a derivation to its provability
destroys every proof-distinguishing quantity at once rather than one at a
time. -/

/-- Into a subsingleton, any two points share a shadow. -/
def NonTrivialFiber.ofSubsingleton {A : Sort uA} {S : Sort uS} {V : Sort uV}
    [Subsingleton S] {shadow : A → S} {invariant : A → V} {a b : A}
    (differentValue : invariant a ≠ invariant b) :
    NonTrivialFiber shadow invariant where
  left := a
  right := b
  sameShadow := Subsingleton.elim _ _
  differentValue := differentValue

/-- **Nothing that separates survives a subsingleton shadow.**  A projection
whose codomain is a proposition retains an invariant only when that invariant
was already constant. -/
theorem factors_subsingleton_iff_constant {A : Sort uA} {S : Sort uS}
    {V : Sort uV} [Subsingleton S] [Nonempty A] {shadow : A → S}
    (invariant : A → V) :
    Factors shadow invariant ↔ ∀ a b, invariant a = invariant b := by
  refine ⟨fun factors a b => factors.constantOnFibers a b (Subsingleton.elim _ _),
    fun constant => ?_⟩
  refine ⟨fun _ => invariant (Classical.arbitrary A), fun a => constant _ a⟩

end Mettapedia.GSLT.Core.NonFactorization
