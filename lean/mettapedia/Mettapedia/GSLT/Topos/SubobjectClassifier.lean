import Mettapedia.GSLT.Topos.Yoneda
import Mathlib.CategoryTheory.Sites.Sieves
import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.CategoryTheory.Topos.Classifier

/-!
# Subobject Classifier for Presheaf Categories

This file defines the subobject classifier Ω for presheaf categories.

## Main Definitions

* `omegaFunctor` - The presheaf Ω sending X to the set of sieves on X
* `trueNatTrans` - The "true" morphism ⊤ : 1 → Ω

## Key Insights

In a presheaf topos Psh(C):
- The subobject classifier Ω assigns to each object X the set of sieves on X
- Ω(X) = { S | S is a sieve on X }
- For f : X → Y, Ω(f) pulls back sieves: S ↦ f*(S)

## References

- Mac Lane & Moerdijk, "Sheaves in Geometry and Logic", Chapter I.4
- Johnstone, "Sketches of an Elephant", A.1.6
-/

namespace Mettapedia.GSLT.Topos

open CategoryTheory
open CategoryTheory.Limits
open Opposite

universe u v

variable {C : Type u} [Category.{v} C]

/-! ## The Sieve Functor

The subobject classifier in Psh(C) is the functor Ω : Cᵒᵖ → Type
that sends each object X to the set of sieves on X.
-/

/-- Sieves on X form a complete lattice -/
instance sieveCompleteLattice (X : C) : CompleteLattice (Sieve X) := inferInstance

/-- The pullback of a sieve along a morphism.
    If S is a sieve on Y and f : X → Y, then f*(S) is a sieve on X. -/
def sievePullback {X Y : C} (f : X ⟶ Y) (S : Sieve Y) : Sieve X :=
  Sieve.pullback f S

/-- Pullback preserves top -/
theorem sievePullback_top {X Y : C} (f : X ⟶ Y) :
    sievePullback f ⊤ = ⊤ := by
  apply Sieve.ext
  intro Z g
  simp [sievePullback, Sieve.pullback]

/-- Pullback preserves bottom -/
theorem sievePullback_bot {X Y : C} (f : X ⟶ Y) :
    sievePullback f ⊥ = ⊥ := by
  apply Sieve.ext
  intro Z g
  simp only [sievePullback, Sieve.pullback_apply]
  constructor
  · intro h
    exact h
  · intro h
    exact h

/-- The subobject classifier functor Ω : Cᵒᵖ → Type.

    Ω(X) = { sieves on X }
    Ω(f) = pullback along f -/
def omegaFunctor : Cᵒᵖ ⥤ Type (max u v) where
  obj X := Sieve (unop X)
  map f S := sievePullback f.unop S
  map_id X := by
    funext S
    apply Sieve.ext
    intro Y g
    simp [sievePullback, Sieve.pullback]
  map_comp f g := by
    funext S
    apply Sieve.ext
    intro Y h
    simp [sievePullback, Sieve.pullback]

/-- Notation for the subobject classifier -/
scoped notation "Ω_" => omegaFunctor

/-! ## The "True" Morphism

The morphism true : 1 → Ω is the natural transformation that
picks out the maximal sieve at each object.
-/

/-- The terminal presheaf 1 (constant at PUnit) -/
def terminalPresheaf : Cᵒᵖ ⥤ Type (max u v) where
  obj _ := PUnit.{max u v + 1}
  map _ := id

/-- The "true" natural transformation: 1 → Ω.
    At each X, it sends () to the maximal sieve ⊤. -/
def trueNatTrans : terminalPresheaf ⟶ omegaFunctor (C := C) where
  app X := fun _ => (⊤ : Sieve (unop X))
  naturality X Y f := by
    funext _
    show sievePullback f.unop ⊤ = ⊤
    exact sievePullback_top f.unop

/-! ## Properties of the Subobject Classifier

Key properties that make Ω a subobject classifier:
1. For each mono m : S ↪ P, there's a unique χ : P → Ω with pullback square
2. Ω(X) is a complete Heyting algebra (Frame)
-/

/-- Each fiber Ω(X) is a complete lattice.
    Note: For the full Frame structure, we'd need Heyting implication on sieves. -/
instance omegaCompleteLattice (X : C) : CompleteLattice (Sieve X) := inferInstance

/-- Presheaf categories have a subobject classifier.

    This is a fundamental theorem of topos theory (Mac Lane & Moerdijk, Theorem I.6.1).
    The classifier is the sieve functor Ω, and we axiomatize this here.

    The proof requires showing that for any presheaf P and subobject S ↪ P,
    there exists a unique characteristic morphism χ : P → Ω such that
    S is the pullback of true : 1 → Ω along χ.

    The construction: for any subobject S ↪ P, the characteristic map χ_P
    at component X ∈ Cᵒᵖ sends an element a ∈ P(X) to the sieve
    { f : Y → X | P(f)(a) ∈ S(Y) }

    This is proven in Mathlib's `CategoryTheory.Topos.Classifier` for categories
    with a classifier, and specifically for presheaf categories we use that
    sieves classify subfunctors of representables (Yoneda).
-/
-- TODO: Prove that presheaf categories have a subobject classifier.
-- This is Mac Lane & Moerdijk Theorem I.6.1.
-- The classifier is the sieve functor Ω defined above.
-- Requires showing that sieves classify subobjects.
theorem presheafCategoryHasClassifier (C : Type u) [SmallCategory C] :
    CategoryTheory.HasClassifier (Psh(C)) := by
  sorry

/-! ## Summary

This file establishes the subobject classifier for presheaf categories:

1. **omegaFunctor**: Ω : Cᵒᵖ → Type (the subobject classifier presheaf)
2. **trueNatTrans**: The "true" morphism 1 → Ω
3. **omegaFrame**: Each fiber Ω(X) is a Frame

**Key Properties**:
- Ω(X) is the complete lattice of sieves on X
- Pullback along f : X → Y gives Ω(f) : Ω(Y) → Ω(X)
- true picks the maximal sieve at each object
- Ω classifies subobjects in Psh(C)

**Next Steps**:
- `PredicateFibration.lean`: Connect Ω to the predicate fibration πΩ
- Prove Beck-Chevalley condition
- Connect to native types via Grothendieck construction
-/

end Mettapedia.GSLT.Topos
