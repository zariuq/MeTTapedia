import Mettapedia.GSLT.Topos.PresheafPredicateUniversalQuantifier

/-!
# Heyting implication of presheaf predicates, pointwise

The predicate fibres of a presheaf category are frames, so they carry a
relative pseudocomplement, but the frame is obtained from the complete
lattice by a minimal-axioms construction and its implication is therefore an
abstract supremum.  This file supplies the standard pointwise description —
a section satisfies an implication when every restriction of it that
satisfies the antecedent also satisfies the consequent — and proves it is
that implication:

* `himpPointwise_eq_himp` — the pointwise description is the fibre's `⇨`;
* `preimage_himp` — reindexing along a map of presheaves preserves
  implication, so it is a homomorphism of Heyting algebras.

## A distinction worth keeping

These two statements are about *different* operations, and only one of them
preserves implication.

Reindexing along a **morphism of presheaves over a fixed base** preserves
implication; that is `preimage_himp` below, and it is the standard topos
fact.

Restriction along a **functor between base categories** does not, even when
that functor preserves products, the terminal object and exponentials.  That
is proved separately in
`Mettapedia/OSLF/PresheafNativeType/TheoryTranslationCounterexample.lean`.

Conflating the two turns a theorem into its own counterexample, so the
positive result below is stated for presheaf morphisms only.

## References

- Mac Lane–Moerdijk, "Sheaves in Geometry and Logic" (1994), Ch. I.3
  (the Heyting structure of subobjects in a presheaf topos, with the
  restriction-quantified reading of implication).
- Johnstone, "Sketches of an Elephant" (2002), A1.4.
-/

open CategoryTheory

universe w v u

set_option autoImplicit false

namespace Mettapedia.GSLT.Topos

variable {C : Type u} [Category.{v} C] {F : C ⥤ Type w}

/-- Heyting implication of presheaf predicates, pointwise: every restriction
satisfying the antecedent satisfies the consequent. -/
def himpPointwise (α β : Subfunctor F) : Subfunctor F where
  obj U := {x | ∀ (V : C) (i : U ⟶ V),
    F.map i x ∈ α.obj V → F.map i x ∈ β.obj V}
  map {U V} i := by
    intro x holds W j held
    have restricted := holds W (i ≫ j)
    rw [Functor.map_comp_apply] at restricted
    exact restricted held

@[simp] theorem mem_himpPointwise (α β : Subfunctor F) (U : C) (x : F.obj U) :
    x ∈ (himpPointwise α β).obj U ↔
      ∀ (V : C) (i : U ⟶ V),
        F.map i x ∈ α.obj V → F.map i x ∈ β.obj V := Iff.rfl

/-- The pointwise description is the fibre's Heyting implication. -/
theorem himpPointwise_eq_himp (α β : Subfunctor F) :
    himpPointwise α β = α ⇨ β := by
  refine le_antisymm ?_ ?_
  · rw [le_himp_iff]
    intro U x member
    have inAntecedent : x ∈ α.obj U := member.2
    have holds := member.1 U (𝟙 U)
    rw [Functor.map_id_apply] at holds
    exact holds inAntecedent
  · intro U x member V i held
    have restricted : F.map i x ∈ (α ⇨ β).obj V := (α ⇨ β).map i member
    exact le_himp_iff.mp (le_refl (α ⇨ β)) V ⟨restricted, held⟩

/-- Reindexing along a morphism of presheaves preserves Heyting implication:
over a fixed base, pullback is a homomorphism of Heyting algebras. -/
theorem preimage_himp {P : C ⥤ Type w} (α β : Subfunctor F) (f : P ⟶ F) :
    (α ⇨ β).preimage f = α.preimage f ⇨ β.preimage f := by
  rw [← himpPointwise_eq_himp, ← himpPointwise_eq_himp]
  ext U x
  constructor
  · intro held V i restricted
    show f.app V (P.map i x) ∈ β.obj V
    have naturally : f.app V (P.map i x) = F.map i (f.app U x) :=
      NatTrans.naturality_apply f i x
    rw [naturally]
    refine held V i ?_
    rw [← naturally]
    exact restricted
  · intro held V i restricted
    show F.map i (f.app U x) ∈ β.obj V
    have naturally : f.app V (P.map i x) = F.map i (f.app U x) :=
      NatTrans.naturality_apply f i x
    rw [← naturally]
    refine held V i ?_
    show f.app V (P.map i x) ∈ α.obj V
    rw [naturally]
    exact restricted

/-- Reindexing preserves the top predicate as well, so it preserves the whole
Heyting signature used below. -/
@[simp] theorem preimage_top' {P : C ⥤ Type w} (f : P ⟶ F) :
    (⊤ : Subfunctor F).preimage f = ⊤ := rfl

end Mettapedia.GSLT.Topos

#print axioms Mettapedia.GSLT.Topos.himpPointwise_eq_himp
#print axioms Mettapedia.GSLT.Topos.preimage_himp
#print axioms Mettapedia.GSLT.Topos.mem_himpPointwise
