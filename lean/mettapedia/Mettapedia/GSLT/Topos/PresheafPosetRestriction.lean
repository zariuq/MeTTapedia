import Mettapedia.GSLT.Topos.PresheafLogicalTransport
import Mathlib.CategoryTheory.Category.Preorder

/-!
# Exact logical transport for ordered contexts

For a functor between posets, preservation of presheaf predicate implication
is equivalent to the order-theoretic back condition: every context below an
image lifts to a context below its source. Necessity is detected using the
principal and strictly principal lower predicates on the terminal presheaf.

The characterization is specific to posets. The general categorical
`LiftsRestrictions` condition remains a sufficient condition, and is not
asserted necessary for arbitrary categories.
-/

set_option autoImplicit false
namespace Mettapedia.GSLT.Topos.LogicalTransport
open _root_.CategoryTheory Opposite
universe u
variable {C D : Type u} [PartialOrder C] [PartialOrder D]

def lowerPredicate (y : D) :
    Subfunctor ((Functor.const Dᵒᵖ).obj PUnit.{u+1}) where
  obj U := fun _ => U.unop ≤ y
  map i _ h := (leOfHom i.unop).trans h

def strictLowerPredicate (y : D) :
    Subfunctor ((Functor.const Dᵒᵖ).obj PUnit.{u+1}) where
  obj U := fun _ => U.unop < y
  map i _ h := lt_of_le_of_lt (leOfHom i.unop) h

theorem liftsRestrictions_iff_order_back (F : C ⥤ D) :
    LiftsRestrictions F ↔ ∀ x y, y ≤ F.obj x → ∃ z, z ≤ x ∧ F.obj z = y := by
  constructor
  · intro h x y below
    obtain ⟨W, j, e, _⟩ := h (op x) (op y) (homOfLE below).op
    exact ⟨W.unop, leOfHom j.unop,
      le_antisymm (leOfHom e.inv.unop) (leOfHom e.hom.unop)⟩
  · intro h U V i
    obtain ⟨z, below, same⟩ := h U.unop V.unop (leOfHom i.unop)
    refine ⟨op z, (homOfLE below).op, eqToIso (congrArg op same), ?_⟩
    apply Subsingleton.elim

/-- For poset contexts, preservation of implication for all predicates is
exactly the usual back condition. Already predicates on the terminal presheaf
can detect a missing lower context. -/
theorem restrict_implication_iff_liftsRestrictions (F : C ⥤ D) :
    (∀ (P : Dᵒᵖ ⥤ Type u) (φ ψ : Subfunctor P),
      restrictPredicate F (φ ⇨ ψ) = restrictPredicate F φ ⇨ restrictPredicate F ψ) ↔
    LiftsRestrictions F := by
  constructor
  · intro preservation
    apply (liftsRestrictions_iff_order_back F).mpr
    intro x y below
    classical
    by_contra missing
    have member : PUnit.unit ∈
        (restrictPredicate F (lowerPredicate y) ⇨
          restrictPredicate F (strictLowerPredicate y)).obj (op x) := by
      rw [← himpPointwise_eq_himp]
      intro V i antecedent
      change F.obj V.unop < y
      apply lt_of_le_of_ne antecedent
      intro same
      exact missing ⟨V.unop, leOfHom i.unop, same⟩
    rw [← preservation] at member
    change PUnit.unit ∈ ((lowerPredicate y) ⇨ strictLowerPredicate y).obj (op (F.obj x)) at member
    rw [← himpPointwise_eq_himp] at member
    have impossible : y < y := member (op y) (homOfLE below).op le_rfl
    exact (lt_irrefl y) impossible
  · intro h P φ ψ
    exact restrict_implication_eq h φ ψ

end Mettapedia.GSLT.Topos.LogicalTransport
