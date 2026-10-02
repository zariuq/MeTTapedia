import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Pullback squares along equal apexes

A pullback square stays a pullback when its apex is replaced by an equal
object and its two legs by the corresponding legs; a functor maps
heterogeneously equal arrows to heterogeneously equal arrows.
-/

set_option autoImplicit false

namespace Mettapedia.CategoryTheory

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe v u v' u'

variable {C : Type u} [Category.{v} C]

/-- **A pullback square along an equal apex.** -/
theorem IsPullback.of_apex_eq {P P' X Y Z : C} (same : P = P') {fst : P ⟶ X} {snd : P ⟶ Y}
    {fst' : P' ⟶ X} {snd' : P' ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (sameFst : HEq fst fst') (sameSnd : HEq snd snd') (square : IsPullback fst snd f g) :
    IsPullback fst' snd' f g := by
  subst same
  cases sameFst
  cases sameSnd
  exact square

/-- Precomposing with a cast of objects does not change an arrow, up to its
domain. -/
theorem eqToHom_comp_heq {P P' X : C} (same : P = P') (g : P' ⟶ X) :
    HEq (eqToHom same ≫ g) g := by
  subst same
  rw [eqToHom_refl, Category.id_comp]

variable {E : Type u'} [Category.{v'} E]

/-- A functor maps heterogeneously equal arrows with equal domains and a common
codomain to heterogeneously equal arrows. -/
theorem Functor.map_heq_of_source (F : C ⥤ E) {a a' b : C} (same : a = a') {u : a ⟶ b}
    {u' : a' ⟶ b} (sameArrow : HEq u u') : HEq (F.map u) (F.map u') := by
  subst same
  cases sameArrow
  rfl

/-- Precomposition preserves heterogeneous equality of arrows into equal
objects. -/
theorem comp_heq {Z a b b' : C} (g : Z ⟶ a) (same : b = b') {x : a ⟶ b} {x' : a ⟶ b'}
    (sameArrow : HEq x x') : HEq (g ≫ x) (g ≫ x') := by
  subst same
  cases sameArrow
  rfl

/-- A functor maps heterogeneously equal arrows between equal objects to
heterogeneously equal arrows. -/
theorem Functor.map_heq (F : C ⥤ E) {a a' b b' : C} (sameSource : a = a') (sameTarget : b = b')
    {u : a ⟶ b} {u' : a' ⟶ b'} (sameArrow : HEq u u') : HEq (F.map u) (F.map u') := by
  subst sameSource
  subst sameTarget
  cases sameArrow
  rfl

end Mettapedia.CategoryTheory
