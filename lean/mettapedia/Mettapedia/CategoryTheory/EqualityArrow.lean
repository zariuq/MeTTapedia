import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.EqToHom

/-!
# Arrows read from equality of objects

An equality arrow retains its actual object equality and has the canonical
`eqToHom` reading. Such readings compose, map under arbitrary functors, and
are unique at fixed endpoints. This does not identify arbitrary isomorphisms
or arbitrary objects.
-/

set_option autoImplicit false

namespace Mettapedia.CategoryTheory

open _root_.CategoryTheory

universe u v w z

variable {C : Type u} [Category.{v} C] {D : Type w} [Category.{z} D]

def EqualityArrow {source target : C} (arrow : source ⟶ target) : Prop :=
  ∃ same : source = target, arrow = eqToHom same

namespace EqualityArrow

theorem of_eqToHom {source target : C} (same : source = target) : EqualityArrow (eqToHom same) :=
  ⟨same, rfl⟩

theorem identity (source : C) : EqualityArrow (𝟙 source) := ⟨rfl, rfl⟩

theorem unique {source target : C} {first second : source ⟶ target}
    (before : EqualityArrow first) (after : EqualityArrow second) : first = second := by
  obtain ⟨one, oneRead⟩ := before
  obtain ⟨two, twoRead⟩ := after
  exact oneRead.trans twoRead.symm

theorem comp {source middle target : C} {before : source ⟶ middle} {after : middle ⟶ target}
    (first : EqualityArrow before) (last : EqualityArrow after) : EqualityArrow (before ≫ after) := by
  obtain ⟨one, oneRead⟩ := first
  obtain ⟨two, twoRead⟩ := last
  exact ⟨one.trans two, (congrArg₂ (fun f g => f ≫ g) oneRead twoRead).trans (eqToHom_trans one two)⟩

theorem map (mapping : C ⥤ D) {source target : C} {arrow : source ⟶ target}
    (reading : EqualityArrow arrow) : EqualityArrow (mapping.map arrow) := by
  obtain ⟨same, value⟩ := reading
  exact ⟨congrArg mapping.obj same,
    (congrArg mapping.map value).trans (eqToHom_map mapping same)⟩

theorem iso_hom_app {first second : C ⥤ D} (same : first = second) (source : C) :
    EqualityArrow ((eqToIso same).hom.app source) :=
  ⟨Functor.congr_obj same source, eqToHom_app same source⟩

end EqualityArrow

end Mettapedia.CategoryTheory
