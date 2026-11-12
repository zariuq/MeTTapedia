import Mathlib.CategoryTheory.Core
import Mathlib.CategoryTheory.Types.Basic

/-!
# Finite event sets with preserved labels

Objects retain a finite position set and its labeling. Morphisms are
bijections preserving those labels. Equal labels do not identify positions.
Forgetting the labels gives a functor to the core of the category of types.
-/

set_option autoImplicit false

namespace Mettapedia.CategoryTheory.LabelledFinite

open _root_.CategoryTheory

universe u

structure Object (Label : Type u) where
  size : Nat
  label : Fin size → Label

structure Iso {Label : Type u} (source target : Object Label) where
  positions : Fin source.size ≃ Fin target.size
  preserves : ∀ event, target.label (positions event) = source.label event

variable {Label : Type u}

theorem Iso.ext {source target : Object Label} {first second : Iso source target}
    (same : first.positions = second.positions) : first = second := by
  cases first
  cases second
  cases same
  rfl

instance labelledGroupoid : Groupoid (Object Label) where
  Hom := Iso
  id source := ⟨Equiv.refl _, fun _ => rfl⟩
  comp first second := ⟨first.positions.trans second.positions,
    fun event => (second.preserves (first.positions event)).trans (first.preserves event)⟩
  id_comp := by intros; apply Iso.ext; rfl
  comp_id := by intros; apply Iso.ext; rfl
  assoc := by intros; apply Iso.ext; rfl
  inv arrow := ⟨arrow.positions.symm, fun event => by
    have same := arrow.preserves (arrow.positions.symm event)
    simpa only [Equiv.apply_symm_apply] using same.symm⟩
  inv_comp := by
    intro source target arrow
    apply Iso.ext
    apply Equiv.ext
    intro event
    exact arrow.positions.apply_symm_apply event
  comp_inv := by
    intro source target arrow
    apply Iso.ext
    apply Equiv.ext
    intro event
    exact arrow.positions.symm_apply_apply event

def forget : Object Label ⥤ Core (Type) where
  obj source := ⟨Fin source.size⟩
  map arrow := ⟨arrow.positions.toIso⟩

end Mettapedia.CategoryTheory.LabelledFinite

#print axioms Mettapedia.CategoryTheory.LabelledFinite.labelledGroupoid
