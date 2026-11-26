import Mettapedia.Languages.MeTTa.HE.ModuleSpace
import Mathlib.Data.Set.Lattice

/-!
# Shared declarations and import

The object glued by a diamond is a support of declaration occurrences.
Two independently written occurrences of the same atom are not one
declaration; the same occurrence reached twice through a shared module is.
This gluing law does not equate the answer order of every enumeration.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SpaceTheory.Modules

section Support

variable {Origin Target : Type*}

def leftInclusion (left right : Set Origin) (atom : left) : (left ∪ right : Set Origin) :=
  ⟨atom.1, Or.inl atom.2⟩

def rightInclusion (left right : Set Origin) (atom : right) : (left ∪ right : Set Origin) :=
  ⟨atom.1, Or.inr atom.2⟩

def Agree {left right : Set Origin} (f : left → Target) (g : right → Target) : Prop :=
  ∀ (origin : Origin) (inLeft : origin ∈ left) (inRight : origin ∈ right),
    f ⟨origin, inLeft⟩ = g ⟨origin, inRight⟩

/-- Union has the pushout property for inclusions over their actual
intersection. Interpretations that disagree on the same occurrence
do not have a common extension. -/
theorem support_pushout {left right : Set Origin} (f : left → Target) (g : right → Target) :
    Agree f g ↔ ∃! interpret : (left ∪ right : Set Origin) → Target,
      (∀ a, interpret (leftInclusion left right a) = f a) ∧
        (∀ a, interpret (rightInclusion left right a) = g a) := by
  classical
  constructor
  · intro same
    let h : (left ∪ right : Set Origin) → Target := fun a =>
      if inLeft : a.1 ∈ left then f ⟨a.1, inLeft⟩
      else g ⟨a.1, a.2.resolve_left inLeft⟩
    have hLeft : ∀ a, h (leftInclusion left right a) = f a := by
      intro a
      simp [h, leftInclusion, a.2]
    have hRight : ∀ a, h (rightInclusion left right a) = g a := by
      intro a
      by_cases present : a.1 ∈ left
      · simpa [h, rightInclusion, present] using same a.1 present a.2
      · simp [h, rightInclusion, present]
    refine ⟨h, ⟨hLeft, hRight⟩, ?_⟩
    intro other properties
    funext a
    rcases a.2 with inLeft | inRight
    · exact (properties.1 ⟨a.1, inLeft⟩).trans (hLeft ⟨a.1, inLeft⟩).symm
    · exact (properties.2 ⟨a.1, inRight⟩).trans (hRight ⟨a.1, inRight⟩).symm
  · rintro ⟨extension, ⟨onLeft, onRight⟩, _⟩ origin inLeft inRight
    exact (onLeft ⟨origin, inLeft⟩).symm.trans (onRight ⟨origin, inRight⟩)

/-- The two injections identify two declarations exactly when they have
the same origin, irrespective of any equal atom payloads. -/
theorem identified_iff_origin {left right : Set Origin} (a : left) (b : right) :
    leftInclusion left right a = rightInclusion left right b ↔ a.1 = b.1 := by
  exact ⟨fun eq => congrArg Subtype.val eq, fun eq => Subtype.ext eq⟩

theorem support_pushout_of_union {left right combined : Set Origin}
    (union : combined = left ∪ right) (f : left → Target) (g : right → Target) :
    Agree f g ↔ ∃! interpret : combined → Target,
      (∀ a : left, interpret ⟨a.val, union.symm ▸ Or.inl a.property⟩ = f a) ∧
      (∀ a : right, interpret ⟨a.val, union.symm ▸ Or.inr a.property⟩ = g a) := by
  subst combined
  exact support_pushout f g

end Support

section HEImports

open Mettapedia.Languages.MeTTa.HE (ModuleNode ModId)

def dependencies (node : ModuleNode) : Set ModId := {id | id ∈ node.deps}

def importedSupport (direct : ModId) (transitive : List ModId) : Set ModId :=
  {id | id ∈ direct :: transitive}

/-- In the existing HE model, a fresh import adds the union. An import of
a known module is a no-op, so it only gives that union if the transitive
dependencies being proposed are already present. -/
theorem he_import_union_iff (node : ModuleNode) (direct : ModId) (transitive : List ModId) :
    dependencies (node.importModule direct transitive) =
        dependencies node ∪ importedSupport direct transitive ↔
      direct ∉ node.deps ∨ ∀ id ∈ transitive, id ∈ node.deps := by
  by_cases known : direct ∈ node.deps
  · rw [node.importModule_of_mem known]
    simp only [known, not_true_eq_false, false_or]
    constructor
    · intro union id member
      have inside : id ∈ dependencies node ∪ importedSupport direct transitive :=
        Or.inr (List.mem_cons_of_mem _ member)
      rw [← union] at inside
      exact inside
    · intro included
      ext id
      change id ∈ node.deps ↔ id ∈ node.deps ∨ id ∈ direct :: transitive
      exact ⟨Or.inl, fun yes => yes.elim (fun found => found) fun added =>
        (List.mem_cons.mp added).elim (fun eq => eq.symm ▸ known) (included _)⟩
  · rw [node.importModule_of_not_mem known]
    simp only [known, not_false_eq_true, true_or, iff_true]
    ext id
    exact ModuleNode.mem_insertDeps

end HEImports

section Controls

theorem repeated_import_has_one_interpretation
    {Origin Target : Type*} (support : Set Origin) (value : support → Target) :
    ∃! interpret : (support ∪ support : Set Origin) → Target,
      (∀ a, interpret (leftInclusion support support a) = value a) ∧
        (∀ a, interpret (rightInclusion support support a) = value a) :=
  (support_pushout value value).mp (fun _ _ _ => rfl)

theorem conflicting_shared_interpretations_have_no_gluing :
    ¬ ∃ h : (({0} : Set Nat) ∪ {0} : Set Nat) → Bool,
      (∀ a, h (leftInclusion {0} {0} a) = false) ∧
        (∀ a, h (rightInclusion {0} {0} a) = true) := by
  rintro ⟨h, left, right⟩
  have equal := (identified_iff_origin
    (left := ({0} : Set Nat)) (right := ({0} : Set Nat))
    ⟨0, rfl⟩ ⟨0, rfl⟩).mpr rfl
  exact Bool.false_ne_true ((left ⟨0, rfl⟩).symm.trans ((congrArg h equal).trans (right ⟨0, rfl⟩)))

end Controls

end Mettapedia.Languages.MeTTa.SpaceTheory.Modules
