import Mettapedia.GSLT.Core.OperationalColimitStageEquality
import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# Filtered stage controls

A noninjective transport identifies two distinct stage terms. A separate
growing diagram adds a reduction later: absence at its first stage does
not imply absence at the shared ambient image.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.IndexedOperational.OperationalColimits.Controls

open CategoryTheory
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

def booleanCarrier : OperationalTheory :=
  ⟨equalityGSLT Bool (fun _ _ => False)⟩

def collapseBoolean : booleanCarrier ⟶ booleanCarrier where
  mapTerm := fun _ => false
  mapEquiv := fun _ => rfl
  mapStep := fun impossible => impossible.elim

def merging : ℕ ⥤ OperationalTheory :=
  Functor.ofSequence (X := fun _ => booleanCarrier) (fun _ => collapseBoolean)

theorem stage_values_distinct : (true : booleanCarrier.theory.Term) ≠ false := by
  decide

theorem merged_images : inject merging 0 true = inject merging 0 false := by
  have first := inject_along merging (homOfLE (show 0 ≤ 1 from Nat.zero_le 1)) true
  have second := inject_along merging (homOfLE (show 0 ≤ 1 from Nat.zero_le 1)) false
  exact first.trans second.symm

theorem merged_has_single_route_witness :
    ∃ stage, ∃ route : (0 : ℕ) ⟶ stage,
      (merging.map route).mapTerm true = (merging.map route).mapTerm false :=
  (inject_eq_iff_equal_after merging true false).mp merged_images

def growingTheory (stage : ℕ) : OperationalTheory :=
  ⟨equalityGSLT Bool (fun left right => 0 < stage ∧ left = false ∧ right = true)⟩

def grow (stage : ℕ) : growingTheory stage ⟶ growingTheory (stage + 1) where
  mapTerm := id
  mapEquiv := fun equivalent => equivalent
  mapStep := fun step => ⟨Nat.lt_succ_of_lt step.1, step.2⟩

def growing : ℕ ⥤ OperationalTheory :=
  Functor.ofSequence (X := growingTheory) grow

theorem no_initial_step : ¬ ∃ next, (growing.obj 0).theory.Step false next := by
  rintro ⟨_, impossible⟩
  exact (Nat.lt_irrefl 0) impossible.1

theorem later_step : (growing.obj 1).theory.Step false true :=
  ⟨Nat.zero_lt_succ 0, rfl, rfl⟩

theorem initial_image_has_step :
    (theory growing).Step (inject growing 0 false) (inject growing 1 true) := by
  have later := (inclusion growing 1).mapStep later_step
  have transported := inject_along growing (homOfLE (show 0 ≤ 1 from Nat.zero_le 1)) false
  rw [transported]
  exact later

theorem initial_absence_does_not_persist :
    ¬ (¬ ∃ next, (theory growing).Step (inject growing 0 false) next) := by
  intro absent
  exact absent ⟨_, initial_image_has_step⟩

#print axioms merged_images
#print axioms merged_has_single_route_witness
#print axioms initial_image_has_step
#print axioms initial_absence_does_not_persist

end Mettapedia.GSLT.IndexedOperational.OperationalColimits.Controls
