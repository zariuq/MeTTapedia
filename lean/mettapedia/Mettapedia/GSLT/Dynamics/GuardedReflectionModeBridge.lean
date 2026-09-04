import Mettapedia.GSLT.Dynamics.SpaceGuardedReflection
import Mettapedia.TypeTheory.GuardedTimeModeTheory

/-!
# Bridge from revision modes to space-guarded reflection

The guarded `Later` predicate used by a modal type theory and the finite
snapshot discipline used by reflective space execution have the same
revision semantics.  This bridge states that agreement and shows that
meaning preservation is independent of the selected tick cost.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.GuardedReflectionModeBridge

open Mettapedia.GSLT.Dynamics.SpaceGuardedReflection
open Mettapedia.TypeTheory.GuardedTimeModeTheory

variable {Atom Prog Sem : Type}

/-- The type-theoretic and operational guarded predicates are definitionally
the same revision observation. -/
theorem later_agrees (predicate : Nat → Prop) (revision : Nat) :
    Later predicate revision =
      SpaceGuardedReflection.later predicate revision :=
  rfl

/-- Every future extension of an append-only space is invisible throughout
the guarded past of the next revision. -/
theorem snapshot_stability_is_guarded (history extension : List Atom) :
    Later
      (fun revision =>
        snapshot (history ++ extension) revision =
          snapshot history revision)
      (history.length + 1) := by
  intro revision earlier
  exact snapshot_stable history extension revision
    (Nat.lt_succ_iff.mp earlier)

/-- One guarded self-improvement tick preserves extensional meaning and has
unit distance under the selected distance grading. -/
theorem improvement_tick_preserves_meaning_and_has_unit_distance
    (improver : GuardedImprover Prog Sem) (initial : Prog) (revision : Nat) :
    improver.meaning (improver.tower initial (revision + 1)) =
        improver.meaning (improver.tower initial revision) ∧
      distanceGrading.gradeOf (guard revision) = 1 := by
  constructor
  · exact improver.sound (improver.tower initial revision)
  · exact distance_guard revision

/-- Meaning preservation does not determine a resource valuation: the same
guarded update has one semantics and two distinct lawful tick costs. -/
theorem meaning_does_not_determine_tick_cost
    (improver : GuardedImprover Prog Sem) (initial : Prog) (revision : Nat) :
    improver.meaning (improver.tower initial (revision + 1)) =
        improver.meaning (improver.tower initial revision) ∧
      distanceGrading.gradeOf (guard revision) ≠
        doubledDistanceGrading.gradeOf (guard revision) := by
  exact ⟨improver.sound (improver.tower initial revision),
    same_modes_distinct_guard_costs revision⟩

/-- Unguarded fixed-point failure coexists with a total, meaning-preserving
guarded tower.  This is the positive/negative discriminator for placing
self-modification behind revision time. -/
theorem guarded_tower_without_unguarded_fixed_point :
    (∀ initial revision : Nat,
      (GuardedImprover.tower
        { meaning := fun _ : Nat => ()
          improve := Nat.succ
          sound := fun _ => rfl }
        initial revision : Nat) = initial + revision) ∧
      ¬ ∃ fixed : Nat, fixed = fixed + 1 := by
  constructor
  · intro initial revision
    induction revision with
    | zero => rfl
    | succ prior inductionHypothesis =>
        simp only [GuardedImprover.tower]
        rw [inductionHypothesis]
        omega
  · exact no_fixed_point_of_progress

#print axioms later_agrees
#print axioms snapshot_stability_is_guarded
#print axioms improvement_tick_preserves_meaning_and_has_unit_distance
#print axioms meaning_does_not_determine_tick_cost
#print axioms guarded_tower_without_unguarded_fixed_point

end Mettapedia.GSLT.Dynamics.GuardedReflectionModeBridge
