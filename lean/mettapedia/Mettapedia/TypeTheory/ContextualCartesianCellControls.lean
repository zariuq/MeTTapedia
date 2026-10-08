import Mettapedia.TypeTheory.ContextualCartesianCellIdentity
import Mettapedia.TypeTheory.ContextualDisplayCartesianControls
import Mathlib.Data.Fin.Basic

/-!
# Complete readings and fixed display contexts

A supplied bounded witness is recovered by the joint cartesian readings
through a nonidentity successor base. Reversing a bounded witness fixes its
base projection but changes the complete substitution, showing why a base
projection alone cannot establish the required identity.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualCartesianCellControls

open CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open ContextualCartesianCellIdentity ContextualDisplayCartesianControls

/-- The complete supplied cartesian readings recover every bounded pair. -/
theorem supplied_factor_identity : actualFactor.substitution = familiesCwf.idS _ := by
  apply cartesian_joint_cancel successor target.val
  · exact actualFactor.over.trans (familiesCwf.comp_id _).symm
  · exact supplied_recovers_every_pair

/-- The first and second component are both retained after the actual lift. -/
theorem recovered_one : actualFactor.substitution (⟨0, ⟨1, by decide⟩⟩ : Σ n : Nat, Fin ((n+1)+1)) =
    ⟨0, ⟨1, by decide⟩⟩ := by
  rw [supplied_factor_identity]
  rfl

def reverseBounded : (Σ n : Nat, Fin (n+2)) → Σ n : Nat, Fin (n+2) :=
  fun point => ⟨point.1, point.2.rev⟩

theorem reverse_fixes_base :
    familiesCwf.compS (familiesCwf.wk (fun n : Nat => Fin (n+2))) reverseBounded =
      familiesCwf.wk (fun n : Nat => Fin (n+2)) := rfl

theorem reverse_changes_complete_pair : reverseBounded ≠ familiesCwf.idS _ := by
  intro equal
  have value := congrArg (fun function => (function (⟨0, 0⟩ : Σ n : Nat, Fin (n+2))).2.val) equal
  change 1 = 0 at value
  cases value

theorem projection_identity_does_not_supply_display_identity :
    familiesCwf.compS (familiesCwf.wk (fun n : Nat => Fin (n+2))) reverseBounded =
      familiesCwf.wk (fun n : Nat => Fin (n+2)) ∧
    reverseBounded ≠ familiesCwf.idS _ :=
  ⟨reverse_fixes_base, reverse_changes_complete_pair⟩

end Mettapedia.TypeTheory.ContextualCartesianCellControls
