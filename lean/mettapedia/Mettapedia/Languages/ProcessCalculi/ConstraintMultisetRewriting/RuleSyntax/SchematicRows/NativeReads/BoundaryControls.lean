import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.Boundary
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.LifetimeControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.HeadRanges

/-! # Boundary controls do not turn refusals or open metadata into emptiness -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.BoundaryControls

open Mettapedia.Machines.ResourceOwnership
open LifetimeControls

def current : RequestBorrow.Stamp Nat := ⟨7, 3⟩

theorem permitted_read :
    (Boundary.request (Value := Nat) current shared 2 handle 17 true true).failure = none := by decide

theorem released_reader_invalidates :
    (Boundary.request (Value := Nat) current (shared.erase cloned) 2 handle 17 true true).failure = some .invalidated := by
  decide

theorem wrong_generation_invalidates :
    (Boundary.request (Value := Nat) {current with epoch := 4} shared 2 handle 17 true true).failure = some .invalidated := by
  decide

theorem wrong_provider_invalidates :
    (Boundary.request (Value := Nat) {current with identity := 8} shared 2 handle 17 true true).failure = some .invalidated := by
  decide

theorem budget_stop_is_explicit :
    (Boundary.request (Value := Nat) current shared 2 handle 17 false true).failure = some .interrupted := by decide

theorem allocation_failure_is_explicit :
    (Boundary.request (Value := Nat) current shared 2 handle 17 true false).failure = some .noMemory := by decide

def keys (i : Nat) : HeadRanges.HeadKey :=
  toLex (if i < 2 then (0, 0) else if i < 4 then (3, 2) else (7, 1))

theorem two_native_ranges_keep_unknowns : HeadRanges.twoRuns keys 6 3 2 = [0, 1, 2, 3] := by decide

theorem arity_mismatch_keeps_only_unknowns : HeadRanges.twoRuns keys 6 3 5 = [0, 1] := by decide

theorem missing_rigid_bucket_keeps_unknowns : HeadRanges.twoRuns keys 6 9 2 = [0, 1] := by decide

def unsortedKeys (i : Nat) : HeadRanges.HeadKey :=
  toLex (if i = 0 then (9, 2) else if i = 1 then (3, 2) else (7, 1))

theorem missing_sortedness_can_lose_a_match :
    unsortedKeys 0 = toLex (9, 2) ∧ 0 ∉ HeadRanges.twoRuns unsortedKeys 3 9 2 := by decide

#print axioms permitted_read
#print axioms released_reader_invalidates
#print axioms two_native_ranges_keep_unknowns
#print axioms missing_rigid_bucket_keeps_unknowns
#print axioms missing_sortedness_can_lose_a_match

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.BoundaryControls
