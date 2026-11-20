import Mettapedia.Languages.MeTTa.PeTTa.MachineHeadSelectionApart

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MachineHeadSelectionApart.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MetaMeTTaComparison (atomAction)
open ListView Unifying

private def integer (value : Int) : Atom := .grounded (.int value)
private def stored (index : Int) (value : Atom) : Atom :=
  MachineHeadSelection.row (.symbol "f") (integer index)
    (MachineClauseReads.head (.expression [value]))
private def query (value : Atom) : Atom :=
  MachineHeadSelection.row (.symbol "f") (.var "index")
    (MachineClauseReads.head (.expression [value]))

private def apartSeven : Disequality.Frame atomAction :=
  ⟨[(.var "value", integer 7)], by
    intro equation member
    obtain rfl := List.mem_singleton.mp member
    change Atom.var "value" ≠ integer 7
    decide +kernel⟩

theorem forbidden_answer_is_refused :
    probe apartSeven [] (stored 0 (integer 7)) (query (.var "value")) = .clash := by
  decide +kernel

theorem retained_negative_information_changes_the_selection :
    (MachineHeadSelection.snapshot [] (query (.var "value"))
      [stored 0 (integer 7), stored 1 (integer 8)]).matched = [0, 1] ∧
      (snapshot apartSeven [] (query (.var "value"))
        [stored 0 (integer 7), stored 1 (integer 8)]).matched = [1] := by decide +kernel

theorem unique_occurrence_respects_retained_apart :
    MachineHeadSelection.verdict (snapshot apartSeven [] (query (.var "value"))
      [stored 0 (integer 7), stored 1 (integer 8)]) = .unique 1 := by decide +kernel

theorem duplicate_allowed_rows_are_still_two_occurrences :
    MachineHeadSelection.verdict (snapshot apartSeven [] (query (.var "value"))
      [stored 0 (integer 8), stored 0 (integer 8)]) = .nonunique := by decide +kernel

private def guardFrame (index : Nat) : Disequality.Frame atomAction :=
  ⟨[(.var (LibTransformStep.tag index "local"), integer 7)], by
    intro equation member
    obtain rfl := List.mem_singleton.mp member
    change Atom.var (LibTransformStep.tag index "local") ≠ integer 7
    intro same
    cases same⟩

theorem a_name_mentioned_only_by_the_negative_frame_is_in_support :
    scope (guardFrame 25) [] (query (integer 7)) = 26 := by decide +kernel

theorem local_opening_does_not_capture_a_frame_only_name :
    MachineHeadSelection.accepted
      (probe (guardFrame 0) [] (stored 0 (.var "local")) (query (integer 7))) = true := by
  decide +kernel

private def unprotectedAnswer : Subst :=
  match MachineHeadSelection.probe [] (stored 0 (.var "local")) (query (integer 7)) with
  | .ok answer => answer
  | _ => []

theorem omitting_frame_support_would_falsely_refuse_this_valid_read :
    apart (guardFrame 0) unprotectedAnswer = false := by decide +kernel

private def twoChecks : Disequality.Frame atomAction :=
  ⟨[(.var "x", integer 7), (.var "y", integer 8)], by
    intro equation member
    rcases List.mem_cons.mp member with first | later
    · obtain rfl := first
      change Atom.var "x" ≠ integer 7
      decide +kernel
    · obtain rfl := List.mem_singleton.mp later
      change Atom.var "y" ≠ integer 8
      decide +kernel⟩

private def pair (first second : Atom) : Atom := .expression [.symbol "Pair", first, second]

theorem every_retained_disequation_is_checked :
    MachineHeadSelection.accepted (probe twoChecks []
      (stored 0 (pair (integer 8) (integer 7))) (query (pair (.var "x") (.var "y")))) = true ∧
      probe twoChecks [] (stored 0 (pair (integer 8) (integer 8)))
        (query (pair (.var "x") (.var "y"))) = .clash := by decide +kernel

theorem computed_allowed_answer_is_a_guarded_source_reading :
    Reading apartSeven [] (stored 0 (integer 8)) (query (.var "value")) :=
  (probe_iff_reading apartSeven [] _ _ idempotent_nil).mp (by decide +kernel)

theorem forbidden_probe_has_no_guarded_source_reading :
    ¬ Reading apartSeven [] (stored 0 (integer 7)) (query (.var "value")) := by
  rw [← probe_iff_reading apartSeven [] _ _ idempotent_nil]
  decide +kernel

private def noApart : Disequality.Frame atomAction :=
  ⟨[], by intro _ absent; cases absent⟩
private def oldName : Atom := .var (LibTransformStep.tag 0 "x")
private def retainedRow : Atom := .expression [.symbol "Saved", oldName]
private def retainedAnswer : Subst :=
  match probe noApart [] (.var "x") (integer 7) [retainedRow] with
  | .ok answer => answer
  | _ => []

theorem names_in_retained_source_rows_advance_the_namespace :
    scope noApart [] (integer 7) [retainedRow] = 1 := by decide +kernel

theorem the_source_local_matches_without_binding_an_unrelated_old_name :
    MachineHeadSelection.accepted (probe noApart [] (.var "x") (integer 7) [retainedRow]) = true ∧
      resolve retainedAnswer oldName = oldName := by decide +kernel

private def requestedOldAnswer : Subst :=
  match probe noApart [] (integer 7) oldName [retainedRow] with
  | .ok answer => answer
  | _ => []

theorem retained_support_does_not_make_legitimate_query_variables_read_only :
    resolve requestedOldAnswer oldName = integer 7 := by decide +kernel

end Mettapedia.Languages.MeTTa.PeTTa.MachineHeadSelectionApart.Controls
