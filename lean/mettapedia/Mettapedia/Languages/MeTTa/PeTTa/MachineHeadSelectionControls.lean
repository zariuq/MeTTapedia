import Mettapedia.Languages.MeTTa.PeTTa.MachineHeadSelection

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MachineHeadSelection.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open ListView Unifying

private def integer (value : Int) : Atom := .grounded (.int value)
private def head (value : Atom) : Atom := MachineClauseReads.head (.expression [value])
private def stored (index : Int) (value : Atom) : Atom := row (.symbol "f") (integer index) (head value)
private def query (value : Atom) : Atom := row (.symbol "f") (.var "index") (head value)

theorem one_open_head_has_one_occurrence :
    verdict (snapshot [] (query (integer 7)) [stored 0 (.var "x")]) = .unique 0 := by
  decide +kernel

theorem identical_payloads_are_two_occurrences :
    (snapshot [] (query (integer 7)) [stored 0 (.var "x"), stored 0 (.var "x")]).matched = [0, 1] ∧
      verdict (snapshot [] (query (integer 7)) [stored 0 (.var "x"), stored 0 (.var "x")]) =
        .nonunique := by decide +kernel

theorem each_candidate_uses_the_incoming_bindings :
    (snapshot [] (query (.var "value")) [stored 0 (integer 1), stored 1 (integer 2)]).matched =
      [0, 1] := by decide +kernel

theorem existing_caller_binding_refuses_only_the_inconsistent_row :
    (snapshot [("value", integer 2)] (query (.var "value"))
      [stored 0 (integer 1), stored 1 (integer 2)]).matched = [1] := by decide +kernel

theorem completed_empty_snapshot_has_no_unique_row :
    verdict (snapshot [] (query (.var "value")) []) = .nonunique := by decide +kernel

theorem theory_growth_can_invalidate_snapshot_uniqueness :
    verdict (snapshot [] (query (integer 7)) [stored 0 (.var "x")]) = .unique 0 ∧
      verdict (snapshot [] (query (integer 7)) [stored 0 (.var "x"), stored 1 (integer 7)]) =
        .nonunique := by decide +kernel

private def incomplete (position : Fin 2) : Unified :=
  if position = 0 then .ok [] else .exhausted

theorem one_found_answer_is_not_unique_while_another_probe_is_pending :
    verdict (scan incomplete) = .pending [0] [1] := by decide +kernel

theorem value_kinds_remain_distinct :
    (snapshot [] (query (.grounded (.string "a")))
      [stored 0 (.symbol "a"), stored 1 (.grounded (.string "a"))]).matched = [1] := by
  decide +kernel

theorem shared_parameter_is_not_two_independent_matches :
    (snapshot []
      (row (.symbol "f") (.var "index")
        (MachineClauseReads.head (.expression [integer 7, integer 8])))
      [row (.symbol "f") (integer 0)
        (MachineClauseReads.head (.expression [.var "x", .var "x"]))]).matched = [] := by
  decide +kernel

theorem computed_open_probe_is_a_source_closure_reading :
    Reading [] (stored 0 (.var "x")) (query (integer 7)) :=
  (probe_iff_reading [] _ _ idempotent_nil).mp (by decide +kernel)

end Mettapedia.Languages.MeTTa.PeTTa.MachineHeadSelection.Controls
