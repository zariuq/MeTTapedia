import Mettapedia.Languages.MeTTa.PeTTa.MachineConditionSyntax

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MachineConditionSyntax.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

private def pattern : Atom := .expression [.symbol "pm:state", .var "x", .var "x"]
private def computation : Atom := .expression [.symbol "pm:chains-for", .var "f",
  .expression [.symbol "pm:items-length", .var "written"]]

theorem nested_computation_is_kept :
    readCondition (.expression [.symbol "let", pattern, computation]) =
      some (.binary .bind pattern computation) := by decide +kernel

theorem computation_is_not_a_table_pattern :
    readCondition (.expression [.symbol "let", pattern, computation]) ≠
      some (.bare (.expression [.symbol "let", pattern, computation])) := by decide +kernel

theorem constructor_payload_is_data :
    readCondition (.expression [.symbol "take",
      .expression [.symbol "let", .var "x", .var "x"]]) =
      some (.unary .take (.expression [.symbol "let", .var "x", .var "x"])) := by decide +kernel

theorem unknown_pattern_head_is_accepted :
    readCondition (.expression [.symbol "NewConstructor", .var "x"]) =
      some (.bare (.expression [.symbol "NewConstructor", .var "x"])) := by decide +kernel

theorem unfinished_binding_syntax_is_not_read_as_a_bare_pattern :
    readCondition (.expression [.symbol "let", .var "pattern"]) = none := by decide +kernel

theorem nullary_pattern_keeps_its_kind :
    readCondition (.expression [.symbol "Nullary"]) ≠ readCondition (.symbol "Nullary") := by
  decide +kernel

theorem ordered_duplicate_conditions_survive :
    readSources (.expression [.symbol ",",
      .expression [.symbol "read", pattern],
      .expression [.symbol "let", .var "result", computation],
      .expression [.symbol "read", pattern]]) =
      some (.joint [.unary .read pattern, .binary .bind (.var "result") computation,
        .unary .read pattern]) := by decide +kernel

theorem unique_and_read_are_distinct :
    readCondition (.expression [.symbol "unique", pattern]) ≠
      readCondition (.expression [.symbol "read", pattern]) := by decide +kernel

theorem collect_keeps_pattern_before_destination :
    readCondition (.expression [.symbol "collect", pattern, .var "heads"]) =
      some (.binary .collect pattern (.var "heads")) := by decide +kernel

theorem collect_does_not_exchange_its_fields :
    readCondition (.expression [.symbol "collect", pattern, .var "heads"]) ≠
      readCondition (.expression [.symbol "collect", .var "heads", pattern]) := by decide +kernel

theorem repeated_variables_remain_shared_occurrences :
    Mettapedia.Languages.ProcessCalculi.MORK.atomFreeVars
      (Condition.binary .bind pattern computation).render = ["x", "x", "f", "written"] := by
  decide +kernel

theorem every_unique_condition_is_present :
    (conditions.filter fun condition => match condition with
      | .unary .unique _ => true
      | _ => false).length = 4 := by decide +kernel

theorem every_collect_condition_is_present :
    (conditions.filter fun condition => match condition with
      | .binary .collect _ _ => true
      | _ => false).length = 2 := by decide +kernel

end Mettapedia.Languages.MeTTa.PeTTa.MachineConditionSyntax.Controls
