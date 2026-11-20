import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.Table.Complete
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.NativeControls

/-!
# Target-table execution controls

The positive run uses nested continuations, and its nine-event prefix is
exhausted rather than terminal. Proposal errors distinguish an invalid rule
index from a mismatching rule. An unknown row remains an irreducible row of
this table, with no invented interpretation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.Table.Controls

open NamesOnTheStep (Expr)
open RuleSyntax.Presentation.Schematic (inst)
open RuleSyntax.Machines (RootStep unknowns)
open RuleSyntax.Machines.PartialRecursive (eNormal eCfg names lhs rhs ruleOf? ruleOf?_lhs)
open PartialRecursive.Controls (nested nestedInput nestedOutput)

theorem nested_table_ten :
    drive Program.schemas 10 (eNormal nested .halt nestedInput) = .stopped (eCfg (.halt nestedOutput)) := by
  change drive Program.schemas 10 (PartialRecursive.point (SourceBudget.start nested nestedInput)).row = _
  rw [Program.drive_agrees]
  rfl

theorem nested_table_nine :
    drive Program.schemas 9 (eNormal nested .halt nestedInput) = .exhausted (eCfg (.ret .halt nestedOutput)) := by
  change drive Program.schemas 9 (PartialRecursive.point (SourceBudget.start nested nestedInput)).row = _
  rw [Program.drive_agrees]
  rfl

theorem nested_table_prefix_is_enabled :
    ∃ run : PartialRecursive.native.Run (PartialRecursive.start nested nestedInput),
      run.word.length = 9 ∧ RuleSyntax.Machines.ReadsBag run.last {eCfg (.ret .halt nestedOutput)} ∧
        ∃ firing, PartialRecursive.native.Admits (s := run.last) firing :=
  Program.exhausted_actual nested_table_nine

theorem invalid_index (row : Expr) : checkAt Program.schemas 99 row = .badIndex := rfl

theorem mismatching_rule : checkAt Program.schemas 0 (eNormal .succ .halt []) = .mismatch := by
  have noAssignment : ¬ ∃ assignment, inst assignment (lhs .zeroCode) = eNormal .succ .halt [] := by
    rintro ⟨assignment, same⟩
    have discriminator := congrArg ruleOf? same
    rw [ruleOf?_lhs] at discriminator
    cases discriminator
  have refused := (applySchema_none_iff (lhs .zeroCode, rhs .zeroCode) (eNormal .succ .halt [])).mpr noAssignment
  change (match applySchema (lhs .zeroCode, rhs .zeroCode) (eNormal .succ .halt []) with
    | none => Proposal.mismatch | some result => Proposal.result result) = .mismatch
  rw [refused]

theorem mismatch_is_not_program_refusal :
    checkAt Program.schemas 0 (eNormal .succ .halt []) = .mismatch ∧
      drive Program.schemas 2 (eNormal .succ .halt []) = .stopped (eCfg (.halt [1])) := by
  refine ⟨mismatching_rule, ?_⟩
  change drive Program.schemas 2 (PartialRecursive.point (SourceBudget.start .succ [])).row = _
  rw [Program.drive_agrees]
  rfl

theorem unknown_row_has_no_step : ¬ ∃ result, RootStep Program.schemas (.sym 999) result := by
  rintro ⟨result, schema, member, assignment, matched, _⟩
  obtain ⟨name, _, rfl⟩ := List.mem_map.mp member
  cases name <;> cases matched

theorem unknown_row_is_retained (budget : Nat) :
    drive Program.schemas budget (.sym 999) = .stopped (.sym 999) := by
  have empty := (successors_empty_iff Program.schemas Program.closed (.sym 999)).mpr unknown_row_has_no_step
  have none := (next?_none_iff Program.schemas (.sym 999)).mpr empty
  cases budget <;> simp [drive, none]

/-- Matching a left side cannot determine a right-side variable that
never occurred there. Such a schema has no licence for this ground-row
executor; its general symbolic meaning remains a separate question. -/
theorem unbound_output_not_determined :
    let schema : Schema := (.const (.sym 1), .var 0)
    (¬ ∀ name ∈ unknowns schema.2, name ∈ unknowns schema.1) ∧
      ∃ first second : Nat → Expr, inst first schema.1 = inst second schema.1 ∧
        inst first schema.2 ≠ inst second schema.2 := by
  refine ⟨?_, (fun _ => .sym 0), (fun _ => .sym 2), rfl, ?_⟩
  · intro closed
    exact List.not_mem_nil (closed 0 (List.mem_singleton_self _))
  · decide

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.Table.Controls

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.Table.Controls.nested_table_prefix_is_enabled
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.Table.Controls.mismatch_is_not_program_refusal
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.Table.Controls.unknown_row_is_retained
