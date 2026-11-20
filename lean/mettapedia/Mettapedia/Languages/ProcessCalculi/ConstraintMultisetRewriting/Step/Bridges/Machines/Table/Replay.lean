import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.Table.Driver
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.Table.Native

/-!
# Every table replay has an actual firing run

The proof follows the executable target-table driver. At each selected row
transition, the existing compiler correspondence provides an admitted firing
at the supplied current native state. Exhaustion retains an enabled endpoint;
a stopped row admits no firing of this table. These are different outcomes.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.Table

open NamesOnTheStep (Expr)
open RuleSyntax.Presentation.Schematic
open RuleSyntax.Machines

abbrev tableStep (schemas : List Schema) := (schematicStep Nat (rootRules schemas)).toStep

variable (schemas : List Schema)
  (closed : ∀ schema ∈ schemas, ∀ name ∈ unknowns schema.2, name ∈ unknowns schema.1)

include closed

/-- The endpoint is the actual supplied state's continuation, not a
freshly initialized copy of the encoded row. -/
theorem drive_has_run (budget : Nat) {row : Expr} {state : SState Nat} (reads : ReadsBag state {row}) :
    ∃ run : (tableStep schemas).Run state, run.word.length ≤ budget ∧
      ReadsBag run.last {(drive schemas budget row).row} ∧
      (∀ final, drive schemas budget row = .exhausted final → run.word.length = budget) := by
  induction budget generalizing row state with
  | zero =>
      refine ⟨.nil state, le_rfl, ?_, fun _ _ => rfl⟩
      cases selected : next? schemas row <;> simpa [drive, selected, Result.row, Interface.Step.Run.last] using reads
  | succ budget ih =>
      cases selected : next? schemas row with
      | none =>
          refine ⟨.nil state, Nat.zero_le _, ?_, ?_⟩
          · simpa [drive, selected, Result.row, Interface.Step.Run.last] using reads
          · intro final exhausted
            simp [drive, selected] at exhausted
      | some next =>
          obtain ⟨firing, admitted, nextReads⟩ :=
            (successor_iff_firing schemas closed reads).mp (next?_mem selected)
          obtain ⟨rest, short, finalReads, exhaustedCount⟩ := ih nextReads
          refine ⟨.cons firing admitted rest, Nat.succ_le_succ short, ?_, ?_⟩
          · simpa only [drive, selected, Interface.Step.Run.last] using finalReads
          · intro final exhausted
            have tailExhausted : drive schemas budget next = .exhausted final := by
              simpa only [drive, selected] using exhausted
            exact congrArg Nat.succ (exhaustedCount final tailExhausted)

theorem stopped_has_run {budget : Nat} {row final : Expr} {state : SState Nat}
    (reads : ReadsBag state {row}) (stopped : drive schemas budget row = .stopped final) :
    ∃ run : (tableStep schemas).Run state, run.word.length ≤ budget ∧ ReadsBag run.last {final} ∧
      ∀ firing, ¬ (tableStep schemas).Admits (s := run.last) firing := by
  obtain ⟨run, short, finalReads, _⟩ := drive_has_run schemas closed budget reads
  rw [stopped] at finalReads
  refine ⟨run, short, finalReads, ?_⟩
  exact (no_successors_iff_no_firing schemas closed finalReads).mp
    ((next?_none_iff schemas final).mp (stopped_is_normal stopped))

/-- An exhausted replay has spent exactly its event budget and the
literal endpoint still admits another firing of the same target table. -/
theorem exhausted_has_run {budget : Nat} {row final : Expr} {state : SState Nat}
    (reads : ReadsBag state {row}) (exhausted : drive schemas budget row = .exhausted final) :
    ∃ run : (tableStep schemas).Run state, run.word.length = budget ∧ ReadsBag run.last {final} ∧
      ∃ firing, (tableStep schemas).Admits (s := run.last) firing := by
  obtain ⟨run, _, finalReads, count⟩ := drive_has_run schemas closed budget reads
  rw [exhausted] at finalReads
  refine ⟨run, count final exhausted, finalReads, ?_⟩
  obtain ⟨next, selected⟩ := exhausted_has_next exhausted
  obtain ⟨firing, admitted, _⟩ :=
    (successor_iff_firing schemas closed finalReads).mp (next?_mem selected)
  exact ⟨firing, admitted⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.Table

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.Table.drive_has_run
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.Table.stopped_has_run
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.Table.exhausted_has_run
