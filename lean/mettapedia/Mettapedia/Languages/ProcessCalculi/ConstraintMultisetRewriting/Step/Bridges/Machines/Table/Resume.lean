import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.Table.Driver

/-!
# Exact resumption of the executable target-table driver

Resuming uses the retained target row. The same static table and first-rule
policy yield exactly the result of a combined event budget, including the
stopped/exhausted distinction. No source evaluator is involved in this law.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.Table

open NamesOnTheStep (Expr)

def resume (schemas : List Schema) (later : Nat) (result : Result) : Result :=
  drive schemas later result.row

theorem resume_drive (schemas : List Schema) (first later : Nat) (row : Expr) :
    resume schemas later (drive schemas first row) = drive schemas (first + later) row := by
  induction first generalizing row with
  | zero =>
      cases selected : next? schemas row <;> simp [resume, drive, selected, Result.row]
  | succ first ih =>
      cases selected : next? schemas row with
      | none =>
          cases later <;> simp [resume, drive, selected, Result.row]
      | some after =>
          simpa only [drive, selected, Nat.succ_add] using ih after

theorem stopped_resume {schemas : List Schema} {first : Nat} {row final : Expr}
    (stopped : drive schemas first row = .stopped final) (later : Nat) :
    resume schemas later (.stopped final) = .stopped final := by
  have terminal := stopped_is_normal stopped
  cases later <;> simp [resume, drive, terminal, Result.row]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.Table

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.Table.resume_drive
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.Table.stopped_resume
