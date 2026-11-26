import Mettapedia.Machines.TIsa.Derivation.SymbolicSearch
import Mettapedia.Machines.TIsa.Derivation.SnapshotMachine

/-!
# The symbolic one-firing instance of the snapshot machine

The shared machine carries the remaining choices, a principal
solution, and a checked publication across its continuations.
For one firing the geometric search is complete at the entry world:
quiescence means there is no admitted source firing, not that a
particular opening or allocation failed.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.Derivation.SymbolicFiring

open Mettapedia.Logic.LP
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting

variable {signature : LPSignature}
  [DecidableEq signature.vars] [DecidableEq signature.constants] [DecidableEq signature.functionSymbols]
  (slots : signature.vars ≃ ℕ) (rules : Rules signature)

def phases : SnapshotMachine.Phases (LiveWorld signature) where
  Candidate := Attempt rules
  Pending := Pending rules
  Accepted := Accepted rules

def schedule : SnapshotMachine.Schedule (phases rules) where
  options := attempts slots rules
  prepare := Attempt.solve
  verify := Pending.check
  publish := Accepted.publish

abbrev Outcome (signature : LPSignature) := SnapshotMachine.Outcome (LiveWorld signature)
abbrev Config := SnapshotMachine.Config (phases rules)

abbrev run := SnapshotMachine.run (schedule slots rules)
abbrev runK {R : Type*} (finish : Outcome signature → R) :=
  SnapshotMachine.runK (schedule slots rules) finish

abbrev transition := SnapshotMachine.transition (schedule slots rules)
abbrev Runs := SnapshotMachine.Runs (schedule slots rules)
abbrev scanResult := SnapshotMachine.scanResult (phases rules)

@[simp] theorem schedule_search (before : LiveWorld signature) :
    SnapshotMachine.search (schedule slots rules) before = search slots rules before := rfl

@[simp] theorem schedule_publish {before : LiveWorld signature} (accepted : Accepted rules before) :
    (schedule slots rules).publish accepted = accepted.publish := rfl

theorem runK_eq {R : Type*} (finish : Outcome signature → R) (fuel : ℕ) (before : LiveWorld signature) :
    runK slots rules finish fuel before = finish (run slots rules fuel before) :=
  SnapshotMachine.runK_eq (schedule slots rules) finish fuel before

theorem scan_reaches (fuel : ℕ) (before : LiveWorld signature) (queries : List (Attempt rules before)) :
    Runs slots rules (.scan fuel before queries) (scanResult rules fuel before (queries.findSome? Attempt.check)) :=
  SnapshotMachine.scan_reaches (schedule slots rules) fuel before queries

theorem complete_run (fuel : ℕ) (before : LiveWorld signature) :
    Runs slots rules (.entry fuel before) (.halt (run slots rules fuel before)) :=
  SnapshotMachine.complete_run (schedule slots rules) fuel before

theorem machine_run_iff (fuel : ℕ) (before : LiveWorld signature) (outcome : Outcome signature) :
    Runs slots rules (.entry fuel before) (.halt outcome) ↔ outcome = run slots rules fuel before :=
  SnapshotMachine.machine_run_iff (schedule slots rules) fuel before outcome

inductive Licensed : ℕ → LiveWorld signature → Outcome signature → Prop
  | quiet {fuel before} :
    (∀ source : Firing before.state rules.program, ¬source.Admits (act signature) before.state) →
    Licensed fuel before (.quiescent before)
  | budget {before} :
    (∃ source : Firing before.state rules.program, source.Admits (act signature) before.state) →
    Licensed 0 before (.exhausted before)
  | fire {fuel before outcome} (source : Firing before.state rules.program)
      (made : source.selection.made = before.reserve 0 source.selection.made.length) :
    source.Admits (act signature) before.state → Licensed fuel (before.commit source made) outcome →
    Licensed (fuel + 1) before outcome

theorem run_licensed (fuel : ℕ) (before : LiveWorld signature) :
    Licensed rules fuel before (run slots rules fuel before) := by
  induction fuel generalizing before with
  | zero =>
    cases found : search slots rules before with
    | none => simpa [run, SnapshotMachine.run, found] using Licensed.quiet (fuel := 0) ((search_empty_iff slots rules before).mp found)
    | some success =>
      simpa [run, SnapshotMachine.run, found] using Licensed.budget (rules := rules) ⟨success.selected.firing, success.admissible⟩
  | succ fuel ih =>
    cases found : search slots rules before with
    | none =>
      simpa [run, SnapshotMachine.run, found] using Licensed.quiet (fuel := fuel + 1) ((search_empty_iff slots rules before).mp found)
    | some success =>
      simpa [run, SnapshotMachine.run, found] using Licensed.fire success.selected.firing success.allocation
        success.admissible (ih success.publish)

theorem every_complete_run_is_licensed (fuel : ℕ) (before : LiveWorld signature) (outcome : Outcome signature)
    (reached : Runs slots rules (.entry fuel before) (.halt outcome)) : Licensed rules fuel before outcome :=
  ((machine_run_iff slots rules fuel before outcome).mp reached).symm ▸ run_licensed slots rules fuel before

end Mettapedia.Machines.TIsa.Derivation.SymbolicFiring
