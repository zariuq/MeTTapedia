import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ReadOnlyQuerySource

/-!
# Common execution boundary for prepared read-only source regions

The optional certificate fixes the exact source, caller and program. Missing
or stale preparation resumes reference execution at the unchanged entrance;
exact-page observation always keeps the reference evaluator. A committed
shortcut has an actual source run, and every completed source observation is
preserved. This entrance adapter is not an effectful-operand replay adapter.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ReadOnlyRegionExecution

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Eval SpaceSemantics ReadOnlyQuerySource

def execute (observation : PureCallExtraction.Observation) (fuel : Nat)
    (program : Program) (caller : Subst) (state : Effects.State) (source : Atom)
    (prepared : Option (Certified program caller source)) : Outcome :=
  match observation with
  | .exactPage => run program fuel {state, control := .evaluate caller source}
  | .completedResult => match prepared with
    | none => run program fuel {state, control := .evaluate caller source}
    | some compiled => if Valid compiled.reads.dedup state then .complete state compiled.values [] []
        else run program fuel {state, control := .evaluate caller source}

theorem no_certificate_uses_reference (observation : PureCallExtraction.Observation) (fuel : Nat)
    (program : Program) (caller : Subst) (state : Effects.State) (source : Atom) :
    execute observation fuel program caller state source none =
      run program fuel {state, control := .evaluate caller source} := by cases observation <;> rfl

theorem exact_page_uses_reference (fuel : Nat) (program : Program) (caller : Subst)
    (state : Effects.State) (source : Atom) (prepared : Option (Certified program caller source)) :
    execute .exactPage fuel program caller state source prepared =
      run program fuel {state, control := .evaluate caller source} := rfl

theorem stale_uses_reference (observation : PureCallExtraction.Observation) (fuel : Nat)
    (program : Program) (caller : Subst) (state : Effects.State) (source : Atom)
    (compiled : Certified program caller source) (stale : ¬Valid compiled.reads state) :
    execute observation fuel program caller state source (some compiled) =
      run program fuel {state, control := .evaluate caller source} := by cases observation <;> simp [execute, stale]

theorem completion_has_source_run (observation : PureCallExtraction.Observation) (fuel : Nat)
    (program : Program) (caller : Subst) (state : Effects.State) (source : Atom)
    (prepared : Option (Certified program caller source)) (after : Effects.State) (answers input output : List Atom)
    (completed : execute observation fuel program caller state source prepared = .complete after answers input output) :
    ∃ sourceFuel, run program sourceFuel {state, control := .evaluate caller source} =
      .complete after answers input output := by
  cases observation with
  | exactPage => exact ⟨fuel, completed⟩
  | completedResult =>
      cases prepared with
      | none => exact ⟨fuel, completed⟩
      | some compiled =>
          by_cases valid : Valid compiled.reads state
          · have same : state = after ∧ compiled.values = answers ∧ [] = input ∧ [] = output := by
              simpa [execute, valid] using completed
            obtain ⟨rfl, rfl, rfl, rfl⟩ := same
            exact (completed_iff compiled state valid state compiled.values [] []).mpr ⟨rfl, rfl, rfl, rfl⟩
          · exact ⟨fuel, by simpa [execute, valid] using completed⟩

theorem preserves_completed_source (observation : PureCallExtraction.Observation) (fuel : Nat)
    (program : Program) (caller : Subst) (state : Effects.State) (source : Atom)
    (prepared : Option (Certified program caller source)) (after : Effects.State) (answers input output : List Atom)
    (completed : run program fuel {state, control := .evaluate caller source} = .complete after answers input output) :
    execute observation fuel program caller state source prepared = .complete after answers input output := by
  cases observation with
  | exactPage => exact completed
  | completedResult =>
      cases prepared with
      | none => exact completed
      | some compiled =>
          by_cases valid : Valid compiled.reads state
          · obtain ⟨rfl, rfl, rfl, rfl⟩ := (completed_iff compiled state valid after answers input output).mp ⟨fuel, completed⟩
            simp [execute, valid]
          · simpa [execute, valid] using completed

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ReadOnlyRegionExecution
