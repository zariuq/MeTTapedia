import Mettapedia.Languages.MeTTa.SpaceTheory.PeTTaLiveOnTheStep

/-! Concrete ordered reads before and after actual edits of the core space. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SpaceTheory.PeTTaLiveExamples

open Mettapedia.GSLT.IndexedOperational (ExecutionPath)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open ProgramReplay
open PeTTaLiveOnTheStep (theory)

private def token : Atom := .symbol "Token"
private def call : Atom := .expression [.symbol "fresh", token]
private def definition : Atom :=
  .expression [.symbol "=", .expression [.symbol "fresh", .var "x"], .var "x"]

private def edit (direction : String) : Atom := .expression [.symbol direction, .symbol "&self", definition]
private def bind (name : String) (value body : Atom) : Atom :=
  .expression [.symbol "let", .var name, value, body]

private def sequence : Atom :=
  bind "installed" (edit "add-atom") <|
    bind "first" call <|
      bind "removed" (edit "remove-atom") <|
        .expression [.symbol "pair", .var "first", call]

private def initial : Snapshot :=
  { core := [], spaces := [], cells := [], control := .evaluate [] sequence, frames := [], input := [], output := [] }

private def answer : Atom := .expression [.symbol "pair", token, call]
private def endSnapshot : Snapshot := LiveRegistry.nativeAdvance 96 initial

private theorem finished : endSnapshot.core = [] ∧ endSnapshot.control = .returned [answer] ∧ endSnapshot.frames = [] := by
  decide +kernel

/-- A single run inserts a function, calls it, removes it, and calls the
same expression again. The first answer is a value and the second is data. -/
theorem insertion_then_removal_changes_only_later_calls :
    ∃ start final, EvalOnTheStep.Shows initial.decode start ∧
      ∃ fired : ExecutionPath (theory Nat) start final,
        EvalOnTheStep.Shows endSnapshot.decode final ∧
        fired.length = (LiveRegistry.emitTrace 96 initial).length ∧
        endSnapshot.decode.state.core = [] ∧ endSnapshot.decode.control = .returned [answer] ∧
        endSnapshot.decode.frames = [] := by
  obtain ⟨start, shown⟩ := PeTTaLiveOnTheStep.shows_snapshot initial
  obtain ⟨final, fired, done, length⟩ := PeTTaLiveOnTheStep.realizes_snapshot_budget 96 initial shown
  exact ⟨start, final, shown, fired, done, length, finished⟩

/-- Negative control: holding the initial registry throughout misses
the function during the interval in which the space contains it. -/
theorem pinned_initial_registry_misses_the_new_definition :
    (retainedSnapshot (PeTTaExecution.programAt []) 96 initial).control =
      .returned [.expression [.symbol "pair", call, call]] ∧
    (retainedSnapshot (PeTTaExecution.programAt []) 96 initial).control ≠ endSnapshot.control := by
  decide +kernel

private def selected : List Eval.Control :=
  Eval.clauses (PeTTaExecution.programAt [definition, definition]) "fresh" [token]

private def pending : Snapshot :=
  { initial with control := .sequence selected [] }

/-- The selected alternatives come from two equal occurrences before the
edit. Starting their resume in the empty core still returns two values. -/
theorem captured_definitions_survive_missing_source :
    ∃ start final, EvalOnTheStep.Shows pending.decode start ∧
      ∃ fired : ExecutionPath (theory Nat) start final,
        EvalOnTheStep.Shows (LiveRegistry.nativeAdvance 24 pending).decode final ∧
        fired.length = (LiveRegistry.emitTrace 24 pending).length ∧
        (LiveRegistry.nativeAdvance 24 pending).control = .returned [token, token] := by
  obtain ⟨start, shown⟩ := PeTTaLiveOnTheStep.shows_snapshot pending
  obtain ⟨final, fired, done, length⟩ := PeTTaLiveOnTheStep.realizes_snapshot_budget 24 pending shown
  exact ⟨start, final, shown, fired, done, length, by decide +kernel⟩

private def operand : Atom := .expression [.symbol "add-atom", .symbol "&self", .symbol "effect"]
private def awaiting : Snapshot :=
  { initial with core := [definition], control := .arguments [] (.function "fresh") [operand] [] 0 }
private def rawAssignment : Atom :=
  .expression [.symbol ":", .symbol "fresh", .expression [.symbol "->", .symbol "Atom", .symbol "Atom"]]
private def newlyTyped : Snapshot := { awaiting with core := [definition, rawAssignment] }

/-- A type assignment in the reached space governs the next argument.
The untyped task schedules an evaluation; the typed one returns the
write-shaped operand as data in that same semantic step. -/
theorem live_type_assignment_changes_next_demand :
    ∃ plain typed plainNext typedNext,
      EvalOnTheStep.Shows awaiting.decode plain ∧ EvalOnTheStep.Shows newlyTyped.decode typed ∧
      (theory Nat).Step plain plainNext ∧ (theory Nat).Step typed typedNext ∧
      EvalOnTheStep.Shows (LiveRegistry.nativeAdvance 1 awaiting).decode plainNext ∧
      EvalOnTheStep.Shows (LiveRegistry.nativeAdvance 1 newlyTyped).decode typedNext ∧
      (LiveRegistry.nativeAdvance 1 awaiting).control = .evaluate [] operand ∧
      (LiveRegistry.nativeAdvance 1 newlyTyped).control = .returned [operand] := by
  obtain ⟨plain, shownPlain⟩ := PeTTaLiveOnTheStep.shows_snapshot awaiting
  obtain ⟨typed, shownTyped⟩ := PeTTaLiveOnTheStep.shows_snapshot newlyTyped
  have stepFor (before : Snapshot) (computed : LiveRegistry.nativeStep before = some (LiveRegistry.nativeAdvance 1 before)) :
      LiveRegistry.theory.Step before.decode (LiveRegistry.nativeAdvance 1 before).decode :=
    LiveRegistry.nativeStep_source _ _ computed
  obtain ⟨plainNext, plainFires, plainResult⟩ := PeTTaLiveOnTheStep.realize_step shownPlain (stepFor awaiting (by decide +kernel))
  obtain ⟨typedNext, typedFires, typedResult⟩ :=
    PeTTaLiveOnTheStep.realize_step shownTyped (stepFor newlyTyped (by decide +kernel))
  exact ⟨plain, typed, plainNext, typedNext, shownPlain, shownTyped, plainFires, typedFires,
    plainResult, typedResult, by decide +kernel⟩

end Mettapedia.Languages.MeTTa.SpaceTheory.PeTTaLiveExamples
