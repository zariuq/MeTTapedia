import Mettapedia.Languages.MeTTa.SpaceTheory.PeTTaEquationalOnTheStep
import Mettapedia.Languages.MeTTa.SpaceTheory.PeTTaEquationalReplacement

/-! A nonlinear request enters from the written atom, and both selected
copies reach the ordinary ordered return. The absent-equation control
still enters an empty frontier rather than obtaining a spurious match. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SpaceTheory.PeTTaEquationalExamples

open Mettapedia.GSLT.IndexedOperational (ExecutionPath)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open ProgramReplay
open Atoms (Content Preference)
open PeTTaEquationalOnTheStep (Request Shows source theory)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines (exists_reads)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Schematic (SState)

private def a : Atom := .symbol "A"
private def b : Atom := .symbol "B"
private def ok : Atom := .symbol "OK"
private def pendingCall : Atom := .expression [.symbol "same", a, b]
private def representative : Atom := .expression [.symbol "same", a, a]
private def fn : Atom := (Content.definition (.expression [.symbol "same", .var "x", .var "x"]) ok).syntax
private def writtenEq : Atom := (Content.equation .rightward a b []).syntax

private def initial : Snapshot :=
  { core := [fn, writtenEq, fn], spaces := [], cells := [],
    control := .returned [], frames := [], input := [.symbol "keep-input"], output := [.symbol "keep-output"] }

private def requestOf (initial : Snapshot) : Request :=
  ⟨initial.decode.state, pendingCall, initial.frames, initial.input, initial.output⟩

private def selected : List Eval.Control :=
  Eval.clauses (PeTTaExecution.programAt initial.core) "same" [a, a]

private theorem licensed :
    (PeTTaEquationEntry.theory initial.core).Step (.inl pendingCall) (.inr selected) := by
  have sameSymbol : AtomEquations.Equivalent initial.core a b :=
    AtomEquations.authored ⟨.rightward, b, [], List.mem_cons_of_mem fn List.mem_cons_self, List.mem_cons_self⟩
  have sameCall : AtomEquations.Equivalent initial.core pendingCall representative :=
    AtomEquations.fill_equivalent (.child [.symbol "same", a] .hole []) (.symm _ _ sameSymbol)
  refine (PeTTaEquationEntry.entry_exact _ _ _).mpr ⟨representative, sameCall, ?_⟩
  apply PeTTaEquationEntry.select_ready initial.core "same" [a, a] (by decide +kernel) (by decide +kernel)
  rw [PeTTaExecution.programAt_exact]
  decide +kernel

private theorem visible (initial : Snapshot) : ∃ start : SState Nat, Shows (.ready (requestOf initial)) start := by
  obtain ⟨start, read⟩ := exists_reads {PeTTaEquationalOnTheStep.encode (.ready (requestOf initial)) initial.cellNames}
  exact ⟨start, initial.cellNames, initial.decode_empty_tail, initial.decode_cell_support, read⟩

private def entered : Snapshot := {initial with control := .sequence selected []}
private def finished : Snapshot := LiveRegistry.nativeAdvance 24 entered

theorem raw_alias_returns_both_occurrences :
    ∃ start final, Shows (.ready (requestOf initial)) start ∧
      ∃ fired : ExecutionPath source (.ready (requestOf initial)) (.running finished.decode),
        fired.length = (LiveRegistry.emitTrace 24 entered).length + 1 ∧
        (∃ physical : ExecutionPath (theory Nat) start final, physical.length = fired.length ∧
          Shows (.running finished.decode) final) ∧
        finished.control = .returned [ok, ok] ∧ finished.input = initial.input ∧ finished.output = initial.output := by
  obtain ⟨start, shown⟩ := visible initial
  obtain ⟨continuation, tailLength⟩ := PeTTaLiveOnTheStep.snapshot_budget_path 24 entered
  let fired : ExecutionPath source (.ready (requestOf initial)) (.running finished.decode) :=
    .cons ⟨.enter licensed⟩ (PeTTaEquationalOnTheStep.ordinaryPath continuation)
  obtain ⟨final, physical, after, length⟩ := PeTTaEquationalOnTheStep.realize_path shown fired
  exact ⟨start, final, shown, fired,
    congrArg (· + 1) ((PeTTaEquationalOnTheStep.ordinary_path_length continuation).trans tailLength),
    ⟨physical, length, after⟩, by decide +kernel⟩

open Mettapedia.GSLT.Contracts.OccurrenceExecution (batches nodes completed readCompleted reports ofTerm
  flattened_settling_batch)
open EvaluationObservations (pettaEquationalView pettaEmit petta_equational_reports_iff
  petta_equational_step_starts_pending)

theorem aliased_call_reports_two_on_transform :
    ∃ mark : SState Nat, Shows (.ready (requestOf initial)) mark ∧
      let observations := readCompleted (sys := theory Nat)
        (ofTerm Shows pettaEquationalView) (·.isSome = true) pettaEmit mark
      reports observations .ordered [ok, ok] ∧ reports observations .count (2 : Nat) := by
  obtain ⟨start, _, shown, run, _, _, _, _, _⟩ := raw_alias_returns_both_occurrences
  let trace := batches pettaEmit ((nodes run).map pettaEquationalView)
  have answer : pettaEquationalView (.running finished.decode) = some [ok, ok] := by decide +kernel
  have ordered : trace.flatten = [ok, ok] :=
    flattened_settling_batch (sys := source) pettaEquationalView
      petta_equational_step_starts_pending run rfl answer
  have settled : (pettaEquationalView (.running finished.decode)).isSome = true := by rw [answer]; rfl
  have returned : completed (sys := source) pettaEquationalView (·.isSome = true) pettaEmit
      (.ready (requestOf initial)) trace := ⟨_, run, settled, rfl⟩
  refine ⟨start, shown, (petta_equational_reports_iff shown .ordered [ok, ok]).mp ⟨trace, returned, ordered⟩, ?_⟩
  exact (petta_equational_reports_iff shown .count (2 : Nat)).mp
    ⟨trace, returned, congrArg List.length ordered⟩

private def diagnostics : Atom := .symbol "diagnostics"
private def live : Snapshot := {initial with core := initial.core ++ [diagnostics]}

theorem aliased_call_reuses_older_snapshot :
    ∃ mark : SState Nat, Shows (.ready (requestOf live)) mark ∧
      let observations := readCompleted (sys := theory Nat (fun _ => initial.core))
        (ofTerm Shows pettaEquationalView) (·.isSome = true) pettaEmit mark
      reports observations .ordered [ok, ok] ∧ reports observations .count (2 : Nat) := by
  have agrees : PeTTaEquationalReplacement.EntryAgreement initial.core live.core pendingCall := by
    apply PeTTaEquationalReplacement.inert_extension
    · rintro a b ⟨_, _, _, written, _⟩
      have impossible := List.mem_singleton.mp written
      cases impossible
    · rw [PeTTaExecution.programAt_exact]
      rfl
  have entered := (PeTTaEquationalReplacement.entry_iff agrees selected).mp licensed
  let next : Snapshot := {live with control := .sequence selected []}
  obtain ⟨rest, _⟩ := PeTTaLiveOnTheStep.snapshot_budget_path 24 next
  let reached := LiveRegistry.nativeAdvance 24 next
  let run : ExecutionPath source (.ready (requestOf live)) (.running reached.decode) :=
    .cons ⟨.enter entered⟩ (PeTTaEquationalOnTheStep.ordinaryPath rest)
  let trace := batches pettaEmit ((nodes run).map pettaEquationalView)
  have answer : pettaEquationalView (.running reached.decode) = some [ok, ok] := by decide +kernel
  have ordered : trace.flatten = [ok, ok] :=
    flattened_settling_batch (sys := source) pettaEquationalView
      petta_equational_step_starts_pending run rfl answer
  have settled : (pettaEquationalView (.running reached.decode)).isSome = true := by rw [answer]; rfl
  have returned : completed (sys := source) pettaEquationalView (·.isSome = true) pettaEmit
      (.ready (requestOf live)) trace := ⟨_, run, settled, rfl⟩
  obtain ⟨mark, shown⟩ := visible live
  have guarded : PeTTaEquationalReplacement.ProtectedAt initial.core
      (.ready (requestOf live)) := .ready _ agrees.symm
  exact ⟨mark, shown,
    (PeTTaEquationalReplacement.protected_reports_on_transform _ shown guarded .ordered [ok, ok]).mp
      ⟨trace, returned, ordered⟩,
    (PeTTaEquationalReplacement.protected_reports_on_transform _ shown guarded .count (2 : Nat)).mp
      ⟨trace, returned, congrArg List.length ordered⟩⟩

private def edited : Snapshot := {initial with core := [fn, fn]}

private theorem no_generator (lhs rhs : Atom) : ¬ AtomEquations.Generator edited.core lhs rhs := by
  rintro ⟨preference, opposite, others, member, _⟩
  cases preference <;> simp [edited, fn, Content.syntax, Preference.symbol] at member

private theorem emptySelection : PeTTaEquationEntry.select edited.core pendingCall = some [] := by
  decide +kernel

/-- Entry after removing the equation has exactly the empty frontier
on every firing. It does not invalidate the ordinary call itself. -/
theorem absent_alias_reads_empty_frontier :
    ∃ start finish, Shows (.ready (requestOf edited)) start ∧
      (theory Nat).Step start finish ∧
      ∀ after, (theory Nat).Step start after → Shows (.running ((requestOf edited).entered [])) after := by
  obtain ⟨start, shown⟩ := visible edited
  have legal : source.Step (.ready (requestOf edited)) (.running ((requestOf edited).entered [])) :=
    .enter ((PeTTaEquationEntry.entry_without_equations edited.core no_generator pendingCall []).mpr emptySelection)
  obtain ⟨finish, fired, _⟩ := PeTTaEquationalOnTheStep.realize_step shown legal
  refine ⟨start, finish, shown, fired, ?_⟩
  intro after claimed
  obtain ⟨_, actual, read⟩ := PeTTaEquationalOnTheStep.reflect_step shown claimed
  cases actual with
  | enter admitted =>
    have chosen := (PeTTaEquationEntry.entry_without_equations edited.core no_generator pendingCall _).mp admitted
    obtain rfl := Option.some.inj (chosen.symm.trans emptySelection)
    exact read

end Mettapedia.Languages.MeTTa.SpaceTheory.PeTTaEquationalExamples
