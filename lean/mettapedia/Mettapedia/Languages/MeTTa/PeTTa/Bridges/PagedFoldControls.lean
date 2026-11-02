import Mettapedia.Languages.MeTTa.PeTTa.Bridges.PagedFoldSourceBoundary
import Mettapedia.Languages.MeTTa.PeTTa.PagedFoldLedger

/-! Actual callback pages, source debits, prefixes and pre-execution refusals. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.PagedFoldControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open SpaceSemantics MeTTaIL.WireKit PagedFoldAdmission

def program : Program := {equations := [], declarations := []}
def sumRequest : Request := ⟨program, .named "+", Effects.empty, [1, 2, 3].map number, number 0⟩

def accepted : Entry → Bool
  | .reference _ => false
  | .admitted _ => true

def sourceSession? : Entry → Option Session
  | .reference _ => none
  | .admitted session => some session

theorem sum_admitted : (sourceSession? (prepare 4 sumRequest)).isSome = true := by decide +kernel
def sumSession : Session := (sourceSession? (prepare 4 sumRequest)).get sum_admitted

def summary (state : PagedFold.State) : Option Atom × List Atom × Nat × Nat :=
  (match state.phase with | .done _ value => some value | _ => none,
    state.prefixes, state.sourceDebit, state.hostDebit)

theorem actual_sum_source_steps_and_host_steps :
    summary (PagedFold.run program (.named "+") 100 sumRequest.start).1 =
      (some (number 6), [1, 3, 6].map number, 42, 7) := by decide +kernel

theorem unused_budget_is_not_charged :
    (PagedFold.run program (.named "+") 100 sumRequest.start).2 = 49 := by decide +kernel

theorem one_step_pages_reach_the_same_sum :
    summary (pages 1 49 sumSession).current = (some (number 6), [1, 3, 6].map number, 42, 7) := by
  rw [pages_are_one_slice]
  decide +kernel

theorem page_inside_a_callback_does_not_restart_it :
    PagedFold.run program (.named "+") (7 + 42) sumRequest.start =
      let first := PagedFold.run program (.named "+") 7 sumRequest.start
      let later := PagedFold.run program (.named "+") 42 first.1
      (later.1, first.2 + later.2) := PagedFold.split_pages program (.named "+") 7 42 sumRequest.start

theorem zero_quantum_never_fabricates_completion :
    summary (pages 0 100 sumSession).current = (none, [], 0, 0) := by
  rw [zero_quantum_keeps_pending_state]
  decide +kernel

def falseCallback : FoldSource.Callback := .inline [] "a" "x" (Effects.boolean false)
def falseRequest : Request := ⟨program, falseCallback, Effects.empty, [number 1, number 1], number 0⟩

theorem repeated_occurrences_return_two_false_values :
    accepted (prepare 4 falseRequest) = true ∧
      summary (PagedFold.run program falseCallback 50 falseRequest.start).1 =
        (some (Effects.boolean false), [Effects.boolean false, Effects.boolean false], 2, 5) := by decide +kernel

def emptyRequest : Request := ⟨program, .named "never-called", Effects.empty, [], .symbol "kept"⟩

theorem empty_fold_does_not_require_a_callable_reducer :
    accepted (prepare 4 emptyRequest) = true ∧
      summary (PagedFold.run program emptyRequest.callback 1 emptyRequest.start).1 =
        (some (.symbol "kept"), [], 0, 1) := by decide +kernel

def multiple : Request :=
  ⟨program, .inline [] "a" "x" (apply "superpose" [.expression [number 1, number 1]]),
    Effects.empty, [number 7], number 0⟩
def missing : Request := ⟨program, .inline [] "a" "x" (apply "empty" []), Effects.empty, [number 7], number 0⟩
def printing : Request := ⟨program, .inline [] "a" "x" (apply "println!" [.var "x"]), Effects.empty, [number 7], number 0⟩

theorem empty_multiple_and_effectful_callbacks_refuse_before_execution :
    accepted (prepare 6 multiple) = false ∧ accepted (prepare 6 missing) = false ∧
      accepted (prepare 6 printing) = false := by decide +kernel

def boundaryOutput (state : PagedFold.State) : Option (List Atom) :=
  match state.phase with
  | .boundary _ (.complete _ _ _ output) => some output
  | .boundary _ (.fault _ configuration) => some configuration.output
  | _ => none

theorem raw_effectful_probe_retains_the_printed_occurrence :
    boundaryOutput (PagedFold.run program printing.callback 50 printing.start).1 = some [number 7] := by decide +kernel

def failing : Request :=
  ⟨program, .inline [] "a" "x"
    (apply "let" [.var "ignored", apply "println!" [.var "x"], apply "%" [number 1, number 0]]),
    Effects.empty, [number 7, number 9], number 0⟩

def boundaryFault (state : PagedFold.State) : Option (Effects.Fault × List Atom × List Atom) :=
  match state.phase with
  | .boundary call (.fault reason configuration) => some (reason, configuration.output, call.remaining)
  | _ => none

theorem fault_retains_output_and_unprocessed_suffix :
    boundaryFault (PagedFold.run program failing.callback 100 failing.start).1 =
      some (.zeroDivisor, [number 7], [number 9]) := by decide +kernel

theorem failed_callback_cannot_replay_its_published_prefix :
    let stopped := (PagedFold.run program failing.callback 100 failing.start).1
    (PagedFold.run program failing.callback 100 stopped).1 = stopped := by
  let stopped := (PagedFold.run program failing.callback 100 failing.start).1
  have terminal : PagedFold.step program failing.callback stopped = none := by
    have observed := fault_retains_output_and_unprocessed_suffix
    change boundaryFault stopped = some _ at observed
    cases shape : stopped.phase with
    | ready | running | done => simp [boundaryFault, shape] at observed
    | boundary => simp [PagedFold.step, shape]
  have frozen := Mettapedia.Machines.MachineCore.runSlice_of_final
    (PagedFold.core program failing.callback) stopped terminal 100
  have projected := congrArg (fun page : PagedFold.State × Nat => page.1) frozen
  exact projected

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.PagedFoldControls
