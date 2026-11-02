import Mettapedia.Languages.MeTTa.PeTTa.EvaluatorAccounting
import Mettapedia.Languages.MeTTa.PeTTa.FoldSource

/-!
# A retained host-fold driver over actual evaluator steps

Each callback runs in the existing PeTTa evaluator. Its full configuration,
entrance, accumulator, item and remaining list remain available across pages.
The driver separates source transitions from host dispatch/return transitions.
Unexpected callback outcomes retain the actual outcome and receiver; there is
no post-execution transition back to an untouched reference invocation.

The source correspondence below is for certified single-answer callbacks.
Effects and nondeterministic callbacks must not be entered speculatively:
collecting all callback answers before the suffix could change SWI interleaving.
The defensive boundary is diagnostic, not a claimed native choicepoint codec.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.PagedFold

open Mettapedia.Machines
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Eval SpaceSemantics

def callStart (callback : FoldSource.Callback) (world : Effects.State) (accumulator item : Atom) : Configuration :=
  {state := world, control := .evaluate (FoldSource.bindings callback accumulator item) (FoldSource.expression callback)}

structure Call where
  accumulator : Atom
  item : Atom
  remaining : List Atom
  entrance : Configuration
  current : Configuration

inductive Phase
  | ready (world : Effects.State) (items : List Atom) (accumulator : Atom)
  | running (call : Call)
  | done (world : Effects.State) (value : Atom)
  | boundary (call : Call) (outcome : Outcome)

structure State where
  phase : Phase
  prefixes : List Atom := []
  sourceDebit : Nat := 0
  hostDebit : Nat := 0

def State.total (state : State) : Nat := state.sourceDebit + state.hostDebit

def step (program : Program) (callback : FoldSource.Callback) (state : State) : Option State :=
  match state.phase with
  | .done _ _ | .boundary _ _ => none
  | .ready world [] accumulator => some {state with phase := .done world accumulator, hostDebit := state.hostDebit + 1}
  | .ready world (item :: rest) accumulator =>
      let initial := callStart callback world accumulator item
      some {state with phase := .running ⟨accumulator, item, rest, initial, initial⟩, hostDebit := state.hostDebit + 1}
  | .running call =>
      match EvaluatorAccounting.observe program call.current with
      | .complete world [value] [] [] =>
          some {state with
            phase := .ready world call.remaining value
            prefixes := state.prefixes ++ [value], hostDebit := state.hostDebit + 1}
      | .exhausted _ =>
          match Eval.step program call.current with
          | some next => some {state with phase := .running {call with current := next}, sourceDebit := state.sourceDebit + 1}
          | none => some {state with phase := .boundary call (.exhausted call.current), hostDebit := state.hostDebit + 1}
      | outcome => some {state with phase := .boundary call outcome, hostDebit := state.hostDebit + 1}

structure Invocation where
  world : Effects.State
  items : List Atom
  initial : Atom

abbrev core (program : Program) (callback : FoldSource.Callback) : MachineCore Invocation where
  State := State
  load input := ⟨.ready input.world input.items input.initial, [], 0, 0⟩
  step := step program callback

abbrev run (program : Program) (callback : FoldSource.Callback) := (core program callback).runSlice

def running (call : Call) (prefixes : List Atom) (sourceDebit hostDebit : Nat) : State :=
  ⟨.running call, prefixes, sourceDebit, hostDebit⟩

theorem running_step (program : Program) (callback : FoldSource.Callback)
    (call : Call) (prefixes : List Atom) (sourceDebit hostDebit : Nat) (next : Configuration)
    (advanced : Eval.step program call.current = some next) :
    step program callback (running call prefixes sourceDebit hostDebit) =
      some (running {call with current := next} prefixes (sourceDebit + 1) hostDebit) := by
  simp only [step, running, EvaluatorAccounting.step_is_pending program call.current next advanced, advanced]

theorem exact_callback_slice (program : Program) (callback : FoldSource.Callback)
    (ticks : Nat) (call : Call) (prefixes : List Atom) (sourceDebit hostDebit : Nat) (next : Configuration)
    (source : EvaluatorAccounting.slice program ticks call.current = (next, ticks)) :
    run program callback ticks (running call prefixes sourceDebit hostDebit) =
      (running {call with current := next} prefixes (sourceDebit + ticks) hostDebit, ticks) := by
  induction ticks generalizing call sourceDebit with
  | zero =>
      have same : call.current = next := congrArg Prod.fst source
      cases call
      cases same
      simp [run, MachineCore.runSlice, running]
  | succ ticks ih =>
      cases advanced : Eval.step program call.current with
      | none =>
          have cost := congrArg Prod.snd source
          simp [EvaluatorAccounting.slice, MachineCore.runSlice, EvaluatorAccounting.core, advanced] at cost
      | some middle =>
          have tailSource : EvaluatorAccounting.slice program ticks middle = (next, ticks) := by
            have endpoint := congrArg Prod.fst source
            have debit := congrArg Prod.snd source
            simp only [EvaluatorAccounting.slice, MachineCore.runSlice, EvaluatorAccounting.core, advanced] at endpoint debit
            exact Prod.ext endpoint (Nat.add_right_cancel debit)
          have first := running_step program callback call prefixes sourceDebit hostDebit middle advanced
          have later := ih {call with current := middle} (sourceDebit + 1) tailSource
          have counted := congrArg (fun page : State × Nat => (page.1, page.2 + 1)) later
          simp only [run, MachineCore.runSlice, core]
          rw [first]
          simpa only [run, core, running, Nat.add_assoc, Nat.add_comm 1] using counted

theorem enter_callback (program : Program) (callback : FoldSource.Callback) (world : Effects.State)
    (item : Atom) (rest prefixes : List Atom) (accumulator : Atom) (sourceDebit hostDebit : Nat) :
    step program callback ⟨.ready world (item :: rest) accumulator, prefixes, sourceDebit, hostDebit⟩ =
      some (running ⟨accumulator, item, rest, callStart callback world accumulator item,
        callStart callback world accumulator item⟩ prefixes sourceDebit (hostDebit + 1)) := rfl

theorem return_callback (program : Program) (callback : FoldSource.Callback)
    (call : Call) (prefixes : List Atom) (sourceDebit hostDebit : Nat)
    (world : Effects.State) (value : Atom) (completed : call.current = finished world [value] [] []) :
    step program callback (running call prefixes sourceDebit hostDebit) =
      some ⟨.ready world call.remaining value, prefixes ++ [value], sourceDebit, hostDebit + 1⟩ := by
  simp [step, running, completed, EvaluatorAccounting.observe]

theorem done_stable (program : Program) (callback : FoldSource.Callback) (world : Effects.State)
    (value : Atom) (prefixes : List Atom) (sourceDebit hostDebit allowance : Nat) :
    run program callback allowance ⟨.done world value, prefixes, sourceDebit, hostDebit⟩ =
      (⟨.done world value, prefixes, sourceDebit, hostDebit⟩, 0) :=
  MachineCore.runSlice_of_final (core program callback) _ rfl allowance

theorem boundary_stable (program : Program) (callback : FoldSource.Callback) (call : Call)
    (outcome : Outcome) (prefixes : List Atom) (sourceDebit hostDebit allowance : Nat) :
    run program callback allowance ⟨.boundary call outcome, prefixes, sourceDebit, hostDebit⟩ =
      (⟨.boundary call outcome, prefixes, sourceDebit, hostDebit⟩, 0) :=
  MachineCore.runSlice_of_final (core program callback) _ rfl allowance

theorem split_pages (program : Program) (callback : FoldSource.Callback) (first second : Nat) (state : State) :
    run program callback (first + second) state =
      let earlier := run program callback first state
      let later := run program callback second earlier.1
      (later.1, earlier.2 + later.2) := MachineCore.runSlice_add (core program callback) first second state

theorem zero_page_retains_every_field (program : Program) (callback : FoldSource.Callback) (state : State) :
    run program callback 0 state = (state, 0) := rfl

end Mettapedia.Languages.MeTTa.PeTTa.PagedFold
