import Mettapedia.Languages.MeTTa.PeTTa.Eval
import Mettapedia.Machines.ResumableRegion

/-!
# Exact source-evaluator debit and retained pages

The existing generic resumable machine executes the actual PeTTa transition
function. Its endpoint readout agrees with the independently defined PeTTa
runner, including completed empty answers, faults, stores and I/O. The debit
counts source transitions actually taken, not the supplied allowance or a
different machine's ticks. Split pages retain the exact configuration.

This is accounting for the declared evaluator profile. It does not identify
these transitions with native instruction counts or wall time.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.EvaluatorAccounting

open Mettapedia.Machines
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Eval SpaceSemantics
open private path_trans from Mettapedia.Languages.MeTTa.PeTTa.Eval

structure Invocation where
  world : Effects.State
  caller : Subst
  source : Atom
  input : List Atom := []
  output : List Atom := []

abbrev core (program : Program) : MachineCore Invocation where
  State := Configuration
  load invocation := {
    state := invocation.world, control := .evaluate invocation.caller invocation.source,
    input := invocation.input, output := invocation.output }
  step := Eval.step program

abbrev slice (program : Program) := (core program).runSlice

def observe (program : Program) (configuration : Configuration) : Outcome := Eval.run program 0 configuration

theorem no_step_run (program : Program) (configuration : Configuration)
    (stopped : Eval.step program configuration = none) (fuel : Nat) :
    Eval.run program fuel configuration = Eval.run program 0 configuration := by
  cases configuration with
  | mk world control frames input output =>
      cases control <;> cases frames <;> cases fuel <;> simp only [Eval.run, stopped]

theorem slice_outcome_exact (program : Program) (fuel : Nat) (configuration : Configuration) :
    observe program (slice program fuel configuration).1 = Eval.run program fuel configuration := by
  induction fuel generalizing configuration with
  | zero => rfl
  | succ fuel ih =>
      cases advanced : Eval.step program configuration with
      | none =>
          simp only [slice, MachineCore.runSlice, core, advanced]
          exact (no_step_run program configuration advanced (fuel + 1)).symm
      | some next =>
          simp only [slice, MachineCore.runSlice, core, advanced]
          exact (ih next).trans (run_succ_of_step program fuel configuration next advanced).symm

theorem debit_replays_source (program : Program) (fuel : Nat) (configuration : Configuration) :
    Eval.run program (slice program fuel configuration).2 configuration = Eval.run program fuel configuration := by
  rw [← slice_outcome_exact program _ configuration, ← slice_outcome_exact program fuel configuration]
  exact congrArg (fun page => observe program page.1)
    (MachineCore.runSlice_replay_used (core program) fuel configuration)

theorem debit_bounded (program : Program) (fuel : Nat) (configuration : Configuration) :
    (slice program fuel configuration).2 ≤ fuel := MachineCore.runSlice_used_le (core program) fuel configuration

theorem split_pages (program : Program) (first second : Nat) (configuration : Configuration) :
    slice program (first + second) configuration =
      let left := slice program first configuration
      let right := slice program second left.1
      (right.1, left.2 + right.2) := MachineCore.runSlice_add (core program) first second configuration

theorem resume_outcome (program : Program) (first second : Nat) (configuration : Configuration) :
    Eval.run program second (slice program first configuration).1 = Eval.run program (first + second) configuration := by
  have split := congrArg (fun page : Configuration × Nat => observe program page.1)
    (split_pages program first second configuration)
  exact (slice_outcome_exact program second (slice program first configuration).1).symm.trans
    (split.symm.trans (slice_outcome_exact program (first + second) configuration))

theorem finite_source_path (program : Program) (fuel : Nat) (configuration : Configuration) :
    (theory program).MultiStep configuration (slice program fuel configuration).1 := by
  have lift : ∀ first last, (core program).Steps first last → (theory program).MultiStep first last := by
    intro first last steps
    induction steps with
    | refl => exact .refl _
    | @tail middle last _ advanced ih => exact path_trans ih (.step (step_transition advanced) (.refl _))
  exact lift _ _ (MachineCore.runSlice_steps (core program) fuel configuration)

theorem step_is_pending (program : Program) (first second : Configuration)
    (advanced : Eval.step program first = some second) : observe program first = .exhausted first := by
  cases first with
  | mk world control frames input output =>
      cases control <;> cases frames <;> first | rfl | simp [Eval.step] at advanced

theorem observe_complete_iff (program : Program) (configuration : Configuration)
    (world : Effects.State) (answers input output : List Atom) :
    observe program configuration = .complete world answers input output ↔
      configuration = finished world answers input output := by
  cases configuration with
  | mk current control frames incoming outgoing =>
      cases control <;> cases frames <;>
        simp [observe, Eval.run, finished, Configuration.mk.injEq, Outcome.complete.injEq, and_comm]

theorem pure_return_has_exact_slice (program : Program) (caller : Subst) (before after : Effects.State)
    (source value : Atom) (returns : PureReturns program caller before source after value) :
    ∃ debit, slice program debit {state := before, control := .evaluate caller source} =
      (finished after [value] [] [], debit) := by
  obtain ⟨fuel, completed⟩ := pure_returns_has_sufficient_fuel program caller before after source value returns
  let initial : Configuration := {state := before, control := .evaluate caller source}
  have endpoint := (observe_complete_iff program (slice program fuel initial).1 after [value] [] []).mp
    ((slice_outcome_exact program fuel initial).trans completed)
  refine ⟨(slice program fuel initial).2, ?_⟩
  change slice program (slice program fuel initial).2 initial = _
  exact (MachineCore.runSlice_replay_used (core program) fuel initial).trans (Prod.ext endpoint rfl)

theorem finished_has_no_additional_debit (program : Program) (fuel : Nat)
    (world : Effects.State) (answers input output : List Atom) :
    slice program fuel (finished world answers input output) = (finished world answers input output, 0) :=
  MachineCore.runSlice_of_final (core program) _ rfl fuel

theorem fault_has_no_additional_debit (program : Program) (fuel : Nat)
    (world : Effects.State) (reason : Effects.Fault) (frames : List Frame) (input output : List Atom) :
    slice program fuel {state := world, control := .fault reason, frames, input, output} =
      ({state := world, control := .fault reason, frames, input, output}, 0) :=
  MachineCore.runSlice_of_final (core program) _ rfl fuel

theorem unused_allowance_is_not_charged (program : Program) (fuel : Nat) (configuration : Configuration)
    (early : (slice program fuel configuration).2 < fuel) :
    Eval.step program (slice program fuel configuration).1 = none :=
  MachineCore.runSlice_under_budget_final (core program) fuel configuration early

namespace Controls

def program : Program := {equations := [], declarations := []}

theorem zero_allowance_keeps_the_whole_receiver (configuration : Configuration) :
    slice program 0 configuration = (configuration, 0) := rfl

theorem false_is_one_answer_not_an_empty_fold (world : Effects.State) :
    observe program (slice program 10 (Eval.start world (Effects.boolean false))).1 =
      .complete world [Effects.boolean false] [] [] := by
  rw [slice_outcome_exact]
  rfl

theorem a_literal_costs_one_source_transition (world : Effects.State) :
    (slice program 10 (Eval.start world (.grounded (.int 7)))).2 = 1 := rfl

theorem completed_empty_is_not_pending (world : Effects.State) :
    observe program (finished world [] [] []) = .complete world [] [] [] ∧
      observe program (Eval.start world (.symbol "pending")) = .exhausted (Eval.start world (.symbol "pending")) := ⟨rfl, rfl⟩

end Controls

end Mettapedia.Languages.MeTTa.PeTTa.EvaluatorAccounting
