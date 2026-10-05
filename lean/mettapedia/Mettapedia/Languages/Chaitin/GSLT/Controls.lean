import Mettapedia.Languages.Chaitin.GSLT.TuringAdequacy
import Mettapedia.Languages.TuringMachine.ClassicMachines

/-!
# Separating executions of the authored Lisp evaluator

The halting examples use proved source runs and the compositional interpreter
theorem, rather than unfolding a large evaluator budget. Divergence and
incorrect outputs are ruled out by reflection. Dynamic bindings remain
observable, and a blocked effect request is not a successful return.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Chaitin.GSLT

open Mettapedia.Computability.StreamingInput

private theorem runFor_next (source : TuringMachine.Machine) (count : Nat)
    (configuration : TuringMachine.Configuration) :
    StateTransition.Reaches source.next? configuration (source.runFor count configuration) := by
  induction count generalizing configuration with
  | zero => exact .refl
  | succ count recurse =>
      simp only [TuringMachine.Machine.runFor]
      cases stepped : source.next? configuration with
      | none => exact .refl
      | some next => exact .head stepped (recurse next)

private theorem haltsAfter_evaluates {source : TuringMachine.Machine} {count : Nat}
    {configuration final : TuringMachine.Configuration}
    (halted : source.HaltsAfter count configuration final) :
    final ∈ StateTransition.eval source.next? configuration := by
  obtain ⟨same, stopped, _⟩ := halted
  exact StateTransition.mem_eval.mpr
    ⟨same ▸ runFor_next source count configuration, stopped⟩

theorem busyBeaver2_returns :
    theory.MultiStep (start (TuringPrograms.machineProgram TuringMachine.busyBeaver2
      TuringMachine.Configuration.blank))
      (result (TuringPrograms.encodeConfiguration TuringMachine.busyBeaver2Final)) :=
  (machine_returns_iff _ _ _).mpr (haltsAfter_evaluates TuringMachine.busyBeaver2_haltsAfter)

theorem busyBeaver4_returns :
    theory.MultiStep (start (TuringPrograms.machineProgram TuringMachine.busyBeaver4
      TuringMachine.Configuration.blank))
      (result (TuringPrograms.encodeConfiguration TuringMachine.busyBeaver4Final)) :=
  (machine_returns_iff _ _ _).mpr (haltsAfter_evaluates TuringMachine.busyBeaver4_haltsAfter)

theorem alternating_never_returns :
    ¬ ∃ value, theory.MultiStep (start (TuringPrograms.machineProgram TuringMachine.alternating
      TuringMachine.Configuration.blank)) (result value) :=
  fun returned => TuringMachine.alternating_never_halts
    ((machine_halts_iff _ TuringMachine.alternating_deterministic _).mpr returned)

theorem busyBeaver2_cannot_return_blank :
    ¬ theory.MultiStep (start (TuringPrograms.machineProgram TuringMachine.busyBeaver2
      TuringMachine.Configuration.blank))
      (result (TuringPrograms.encodeConfiguration TuringMachine.Configuration.blank)) := by
  intro returned
  have attempted := (machine_returns_iff _ _ _).mp returned
  have correct := haltsAfter_evaluates TuringMachine.busyBeaver2_haltsAfter
  have same := Part.mem_unique attempted correct
  have states := congrArg TuringMachine.Configuration.state same
  contradiction

theorem empty_table_returns_input (configuration : TuringMachine.Configuration) :
    theory.MultiStep (start (TuringPrograms.machineProgram ⟨[]⟩ configuration))
      (result (TuringPrograms.encodeConfiguration configuration)) := by
  apply (machine_returns_iff _ _ _).mpr
  exact StateTransition.mem_eval.mpr ⟨.refl, rfl⟩

theorem quote_rebinding_observed :
    theory.MultiStep (start (Expressions.quote (.symbol "payload"))
      [(.symbol "'", .symbol "car"), (.symbol "payload", .list [.number 7, .number 8])])
      (result (.number 7)) :=
  pureEval_generated PureEvaluation.quote_name_can_be_rebound

theorem unused_input_branch_returns :
    theory.MultiStep (start (Expressions.ifExpr (.number 1) (.number 7)
      (Expressions.call "read-bit" []))) (result (.number 7)) := by
  apply pureEval_generated
  exact PureEvaluation.eval_if (environment := cleanEnvironment)
    (no := Expressions.call "read-bit" []) (by decide)
    (PureEvaluation.eval_number cleanEnvironment 1) (PureEvaluation.eval_number cleanEnvironment 7)

/-- Reading is an effect of the historical streaming evaluator. The pure
language has no rule pretending to supply its answer. -/
theorem read_request_blocked :
    reducts (.apply (.symbol "read-bit") [] cleanEnvironment .done) = [] := by
  rw [reducts_apply]
  simp [purePrimitive, LambdaCondition]

theorem read_request_normal : theory.IsNormalForm
    (encodeConfiguration (.apply (.symbol "read-bit") [] cleanEnvironment .done)) := by
  rintro ⟨target, step⟩
  have raw := (theory_step_iff _ target).mp step
  have compiled := (step_iff_reduct _ target).mp raw
  change target ∈ reducts (.apply (.symbol "read-bit") [] cleanEnvironment .done) at compiled
  rw [read_request_blocked] at compiled
  cases compiled

theorem read_request_is_not_result (value : SExpr) :
    encodeConfiguration (.apply (.symbol "read-bit") [] cleanEnvironment .done) ≠ result value := by
  intro same
  have impossible := encodeConfiguration_injective same
  cases impossible

end Mettapedia.Languages.Chaitin.GSLT
