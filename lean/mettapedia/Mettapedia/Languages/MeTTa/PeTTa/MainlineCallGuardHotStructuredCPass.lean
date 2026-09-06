import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteOperational
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteStructuredCProgram
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardStructuredCPass

/-!
# The hot dispatch as a pass

The exported hot StructuredC program is two dispatch functions: from the tag
of the argument mode at hand to the scheduler action it requires, and the
same for the result mode.  What they realize of the executor is its mode
decision: at an argument state the action scheduled for the head mode, at a
result state the action scheduled for the plan's result mode.  Everything
else in the seventeen rows stays with the scheduler.

So the hot representation's run view is the invocation of a dispatch body on
the mode tag read from the state, exiting at the returned action symbol, and
the source it covers is the mode-decision view of the executor
representation: the zero-step run view whose observation is the scheduled
action.  The pass is the identity on terms; its two directions are the
closed evaluations of the dispatch bodies on every tag, and the absence of a
run from any state that schedules nothing.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardHotStructuredCPass

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.LanguageDef.IRPass
open Mettapedia.GSLT.LanguageDef.IRRunView
open Mettapedia.GSLT.LanguageDef.StructuredC.Builder
open Mettapedia.GSLT.LanguageDef.StructuredCStructuralRuntime
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.Languages.MeTTa.PeTTa.MainlineTypeQueryGSLT
open Mettapedia.Languages.MeTTa.PeTTa.CallGuardNativeKernel
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardPlan
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardControl
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteControlProgram
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteStructuredCProgram
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteOperational
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCOneStepSimulation
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCFinishSemantics
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardStructuredCPass

/-! ## Tags and actions, from the dispatch table -/

def argumentInstruction : ArgMode → Instruction
  | .rawAtom => .argumentRaw
  | .evalUnchecked => .argumentUnchecked
  | .evalSoftcutType _ => .argumentChecked

def resultInstruction : ResultMode → Instruction
  | .resultUnchecked => .resultUnchecked
  | .resultSoftcutType _ => .resultChecked

def argumentTag : ArgMode → String
  | .rawAtom => "PETTA_MAINLINE_CALL_GUARD_ARG_RAW_ATOM"
  | .evalUnchecked => "PETTA_MAINLINE_CALL_GUARD_ARG_EVAL_UNCHECKED"
  | .evalSoftcutType _ => "PETTA_MAINLINE_CALL_GUARD_ARG_EVAL_SOFTCUT_TYPE"

def argumentAction : ArgMode → String
  | .rawAtom => "CETTA_PETTA_CALL_GUARD_HOT_SCHEDULE_RAW_V1"
  | .evalUnchecked => "CETTA_PETTA_CALL_GUARD_HOT_SCHEDULE_UNCHECKED_V1"
  | .evalSoftcutType _ => "CETTA_PETTA_CALL_GUARD_HOT_SCHEDULE_CHECKED_V1"

def resultTag : ResultMode → String
  | .resultUnchecked => "PETTA_MAINLINE_CALL_GUARD_RESULT_UNCHECKED"
  | .resultSoftcutType _ => "PETTA_MAINLINE_CALL_GUARD_RESULT_SOFTCUT_TYPE"

def resultAction : ResultMode → String
  | .resultUnchecked => "CETTA_PETTA_CALL_GUARD_HOT_ACCEPT_UNCHECKED_RESULT_V1"
  | .resultSoftcutType _ => "CETTA_PETTA_CALL_GUARD_HOT_CHECK_RESULT_V1"

/-- The tags and actions are read off the exported dispatch table. -/
theorem argumentCase_exact (mode : ArgMode) :
    argumentActionCase? (argumentInstruction mode) =
      some ⟨argumentInstruction mode, argumentTag mode, argumentAction mode⟩ := by
  cases mode <;> rfl

theorem resultCase_exact (mode : ResultMode) :
    resultActionCase? (resultInstruction mode) =
      some ⟨resultInstruction mode, resultTag mode, resultAction mode⟩ := by
  cases mode <;> rfl

def engineFault : String := "CETTA_PETTA_CALL_GUARD_HOT_ENGINE_FAULT_V1"

/-! ## The dispatch bodies -/

def functionBody? : Pattern → Option Pattern
  | .apply "structured-c:function" [_, _, _, body] => some body
  | _ => none

def argumentDispatchBody : Pattern :=
  (functionBody? (argumentActionFunction program)).getD inadmissibleConfig

def resultDispatchBody : Pattern :=
  (functionBody? (resultActionFunction program)).getD inadmissibleConfig

/-- The pass executes exactly the bodies of the exported dispatch program. -/
theorem dispatch_image :
    lowerHotModeProgram? program = some generatedHotModeProgram ∧
      functionBody? (argumentActionFunction program) = some argumentDispatchBody ∧
        functionBody? (resultActionFunction program) = some resultDispatchBody :=
  ⟨lower_authentic_program_exact, rfl, rfl⟩

/-! ## The mode-decision view of the executor representation -/

/-- The action the scheduler must take next, read from the state. -/
def scheduledAction? (state : Pattern) : Option Pattern :=
  match decodeExecuteControl? state with
  | some (.arguments _ _ _ _ _ (mode :: _) _ _ _ _) => some (valueSymbol (argumentAction mode))
  | some (.result _ _ plan _ _ _) => some (valueSymbol (resultAction plan.resultMode))
  | _ => none

def decisionProtocol : RunProtocol := ⟨id, scheduledAction?⟩

/-- Observe the scheduled action of the current state: a zero-step run. -/
abbrev modeDecisionRuns : GSLT := strategyRunView executeIR decisionProtocol 1 0

theorem modeDecisionRuns_step_iff (source target : Pattern) :
    modeDecisionRuns.Step source target ↔ scheduledAction? source = some target := by
  rw [strategyRunView_step_iff_strategy_of_equiv_eq executeIR decisionProtocol 1 0
    (fun equal => (executeIR_equiv_iff _ _).1 equal)]
  rfl

/-! ## The dispatch run view -/

def modeEnvironment (tag : String) : Pattern :=
  bindName "mode" (valueSymbol tag) environmentEmpty

/-- Invoke the dispatch body on the tag of the state's mode at hand. -/
def dispatchEntry (state : Pattern) : Pattern :=
  match decodeExecuteControl? state with
  | some (.arguments _ _ _ _ _ (mode :: _) _ _ _ _) =>
      StructuredC.run argumentDispatchBody (modeEnvironment (argumentTag mode)) readyReceipt
  | some (.result _ _ plan _ _ _) =>
      StructuredC.run resultDispatchBody (modeEnvironment (resultTag plan.resultMode)) readyReceipt
  | _ => inadmissibleConfig

/-- Exit at a returned action; an engine fault is not an action. -/
def returnedAction? : Pattern → Option Pattern
  | .apply "structured-c:halted" [.apply "structured-c:outcome-return" [value], _, _] =>
      if value = valueSymbol engineFault then none else some value
  | _ => none

def dispatchProtocol : RunProtocol := ⟨dispatchEntry, returnedAction?⟩

abbrev dispatchRuns : GSLT := strategyRunView structuredCIR dispatchProtocol 1 64

theorem dispatchRuns_step_iff (source target : Pattern) :
    dispatchRuns.Step source target ↔
      returnedAction? (normalizeFirstUsing coldRelations StructuredC.language 1 64
        (dispatchEntry source)) = some target := by
  rw [strategyRunView_step_iff_strategy_of_equiv_eq structuredCIR dispatchProtocol 1 64
    (fun equal => (structuredCEquiv_iff _ _).1 equal)]
  rfl

/-! ## The closed evaluations of the dispatch bodies -/

def argumentInvocation (tag : String) : Pattern :=
  StructuredC.run argumentDispatchBody (modeEnvironment tag) readyReceipt

def resultInvocation (tag : String) : Pattern :=
  StructuredC.run resultDispatchBody (modeEnvironment tag) readyReceipt

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem argument_raw_dispatch :
    returnedAction? (normalizeFirstUsing coldRelations StructuredC.language 1 64
      (argumentInvocation (argumentTag .rawAtom))) =
      some (valueSymbol (argumentAction .rawAtom)) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem argument_unchecked_dispatch :
    returnedAction? (normalizeFirstUsing coldRelations StructuredC.language 1 64
      (argumentInvocation (argumentTag .evalUnchecked))) =
      some (valueSymbol (argumentAction .evalUnchecked)) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem argument_checked_dispatch :
    returnedAction? (normalizeFirstUsing coldRelations StructuredC.language 1 64
      (argumentInvocation "PETTA_MAINLINE_CALL_GUARD_ARG_EVAL_SOFTCUT_TYPE")) =
      some (valueSymbol "CETTA_PETTA_CALL_GUARD_HOT_SCHEDULE_CHECKED_V1") := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem result_unchecked_dispatch :
    returnedAction? (normalizeFirstUsing coldRelations StructuredC.language 1 64
      (resultInvocation (resultTag .resultUnchecked))) =
      some (valueSymbol (resultAction .resultUnchecked)) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem result_checked_dispatch :
    returnedAction? (normalizeFirstUsing coldRelations StructuredC.language 1 64
      (resultInvocation "PETTA_MAINLINE_CALL_GUARD_RESULT_SOFTCUT_TYPE")) =
      some (valueSymbol "CETTA_PETTA_CALL_GUARD_HOT_CHECK_RESULT_V1") := by
  decide +kernel

theorem argument_dispatch (mode : ArgMode) :
    returnedAction? (normalizeFirstUsing coldRelations StructuredC.language 1 64
      (argumentInvocation (argumentTag mode))) = some (valueSymbol (argumentAction mode)) := by
  cases mode with
  | rawAtom => exact argument_raw_dispatch
  | evalUnchecked => exact argument_unchecked_dispatch
  | evalSoftcutType _ => exact argument_checked_dispatch

theorem result_dispatch (mode : ResultMode) :
    returnedAction? (normalizeFirstUsing coldRelations StructuredC.language 1 64
      (resultInvocation (resultTag mode))) = some (valueSymbol (resultAction mode)) := by
  cases mode with
  | resultUnchecked => exact result_unchecked_dispatch
  | resultSoftcutType _ => exact result_checked_dispatch

theorem returnedAction?_inadmissible : returnedAction? inadmissibleConfig = none := by
  rfl

/-! ## The pass -/

theorem dispatchRun_of_decision {source target : Pattern}
    (step : modeDecisionRuns.Step source target) : dispatchRuns.Step source target := by
  rw [modeDecisionRuns_step_iff] at step
  rw [dispatchRuns_step_iff]
  unfold scheduledAction? at step
  unfold dispatchEntry
  cases decoded : decodeExecuteControl? source with
  | none => simp [decoded] at step
  | some control =>
      rw [decoded] at step
      cases control with
      | arguments snapshot call plan remaining index modes sources values accepted events =>
          cases modes with
          | nil => simp at step
          | cons mode modes =>
              simp only [Option.some.injEq] at step
              subst step
              exact argument_dispatch mode
      | result snapshot call plan remaining accepted events =>
          simp only [Option.some.injEq] at step
          subst step
          exact result_dispatch plan.resultMode
      | request _ _ _ => simp at step
      | plans _ _ _ _ _ => simp at step
      | halted _ => simp at step

theorem decision_of_dispatchRun {source exit : Pattern}
    (run : dispatchRuns.Step source exit) :
    ∃ target, modeDecisionRuns.Step source target ∧
      structuredCIR.semantics.Equiv target exit := by
  rw [dispatchRuns_step_iff] at run
  refine ⟨exit, ?_, (structuredCEquiv_iff _ _).2 rfl⟩
  rw [modeDecisionRuns_step_iff]
  unfold dispatchEntry at run
  unfold scheduledAction?
  cases decoded : decodeExecuteControl? source with
  | none =>
      rw [decoded] at run
      change returnedAction? (normalizeFirstUsing coldRelations StructuredC.language 1 64
        inadmissibleConfig) = some exit at run
      rw [normalizeFirst_inadmissible, returnedAction?_inadmissible] at run
      cases run
  | some control =>
      rw [decoded] at run
      cases control with
      | arguments snapshot call plan remaining index modes sources values accepted events =>
          cases modes with
          | nil =>
              change returnedAction? (normalizeFirstUsing coldRelations StructuredC.language 1 64
                inadmissibleConfig) = some exit at run
              rw [normalizeFirst_inadmissible, returnedAction?_inadmissible] at run
              cases run
          | cons mode modes =>
              change returnedAction? (normalizeFirstUsing coldRelations StructuredC.language 1 64
                (argumentInvocation (argumentTag mode))) = some exit at run
              rw [argument_dispatch mode] at run
              exact run
      | result snapshot call plan remaining accepted events =>
          change returnedAction? (normalizeFirstUsing coldRelations StructuredC.language 1 64
            (resultInvocation (resultTag plan.resultMode))) = some exit at run
          rw [result_dispatch plan.resultMode] at run
          exact run
      | request _ _ _ =>
          change returnedAction? (normalizeFirstUsing coldRelations StructuredC.language 1 64
            inadmissibleConfig) = some exit at run
          rw [normalizeFirst_inadmissible, returnedAction?_inadmissible] at run
          cases run
      | plans _ _ _ _ _ =>
          change returnedAction? (normalizeFirstUsing coldRelations StructuredC.language 1 64
            inadmissibleConfig) = some exit at run
          rw [normalizeFirst_inadmissible, returnedAction?_inadmissible] at run
          cases run
      | halted _ =>
          change returnedAction? (normalizeFirstUsing coldRelations StructuredC.language 1 64
            inadmissibleConfig) = some exit at run
          rw [normalizeFirst_inadmissible, returnedAction?_inadmissible] at run
          cases run

/-- The hot pass: the mode-decision view of the executor, covered by the
dispatch runs of the exported program. -/
def hotToStructuredCPass : SemanticCoveredTranslation modeDecisionRuns dispatchRuns where
  mapTerm := id
  mapEquiv equivalent :=
    (structuredCEquiv_iff _ _).2 ((executeIR_equiv_iff _ _).1 equivalent)
  mapStep := dispatchRun_of_decision
  liftStep run := by
    obtain ⟨target, step, equal⟩ := decision_of_dispatchRun run
    exact ⟨target, step, equal⟩

/-! ## Canaries -/

namespace Canary

def checkedPlan : GuardPlan :=
  ⟨0, [.evalSoftcutType (.atom "Number")], .resultUnchecked, ⟨0, "f", [.atom "Number"], .atom "Number"⟩⟩

def emptySnapshot : Snapshot := ⟨0, [], [], []⟩

def checkedCall : Call := ⟨"f", [.atom "x"], [.atom "x"], .atom "y"⟩

/-- An argument state whose head mode is a softcut type check. -/
def checkedState : ExecuteControl :=
  .arguments emptySnapshot checkedCall checkedPlan [] 0 [.evalSoftcutType (.atom "Number")]
    [.atom "x"] [.atom "x"] [] []

theorem checked_schedules :
    scheduledAction? (encodeExecuteControl checkedState) =
      some (valueSymbol "CETTA_PETTA_CALL_GUARD_HOT_SCHEDULE_CHECKED_V1") := by
  simp [scheduledAction?, checkedState, argumentAction]

/-- Positive: the decision lifts through the pass to a dispatch run returning
the scheduled action. -/
theorem checked_dispatched :
    dispatchRuns.Step (encodeExecuteControl checkedState)
      (valueSymbol "CETTA_PETTA_CALL_GUARD_HOT_SCHEDULE_CHECKED_V1") :=
  hotToStructuredCPass.mapStep ((modeDecisionRuns_step_iff _ _).2 checked_schedules)

/-- A halted state schedules nothing and has no dispatch run. -/
theorem halted_no_dispatch (observation : ControlObservation) (target : Pattern) :
    ¬ dispatchRuns.Step (encodeExecuteControl (.halted observation)) target := by
  intro run
  obtain ⟨_, step, _⟩ := decision_of_dispatchRun run
  rw [modeDecisionRuns_step_iff] at step
  simp [scheduledAction?] at step

/-- The decision view with one invented decision at a halted state. -/
def inventingDecisions (observation : ControlObservation) : GSLT where
  Term := Pattern
  equations := modeDecisionRuns.equations
  rewrites source target :=
    modeDecisionRuns.Step source target ∨
      (source = encodeExecuteControl (.halted observation) ∧
        target = valueSymbol "CETTA_PETTA_CALL_GUARD_HOT_SCHEDULE_RAW_V1")
  rewrites_resp_left := by
    intro source source' target equal step
    have same : source = source' := (executeIR_equiv_iff _ _).1 equal
    subst same
    exact ⟨target, step, modeDecisionRuns.equations.iseqv.refl target⟩
  rewrites_resp_right := by
    intro source target target' step equal
    have same : target = target' := (executeIR_equiv_iff _ _).1 equal
    subst same
    exact step

/-- Negative: the invented decision has no dispatch run to map to, so no
cover with the identity term map reaches the dispatch runs from it. -/
theorem negative_canary (observation : ControlObservation) :
    ¬ ∃ cover : SemanticCoveredTranslation (inventingDecisions observation) dispatchRuns,
      cover.mapTerm = id := by
  rintro ⟨cover, mapTerm⟩
  have invented : (inventingDecisions observation).Step
      (encodeExecuteControl (.halted observation))
      (valueSymbol "CETTA_PETTA_CALL_GUARD_HOT_SCHEDULE_RAW_V1") :=
    Or.inr ⟨rfl, rfl⟩
  have run := cover.mapStep invented
  rw [mapTerm] at run
  exact halted_no_dispatch observation _ run

end Canary

#print axioms hotToStructuredCPass
#print axioms dispatch_image
#print axioms Canary.checked_dispatched
#print axioms Canary.negative_canary

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardHotStructuredCPass
