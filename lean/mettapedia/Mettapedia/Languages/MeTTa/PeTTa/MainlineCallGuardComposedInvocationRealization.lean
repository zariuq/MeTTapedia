import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardComposedRealization
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteStructuredCPass

/-!
# The composed call guard realized by StructuredC invocations in both phases

The composed representation of `MainlineCallGuardComposedRealization` runs
the cold phase as StructuredC invocations and the hot phase as steps of the
executor representation.  With the hot lowering a pass on steps, the hot
phase becomes StructuredC invocations as well: one invocation of the
generated hot body on a loaded executor state is one executor step.  The
composed theory of ControlNTT is covered by this representation with the
same encoding on the cold side and the hot state loader on the hot side.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardComposedInvocationRealization

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.LanguageDef.IRPass
open Mettapedia.GSLT.LanguageDef.IRRunView
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.MeTTa.PeTTa.MainlineTypeQueryGSLT
open Mettapedia.Languages.MeTTa.PeTTa.CallGuardNativeKernel
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardProjection
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardPlan
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardControl
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardOperational
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardStructuredCBiformTheory
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteOperational
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardComposedRealization

namespace Hot
export Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteStructuredCTotalRealization
  (runControl runBudget)
export Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteStructuredCPass
  (hotStructuredCIR structuredCProtocol hotStructuredCRuns invocationExit
    strategyRun_of_executeStep executeStep_of_strategyRun structuredCEquiv_iff
    storedControl? storedControl?_runControl)
end Hot

/-! ## One hot invocation -/

/-- One invocation of the generated hot body: the exit of the first-reduct
strategy run under the invocation protocol. -/
def hotInvoke? (config : Pattern) : Option Pattern :=
  Hot.invocationExit
    (strategyEndpoint Hot.hotStructuredCIR Hot.structuredCProtocol 1 Hot.runBudget config)

theorem hotStructuredCRuns_step_iff_invoke (source target : Pattern) :
    Hot.hotStructuredCRuns.Step source target ↔ hotInvoke? source = some target := by
  rw [strategyRunView_step_iff_strategy_of_equiv_eq Hot.hotStructuredCIR Hot.structuredCProtocol 1
    Hot.runBudget (fun equal => (Hot.structuredCEquiv_iff _ _).1 equal)]
  rfl

/-- On loaded states, one hot invocation is one executor step. -/
theorem hotInvoke?_runControl (control : ExecuteControl) :
    hotInvoke? (Hot.runControl control) = (executeStep? control).map Hot.runControl := by
  cases step : executeStep? control with
  | some target => exact Hot.strategyRun_of_executeStep step
  | none =>
      cases found : hotInvoke? (Hot.runControl control) with
      | none => rfl
      | some exit =>
          exfalso
          obtain ⟨target, stepped, _⟩ :=
            Hot.executeStep_of_strategyRun (source := control) found
          rw [step] at stepped
          cases stepped

theorem hotRunControl_injective {left right : ExecuteControl}
    (equal : Hot.runControl left = Hot.runControl right) : left = right := by
  have stored := congrArg Hot.storedControl? equal
  rw [Hot.storedControl?_runControl, Hot.storedControl?_runControl] at stored
  exact Option.some.inj stored

/-! ## The composed invocation representation -/

/-- One step: a declaration run of the cold invocation view, the hand-off
into the loaded hot request, or one hot invocation. -/
inductive ComposedInvocationStep : Pattern → Pattern → Prop
  | cold (owned call config config' : Pattern)
      (run : invokeUntil (budgetOf config) config = some config') :
      ComposedInvocationStep (compilingPattern owned call config)
        (compilingPattern owned call config')
  | boundary (owned : OwnedSnapshot) (call : Call) (result : CompilationResult) :
      ComposedInvocationStep
        (compilingPattern (encodeOwned owned) (encodeCall call) (runControl (.halted result)))
        (executingPattern (Hot.runControl (.request owned call result)))
  | hot (config config' : Pattern) (run : hotInvoke? config = some config') :
      ComposedInvocationStep (executingPattern config) (executingPattern config')

def composedInvocationRuns : GSLT where
  Term := Pattern
  equations := ⟨Eq, eq_equivalence⟩
  rewrites := ComposedInvocationStep
  rewrites_resp_left := by
    intro source source' target equal step
    cases equal
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    cases equal
    exact step

/-- The composed encoding: the cold phase loads the fine compiler state, the
hot phase loads the executor state. -/
def encodeCallGuardInvocation : CallGuardControl → Pattern
  | .compiling owned call compiler =>
      compilingPattern (encodeOwned owned) (encodeCall call) (runControl (fineOf compiler))
  | .executing executor => executingPattern (Hot.runControl executor)

theorem composedInvocationStep_of_callGuardStep {source target : CallGuardControl}
    (step : callGuardStep? source = some target) :
    ComposedInvocationStep (encodeCallGuardInvocation source)
      (encodeCallGuardInvocation target) := by
  cases source with
  | compiling owned call compiler =>
      cases coarse : compileStep? compiler with
      | some next =>
          simp only [callGuardStep?, coarse, Option.some.injEq] at step
          subst step
          apply ComposedInvocationStep.cold
          rw [invokeUntil_coarse, coarse]
          rfl
      | none =>
          cases compiler with
          | running owner revision head arity remaining accepted =>
              obtain ⟨next, stepped⟩ :=
                compile_running_has_next owner revision head arity remaining accepted
              rw [stepped] at coarse
              cases coarse
          | halted result =>
              simp only [callGuardStep?, coarse, Option.some.injEq] at step
              subst step
              exact ComposedInvocationStep.boundary owned call result
  | executing executor =>
      cases hot : executeStep? executor with
      | none => simp [callGuardStep?, hot] at step
      | some next =>
          simp only [callGuardStep?, hot, Option.map_some, Option.some.injEq] at step
          subst step
          apply ComposedInvocationStep.hot
          rw [hotInvoke?_runControl, hot]
          rfl

theorem ComposedInvocationStep.inv {source target : Pattern}
    (step : ComposedInvocationStep source target) :
    (∃ owned call config config', source = compilingPattern owned call config ∧
        target = compilingPattern owned call config' ∧
        invokeUntil (budgetOf config) config = some config') ∨
      (∃ (owned : OwnedSnapshot) (call : Call) (result : CompilationResult),
        source = compilingPattern (encodeOwned owned) (encodeCall call)
          (runControl (.halted result)) ∧
        target = executingPattern (Hot.runControl (.request owned call result))) ∨
      (∃ config config', source = executingPattern config ∧ target = executingPattern config' ∧
        hotInvoke? config = some config') := by
  cases step with
  | cold owned call config config' run => exact Or.inl ⟨owned, call, config, config', rfl, rfl, run⟩
  | boundary owned call result => exact Or.inr (Or.inl ⟨owned, call, result, rfl, rfl⟩)
  | hot config config' run => exact Or.inr (Or.inr ⟨config, config', rfl, rfl, run⟩)

theorem callGuardStep_of_composedInvocationStep {source : CallGuardControl} {target : Pattern}
    (step : ComposedInvocationStep (encodeCallGuardInvocation source) target) :
    ∃ next, callGuardStep? source = some next ∧ encodeCallGuardInvocation next = target := by
  rcases step.inv with ⟨owned', call', config, config', sourceEq, targetEq, run⟩ |
    ⟨owned', call', result, sourceEq, targetEq⟩ | ⟨config, config', sourceEq, targetEq, run⟩
  · cases source with
    | compiling owned call compiler =>
        simp only [encodeCallGuardInvocation, compilingPattern, Pattern.apply.injEq,
          List.cons.injEq, and_true, true_and] at sourceEq
        obtain ⟨ownedEq, callEq, configEq⟩ := sourceEq
        subst ownedEq
        subst callEq
        subst configEq
        subst targetEq
        rw [invokeUntil_coarse] at run
        cases coarse : compileStep? compiler with
        | none => rw [coarse] at run; cases run
        | some next =>
            rw [coarse] at run
            simp only [Option.map_some, Option.some.injEq] at run
            subst run
            exact ⟨.compiling owned call next, by simp [callGuardStep?, coarse], rfl⟩
    | executing executor =>
        simp [encodeCallGuardInvocation, compilingPattern, executingPattern] at sourceEq
  · cases source with
    | compiling owned call compiler =>
        simp only [encodeCallGuardInvocation, compilingPattern, Pattern.apply.injEq,
          List.cons.injEq, and_true, true_and] at sourceEq
        obtain ⟨ownedEq, callEq, configEq⟩ := sourceEq
        have ownedSame := encodeOwned_injective ownedEq
        have callSame := encodeCall_injective callEq
        have compilerSame : compiler = .halted result :=
          fineOf_eq_halted (runControl_injective configEq)
        subst ownedSame
        subst callSame
        subst compilerSame
        subst targetEq
        exact ⟨.executing (.request owned call result), rfl, rfl⟩
    | executing executor =>
        simp [encodeCallGuardInvocation, compilingPattern, executingPattern] at sourceEq
  · cases source with
    | compiling owned call compiler =>
        simp [encodeCallGuardInvocation, compilingPattern, executingPattern] at sourceEq
    | executing executor =>
        simp only [encodeCallGuardInvocation, executingPattern, Pattern.apply.injEq,
          List.cons.injEq, and_true, true_and] at sourceEq
        subst sourceEq
        subst targetEq
        rw [hotInvoke?_runControl] at run
        cases hot : executeStep? executor with
        | none => rw [hot] at run; cases run
        | some next =>
            rw [hot] at run
            simp only [Option.map_some, Option.some.injEq] at run
            subst run
            exact ⟨.executing next, by simp [callGuardStep?, hot], rfl⟩

/-- The composed call-guard theory of ControlNTT is covered by StructuredC
invocations in both phases. -/
def composedInvocationRealization :
    SemanticCoveredTranslation MainlineCallGuardControl.callGuardGSLT composedInvocationRuns where
  mapTerm := encodeCallGuardInvocation
  mapEquiv equal := congrArg encodeCallGuardInvocation equal
  mapStep := composedInvocationStep_of_callGuardStep
  liftStep := by
    intro source target step
    obtain ⟨next, stepped, encoded⟩ := callGuardStep_of_composedInvocationStep step
    exact ⟨next, stepped, encoded⟩

theorem composedInvocationRealization_source :
    composedInvocationRealization.mapTerm = encodeCallGuardInvocation ∧
      ∀ source target, MainlineCallGuardControl.callGuardGSLT.Step source target ↔
        callGuardStep? source = some target :=
  ⟨rfl, fun _ _ => Iff.rfl⟩

/-! ## Canaries -/

namespace Canary

def emptyOwned : OwnedSnapshot := ⟨⟨0⟩, ⟨0, [], [], []⟩⟩

def emptyCall : Call := ⟨"f", [], [], .atom "y"⟩

def emptyFamily : CompiledGuardFamily := ⟨⟨0⟩, 0, "f", 0, []⟩

def requested : CallGuardControl :=
  .executing (.request emptyOwned emptyCall (.compiled emptyFamily))

def planning : CallGuardControl := .executing (.plans emptyOwned.snapshot emptyCall [] [] [])

theorem requested_steps : callGuardStep? requested = some planning := rfl

/-- Positive: the executor's request step is one hot invocation of the loaded
states. -/
theorem request_realized :
    composedInvocationRuns.Step (encodeCallGuardInvocation requested)
      (encodeCallGuardInvocation planning) :=
  composedInvocationStep_of_callGuardStep requested_steps

theorem request_invocation :
    hotInvoke? (Hot.runControl (.request emptyOwned emptyCall (.compiled emptyFamily))) =
      some (Hot.runControl (.plans emptyOwned.snapshot emptyCall [] [] [])) := by
  rw [hotInvoke?_runControl]
  rfl

/-- A loaded halted executor state has no composed step. -/
theorem halted_final (observation : ControlObservation) (target : Pattern) :
    ¬ ComposedInvocationStep (executingPattern (Hot.runControl (.halted observation))) target := by
  intro step
  rcases step.inv with ⟨_, _, _, _, sourceEq, _, _⟩ | ⟨_, _, _, sourceEq, _⟩ |
    ⟨config, config', sourceEq, _, run⟩
  · simp [compilingPattern, executingPattern] at sourceEq
  · simp [compilingPattern, executingPattern] at sourceEq
  · simp only [executingPattern, Pattern.apply.injEq, List.cons.injEq, and_true, true_and]
      at sourceEq
    subst sourceEq
    rw [hotInvoke?_runControl] at run
    simp [executeStep?] at run

/-- The composed representation with one invented transition out of a loaded
halted executor state. -/
def inventingRuns (observation : ControlObservation) : GSLT where
  Term := Pattern
  equations := ⟨Eq, eq_equivalence⟩
  rewrites source target :=
    ComposedInvocationStep source target ∨
      (source = executingPattern (Hot.runControl (.halted observation)) ∧ target = source)
  rewrites_resp_left := by
    intro source source' target equal step
    cases equal
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    cases equal
    exact step

/-- Negative: no cover with the composed encoding reaches the inventing
representation. -/
theorem negative_canary (observation : ControlObservation) :
    ¬ ∃ cover : SemanticCoveredTranslation MainlineCallGuardControl.callGuardGSLT
        (inventingRuns observation),
      cover.mapTerm = encodeCallGuardInvocation := by
  rintro ⟨cover, mapTerm⟩
  have invented : (inventingRuns observation).Step
      (cover.mapTerm (.executing (.halted observation)))
      (executingPattern (Hot.runControl (.halted observation))) := by
    rw [mapTerm]
    exact Or.inr ⟨rfl, rfl⟩
  obtain ⟨next, step, _⟩ := cover.liftStep invented
  change callGuardStep? _ = some next at step
  simp [callGuardStep?, executeStep?] at step

end Canary

#print axioms composedInvocationRealization
#print axioms hotInvoke?_runControl
#print axioms Canary.request_realized
#print axioms Canary.negative_canary

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardComposedInvocationRealization
