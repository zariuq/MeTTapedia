import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardStructuredCBiformTheory
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardHotStructuredCPass
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardControlNTT

/-!
# The composed call-guard theory, realized

The composed source theory of the call guard is `callGuardGSLT`: the cold
compiler inspecting one declaration per step, the hand-off of the compiled
family to the executor, and the executor's steps.  Its realization composes
the two lowerings.

The cold phase is realized by the StructuredC invocation view of Step 1:
one declaration is one run of invocations until the loaded state is again a
declaration boundary, a running or halted state.  The invocation view is
the target of `coldToStructuredCPass`, and one declaration-inspection step
of the coarse compiler is exactly that run of the fine compiler, which is
proved here as `stopRun_budget`.  The hand-off is the re-encoding of the
compiled family from the cold ABI value into the executor representation.
The hot phase is realized by the executor representation itself, exactly
by `executeIR_step_iff`; its mode decisions are what the exported dispatch
program covers (`hotToStructuredCPass`).  No StructuredC program realizes
the whole executor, and none is claimed.

The result is a cover of the composed theory by the composed representation:
every composed step is realized, and nothing else is.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardComposedRealization

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
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileCodec
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardStructuredCPass
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardStructuredCBiformTheory
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteOperational

/-! ## The coarse compiler as runs of the fine compiler -/

/-- The coarse compiler's states are the declaration boundaries of the fine
compiler. -/
def fineOf : CompileControl → CompileLanguageControl
  | .running owner revision head arity remaining accepted =>
      .running owner revision head arity remaining accepted
  | .halted result => .halted result

theorem fineOf_injective : Function.Injective fineOf := by
  intro left right equal
  cases left <;> cases right <;> simp [fineOf] at equal <;> simp [equal]

theorem fineOf_eq_halted {control : CompileControl} {result : CompilationResult}
    (equal : fineOf control = .halted result) : control = .halted result := by
  cases control <;> simp [fineOf] at equal
  simp [equal]

/-- A fine state at a declaration boundary. -/
def observable : CompileLanguageControl → Bool
  | .running _ _ _ _ _ _ => true
  | .halted _ => true
  | _ => false

def coarseOf? : CompileLanguageControl → Option CompileControl
  | .running owner revision head arity remaining accepted =>
      some (.running owner revision head arity remaining accepted)
  | .halted result => some (.halted result)
  | _ => none

@[simp] theorem coarseOf?_fineOf (control : CompileControl) : coarseOf? (fineOf control) = some control := by
  cases control <;> rfl

/-- Run the fine compiler until the next declaration boundary. -/
def stopRun : Nat → CompileLanguageControl → Option CompileLanguageControl
  | 0, _ => none
  | fuel + 1, state =>
      match compileLanguageStep? state with
      | none => none
      | some next => if observable next then some next else stopRun fuel next

/-- Fine steps needed for one coarse step. -/
def budget : CompileControl → Nat
  | .running _ _ _ _ [] _ => 1
  | .running _ _ _ _ (declaration :: _) _ => declaration.inputTypes.length + 3
  | .halted _ => 0

theorem stopRun_arguments (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declaration : ArrowDeclaration) (remaining : List ArrowDeclaration)
    (accepted : List GuardPlan) :
    ∀ (inputs : List Term) (modes : List ArgMode),
      stopRun (inputs.length + 2)
          (.arguments owner revision head arity declaration remaining inputs modes accepted) =
        some (match compileArgumentModes inputs with
          | none => .halted .outsideFragment
          | some more =>
              match compileResultMode declaration.outputType with
              | none => .halted .outsideFragment
              | some resultMode =>
                  .running owner revision head arity remaining
                    (accepted ++ [⟨declaration.occurrence, modes ++ more, resultMode, declaration⟩]))
  | [], modes => by
      simp only [List.length_nil, stopRun, compileLanguageStep?, observable,
        compileArgumentModes]
      cases compileResultMode declaration.outputType <;> simp
  | expected :: inputs, modes => by
      show stopRun (inputs.length + 2 + 1) _ = _
      rw [stopRun]
      simp only [compileLanguageStep?, compileArgumentModes]
      cases compileArgMode expected with
      | none => simp [observable]
      | some mode =>
          simp only [observable, Bool.false_eq_true, if_false]
          rw [stopRun_arguments owner revision head arity declaration remaining accepted inputs
            (modes ++ [mode])]
          cases compileArgumentModes inputs with
          | none => rfl
          | some more =>
              cases compileResultMode declaration.outputType <;> simp

/-- One coarse step is one run of the fine compiler to the next boundary. -/
theorem stopRun_budget (control : CompileControl) :
    stopRun (budget control) (fineOf control) = (compileStep? control).map fineOf := by
  cases control with
  | halted result => rfl
  | running owner revision head arity remaining accepted =>
      cases remaining with
      | nil => rfl
      | cons declaration remaining =>
          by_cases relevant : Relevant declaration head arity
          · show stopRun (declaration.inputTypes.length + 2 + 1) _ = _
            rw [stopRun]
            simp only [fineOf, compileLanguageStep?, relevant, if_true, observable,
              Bool.false_eq_true, if_false]
            rw [stopRun_arguments]
            simp only [compileStep?, relevant, if_true, compileGuard, List.nil_append]
            cases compileArgumentModes declaration.inputTypes with
            | none => rfl
            | some modes =>
                cases compileResultMode declaration.outputType with
                | none => rfl
                | some resultMode => rfl
          · show stopRun (declaration.inputTypes.length + 2 + 1) _ = _
            rw [stopRun]
            simp [fineOf, compileLanguageStep?, relevant, observable, compileStep?]

/-! ## Invocations to the next boundary -/

/-- One StructuredC invocation, as a function. -/
def invoke? (config : Pattern) : Option Pattern :=
  invocationExit (strategyEndpoint structuredCIR structuredCProtocol 1 64 config)

theorem structuredCRuns_step_iff_invoke (source target : Pattern) :
    structuredCRuns.Step source target ↔ invoke? source = some target := by
  rw [strategyRunView_step_iff_strategy_of_equiv_eq structuredCIR structuredCProtocol 1 64
    (fun equal => (structuredCEquiv_iff _ _).1 equal)]
  rfl

/-- On loaded states, one invocation is one fine step. -/
theorem invoke?_runControl (control : CompileLanguageControl) :
    invoke? (runControl control) = (compileLanguageStep? control).map runControl := by
  cases step : compileLanguageStep? control with
  | some target => exact strategyRun_of_compileStep step
  | none =>
      cases found : invoke? (runControl control) with
      | none => rfl
      | some exit =>
          exfalso
          obtain ⟨target, stepped, _⟩ := compileStep_of_strategyRun (source := control) found
          rw [step] at stepped
          cases stepped

def configObservable (config : Pattern) : Bool :=
  match storedControl? config with
  | some state => observable state
  | none => false

/-- Invoke until the loaded state is a declaration boundary. -/
def invokeUntil : Nat → Pattern → Option Pattern
  | 0, _ => none
  | fuel + 1, config =>
      match invoke? config with
      | none => none
      | some next => if configObservable next then some next else invokeUntil fuel next

theorem invokeUntil_runControl (fuel : Nat) (state : CompileLanguageControl) :
    invokeUntil fuel (runControl state) = (stopRun fuel state).map runControl := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel inductionHypothesis =>
      simp only [invokeUntil, stopRun, invoke?_runControl]
      cases compileLanguageStep? state with
      | none => rfl
      | some next =>
          simp only [Option.map_some, configObservable, storedControl?_runControl]
          by_cases seen : observable next = true
          · simp [seen]
          · simp [seen, inductionHypothesis]

/-- The invocation budget read from the loaded state. -/
def budgetOf (config : Pattern) : Nat :=
  match storedControl? config >>= coarseOf? with
  | some control => budget control
  | none => 0

theorem budgetOf_runControl (control : CompileControl) :
    budgetOf (runControl (fineOf control)) = budget control := by
  simp [budgetOf, storedControl?_runControl]

theorem invokeUntil_coarse (control : CompileControl) :
    invokeUntil (budgetOf (runControl (fineOf control))) (runControl (fineOf control)) =
      (compileStep? control).map (fun next => runControl (fineOf next)) := by
  rw [budgetOf_runControl, invokeUntil_runControl, stopRun_budget]
  cases compileStep? control <;> rfl

/-! ## The composed representation -/

def compilingPattern (owned call config : Pattern) : Pattern :=
  .apply "petta-call-guard:compiling" [owned, call, config]

def executingPattern (state : Pattern) : Pattern :=
  .apply "petta-call-guard:executing" [state]

/-- One step of the composed representation: a declaration run of the
StructuredC invocation view, the hand-off, or one executor representation
step. -/
inductive ComposedStep : Pattern → Pattern → Prop
  | cold (owned call config config' : Pattern)
      (run : invokeUntil (budgetOf config) config = some config') :
      ComposedStep (compilingPattern owned call config) (compilingPattern owned call config')
  | boundary (owned : OwnedSnapshot) (call : Call) (result : CompilationResult) :
      ComposedStep
        (compilingPattern (encodeOwned owned) (encodeCall call) (runControl (.halted result)))
        (executingPattern (encodeExecuteControl (.request owned call result)))
  | hot (state state' : Pattern) (step : executeIR.semantics.Step state state') :
      ComposedStep (executingPattern state) (executingPattern state')

def composedRuns : GSLT where
  Term := Pattern
  equations := ⟨Eq, eq_equivalence⟩
  rewrites := ComposedStep
  rewrites_resp_left := by
    intro source source' target equal step
    cases equal
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    cases equal
    exact step

/-! ## Encoding the composed theory -/

def encodeCallGuard : CallGuardControl → Pattern
  | .compiling owned call compiler =>
      compilingPattern (encodeOwned owned) (encodeCall call) (runControl (fineOf compiler))
  | .executing executor => executingPattern (encodeExecuteControl executor)

theorem encodeOwned_injective : Function.Injective encodeOwned := by
  intro left right equal
  have decoded := congrArg decodeOwned? equal
  simpa using decoded

theorem encodeCall_injective : Function.Injective encodeCall := by
  intro left right equal
  have decoded := congrArg decodeCall? equal
  simpa using decoded

theorem runControl_fineOf_injective {left right : CompileControl}
    (equal : runControl (fineOf left) = runControl (fineOf right)) : left = right :=
  fineOf_injective (runControl_injective equal)

/-! ## The realization -/

theorem composedStep_of_callGuardStep {source target : CallGuardControl}
    (step : callGuardStep? source = some target) :
    ComposedStep (encodeCallGuard source) (encodeCallGuard target) := by
  cases source with
  | compiling owned call compiler =>
      cases coarse : compileStep? compiler with
      | some next =>
          simp only [callGuardStep?, coarse, Option.some.injEq] at step
          subst step
          apply ComposedStep.cold
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
              exact ComposedStep.boundary owned call result
  | executing executor =>
      cases hot : executeStep? executor with
      | none => simp [callGuardStep?, hot] at step
      | some next =>
          simp only [callGuardStep?, hot, Option.map_some, Option.some.injEq] at step
          subst step
          exact ComposedStep.hot _ _ ((executeIR_step_iff _ _).2 ⟨next, hot, rfl⟩)

theorem ComposedStep.inv {source target : Pattern} (step : ComposedStep source target) :
    (∃ owned call config config', source = compilingPattern owned call config ∧
        target = compilingPattern owned call config' ∧
        invokeUntil (budgetOf config) config = some config') ∨
      (∃ (owned : OwnedSnapshot) (call : Call) (result : CompilationResult),
        source = compilingPattern (encodeOwned owned) (encodeCall call) (runControl (.halted result)) ∧
        target = executingPattern (encodeExecuteControl (.request owned call result))) ∨
      (∃ state state', source = executingPattern state ∧ target = executingPattern state' ∧
        executeIR.semantics.Step state state') := by
  cases step with
  | cold owned call config config' run => exact Or.inl ⟨owned, call, config, config', rfl, rfl, run⟩
  | boundary owned call result => exact Or.inr (Or.inl ⟨owned, call, result, rfl, rfl⟩)
  | hot state state' hotStep => exact Or.inr (Or.inr ⟨state, state', rfl, rfl, hotStep⟩)

theorem callGuardStep_of_composedStep {source : CallGuardControl} {target : Pattern}
    (step : ComposedStep (encodeCallGuard source) target) :
    ∃ next, callGuardStep? source = some next ∧ encodeCallGuard next = target := by
  rcases step.inv with ⟨owned', call', config, config', sourceEq, targetEq, run⟩ |
    ⟨owned', call', result, sourceEq, targetEq⟩ | ⟨state, state', sourceEq, targetEq, hotStep⟩
  · cases source with
    | compiling owned call compiler =>
        simp only [encodeCallGuard, compilingPattern, Pattern.apply.injEq, List.cons.injEq,
          and_true, true_and] at sourceEq
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
        simp [encodeCallGuard, compilingPattern, executingPattern] at sourceEq
  · cases source with
    | compiling owned call compiler =>
        simp only [encodeCallGuard, compilingPattern, Pattern.apply.injEq, List.cons.injEq,
          and_true, true_and] at sourceEq
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
        simp [encodeCallGuard, compilingPattern, executingPattern] at sourceEq
  · cases source with
    | compiling owned call compiler =>
        simp [encodeCallGuard, compilingPattern, executingPattern] at sourceEq
    | executing executor =>
        simp only [encodeCallGuard, executingPattern, Pattern.apply.injEq, List.cons.injEq,
          and_true, true_and] at sourceEq
        subst sourceEq
        subst targetEq
        obtain ⟨next, stepped, rfl⟩ := (executeIR_step_iff executor _).1 hotStep
        exact ⟨.executing next, by simp [callGuardStep?, stepped], rfl⟩

/-- The composed call-guard theory of ControlNTT is covered by the composed
representation: the cold declaration runs of the StructuredC invocation view,
the hand-off, and the executor representation. -/
def composedRealization : SemanticCoveredTranslation MainlineCallGuardControl.callGuardGSLT composedRuns where
  mapTerm := encodeCallGuard
  mapEquiv equal := congrArg encodeCallGuard equal
  mapStep := composedStep_of_callGuardStep
  liftStep := by
    intro source target step
    obtain ⟨next, stepped, encoded⟩ := callGuardStep_of_composedStep step
    exact ⟨next, stepped, encoded⟩

/-- The composed source is the one whose native types ControlNTT generates. -/
theorem composedRealization_source :
    composedRealization.mapTerm = encodeCallGuard ∧
      ∀ source target, MainlineCallGuardControl.callGuardGSLT.Step source target ↔
        callGuardStep? source = some target :=
  ⟨rfl, fun _ _ => Iff.rfl⟩

/-! ## Canaries -/

namespace Canary

def emptyOwned : OwnedSnapshot := ⟨⟨0⟩, ⟨0, [], [], []⟩⟩

def emptyCall : Call := ⟨"f", [], [], .atom "y"⟩

/-- The start of the composed theory on the empty snapshot. -/
def start : CallGuardControl := callGuardStart emptyOwned emptyCall

def compiled : CallGuardControl :=
  .compiling emptyOwned emptyCall (.halted (.compiled ⟨⟨0⟩, 0, "f", 0, []⟩))

theorem start_steps : callGuardStep? start = some compiled := rfl

/-- Positive: the first coarse step (finishing the empty declaration list)
is realized by a declaration run of the invocation view. -/
theorem start_realized :
    composedRuns.Step (encodeCallGuard start) (encodeCallGuard compiled) :=
  composedRealization.mapStep start_steps

def requested : CallGuardControl :=
  .executing (.request emptyOwned emptyCall (.compiled ⟨⟨0⟩, 0, "f", 0, []⟩))

theorem compiled_steps : callGuardStep? compiled = some requested := rfl

/-- Positive: the hand-off is realized. -/
theorem handoff_realized :
    composedRuns.Step (encodeCallGuard compiled) (encodeCallGuard requested) :=
  composedRealization.mapStep compiled_steps

/-- A halted executor is the end: no composed step leaves it. -/
theorem halted_final (observation : ControlObservation) (target : Pattern) :
    ¬ composedRuns.Step (encodeCallGuard (.executing (.halted observation))) target := by
  intro step
  obtain ⟨next, stepped, _⟩ := callGuardStep_of_composedStep step
  simp [callGuardStep?, executeStep?] at stepped

/-- The composed representation with one invented step out of a halted
executor. -/
def inventingRuns (observation : ControlObservation) : GSLT where
  Term := Pattern
  equations := ⟨Eq, eq_equivalence⟩
  rewrites source target :=
    ComposedStep source target ∨
      (source = encodeCallGuard (.executing (.halted observation)) ∧
        target = executingPattern inadmissibleConfig)
  rewrites_resp_left := by
    intro source source' target equal step
    cases equal
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    cases equal
    exact step

/-- Negative: no cover with the composed encoding reaches the inventing
representation from the composed theory. -/
theorem negative_canary (observation : ControlObservation) :
    ¬ ∃ cover : SemanticCoveredTranslation MainlineCallGuardControl.callGuardGSLT
        (inventingRuns observation),
      cover.mapTerm = encodeCallGuard := by
  rintro ⟨cover, mapTerm⟩
  have invented : (inventingRuns observation).Step
      (cover.mapTerm (.executing (.halted observation))) (executingPattern inadmissibleConfig) := by
    rw [mapTerm]
    exact Or.inr ⟨rfl, rfl⟩
  obtain ⟨next, stepped, _⟩ := cover.liftStep invented
  change callGuardStep? _ = some next at stepped
  simp [callGuardStep?, executeStep?] at stepped

end Canary

#print axioms stopRun_budget
#print axioms composedRealization
#print axioms Canary.start_realized
#print axioms Canary.negative_canary

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardComposedRealization
