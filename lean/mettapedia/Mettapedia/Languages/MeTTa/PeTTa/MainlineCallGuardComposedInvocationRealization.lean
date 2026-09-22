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

/-! ## The composed representation over the two lane covers

`SemanticCoveredTranslation.comp` already composes equation-class covers, with
the identity, left and right unit laws, and associativity supplied by the
category of semantic covered theories; both lowering lanes are already such
composites.  Sequential composition cannot join the two lanes, because the
target of neither lane pass is the source of the other: the cold lane ends in
the cold invocation view over `coldRelations` and the hot lane begins at the
admitted executor language over its own relation environment.  What relates the
lanes here is the composed representation's own step relation, and the two
facts below say exactly how its steps are built out of the lane covers.

The cold direction is one-way by construction: a declaration step of the
coarse compiler is a bounded iteration of cold invocations that stops at the
next declaration boundary, so it is a finite run of the cold lane's cover,
while a finite run of that cover need not stop at a boundary.  The hot
direction is exact: one hot phase step is one step of the hot lane's cover.
-/

namespace Cold
export Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardStructuredCPass (structuredCRuns)
end Cold

/-- Every bounded iteration of cold invocations is a finite run of the cold
lane's cover.  In particular the cold phase of a composed step is such a
run. -/
theorem reflTransGen_of_invokeUntil :
    ∀ (fuel : Nat) (config config' : Pattern), invokeUntil fuel config = some config' →
      Relation.ReflTransGen Cold.structuredCRuns.Step config config' := by
  intro fuel
  induction fuel with
  | zero => intro config config' run; cases run
  | succ fuel inductionHypothesis =>
      intro config config' run
      cases found : invoke? config with
      | none =>
          simp only [invokeUntil, found] at run
          cases run
      | some next =>
          have first : Cold.structuredCRuns.Step config next :=
            (structuredCRuns_step_iff_invoke config next).2 found
          simp only [invokeUntil, found] at run
          by_cases boundary : configObservable next = true
          · rw [if_pos boundary] at run
            have same : next = config' := Option.some.inj run
            subst same
            exact Relation.ReflTransGen.single first
          · rw [if_neg boundary] at run
            exact Relation.ReflTransGen.head first (inductionHypothesis next config' run)

/-- The cold phase of a composed step is a finite run of the cold lane's
cover. -/
theorem reflTransGen_of_coldPhase {owned call config config' : Pattern}
    (step : ComposedInvocationStep (compilingPattern owned call config)
      (compilingPattern owned call config')) :
    Relation.ReflTransGen Cold.structuredCRuns.Step config config' := by
  rcases step.inv with ⟨_, _, source, target, sourceEq, targetEq, run⟩ |
    ⟨_, _, _, _, targetEq⟩ | ⟨_, _, sourceEq, _, _⟩
  · simp only [compilingPattern, Pattern.apply.injEq, List.cons.injEq, and_true,
      true_and] at sourceEq targetEq
    obtain ⟨_, _, sourceConfig⟩ := sourceEq
    obtain ⟨_, _, targetConfig⟩ := targetEq
    subst sourceConfig
    subst targetConfig
    exact reflTransGen_of_invokeUntil _ _ _ run
  · simp [compilingPattern, executingPattern] at targetEq
  · simp [compilingPattern, executingPattern] at sourceEq

/-- The hot phase of a composed step is exactly one step of the hot lane's
cover. -/
theorem composedInvocationStep_executing_iff (config config' : Pattern) :
    ComposedInvocationStep (executingPattern config) (executingPattern config') ↔
      Hot.hotStructuredCRuns.Step config config' := by
  constructor
  · intro step
    rcases step.inv with ⟨_, _, _, _, sourceEq, _, _⟩ | ⟨_, _, _, sourceEq, _⟩ |
      ⟨source, target, sourceEq, targetEq, run⟩
    · simp [compilingPattern, executingPattern] at sourceEq
    · simp [compilingPattern, executingPattern] at sourceEq
    · simp only [executingPattern, Pattern.apply.injEq, List.cons.injEq, and_true,
        true_and] at sourceEq targetEq
      subst sourceEq
      subst targetEq
      exact (hotStructuredCRuns_step_iff_invoke _ _).2 run
  · intro step
    exact ComposedInvocationStep.hot config config'
      ((hotStructuredCRuns_step_iff_invoke _ _).1 step)

/-! ## Observations carried along the composed cover

The composed theory's only observation is which control the machine is at, and
the composed encoding carries it exactly: the encoding is injective, because
the two phases use distinct heads and each phase's payload is injectively
encoded.  With that hypothesis discharged the Hennessy--Milner transport
applies to the composed cover, and adequacy is a corollary rather than a
separate argument.
-/

theorem encodeCallGuardInvocation_injective :
    Function.Injective encodeCallGuardInvocation := by
  intro left right equal
  cases left with
  | compiling ownedLeft callLeft compilerLeft =>
      cases right with
      | compiling ownedRight callRight compilerRight =>
          simp only [encodeCallGuardInvocation, compilingPattern, Pattern.apply.injEq,
            List.cons.injEq, and_true, true_and] at equal
          obtain ⟨ownedEq, callEq, configEq⟩ := equal
          rw [encodeOwned_injective ownedEq, encodeCall_injective callEq,
            runControl_fineOf_injective configEq]
      | executing _ =>
          simp [encodeCallGuardInvocation, compilingPattern, executingPattern] at equal
  | executing executorLeft =>
      cases right with
      | compiling _ _ _ =>
          simp [encodeCallGuardInvocation, compilingPattern, executingPattern] at equal
      | executing executorRight =>
          simp only [encodeCallGuardInvocation, executingPattern, Pattern.apply.injEq,
            List.cons.injEq, and_true, true_and] at equal
          rw [hotRunControl_injective equal]

/-- The composed theory observes which control it is at. -/
def controlObserved : ObservedGSLT MainlineCallGuardControl.callGuardGSLT where
  Atom := CallGuardControl
  observes control term := term = control

theorem controlObserved_resp (control : CallGuardControl)
    {left right : CallGuardControl}
    (equivalent : MainlineCallGuardControl.callGuardGSLT.Equiv left right) :
    controlObserved.observes control left ↔ controlObserved.observes control right := by
  have same : left = right := equivalent
  subst same
  exact Iff.rfl

/-- The composed representation observes which encoded control it is at. -/
def encodedControlObserved : ObservedGSLT composedInvocationRuns where
  Atom := CallGuardControl
  observes control pattern := pattern = encodeCallGuardInvocation control

theorem encodedControlObserved_resp (control : CallGuardControl) {left right : Pattern}
    (equivalent : composedInvocationRuns.Equiv left right) :
    encodedControlObserved.observes control left ↔
      encodedControlObserved.observes control right := by
  have same : left = right := equivalent
  subst same
  exact Iff.rfl

/-- Which control the machine is at is carried exactly by the composed
encoding. -/
theorem encodeCallGuardInvocation_observes_iff (control term : CallGuardControl) :
    controlObserved.observes control term ↔
      encodedControlObserved.observes (id control)
        (composedInvocationRealization.mapTerm term) :=
  ⟨fun observed => congrArg encodeCallGuardInvocation observed,
    fun observed => encodeCallGuardInvocation_injective observed⟩

/-- The composed call guard is a cover of the observed step systems: the
composed realization covers the steps, and the control observations are
carried exactly. -/
def composedInvocationSystemCover :
    HennessyMilner.SystemCover
      (HennessyMilner.System.ofObserved controlObserved controlObserved_resp)
      (HennessyMilner.System.ofObserved encodedControlObserved encodedControlObserved_resp) :=
  composedInvocationRealization.systemCover controlObserved encodedControlObserved
    controlObserved_resp encodedControlObserved_resp id
    encodeCallGuardInvocation_observes_iff

/-- Adequacy along the composed cover, with the atom and label renamings the
transport records. -/
theorem composedInvocation_sat_map
    (formula : HennessyMilner.Formula CallGuardControl Unit) (control : CallGuardControl) :
    (HennessyMilner.System.ofObserved encodedControlObserved encodedControlObserved_resp).sat
        (HennessyMilner.Formula.map (Atom := CallGuardControl) (Label := Unit)
          (Atom' := CallGuardControl) (Label' := Unit) id id formula)
        (encodeCallGuardInvocation control) ↔
      (HennessyMilner.System.ofObserved controlObserved controlObserved_resp).sat
        formula control :=
  composedInvocationSystemCover.sat_map formula control

/-- Adequacy, stated on the formula itself: a Hennessy--Milner formula over
control observations holds of an encoded control exactly when it holds of that
control in the composed theory. -/
theorem composedInvocation_sat_iff
    (formula : HennessyMilner.Formula CallGuardControl Unit) (control : CallGuardControl) :
    (HennessyMilner.System.ofObserved encodedControlObserved encodedControlObserved_resp).sat
        formula (encodeCallGuardInvocation control) ↔
      (HennessyMilner.System.ofObserved controlObserved controlObserved_resp).sat
        formula control := by
  have mapped := composedInvocation_sat_map formula control
  rwa [HennessyMilner.Formula.map_id] at mapped

/-- Observed bisimilarity is exact along the composed cover: the atom and label
renamings are the identity, so both directions of the transport apply. -/
theorem composedInvocation_bisimilar_iff (left right : CallGuardControl) :
    (HennessyMilner.System.ofObserved encodedControlObserved
        encodedControlObserved_resp).Bisimilar
        (encodeCallGuardInvocation left) (encodeCallGuardInvocation right) ↔
      (HennessyMilner.System.ofObserved controlObserved controlObserved_resp).Bisimilar
        left right :=
  composedInvocationSystemCover.bisimilar_map_iff (fun atom => ⟨atom, rfl⟩)
    (fun label => ⟨label, rfl⟩) left right

/-! ## Negative control: steps covered, observations not carried

Covering steps is not enough.  The composed encoding covers every step of the
composed theory, proved above; paired with an observation of the representation
that sees only the executing phase and not which control the phase holds, the
carried-observation law fails outright, so no system translation — hence no
system cover — has that data, and the atomic formula separating two executing
controls exhibits the failure directly.
-/

namespace PhaseOnly

def phaseOwned : OwnedSnapshot := ⟨⟨0⟩, ⟨0, [], [], []⟩⟩

def phaseCall : Call := ⟨"f", [], [], .atom "y"⟩

def phaseFamily : CompiledGuardFamily := ⟨⟨0⟩, 0, "f", 0, []⟩

def requested : CallGuardControl :=
  .executing (.request phaseOwned phaseCall (.compiled phaseFamily))

def planning : CallGuardControl := .executing (.plans phaseOwned.snapshot phaseCall [] [] [])

theorem requested_steps : callGuardStep? requested = some planning := rfl

theorem requested_ne_planning : requested ≠ planning := by
  simp [requested, planning]

/-- An observation of the composed representation that sees only the executing
phase: it ignores its atom, so every loaded executor state looks alike. -/
def phaseObserved : ObservedGSLT composedInvocationRuns where
  Atom := CallGuardControl
  observes _atom pattern := ∃ executor : ExecuteControl,
    pattern = executingPattern (Hot.runControl executor)

theorem phaseObserved_resp (control : CallGuardControl) {left right : Pattern}
    (equivalent : composedInvocationRuns.Equiv left right) :
    phaseObserved.observes control left ↔ phaseObserved.observes control right := by
  have same : left = right := equivalent
  subst same
  exact Iff.rfl

/-- The step is covered: the composed encoding maps the executor's request step
to a composed step. -/
theorem step_covered :
    composedInvocationRuns.Step (encodeCallGuardInvocation requested)
      (encodeCallGuardInvocation planning) :=
  composedInvocationRealization.mapStep requested_steps

/-- The observation is not carried: the phase observation holds of the encoded
`planning` at the atom `requested`, which the composed theory does not observe
there. -/
theorem observation_not_carried :
    phaseObserved.observes requested (encodeCallGuardInvocation planning) ∧
      ¬ controlObserved.observes requested planning :=
  ⟨⟨_, rfl⟩, fun observed => requested_ne_planning observed.symm⟩

/-- Hence no system translation of the observed systems has the composed
encoding as its term map, whatever it does to atoms. -/
theorem no_systemTranslation :
    ¬ ∃ translation : HennessyMilner.SystemTranslation
        (HennessyMilner.System.ofObserved controlObserved controlObserved_resp)
        (HennessyMilner.System.ofObserved phaseObserved phaseObserved_resp),
      translation.mapTerm = encodeCallGuardInvocation := by
  rintro ⟨translation, mapTerm⟩
  have carried := (translation.observes_iff requested planning).2
    (by rw [mapTerm]; exact ⟨_, rfl⟩)
  exact requested_ne_planning carried.symm

/-- A fortiori no system cover does, so the Hennessy--Milner transport is
unavailable for this observation although every step is covered. -/
theorem no_systemCover :
    ¬ ∃ cover : HennessyMilner.SystemCover
        (HennessyMilner.System.ofObserved controlObserved controlObserved_resp)
        (HennessyMilner.System.ofObserved phaseObserved phaseObserved_resp),
      cover.mapTerm = encodeCallGuardInvocation := by
  rintro ⟨cover, mapTerm⟩
  exact no_systemTranslation ⟨cover.toSystemTranslation, mapTerm⟩

/-- The formula that fails to transport: `planning` satisfies the atom
`requested` in the phase-observed representation but not in the composed
theory. -/
theorem sat_not_reflected :
    (HennessyMilner.System.ofObserved phaseObserved phaseObserved_resp).sat
        (.atom requested) (encodeCallGuardInvocation planning) ∧
      ¬ (HennessyMilner.System.ofObserved controlObserved controlObserved_resp).sat
        (.atom requested) planning :=
  observation_not_carried

end PhaseOnly

#print axioms composedInvocationRealization
#print axioms hotInvoke?_runControl
#print axioms Canary.request_realized
#print axioms Canary.negative_canary

#print axioms reflTransGen_of_invokeUntil
#print axioms reflTransGen_of_coldPhase
#print axioms composedInvocationStep_executing_iff
#print axioms encodeCallGuardInvocation_injective
#print axioms composedInvocationSystemCover
#print axioms composedInvocation_sat_map
#print axioms composedInvocation_sat_iff
#print axioms composedInvocation_bisimilar_iff
#print axioms PhaseOnly.step_covered
#print axioms PhaseOnly.observation_not_carried
#print axioms PhaseOnly.no_systemTranslation
#print axioms PhaseOnly.no_systemCover
#print axioms PhaseOnly.sat_not_reflected

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardComposedInvocationRealization
