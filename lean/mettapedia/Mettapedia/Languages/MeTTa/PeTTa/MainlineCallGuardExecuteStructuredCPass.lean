import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteStructuredCTotalRealization
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteMatchMachinePass
import Mettapedia.GSLT.LanguageDef.IRRunView

/-!
# The hot lowering as a pass on steps

StructuredC with the hot handler's relation environment is a representation.
Its invocation protocol enters a configuration only when the state it stores
is not halted and exits at a halted configuration by loading the observed
state into the next invocation.  Under the first-reduct strategy, one
invocation of the generated hot body is one step of that run view.

The admitted ordered-match machine run view over the executor language is
covered, through the state loader, by the StructuredC run view: every
machine run of the executor is an invocation of the generated body, and
every invocation from a loaded state is such a run.  Composed with the
identity cover from the executor language into the machine, the executor's
steps from canonical states are covered by StructuredC invocations.  This
replaces the mode-decision cover as the hot cover on steps; the dispatch
cover remains the mode projection.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteStructuredCPass

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.LanguageDef.IRPass
open Mettapedia.GSLT.LanguageDef.IRRunView
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.TotalGSLT
open Mettapedia.GSLT.LanguageDef.StructuredCStructuralRuntime
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.Languages.MeTTa.PeTTa.MainlineTypeQueryGSLT
open Mettapedia.Languages.MeTTa.PeTTa.CallGuardNativeKernel
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardPlan
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardControl
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteOperational
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCFinishSemantics
  (readyReceipt)
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteStructuredCSemantics
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteSourceDerivedStructuredC
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteStructuredCTransitionProgram
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteStructuredCTotalRealization
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteMatchMachinePass
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecutePatternMatrixCompilation
  (sourceLanguage)

/-! ## StructuredC as a representation -/

/-- StructuredC with the hot handler's relation environment. -/
def hotStructuredCIR : IRLanguage := ⟨StructuredC.validated, relations⟩

theorem structuredC_isEquationFree : StructuredC.language.isEquationFree = true := by
  decide

theorem structuredCStep_iff (source target : Pattern) :
    hotStructuredCIR.semantics.Step source target ↔
      langReducesUsing relations StructuredC.language source target := by
  change StepModuloEquations (engineBasePremises relations) StructuredC.language source target ↔ _
  rw [stepModuloEquations_iff_step_of_no_generators structuredC_isEquationFree]
  rfl

theorem structuredCEquiv_iff (left right : Pattern) :
    hotStructuredCIR.semantics.Equiv left right ↔ left = right :=
  gsltModuloEquations_equiv_iff_eq_of_no_generators structuredC_isEquationFree left right

/-! ## The invocation protocol -/

/-- A configuration entered by no invocation and left by no exit. -/
def inadmissibleConfig : Pattern := .apply "structured-c:inadmissible" []

/-- The state stored by a running configuration. -/
def storedControl? : Pattern → Option ExecuteControl
  | .apply "structured-c:run" [_, environment, _] => do
      let stored ← lookup? environment (StructuredC.Builder.identifier "state")
      decodeStateValue? stored
  | _ => none

/-- Whether the stored state is halted: such a configuration is not invoked,
because a halted state has no executor step. -/
def haltedState? (config : Pattern) : Bool :=
  match storedControl? config with
  | some (.halted _) => true
  | _ => false

theorem storedControl?_runControl (control : ExecuteControl) :
    storedControl? (runControl control) = some control := by
  show (do
      let stored ← lookup? (initialEnvironment control) (StructuredC.Builder.identifier "state")
      decodeStateValue? stored) = some control
  rw [initialEnvironment, lookup_bindName_same]
  simp

theorem haltedState?_runControl (control : ExecuteControl) :
    haltedState? (runControl control) = true ↔ ∃ observation, control = .halted observation := by
  simp only [haltedState?, storedControl?_runControl]
  cases control <;> simp

/-- Enter a configuration only when its stored state is not halted. -/
def invocationEntry (config : Pattern) : Pattern :=
  if haltedState? config then inadmissibleConfig else config

/-- Exit at a halted configuration by loading the observed state into the
next invocation. -/
def invocationExit (final : Pattern) : Option Pattern :=
  (terminalControl? final).map runControl

def structuredCProtocol : RunProtocol := ⟨invocationEntry, invocationExit⟩

/-- The StructuredC invocation run view under the first-reduct strategy with
the realization's step budget. -/
abbrev hotStructuredCRuns : GSLT :=
  strategyRunView hotStructuredCIR structuredCProtocol 1 runBudget

theorem inadmissible_no_reducts :
    rewriteAt (engineBasePremises relations) StructuredC.language 1 inadmissibleConfig = [] := by
  decide +kernel

theorem normalizeFirst_inadmissible (stepFuel : Nat) :
    normalizeFirstUsing relations StructuredC.language 1 stepFuel inadmissibleConfig =
      inadmissibleConfig := by
  cases stepFuel with
  | zero => rfl
  | succ _ =>
      unfold normalizeFirstUsing normalizeFirstAt
      rw [inadmissible_no_reducts]

theorem invocationExit_inadmissible : invocationExit inadmissibleConfig = none := by
  rfl

theorem haltedState?_inadmissible : haltedState? inadmissibleConfig = false := by
  rfl

/-- Existence: an executor step is a strategy run of the generated body. -/
theorem strategyRun_of_executeStep {source target : ExecuteControl}
    (step : executeStep? source = some target) :
    StrategyRun hotStructuredCIR structuredCProtocol 1 runBudget (runControl source)
      (runControl target) := by
  have notHalted : haltedState? (runControl source) = false := by
    apply Bool.eq_false_of_not_eq_true
    intro halted
    obtain ⟨observation, rfl⟩ := (haltedState?_runControl source).1 halted
    simp [executeStep?] at step
  unfold StrategyRun strategyEndpoint
  simp only [structuredCProtocol, invocationEntry, notHalted, Bool.false_eq_true, if_false,
    invocationExit]
  obtain ⟨final, _, normalized, terminal⟩ := normalized_observation source target step
  change (terminalControl?
      (normalizeFirstUsing relations StructuredC.language 1 runBudget (runControl source))).map
        runControl = some (runControl target)
  rw [show relations = relationEnv handler from rfl, normalized, terminal]
  rfl

/-- Exactness: a strategy run of the generated body from a loaded state is
that state's executor step, and the exit is the loaded target. -/
theorem executeStep_of_strategyRun {source : ExecuteControl} {exit : Pattern}
    (run : StrategyRun hotStructuredCIR structuredCProtocol 1 runBudget (runControl source) exit) :
    ∃ target, executeStep? source = some target ∧ exit = runControl target := by
  unfold StrategyRun strategyEndpoint at run
  by_cases halted : haltedState? (runControl source) = true
  · simp only [structuredCProtocol, invocationEntry, halted, if_true] at run
    change invocationExit
        (normalizeFirstUsing relations StructuredC.language 1 runBudget inadmissibleConfig) =
      some exit at run
    rw [normalizeFirst_inadmissible, invocationExit_inadmissible] at run
    cases run
  · have notHalted : haltedState? (runControl source) = false :=
      Bool.eq_false_of_not_eq_true halted
    simp only [structuredCProtocol, invocationEntry, notHalted, Bool.false_eq_true, if_false] at run
    have live : ∀ observation, source ≠ .halted observation := by
      intro observation equal
      exact halted ((haltedState?_runControl source).2 ⟨observation, equal⟩)
    obtain ⟨target, step⟩ := Option.isSome_iff_exists.mp (executeStep?_isSome source live)
    obtain ⟨final, _, normalized, terminal⟩ := normalized_observation source target step
    change (terminalControl?
        (normalizeFirstUsing relations StructuredC.language 1 runBudget (runControl source))).map
          runControl = some exit at run
    rw [show relations = relationEnv handler from rfl, normalized, terminal] at run
    exact ⟨target, step, (Option.some.inj run).symm⟩

/-! ## Admission on the machine side -/

/-- Canonical decoding: the term must be the encoding of what it decodes to. -/
def canonicalExecute? (source : Pattern) : Option ExecuteControl := do
  let control ← decodeExecuteControl? source
  if encodeExecuteControl control = source then some control else none

@[simp] theorem canonicalExecute?_encode (control : ExecuteControl) :
    canonicalExecute? (encodeExecuteControl control) = some control := by
  simp [canonicalExecute?]

theorem canonicalExecute?_isSome_iff_image (source : Pattern) :
    (canonicalExecute? source).isSome = true ↔ ∃ control, encodeExecuteControl control = source := by
  constructor
  · intro canonical
    obtain ⟨control, decoded⟩ := Option.isSome_iff_exists.mp canonical
    unfold canonicalExecute? at decoded
    obtain ⟨found, _, checked⟩ := Option.bind_eq_some_iff.mp decoded
    split at checked
    · rename_i equal
      cases checked
      exact ⟨_, equal⟩
    · cases checked
  · rintro ⟨control, rfl⟩
    simp

/-- The machine started in its failure program: no successor, no exit. -/
def stuckMachine (source : Pattern) : Pattern :=
  Machine.encodeState (.run .failure source [])

theorem stuckMachine_no_step (source target : Pattern) :
    ¬ machineIR.semantics.Step (stuckMachine source) target := by
  intro step
  change (Machine.ir relationEnv sourceLanguage).semantics.Step
    (Machine.encodeState (.run .failure source [])) target at step
  rw [Mettapedia.GSLT.LanguageDef.OrderedMatchMachineLanguage.step_iff_machineStep] at step
  obtain ⟨next, member, _⟩ := step
  simp [Mettapedia.GSLT.LanguageDef.OrderedMatchMachineLanguage.machineStep] at member

theorem exit?_stuckMachine (source : Pattern) : exit? (stuckMachine source) = none := by
  rfl

theorem reaches_stuckMachine {source final : Pattern}
    (run : reaches machineIR (stuckMachine source) final) : final = stuckMachine source := by
  induction run with
  | refl => rfl
  | tail _ step later =>
      subst later
      exact absurd step (stuckMachine_no_step source _)

/-- Load a term into the machine only when it is a canonical state
encoding. -/
def admittedEntry (source : Pattern) : Pattern :=
  if (canonicalExecute? source).isSome then protocol.entry source else stuckMachine source

def admittedProtocol : RunProtocol := ⟨admittedEntry, exit?⟩

/-- The admitted machine run view: one executor step from a canonical
state. -/
abbrev machineAdmittedRuns : GSLT := runView machineIR admittedProtocol

theorem machineAdmittedRuns_step_iff (source target : Pattern) :
    machineAdmittedRuns.Step source target ↔
      (∃ control, encodeExecuteControl control = source) ∧ machineRuns.Step source target := by
  rw [runView_step_iff_raw_of_equiv_eq machineIR admittedProtocol
    (fun equal => (machineEquiv_iff _ _).mp equal)]
  rw [runView_step_iff_raw_of_equiv_eq machineIR protocol
    (fun equal => (machineEquiv_iff _ _).mp equal)]
  by_cases canonical : (canonicalExecute? source).isSome = true
  · have image := (canonicalExecute?_isSome_iff_image source).1 canonical
    simp only [RawRun, admittedProtocol, admittedEntry, canonical, if_true]
    exact ⟨fun run => ⟨image, run⟩, fun ⟨_, run⟩ => run⟩
  · have noImage : ¬ ∃ control, encodeExecuteControl control = source :=
      fun image => canonical ((canonicalExecute?_isSome_iff_image source).2 image)
    simp only [RawRun, admittedProtocol, admittedEntry, canonical, Bool.false_eq_true, if_false]
    constructor
    · rintro ⟨final, run, exitEq⟩
      rw [reaches_stuckMachine run, exit?_stuckMachine] at exitEq
      cases exitEq
    · rintro ⟨image, _⟩
      exact absurd image noImage

/-! ## The pass -/

/-- Load a canonical state into the generated body. -/
def loadState (source : Pattern) : Pattern :=
  match canonicalExecute? source with
  | some control => runControl control
  | none => inadmissibleConfig

@[simp] theorem loadState_encode (control : ExecuteControl) :
    loadState (encodeExecuteControl control) = runControl control := by
  simp [loadState]

theorem loadState_of_noImage {source : Pattern}
    (noImage : ¬ ∃ control, encodeExecuteControl control = source) :
    loadState source = inadmissibleConfig := by
  have decoded : canonicalExecute? source = none := by
    cases decoded : canonicalExecute? source with
    | none => rfl
    | some control =>
        exact absurd ((canonicalExecute?_isSome_iff_image source).1 (by simp [decoded])) noImage
  simp [loadState, decoded]

/-- Forward: an admitted machine run is a StructuredC run of the loaded
states. -/
theorem structuredCRun_of_machineAdmittedRun {source target : Pattern}
    (run : machineAdmittedRuns.Step source target) :
    hotStructuredCRuns.Step (loadState source) (loadState target) := by
  obtain ⟨⟨control, rfl⟩, machineRun⟩ := (machineAdmittedRuns_step_iff _ _).1 run
  have executeStep := executeStep_of_machineRun machineRun
  obtain ⟨next, step, rfl⟩ := (executeIR_step_iff control target).1 executeStep
  rw [loadState_encode, loadState_encode]
  exact (strategyRunView_step_iff_strategy_of_equiv_eq hotStructuredCIR structuredCProtocol 1
    runBudget (fun equal => (structuredCEquiv_iff _ _).1 equal) _ _).2
    (strategyRun_of_executeStep step)

/-- Backward: a StructuredC run from a loaded state is an admitted machine
run whose loaded target is the exit. -/
theorem machineAdmittedRun_of_structuredCRun {source exit : Pattern}
    (run : hotStructuredCRuns.Step (loadState source) exit) :
    ∃ target, machineAdmittedRuns.Step source target ∧
      hotStructuredCIR.semantics.Equiv (loadState target) exit := by
  have strategy := (strategyRunView_step_iff_strategy_of_equiv_eq hotStructuredCIR
    structuredCProtocol 1 runBudget (fun equal => (structuredCEquiv_iff _ _).1 equal) _ _).1 run
  by_cases image : ∃ control, encodeExecuteControl control = source
  · obtain ⟨control, rfl⟩ := image
    rw [loadState_encode] at strategy
    obtain ⟨next, step, rfl⟩ := executeStep_of_strategyRun strategy
    refine ⟨encodeExecuteControl next, ?_, ?_⟩
    · exact (machineAdmittedRuns_step_iff _ _).2 ⟨⟨control, rfl⟩,
        machineRun_of_executeStep ((executeIR_step_iff control _).2 ⟨next, step, rfl⟩)⟩
    · rw [loadState_encode]
      exact (structuredCEquiv_iff _ _).2 rfl
  · exfalso
    rw [loadState_of_noImage image] at strategy
    unfold StrategyRun strategyEndpoint at strategy
    simp only [structuredCProtocol, invocationEntry, haltedState?_inadmissible,
      Bool.false_eq_true, if_false] at strategy
    change invocationExit
        (normalizeFirstUsing relations StructuredC.language 1 runBudget inadmissibleConfig) =
      some exit at strategy
    rw [normalizeFirst_inadmissible, invocationExit_inadmissible] at strategy
    cases strategy

/-- The pass from the admitted machine run view into the hot StructuredC run
view: the state loader is the term map. -/
def machineToStructuredCPass :
    SemanticCoveredTranslation machineAdmittedRuns hotStructuredCRuns where
  mapTerm := loadState
  mapEquiv equivalent :=
    (structuredCEquiv_iff _ _).2 (congrArg loadState ((machineEquiv_iff _ _).1 equivalent))
  mapStep := structuredCRun_of_machineAdmittedRun
  liftStep := machineAdmittedRun_of_structuredCRun

/-! ## The admitted executor language and the composite -/

/-- The executor language restricted to canonical sources. -/
def executeAdmitted : GSLT where
  Term := Pattern
  equations := ⟨Eq, eq_equivalence⟩
  rewrites source target :=
    (∃ control, encodeExecuteControl control = source) ∧ executeIR.semantics.Step source target
  rewrites_resp_left := by
    intro source source' target equal step
    cases equal
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    cases equal
    exact step

/-- The admitted executor language into the admitted machine run view. -/
def executeAdmittedToMachineAdmittedPass :
    SemanticCoveredTranslation executeAdmitted machineAdmittedRuns where
  mapTerm := id
  mapEquiv equal := (machineEquiv_iff _ _).2 equal
  mapStep step :=
    (machineAdmittedRuns_step_iff _ _).2 ⟨step.1, machineRun_of_executeStep step.2⟩
  liftStep := by
    intro source target run
    obtain ⟨image, machineRun⟩ := (machineAdmittedRuns_step_iff _ _).1 run
    exact ⟨target, ⟨image, executeStep_of_machineRun machineRun⟩, (machineEquiv_iff _ _).2 rfl⟩

/-- The composite: the admitted executor language covered by StructuredC
invocations of the generated hot body. -/
def executeToStructuredCPass : SemanticCoveredTranslation executeAdmitted hotStructuredCRuns :=
  executeAdmittedToMachineAdmittedPass.comp machineToStructuredCPass

theorem executeToStructuredCPass_mapTerm : executeToStructuredCPass.mapTerm = loadState :=
  rfl

/-- The admitted executor language includes into the executor language. -/
def admissionInclusion : OperationalTranslation executeAdmitted executeIR.semantics where
  mapTerm := id
  mapEquiv equal := (executeEquiv_iff _ _).2 equal
  mapStep step := step.2

/-- The inclusion is a cover exactly when every executor step starts from a
canonical encoding.  Nothing here asserts that it does. -/
theorem admission_cover_iff :
    (∃ cover : SemanticCoveredTranslation executeAdmitted executeIR.semantics,
        cover.mapTerm = id) ↔
      ∀ source target, executeIR.semantics.Step source target →
        ∃ control, encodeExecuteControl control = source := by
  constructor
  · rintro ⟨cover, mapTerm⟩ source target step
    have lifted := cover.liftStep (sourceTerm := source) (targetTerm := target)
      (by rw [mapTerm]; exact step)
    obtain ⟨_, ⟨image, _⟩, _⟩ := lifted
    exact image
  · intro canonical
    refine ⟨{ admissionInclusion with liftStep := ?_ }, rfl⟩
    intro source target step
    exact ⟨target, ⟨canonical source target step, step⟩, (executeEquiv_iff _ _).2 rfl⟩

/-! ## The program the pass executes is the source-derived program -/

/-- Every loaded state runs the generated hot body, and that body is exactly
what the source-derived chain produces. -/
theorem pass_runs_sourceDerived_body (control : ExecuteControl) :
    loadState (encodeExecuteControl control) =
        StructuredC.run generatedHotBody (initialEnvironment control) readyReceipt ∧
      sourceDerivedHotBody? = some generatedHotBody ∧
        sourceDerivedHotProgram? = some generatedHotProgram :=
  ⟨by rw [loadState_encode]; rfl, sourceDerived_eq, sourceDerivedHotProgram?_eq⟩

/-! ## Canaries -/

namespace Canary

def emptySnapshot : Snapshot := ⟨0, [], [], []⟩

def emptyCall : Call := ⟨"f", [], [], .atom "y"⟩

/-- No plan remains: the executor halts executed. -/
def sourceControl : ExecuteControl := .plans emptySnapshot emptyCall [] [] []

def targetControl : ExecuteControl := .halted ⟨.executed [], []⟩

theorem source_steps : executeStep? sourceControl = some targetControl := rfl

/-- Positive: a real executor step is an admitted executor step. -/
theorem admitted_step :
    executeAdmitted.Step (encodeExecuteControl sourceControl)
      (encodeExecuteControl targetControl) :=
  ⟨⟨sourceControl, rfl⟩, (executeIR_step_iff sourceControl _).2 ⟨targetControl, source_steps, rfl⟩⟩

/-- Positive: it lifts through both covers into a StructuredC invocation of
the loaded states. -/
theorem lifted_through_both_covers :
    hotStructuredCRuns.Step (runControl sourceControl) (runControl targetControl) := by
  have run := executeToStructuredCPass.mapStep admitted_step
  rw [executeToStructuredCPass_mapTerm, loadState_encode, loadState_encode] at run
  exact run

/-- A halted state is admitted but has no step on either side. -/
def haltedControl : ExecuteControl := .halted ⟨.fallback .outsideFragment, []⟩

theorem halted_no_admitted_step (target : Pattern) :
    ¬ machineAdmittedRuns.Step (encodeExecuteControl haltedControl) target := by
  intro run
  obtain ⟨_, machineRun⟩ := (machineAdmittedRuns_step_iff _ _).1 run
  exact halted_no_step _ target (executeStep_of_machineRun machineRun)

/-- The StructuredC run view with one invented transition out of the loaded
halted state. -/
def inventingRuns : GSLT where
  Term := Pattern
  equations := hotStructuredCRuns.equations
  rewrites source target :=
    hotStructuredCRuns.Step source target ∨
      (source = runControl haltedControl ∧ target = inadmissibleConfig)
  rewrites_resp_left := by
    intro source source' target equal step
    have same : source = source' := (structuredCEquiv_iff _ _).1 equal
    subst same
    exact ⟨target, step, hotStructuredCRuns.equations.iseqv.refl target⟩
  rewrites_resp_right := by
    intro source target target' step equal
    have same : target = target' := (structuredCEquiv_iff _ _).1 equal
    subst same
    exact step

/-- Negative: no cover with the loading term map reaches the inventing view,
because the invented transition has no admitted machine run to lift to. -/
theorem negative_canary :
    ¬ ∃ cover : SemanticCoveredTranslation machineAdmittedRuns inventingRuns,
      cover.mapTerm = loadState := by
  rintro ⟨cover, mapTerm⟩
  have invented : inventingRuns.Step (cover.mapTerm (encodeExecuteControl haltedControl))
      inadmissibleConfig := by
    rw [mapTerm, loadState_encode]
    exact Or.inr ⟨rfl, rfl⟩
  obtain ⟨target, run, _⟩ := cover.liftStep invented
  exact halted_no_admitted_step target run

end Canary

#print axioms machineToStructuredCPass
#print axioms executeToStructuredCPass
#print axioms admission_cover_iff
#print axioms pass_runs_sourceDerived_body
#print axioms Canary.lifted_through_both_covers
#print axioms Canary.negative_canary

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteStructuredCPass
