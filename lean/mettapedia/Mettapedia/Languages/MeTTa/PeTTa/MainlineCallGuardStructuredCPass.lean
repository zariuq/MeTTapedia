import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardMatchMachinePass
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCTotalRealization
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardSourceDerivedStructuredCProgram

/-!
# The cold call-guard lowering to StructuredC as a pass

StructuredC is a representation: the StructuredC language definition with
the cold compiler's reference catalogs as its relation environment.  Its
invocation run view follows the first-reduct strategy with the realization's
bounds, enters a configuration only when the stored state is not halted, and
exits at a halted configuration by reading the canonical state back into the
next invocation.  One such run is one cold compiler step.

Admission is a protocol, not a decoder hack.  The ordered-match machine's
run view is admitted at its entry: a source term is loaded only when it is
a canonical control encoding, otherwise the machine is started in its
failure program, which has no successor and no exit.  The pass from the
admitted machine run view into the StructuredC run view loads the decoded
state into the generated body; its two cover directions are the total
realization's existence theorem and its exact-observation theorem.

The cold language enters through the same admission: the admitted cold
GSLT is the cold language restricted to canonical sources.  Its inclusion
into the full cold language is a forward pass, and it is a cover exactly when
every cold step starts from a canonical encoding, which is stated and not
assumed.  The composite `coldToStructuredCPass` is the admitted cold language
covered by StructuredC runs, and the program those runs execute is exactly
the program the source-derived compiler produces.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardStructuredCPass

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.LanguageDef.IRPass
open Mettapedia.GSLT.LanguageDef.IRRunView
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.TotalGSLT
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardPlan
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardOperational
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileCodec
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardPatternMatrixCompilation
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardMatchMachinePass
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCOneStepSimulation
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCFinishSemantics
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCDispatcher
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCProgram
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCTotalRealization
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardSourceDerivedStructuredCProgram

/-! ## StructuredC as a representation -/

/-- StructuredC with the cold compiler's reference catalogs. -/
def structuredCIR : IRLanguage := ⟨StructuredC.validated, coldRelations⟩

theorem structuredC_isEquationFree : StructuredC.language.isEquationFree = true := by
  decide

theorem structuredCStep_iff (source target : Pattern) :
    structuredCIR.semantics.Step source target ↔
      langReducesUsing coldRelations StructuredC.language source target := by
  change StepModuloEquations (engineBasePremises coldRelations) StructuredC.language source
      target ↔ _
  rw [stepModuloEquations_iff_step_of_no_generators structuredC_isEquationFree]
  rfl

theorem structuredCEquiv_iff (left right : Pattern) :
    structuredCIR.semantics.Equiv left right ↔ left = right :=
  gsltModuloEquations_equiv_iff_eq_of_no_generators structuredC_isEquationFree left right

/-- The realization's own GSLT and the representation's semantics have the
same steps. -/
theorem coldGSLT_step_iff (source target : Pattern) :
    coldGSLT.Step source target ↔ structuredCIR.semantics.Step source target := by
  rw [structuredCStep_iff]
  exact languageGSLTUsing_step coldRelations StructuredC.language coldLaws source target

/-! ## The invocation protocol -/

/-- A configuration entered by no invocation and left by no exit. -/
def inadmissibleConfig : Pattern := .apply "structured-c:inadmissible" []

/-- The canonical control stored by a running configuration. -/
def storedControl? : Pattern → Option CompileLanguageControl
  | .apply "structured-c:run" [_, environment, _] => do
      let stored ← StructuredCStructuralRuntime.lookup? environment
        (StructuredC.Builder.identifier "state")
      decodeStateValue? stored
  | _ => none

/-- Whether the stored control is halted: such a configuration is not
invoked, because a halted control has no compiler step. -/
def haltedState? (config : Pattern) : Bool :=
  match storedControl? config with
  | some (.halted _) => true
  | _ => false

theorem storedControl?_runControl (control : CompileLanguageControl) :
    storedControl? (runControl control) = some control := by
  show (do
      let stored ← StructuredCStructuralRuntime.lookup? (initialEnvironment control)
        (StructuredC.Builder.identifier "state")
      decodeStateValue? stored) = some control
  rw [initialEnvironment, StructuredCStructuralRuntime.lookup_bindName_same]
  simp [decodeStateValue?, decodeAbiWith?, stateValue, abiValue, abiPayload?,
    StructuredC.Builder.node]

theorem haltedState?_runControl (control : CompileLanguageControl) :
    haltedState? (runControl control) = true ↔ ∃ result, control = .halted result := by
  simp only [haltedState?, storedControl?_runControl]
  cases control <;> simp

/-- Enter a configuration only when its stored control is not halted. -/
def invocationEntry (config : Pattern) : Pattern :=
  if haltedState? config then inadmissibleConfig else config

/-- Exit at a halted configuration by loading the observed control into the
next invocation. -/
def invocationExit (final : Pattern) : Option Pattern :=
  (terminalControl? final).map runControl

def structuredCProtocol : RunProtocol := ⟨invocationEntry, invocationExit⟩

/-- The StructuredC invocation run view, under the first-reduct strategy
with the realization's contextual and step bounds. -/
abbrev structuredCRuns : GSLT := strategyRunView structuredCIR structuredCProtocol 1 64

theorem inadmissible_no_reducts :
    rewriteAt (engineBasePremises coldRelations) StructuredC.language 1 inadmissibleConfig = [] := by
  decide +kernel

theorem normalizeFirst_inadmissible (stepFuel : Nat) :
    normalizeFirstUsing coldRelations StructuredC.language 1 stepFuel inadmissibleConfig =
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

/-- A non-halted control has a compiler step. -/
theorem step_of_not_halted (control : CompileLanguageControl)
    (notHalted : ¬ ∃ result, control = .halted result) :
    ∃ target, compileLanguageStep? control = some target := by
  cases control with
  | halted result => exact absurd ⟨result, rfl⟩ notHalted
  | running owner revision head arity remaining accepted =>
      cases remaining with
      | nil => exact ⟨_, rfl⟩
      | cons declaration remaining =>
          simp only [compileLanguageStep?]
          split <;> exact ⟨_, rfl⟩
  | arguments owner revision head arity declaration remaining inputCursor modes accepted =>
      cases inputCursor with
      | nil => exact ⟨_, rfl⟩
      | cons expected inputs =>
          simp only [compileLanguageStep?]
          cases compileArgMode expected <;> exact ⟨_, rfl⟩
  | result owner revision head arity declaration remaining modes accepted =>
      simp only [compileLanguageStep?]
      cases compileResultMode declaration.outputType <;> exact ⟨_, rfl⟩

/-- Existence: a compiler step is a strategy run of the generated body. -/
theorem strategyRun_of_compileStep {source target : CompileLanguageControl}
    (step : compileLanguageStep? source = some target) :
    StrategyRun structuredCIR structuredCProtocol 1 64 (runControl source) (runControl target) := by
  have notHalted : haltedState? (runControl source) = false := by
    apply Bool.eq_false_of_not_eq_true
    intro halted
    obtain ⟨result, rfl⟩ := (haltedState?_runControl source).1 halted
    simp [compileLanguageStep?] at step
  unfold StrategyRun strategyEndpoint
  simp only [structuredCProtocol, invocationEntry, notHalted, Bool.false_eq_true, if_false,
    invocationExit]
  have observed :=
    (normalized_observation_iff_of_step (step : compileLanguageGSLT.Step source target) target).2
      rfl
  change (terminalControl?
      (normalizeFirstUsing coldRelations StructuredC.language 1 64 (runControl source))).map
        runControl = some (runControl target)
  rw [observed]
  rfl

/-- Exactness: a strategy run of the generated body from a loaded control
is that control's compiler step, and the exit is the loaded target. -/
theorem compileStep_of_strategyRun {source : CompileLanguageControl} {exit : Pattern}
    (run : StrategyRun structuredCIR structuredCProtocol 1 64 (runControl source) exit) :
    ∃ target, compileLanguageStep? source = some target ∧ exit = runControl target := by
  unfold StrategyRun strategyEndpoint at run
  by_cases halted : haltedState? (runControl source) = true
  · simp only [structuredCProtocol, invocationEntry, halted, if_true] at run
    change invocationExit
        (normalizeFirstUsing coldRelations StructuredC.language 1 64 inadmissibleConfig) =
      some exit at run
    rw [normalizeFirst_inadmissible, invocationExit_inadmissible] at run
    cases run
  · have notHalted : haltedState? (runControl source) = false :=
      Bool.eq_false_of_not_eq_true halted
    simp only [structuredCProtocol, invocationEntry, notHalted, Bool.false_eq_true, if_false] at run
    obtain ⟨target, step⟩ := step_of_not_halted source
      (fun ⟨result, equal⟩ => halted ((haltedState?_runControl source).2 ⟨result, equal⟩))
    change (terminalControl?
        (normalizeFirstUsing coldRelations StructuredC.language 1 64 (runControl source))).map
          runControl = some exit at run
    obtain ⟨observed, observedEq, exitEq⟩ := Option.map_eq_some_iff.1 run
    have same : observed = target :=
      (normalized_observation_iff_of_step (step : compileLanguageGSLT.Step source target)
        observed).1 observedEq
    subst same
    exact ⟨observed, step, exitEq.symm⟩

/-! ## Admission on the machine side -/

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

/-- Load a term into the machine only when it is a canonical control
encoding. -/
def admittedEntry (source : Pattern) : Pattern :=
  if (canonicalCompileControlCodec.decode source).isSome then protocol.entry source
  else stuckMachine source

def admittedProtocol : RunProtocol := ⟨admittedEntry, exit?⟩

/-- The admitted machine run view: one cold step from a canonical state. -/
abbrev machineAdmittedRuns : GSLT := runView machineIR admittedProtocol

theorem machineAdmittedRuns_step_iff (source target : Pattern) :
    machineAdmittedRuns.Step source target ↔
      (∃ control, encodeCompileLanguageControl control = source) ∧
        machineRuns.Step source target := by
  rw [runView_step_iff_raw_of_equiv_eq machineIR admittedProtocol
    (fun equal => (machineEquiv_iff _ _).mp equal)]
  rw [runView_step_iff_raw_of_equiv_eq machineIR protocol
    (fun equal => (machineEquiv_iff _ _).mp equal)]
  by_cases canonical : (canonicalCompileControlCodec.decode source).isSome = true
  · have image := (canonical_decode_isSome_iff_image source).1 canonical
    simp only [RawRun, admittedProtocol, admittedEntry, canonical, if_true]
    exact ⟨fun run => ⟨image, run⟩, fun ⟨_, run⟩ => run⟩
  · have noImage : ¬ ∃ control, encodeCompileLanguageControl control = source :=
      fun image => canonical ((canonical_decode_isSome_iff_image source).2 image)
    simp only [RawRun, admittedProtocol, admittedEntry, canonical, Bool.false_eq_true, if_false]
    constructor
    · rintro ⟨final, run, exitEq⟩
      rw [reaches_stuckMachine run, exit?_stuckMachine] at exitEq
      cases exitEq
    · rintro ⟨image, _⟩
      exact absurd image noImage

/-! ## The pass -/

/-- Load a canonical control into the generated body. -/
def loadState (source : Pattern) : Pattern :=
  match canonicalCompileControlCodec.decode source with
  | some control => runControl control
  | none => inadmissibleConfig

@[simp] theorem loadState_encode (control : CompileLanguageControl) :
    loadState (encodeCompileLanguageControl control) = runControl control := by
  have decoded : canonicalCompileControlCodec.decode (encodeCompileLanguageControl control) =
      some control :=
    (canonical_decode_eq_some_iff _ control).2 ⟨decodeCompileLanguageControl_encode control, rfl⟩
  simp [loadState, decoded]

theorem loadState_of_noImage {source : Pattern}
    (noImage : ¬ ∃ control, encodeCompileLanguageControl control = source) :
    loadState source = inadmissibleConfig := by
  have decoded : canonicalCompileControlCodec.decode source = none := by
    cases decoded : canonicalCompileControlCodec.decode source with
    | none => rfl
    | some control =>
        exact absurd ((canonical_decode_isSome_iff_image source).1 (by simp [decoded])) noImage
  simp [loadState, decoded]

/-- Forward: an admitted machine run is a StructuredC run of the loaded
states. -/
theorem structuredCRun_of_machineAdmittedRun {source target : Pattern}
    (run : machineAdmittedRuns.Step source target) :
    structuredCRuns.Step (loadState source) (loadState target) := by
  obtain ⟨⟨control, rfl⟩, machineRun⟩ := (machineAdmittedRuns_step_iff _ _).1 run
  have coldStep := coldStep_of_machineRun machineRun
  obtain ⟨next, step, rfl⟩ :=
    (language_step_iff_compileLanguageStep control target).1 ((coldStep_iff _ _).1 coldStep)
  rw [loadState_encode, loadState_encode]
  exact (strategyRunView_step_iff_strategy_of_equiv_eq structuredCIR structuredCProtocol 1 64
    (fun equal => (structuredCEquiv_iff _ _).1 equal) _ _).2 (strategyRun_of_compileStep step)

/-- Backward: a StructuredC run from a loaded state is an admitted machine
run whose loaded target is the exit. -/
theorem machineAdmittedRun_of_structuredCRun {source exit : Pattern}
    (run : structuredCRuns.Step (loadState source) exit) :
    ∃ target, machineAdmittedRuns.Step source target ∧
      structuredCIR.semantics.Equiv (loadState target) exit := by
  have strategy := (strategyRunView_step_iff_strategy_of_equiv_eq structuredCIR
    structuredCProtocol 1 64 (fun equal => (structuredCEquiv_iff _ _).1 equal) _ _).1 run
  by_cases image : ∃ control, encodeCompileLanguageControl control = source
  · obtain ⟨control, rfl⟩ := image
    rw [loadState_encode] at strategy
    obtain ⟨next, step, rfl⟩ := compileStep_of_strategyRun strategy
    refine ⟨encodeCompileLanguageControl next, ?_, ?_⟩
    · exact (machineAdmittedRuns_step_iff _ _).2 ⟨⟨control, rfl⟩,
        machineRun_of_coldStep ((coldStep_iff _ _).2
          ((language_step_iff_compileLanguageStep control _).2 ⟨next, step, rfl⟩))⟩
    · rw [loadState_encode]
      exact (structuredCEquiv_iff _ _).2 rfl
  · exfalso
    rw [loadState_of_noImage image] at strategy
    unfold StrategyRun strategyEndpoint at strategy
    simp only [structuredCProtocol, invocationEntry, haltedState?_inadmissible,
      Bool.false_eq_true, if_false] at strategy
    change invocationExit
        (normalizeFirstUsing coldRelations StructuredC.language 1 64 inadmissibleConfig) =
      some exit at strategy
    rw [normalizeFirst_inadmissible, invocationExit_inadmissible] at strategy
    cases strategy

/-- The pass from the admitted machine run view into the StructuredC run
view. -/
def machineToStructuredCPass : SemanticCoveredTranslation machineAdmittedRuns structuredCRuns where
  mapTerm := loadState
  mapEquiv equivalent :=
    (structuredCEquiv_iff _ _).2 (congrArg loadState ((machineEquiv_iff _ _).1 equivalent))
  mapStep := structuredCRun_of_machineAdmittedRun
  liftStep := machineAdmittedRun_of_structuredCRun

/-! ## The admitted cold language and the composite -/

/-- The cold language restricted to canonical sources: the admission
boundary of the cold representation. -/
def coldAdmitted : GSLT where
  Term := Pattern
  equations := ⟨Eq, eq_equivalence⟩
  rewrites source target :=
    (∃ control, encodeCompileLanguageControl control = source) ∧
      coldIR.semantics.Step source target
  rewrites_resp_left := by
    intro source source' target equal step
    cases equal
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    cases equal
    exact step

/-- The admitted cold language into the admitted machine run view. -/
def coldAdmittedToMachineAdmittedPass :
    SemanticCoveredTranslation coldAdmitted machineAdmittedRuns where
  mapTerm := id
  mapEquiv equal := (machineEquiv_iff _ _).2 equal
  mapStep step :=
    (machineAdmittedRuns_step_iff _ _).2 ⟨step.1, machineRun_of_coldStep step.2⟩
  liftStep := by
    intro source target run
    obtain ⟨image, machineRun⟩ := (machineAdmittedRuns_step_iff _ _).1 run
    exact ⟨target, ⟨image, coldStep_of_machineRun machineRun⟩, (machineEquiv_iff _ _).2 rfl⟩

/-- The composite: the admitted cold language covered by StructuredC runs. -/
def coldToStructuredCPass : SemanticCoveredTranslation coldAdmitted structuredCRuns :=
  coldAdmittedToMachineAdmittedPass.comp machineToStructuredCPass

theorem coldToStructuredCPass_mapTerm : coldToStructuredCPass.mapTerm = loadState :=
  rfl

/-- The admitted cold language includes into the cold language. -/
def admissionInclusion : OperationalTranslation coldAdmitted coldIR.semantics where
  mapTerm := id
  mapEquiv equal := (coldEquiv_iff _ _).2 equal
  mapStep step := step.2

/-- The inclusion is a cover exactly when every cold step starts from a
canonical encoding.  Nothing here asserts that it does. -/
theorem admission_cover_iff :
    (∃ cover : SemanticCoveredTranslation coldAdmitted coldIR.semantics, cover.mapTerm = id) ↔
      ∀ source target, coldIR.semantics.Step source target →
        ∃ control, encodeCompileLanguageControl control = source := by
  constructor
  · rintro ⟨cover, mapTerm⟩ source target step
    have lifted := cover.liftStep (sourceTerm := source) (targetTerm := target)
      (by rw [mapTerm]; exact step)
    obtain ⟨_, ⟨image, _⟩, _⟩ := lifted
    exact image
  · intro canonical
    refine ⟨{ admissionInclusion with liftStep := ?_ }, rfl⟩
    intro source target step
    exact ⟨target, ⟨canonical source target step, step⟩, (coldEquiv_iff _ _).2 rfl⟩

/-! ## The program the pass executes is the source-derived program -/

/-- Every loaded state runs the generated cold body, and that body is
exactly what the source-derived compiler produces. -/
theorem pass_runs_sourceDerived_body (control : CompileLanguageControl) :
    loadState (encodeCompileLanguageControl control) =
        StructuredC.run generatedColdBody (initialEnvironment control) readyReceipt ∧
      sourceDerivedColdBody? = some generatedColdBody ∧
        sourceDerivedColdProgram? = some generatedColdProgram :=
  ⟨by rw [loadState_encode]; rfl, sourceDerivedColdBody?_eq_generated,
    sourceDerivedColdProgram?_eq_generated⟩

/-! ## Canaries -/

namespace Canary

/-- The empty declaration list at head `f`, arity `0`. -/
def sourceControl : CompileLanguageControl :=
  .running ⟨0⟩ 0 "f" 0 [] []

def targetControl : CompileLanguageControl :=
  .halted (.compiled ⟨⟨0⟩, 0, "f", 0, []⟩)

theorem source_steps : compileLanguageStep? sourceControl = some targetControl :=
  rfl

/-- Positive: a real cold step is an admitted cold step. -/
theorem admitted_step :
    coldAdmitted.Step (encodeCompileLanguageControl sourceControl)
      (encodeCompileLanguageControl targetControl) :=
  ⟨⟨sourceControl, rfl⟩,
    (coldStep_iff _ _).2
      ((language_step_iff_compileLanguageStep sourceControl _).2
        ⟨targetControl, source_steps, rfl⟩)⟩

/-- Positive: it lifts through both covers into a StructuredC run of the
loaded states. -/
theorem lifted_through_both_covers :
    structuredCRuns.Step (runControl sourceControl) (runControl targetControl) := by
  have run := coldToStructuredCPass.mapStep admitted_step
  rw [coldToStructuredCPass_mapTerm, loadState_encode, loadState_encode] at run
  exact run

/-- A halted control is admitted but has no step on either side. -/
def haltedControl : CompileLanguageControl :=
  .halted .outsideFragment

theorem halted_no_admitted_step (target : Pattern) :
    ¬ machineAdmittedRuns.Step (encodeCompileLanguageControl haltedControl) target := by
  intro run
  obtain ⟨_, machineRun⟩ := (machineAdmittedRuns_step_iff _ _).1 run
  obtain ⟨next, step, _⟩ := (language_step_iff_compileLanguageStep haltedControl target).1
    ((coldStep_iff _ _).1 (coldStep_of_machineRun machineRun))
  simp [haltedControl, compileLanguageStep?] at step

/-- The StructuredC run view with one invented transition out of the loaded
halted control. -/
def inventingRuns : GSLT where
  Term := Pattern
  equations := structuredCRuns.equations
  rewrites source target :=
    structuredCRuns.Step source target ∨
      (source = runControl haltedControl ∧ target = inadmissibleConfig)
  rewrites_resp_left := by
    intro source source' target equal step
    have same : source = source' := (structuredCEquiv_iff _ _).1 equal
    subst same
    exact ⟨target, step, structuredCRuns.equations.iseqv.refl target⟩
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
  have invented : inventingRuns.Step (cover.mapTerm (encodeCompileLanguageControl haltedControl))
      inadmissibleConfig := by
    rw [mapTerm, loadState_encode]
    exact Or.inr ⟨rfl, rfl⟩
  obtain ⟨target, run, _⟩ := cover.liftStep invented
  exact halted_no_admitted_step target run

end Canary

#print axioms machineToStructuredCPass
#print axioms coldToStructuredCPass
#print axioms admission_cover_iff
#print axioms pass_runs_sourceDerived_body
#print axioms Canary.lifted_through_both_covers
#print axioms Canary.negative_canary

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardStructuredCPass
