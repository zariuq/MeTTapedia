import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteStructuredCTransitionProgram
import Mettapedia.GSLT.LanguageDef.StructuredCStraightLine

/-!
# Total realization of the completed-call executor by the generated hot body

Every loaded non-halted executor state, run through the generated hot body
under the hot handler, halts with the executor's next state in the state
slot. The interpreter first selects the phase without unfolding its branch
bodies. Each phase and argument mode is then realized using the handler's
projection, query, decision, and delta laws. `observation_iff` and
`normalized_observation` connect the resulting state to the executor's step
and the first-reduct normalization of the StructuredC LanguageDef.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteStructuredCTotalRealization

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.StructuredCStructuralRuntime
open Mettapedia.GSLT.LanguageDef.StructuredCStraightLine
open Mettapedia.Languages.MeTTa.PeTTa.MainlineTypeQueryGSLT
open Mettapedia.Languages.MeTTa.PeTTa.CallGuardNativeKernel
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardProjection
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardPlan
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardControl
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardOperational
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteOperational
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCFinishSemantics
  (abiValue readyReceipt externalReceipt valueUnit)
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteStructuredCSemantics
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteSourceDerivedStructuredC
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteStructuredCTransitionProgram

/-- One invocation: the generated body on the loaded state. -/

def runControl (control : ExecuteControl) : Pattern :=
  StructuredC.run generatedHotBody (initialEnvironment control) readyReceipt

/-- The state slot of a halted configuration. -/

def terminalControl? : Pattern → Option ExecuteControl
  | .apply "structured-c:halted" [_, environment, _] => do
      let value ← lookup? environment (StructuredC.Builder.identifier "state")
      decodeStateValue? value
  | _ => none

/-- The step budget of one invocation; no row needs more than a quarter of
it. -/

def runBudget : Nat := 256

/-- What one invocation observes: the state in the slot when it halts. -/

def observation (control : ExecuteControl) : Option ExecuteControl :=
  (runSteps? handler runBudget (runControl control)).bind terminalControl?
open Mettapedia.GSLT.LanguageDef.StructuredC.Builder

private theorem phase_evaluated (control : ExecuteControl) (environment receipt : Pattern)
    (stored : lookup? environment (identifier "state") = some (stateValue control)) :
    evaluate? handler (frameQuery .phase) environment receipt =
      some ⟨.value (phaseValue control), environment,
        externalReceipt FrameQuery.phase.externalName receipt⟩ := by
  apply evaluate_variable_call_exact handler FrameQuery.phase.externalName
    ["state"] [stateValue control]
  · exact .cons stored .nil
  · apply handler_of_readHandler
    exact readHandler_frameQuery_exact .phase control _ _ _ rfl stored

private theorem phase_value (control : ExecuteControl) (environment receipt : Pattern)
    (stored : lookup? environment (identifier "state") = some (stateValue control)) :
    evaluateValue? handler (frameQuery .phase) environment receipt =
      some (phaseValue control, environment, externalReceipt FrameQuery.phase.externalName receipt) := by
  unfold evaluateValue?
  rw [phase_evaluated control environment receipt stored]

private def phaseBody : ExecuteControl → Pattern
  | .request _ _ _ => requestDispatcher generatedRows
  | .plans _ _ _ _ _ => plansDispatcher generatedRows
  | .arguments _ _ _ _ _ _ _ _ _ _ => argumentsDispatcher generatedRows
  | .result _ _ _ _ _ _ => resultDispatcher generatedRows
  | .halted _ => outcomeBody terminalOutcome

private theorem phase_step (control : ExecuteControl) :
    step? handler (StructuredC.run generatedHotBody (initialEnvironment control) readyReceipt) =
      some (StructuredC.run (StructuredC.appendStatements (phaseBody control) StructuredC.nilStatements)
        (initialEnvironment control) (externalReceipt FrameQuery.phase.externalName readyReceipt)) := by
  have stored : lookup? (initialEnvironment control) (identifier "state") = some (stateValue control) :=
    lookup_bindName_same _ _ _
  simp only [generatedHotBody, assembleHotBody, statements, StructuredC.run, StructuredC.a,
    StructuredC.nilStatements, node, switch, cases, caseBranch, step?, statementStep?,
    phase_value control (initialEnvironment control) readyReceipt stored]
  cases control <;> rfl

private theorem observation_phase (control : ExecuteControl) : observation control =
    (runSteps? handler 255
      (StructuredC.run (StructuredC.appendStatements (phaseBody control) StructuredC.nilStatements)
        (initialEnvironment control) (externalReceipt FrameQuery.phase.externalName readyReceipt))).bind
      terminalControl? := by
  unfold observation runControl runBudget
  rw [runSteps?_of_step_exact handler 255 rfl (phase_step control)]

/-- The whole symbolic evaluation of one invocation. -/

macro "hot_simp" : tactic =>
  `(tactic| (rw [observation_phase]; simp [*, phaseBody,
    terminalControl?, runSteps?, step?, statementStep?, evaluateValue?, isHalted, evaluate?, evaluateLeaf?,
    evaluateLeaves?, expressionList?, externalName?, identifierName?, store?, selectBranch?,
    selectCase?, lookup?, bindName, environmentBind, environmentEmpty, trueValue, falseValue,
    StructuredC.Builder.node, StructuredC.Builder.token, StructuredC.Builder.identifier,
    StructuredC.Builder.externalName, StructuredC.Builder.namedType,
    StructuredC.Builder.valueSymbol, StructuredC.Builder.constant, StructuredC.Builder.symbol,
    StructuredC.Builder.variableExpression, StructuredC.Builder.expressions,
    StructuredC.Builder.call, StructuredC.Builder.statements,
    StructuredC.Builder.appendStatements, StructuredC.Builder.effect,
    StructuredC.Builder.declare, StructuredC.Builder.ifThenElse, StructuredC.Builder.returnSymbol,
    StructuredC.Builder.returnExpression, StructuredC.Builder.caseBranch,
    StructuredC.Builder.cases, StructuredC.Builder.switch, StructuredC.run, StructuredC.halted,
    StructuredC.consStatement, StructuredC.nilStatements, StructuredC.a,
    StructuredC.appendStatements, generatedHotBody, assembleHotBody, requestDispatcher,
    plansDispatcher, argumentsDispatcher, resultDispatcher, generatedRows, rowBody, guardedBody,
    deltaStatements,
    Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteSourceDerivedStructuredC.sequence,
    spliceStatements, bindProjections, bindProjection, frameQuery, outcomeBody, stateArgument,
    variableExpressions, targetVariable, projectionVariable, projectionType, deltaOutcome,
    advancedOutcome, haltedOutcome, noTransitionOutcome, terminalOutcome, engineFaultOutcome,
    requestOutsideFragmentRow, requestForeignOwnerRow, requestStaleRevisionRow,
    requestWrongHeadRow, requestWrongArityRow, requestCurrentRow, plansFinishedRow,
    planHeadMismatchRow, planHeadMatchesRow, argumentsFinishedRow, rawArgumentAcceptedRow,
    rawArgumentRejectedRow, uncheckedArgumentRow, checkedArgumentExactRow,
    checkedArgumentMetatypeAcceptedRow, checkedArgumentMetatypeRejectedRow,
    argumentShapeMismatchRow, uncheckedResultRow, checkedResultExactRow,
    checkedResultMetatypeAcceptedRow, checkedResultMetatypeRejectedRow, reasonExpression,
    fallbackSymbol, callVariables, familyVariables, declarationVariables, planVariables,
    fallbackRow, advanceOperands, installOperands,
    handler_projection_exact, handler_frameQuery_exact, handler_decision_exact, handler_delta_exact,
    lookup_bindName_same, lookup_bindName_of_ne, Projection.value?,
    FrameQuery.value?, Decision.decide?, Delta.apply?, call?, snapshot?, family?, plan?,
    remaining?, accepted?, events?, expected?, phaseValue, argumentModeTagValue,
    resultModeTagValue, boolValue, requestPhase, plansPhase, argumentsPhase, resultPhase,
    haltedPhase, rawModeTag, uncheckedModeTag, checkedModeTag, uncheckedResultTag,
    checkedResultTag, initialEnvironment, readyReceipt, externalReceipt, valueUnit, reasonValue,
    decodeReasonValue?, shapeMismatch, requestClass, Option.bind]))

/-- The executor's step, resolved by its own case split. -/

macro "executor_step" : tactic =>
  `(tactic| (simp [*, executeStep?, runArgMode, runResultMode, getTypeDecision,
    getMetatypeDecision] at *; subst_vars))

private theorem observation_request (current : OwnedSnapshot) (call : Call)
    (compilation : CompilationResult) (next : ExecuteControl)
    (step : executeStep? (.request current call compilation) = some next) :
    observation (.request current call compilation) = some next := by
  rcases call with ⟨function, sources, values, result⟩
  cases compilation with
  | outsideFragment => executor_step; hot_simp
  | compiled family =>
      by_cases ownerCurrent : family.owner = current.owner
      · by_cases revisionCurrent : family.revision = current.snapshot.revision
        · by_cases headMatches : family.head = function
          · by_cases arityMatches : family.arity = sources.length
            · executor_step; hot_simp
            · executor_step; hot_simp
          · executor_step; hot_simp
        · executor_step; hot_simp
      · executor_step; hot_simp

private theorem observation_plans (snapshot : Snapshot) (call : Call)
    (remaining : List GuardPlan) (accepted : List ArrowDeclaration) (events : List ControlEvent)
    (next : ExecuteControl) (step : executeStep? (.plans snapshot call remaining
      accepted events) = some next) :
    observation (.plans snapshot call remaining accepted events) = some next := by
  rcases call with ⟨function, sources, values, result⟩
  cases remaining with
  | nil => executor_step; hot_simp
  | cons plan remaining =>
      rcases plan with ⟨occurrence, planModes, resultMode,
        ⟨declarationOccurrence, declarationFunction, inputs, output⟩⟩
      by_cases headMatches : declarationFunction = function
      · executor_step; hot_simp
      · executor_step; hot_simp

private theorem observation_arguments_finished (snapshot : Snapshot) (call : Call) (plan : GuardPlan)
    (remaining : List GuardPlan) (index : Nat) (sources values : List Term)
    (accepted : List ArrowDeclaration) (events : List ControlEvent) (next : ExecuteControl)
    (step : executeStep? (.arguments snapshot call plan remaining index ([]) (sources) (values)
      accepted events) = some next) :
    observation (.arguments snapshot call plan remaining index ([]) (sources) (values)
      accepted events) = some next := by
  rcases plan with ⟨occurrence, planModes, resultMode,
    ⟨declarationOccurrence, declarationFunction, inputs, output⟩⟩
  cases sources <;> cases values <;> (executor_step; hot_simp)

private theorem observation_arguments_missing_source (snapshot : Snapshot) (call : Call) (plan : GuardPlan)
    (remaining : List GuardPlan) (index : Nat) (mode : ArgMode) (modes : List ArgMode) (values : List Term)
    (accepted : List ArrowDeclaration) (events : List ControlEvent) (next : ExecuteControl)
    (step : executeStep? (.arguments snapshot call plan remaining index (mode :: modes) ([]) (values)
      accepted events) = some next) :
    observation (.arguments snapshot call plan remaining index (mode :: modes) ([]) (values)
      accepted events) = some next := by
  rcases plan with ⟨occurrence, planModes, resultMode,
    ⟨declarationOccurrence, declarationFunction, inputs, output⟩⟩
  cases values <;> (executor_step; hot_simp)

private theorem observation_arguments_missing_value (snapshot : Snapshot) (call : Call) (plan : GuardPlan)
    (remaining : List GuardPlan) (index : Nat) (mode : ArgMode) (modes : List ArgMode) (source : Term) (sources : List Term)
    (accepted : List ArrowDeclaration) (events : List ControlEvent) (next : ExecuteControl)
    (step : executeStep? (.arguments snapshot call plan remaining index (mode :: modes) (source :: sources) ([])
      accepted events) = some next) :
    observation (.arguments snapshot call plan remaining index (mode :: modes) (source :: sources) ([])
      accepted events) = some next := by
  rcases plan with ⟨occurrence, planModes, resultMode,
    ⟨declarationOccurrence, declarationFunction, inputs, output⟩⟩
  executor_step; hot_simp

private theorem observation_arguments_raw (snapshot : Snapshot) (call : Call) (plan : GuardPlan)
    (remaining : List GuardPlan) (index : Nat) (modes : List ArgMode) (source value : Term) (sources values : List Term)
    (accepted : List ArrowDeclaration) (events : List ControlEvent) (next : ExecuteControl)
    (step : executeStep? (.arguments snapshot call plan remaining index (.rawAtom :: modes) (source :: sources) (value :: values)
      accepted events) = some next) :
    observation (.arguments snapshot call plan remaining index (.rawAtom :: modes) (source :: sources) (value :: values)
      accepted events) = some next := by
  rcases plan with ⟨occurrence, planModes, resultMode,
    ⟨declarationOccurrence, declarationFunction, inputs, output⟩⟩
  by_cases equal : value = source
  · executor_step; hot_simp
  · executor_step; hot_simp

private theorem observation_arguments_unchecked (snapshot : Snapshot) (call : Call) (plan : GuardPlan)
    (remaining : List GuardPlan) (index : Nat) (modes : List ArgMode) (source value : Term) (sources values : List Term)
    (accepted : List ArrowDeclaration) (events : List ControlEvent) (next : ExecuteControl)
    (step : executeStep? (.arguments snapshot call plan remaining index (.evalUnchecked :: modes) (source :: sources) (value :: values)
      accepted events) = some next) :
    observation (.arguments snapshot call plan remaining index (.evalUnchecked :: modes) (source :: sources) (value :: values)
      accepted events) = some next := by
  rcases plan with ⟨occurrence, planModes, resultMode,
    ⟨declarationOccurrence, declarationFunction, inputs, output⟩⟩
  executor_step; hot_simp

private theorem observation_arguments_checked (snapshot : Snapshot) (call : Call) (plan : GuardPlan)
    (remaining : List GuardPlan) (index : Nat) (expected : Term) (modes : List ArgMode) (source value : Term) (sources values : List Term)
    (accepted : List ArrowDeclaration) (events : List ControlEvent) (next : ExecuteControl)
    (step : executeStep? (.arguments snapshot call plan remaining index (.evalSoftcutType expected :: modes) (source :: sources) (value :: values)
      accepted events) = some next) :
    observation (.arguments snapshot call plan remaining index (.evalSoftcutType expected :: modes) (source :: sources) (value :: values)
      accepted events) = some next := by
  rcases plan with ⟨occurrence, planModes, resultMode,
    ⟨declarationOccurrence, declarationFunction, inputs, output⟩⟩
  by_cases exact : GetType snapshot value expected
  · executor_step; hot_simp
  · by_cases metatype : GetMetatype snapshot value expected
    · executor_step; hot_simp
    · executor_step; hot_simp

private theorem observation_result (snapshot : Snapshot) (call : Call) (plan : GuardPlan)
    (remaining : List GuardPlan) (accepted : List ArrowDeclaration) (events : List ControlEvent)
    (next : ExecuteControl) (step : executeStep? (.result snapshot call plan remaining
      accepted events) = some next) :
    observation (.result snapshot call plan remaining accepted events) = some next := by
  rcases call with ⟨function, sources, values, result⟩
  rcases plan with ⟨occurrence, planModes, resultMode,
    ⟨declarationOccurrence, declarationFunction, inputs, output⟩⟩
  cases resultMode with
  | resultUnchecked => executor_step; hot_simp
  | resultSoftcutType expected =>
      by_cases exact : GetType snapshot result expected
      · executor_step; hot_simp
      · by_cases metatype : GetMetatype snapshot result expected
        · executor_step; hot_simp
        · executor_step; hot_simp

/-- Every loaded non-halted state observes exactly the executor's next state. -/

theorem observation_exact (control next : ExecuteControl)
    (step : executeStep? control = some next) : observation control = some next := by
  cases control with
  | halted observation => simp [executeStep?] at step
  | request current call compilation => exact observation_request current call compilation next step
  | plans snapshot call remaining accepted events =>
      exact observation_plans snapshot call remaining accepted events next step
  | arguments snapshot call plan remaining index modes sources values accepted events =>
      cases modes with
      | nil =>
          exact observation_arguments_finished snapshot call plan remaining index sources values accepted events next step
      | cons mode modes =>
          cases sources with
          | nil =>
              exact observation_arguments_missing_source snapshot call plan remaining index mode modes values accepted events next step
          | cons source sources =>
              cases values with
              | nil =>
                  exact observation_arguments_missing_value snapshot call plan remaining index mode modes source sources accepted events next step
              | cons value values =>
                  cases mode with
                  | rawAtom =>
                      exact observation_arguments_raw snapshot call plan remaining index modes source value sources values accepted events next step
                  | evalUnchecked =>
                      exact observation_arguments_unchecked snapshot call plan remaining index modes source value sources values accepted events next step
                  | evalSoftcutType expected =>
                      exact observation_arguments_checked snapshot call plan remaining index expected modes source value sources values accepted events next step
  | result snapshot call plan remaining accepted events =>
      exact observation_result snapshot call plan remaining accepted events next step

/-- The executor steps from every non-halted state. -/
theorem executeStep?_isSome (control : ExecuteControl) (live : ∀ o, control ≠ .halted o) :
    (executeStep? control).isSome := by
  cases control with
  | halted observation => exact absurd rfl (live observation)
  | request current call compilation =>
      cases compilation with
      | outsideFragment => rfl
      | compiled family =>
          simp only [executeStep?]
          split <;> (try split) <;> (try split) <;> (try split) <;> rfl
  | plans snapshot call remaining accepted events =>
      cases remaining with
      | nil => rfl
      | cons plan remaining => simp only [executeStep?]; split <;> rfl
  | arguments snapshot call plan remaining index modes sources values accepted events =>
      cases modes with
      | nil => cases sources <;> cases values <;> rfl
      | cons mode modes =>
          cases sources with
          | nil => cases values <;> rfl
          | cons source sources =>
              cases values with
              | nil => rfl
              | cons value values => simp only [executeStep?]; split <;> rfl
  | result snapshot call plan remaining accepted events =>
      simp only [executeStep?]; split <;> rfl

/-- For a live state, the observation is exactly the executor's step. -/
theorem observation_iff (control next : ExecuteControl) (live : ∀ o, control ≠ .halted o) :
    observation control = some next ↔ executeStep? control = some next := by
  constructor
  · intro observed
    obtain ⟨stepped, isStep⟩ := Option.isSome_iff_exists.mp (executeStep?_isSome control live)
    have exact := observation_exact control stepped isStep
    rw [exact] at observed
    cases observed
    exact isStep
  · exact observation_exact control next

/-- The observation as the first-reduct normalization of the StructuredC
LanguageDef: the invocation halts at a configuration whose state slot is the
next state. -/
theorem normalized_observation (control next : ExecuteControl)
    (step : executeStep? control = some next) :
    ∃ final, runSteps? handler runBudget (runControl control) = some final ∧
      normalizeFirstUsing (relationEnv handler) StructuredC.language 1 runBudget
        (runControl control) = final ∧
      terminalControl? final = some next := by
  have observed := observation_exact control next step
  unfold observation at observed
  obtain ⟨final, ran, terminal⟩ := Option.bind_eq_some_iff.mp observed
  exact ⟨final, ran, normalizeFirst_of_runSteps? handler ran, terminal⟩

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteStructuredCTotalRealization
