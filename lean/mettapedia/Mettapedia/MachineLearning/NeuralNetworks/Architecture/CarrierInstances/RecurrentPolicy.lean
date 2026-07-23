import Mettapedia.MachineLearning.NeuralNetworks.Architecture.CarrierInstances.Recurrent
import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.CarrierDecisionPipeline

/-!
# Recurrent policy-port semantics

The recurrent TGAD arm first embeds seven typed construction fields, clamps
only the argument, depth, and open-hole indices, adds the masked source
summary, initializes one hidden vector from that summary, and then applies one
recurrent transition per action.  The emitted hidden state is the decision
state consumed by the common source-attention and legal-action readout.

This file gives the ideal, implementation-independent finite semantics.  It
also connects teacher-forced scanning to incremental execution through the
common `StateCarrier` interface.  A separate source checker pins these stages
to the concrete Python port.  No floating-point or library-internal GRU
equivalence is claimed here.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.Architecture

open StateCarrier
open Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder

universe uEnvironment uCommand uSummary uInput uHidden uPolicy

/-! ## Source-shaped typed construction fields -/

/-- The seven discrete fields supplied to the recurrent policy at one action
position, before embedding and projection. -/
structure RecurrentPolicyMetadata where
  previousAction : ℕ
  role : ℕ
  parent : ℕ
  argument : ℕ
  depth : ℕ
  openHoles : ℕ
  position : ℕ
  deriving DecidableEq, Repr

/-- Exact embedding order and clamps of the recurrent state-input path.  The
position is deliberately not clamped: the source checks it against the action
budget before looking it up. -/
def recurrentEmbeddingFields {Embedding : Type*}
    (maxDepth maxActions : ℕ)
    (previousActionEmbedding roleEmbedding parentEmbedding
      argumentEmbedding depthEmbedding openHolesEmbedding positionEmbedding :
        ℕ → Embedding)
    (metadata : RecurrentPolicyMetadata) : List Embedding :=
  [ previousActionEmbedding metadata.previousAction
  , roleEmbedding metadata.role
  , parentEmbedding metadata.parent
  , argumentEmbedding (min metadata.argument 4)
  , depthEmbedding (min metadata.depth maxDepth)
  , openHolesEmbedding (min metadata.openHoles maxActions)
  , positionEmbedding metadata.position ]

@[simp] theorem recurrentEmbeddingFields_length {Embedding : Type*}
    (maxDepth maxActions : ℕ)
    (previousActionEmbedding roleEmbedding parentEmbedding
      argumentEmbedding depthEmbedding openHolesEmbedding positionEmbedding :
        ℕ → Embedding)
    (metadata : RecurrentPolicyMetadata) :
    (recurrentEmbeddingFields maxDepth maxActions previousActionEmbedding
      roleEmbedding parentEmbedding argumentEmbedding depthEmbedding
      openHolesEmbedding positionEmbedding metadata).length = 7 := rfl

/-- Projection of the ordered seven-field embedding row. -/
def recurrentStateInput {Embedding Input : Type*}
    (project : List Embedding → Input)
    (maxDepth maxActions : ℕ)
    (previousActionEmbedding roleEmbedding parentEmbedding
      argumentEmbedding depthEmbedding openHolesEmbedding positionEmbedding :
        ℕ → Embedding)
    (metadata : RecurrentPolicyMetadata) : Input :=
  project <| recurrentEmbeddingFields maxDepth maxActions
    previousActionEmbedding roleEmbedding parentEmbedding argumentEmbedding
    depthEmbedding openHolesEmbedding positionEmbedding metadata

/-- The separate source guard for an unclamped position index. -/
def recurrentPositionAdmissible (maxActions : ℕ)
    (metadata : RecurrentPolicyMetadata) : Prop :=
  metadata.position < maxActions

/-! ## Generic recurrent policy port -/

/-- One recurrent policy port with an explicit source-summary path, initial
hidden map, recurrent transition, and downstream policy readout. -/
structure RecurrentPolicyPort
    (Environment : Type uEnvironment) (Command : Type uCommand)
    (Summary : Type uSummary) (Input : Type uInput)
    (Hidden : Type uHidden) (Policy : Type uPolicy) where
  summarize : Environment → Summary
  stateInput : Command → Input
  combineSummary : Input → Summary → Input
  initialProjection : Summary → Hidden
  initialActivation : Hidden → Hidden
  transition : Input → Hidden → Hidden
  policyReadout : Environment → Hidden → Policy

namespace RecurrentPolicyPort

variable {Environment : Type uEnvironment} {Command : Type uCommand}
  {Summary : Type uSummary} {Input : Type uInput}
  {Hidden : Type uHidden} {Policy : Type uPolicy}

/-- Initial hidden state produced from the source summary. -/
def initialState
    (port : RecurrentPolicyPort Environment Command Summary Input Hidden Policy)
    (environment : Environment) : Hidden :=
  port.initialActivation (port.initialProjection (port.summarize environment))

/-- Input supplied to the recurrent cell after source-summary injection. -/
def cellInput
    (port : RecurrentPolicyPort Environment Command Summary Input Hidden Policy)
    (environment : Environment) (command : Command) : Input :=
  port.combineSummary (port.stateInput command) (port.summarize environment)

/-- One incremental recurrent transition. -/
def step
    (port : RecurrentPolicyPort Environment Command Summary Input Hidden Policy)
    (environment : Environment) (command : Command) (hidden : Hidden) : Hidden :=
  port.transition (port.cellInput environment command) hidden

/-- Embed the recurrent policy port into the common structured carrier.  Read
is the whole hidden state, routing is trivial, and the proposal replaces the
old state. -/
def toCarrier
    (port : RecurrentPolicyPort Environment Command Summary Input Hidden Policy) :
    StateCarrier Environment Unit Command Hidden Hidden Unit Hidden Hidden Policy :=
  replacementCarrier
    (fun environment _slow ↦ port.initialState environment)
    (fun environment _slow command hidden ↦ port.step environment command hidden)
    (fun _environment _slow hidden ↦ hidden)
    (fun environment _slow hidden ↦ port.policyReadout environment hidden)

@[simp] theorem toCarrier_initialState_eq
    (port : RecurrentPolicyPort Environment Command Summary Input Hidden Policy)
    (environment : Environment) :
    port.toCarrier.initialState environment () = port.initialState environment := rfl

@[simp] theorem toCarrier_step_eq
    (port : RecurrentPolicyPort Environment Command Summary Input Hidden Policy)
    (environment : Environment) (command : Command) (hidden : Hidden) :
    port.toCarrier.step environment () command hidden =
      port.step environment command hidden := rfl

@[simp] theorem toCarrier_policyAtState_eq
    (port : RecurrentPolicyPort Environment Command Summary Input Hidden Policy)
    (environment : Environment) (hidden : Hidden) :
    port.toCarrier.policyAtState environment () hidden =
      port.policyReadout environment hidden := rfl

/-- Hidden states emitted after every recurrent transition.  Unlike a carrier
trajectory, this sequence does not include the initial hidden state. -/
def hiddenSequenceFrom
    (port : RecurrentPolicyPort Environment Command Summary Input Hidden Policy)
    (environment : Environment) : Hidden → List Command → List Hidden
  | _hidden, [] => []
  | hidden, command :: commands =>
      let next := port.step environment command hidden
      next :: port.hiddenSequenceFrom environment next commands

/-- Teacher-forced decision states from the port's declared initializer. -/
def teacherForced
    (port : RecurrentPolicyPort Environment Command Summary Input Hidden Policy)
    (environment : Environment) (commands : List Command) : List Hidden :=
  port.hiddenSequenceFrom environment (port.initialState environment) commands

/-- Final recurrent state after an explicit prefix. -/
def finalStateFrom
    (port : RecurrentPolicyPort Environment Command Summary Input Hidden Policy)
    (environment : Environment) (hidden : Hidden)
    (commands : List Command) : Hidden :=
  port.toCarrier.run environment () hidden commands

/-- Final recurrent state after an explicit prefix from the declared initial
state. -/
def finalState
    (port : RecurrentPolicyPort Environment Command Summary Input Hidden Policy)
    (environment : Environment) (commands : List Command) : Hidden :=
  port.toCarrier.runFromInitial environment () commands

/-- Teacher-forced states are exactly the tail of the common carrier
trajectory. -/
theorem hiddenSequenceFrom_eq_trajectory_tail
    (port : RecurrentPolicyPort Environment Command Summary Input Hidden Policy)
    (environment : Environment) (hidden : Hidden) (commands : List Command) :
    port.hiddenSequenceFrom environment hidden commands =
      (port.toCarrier.trajectory environment () hidden commands).tail := by
  induction commands generalizing hidden with
  | nil => rfl
  | cons command commands inductionHypothesis =>
      simp only [hiddenSequenceFrom, StateCarrier.trajectory_cons,
        List.tail_cons]
      change port.step environment command hidden ::
          port.hiddenSequenceFrom environment
            (port.step environment command hidden) commands =
        port.toCarrier.trajectory environment ()
          (port.step environment command hidden) commands
      rw [inductionHypothesis]
      cases commands <;> rfl

/-- Splitting a command word preserves the exact emitted hidden sequence,
with the second part starting at the first part's final recurrent state. -/
theorem hiddenSequenceFrom_append
    (port : RecurrentPolicyPort Environment Command Summary Input Hidden Policy)
    (environment : Environment) (hidden : Hidden)
    (first second : List Command) :
    port.hiddenSequenceFrom environment hidden (first ++ second) =
      port.hiddenSequenceFrom environment hidden first ++
        port.hiddenSequenceFrom environment
          (port.finalStateFrom environment hidden first) second := by
  induction first generalizing hidden with
  | nil => rfl
  | cons command commands inductionHypothesis =>
      simp only [List.cons_append, hiddenSequenceFrom]
      rw [inductionHypothesis]
      rfl

/-- Teacher forcing followed by one more command is exactly incremental
execution from the prefix's final state. -/
theorem teacherForced_append_one
    (port : RecurrentPolicyPort Environment Command Summary Input Hidden Policy)
    (environment : Environment) (prior : List Command) (command : Command) :
    port.teacherForced environment (prior ++ [command]) =
      port.teacherForced environment prior ++
        [port.step environment command (port.finalState environment prior)] := by
  simpa [teacherForced, finalState, finalStateFrom,
    StateCarrier.runFromInitial, hiddenSequenceFrom] using
    port.hiddenSequenceFrom_append environment (port.initialState environment)
      prior [command]

/-- The final state obeys the same prefix/suffix decomposition as the common
carrier run. -/
theorem finalState_append
    (port : RecurrentPolicyPort Environment Command Summary Input Hidden Policy)
    (environment : Environment) (first second : List Command) :
    port.finalState environment (first ++ second) =
      port.finalStateFrom environment (port.finalState environment first) second := by
  exact port.toCarrier.run_append environment ()
    (port.initialState environment) first second

/-! ## Composition with the common legal-action readout -/

/-- After an arbitrary recurrent step, the common source-policy readout still
has support exactly equal to the external legal mask. -/
theorem sourcePolicyAfterStep_isSome
    {MemoryKey Operator MemoryValue Readout Embedding : Type*}
    [Fintype MemoryKey]
    [AddCommMonoid MemoryValue] [Module ℝ MemoryValue]
    (port : RecurrentPolicyPort Environment Command Summary Input Hidden Policy)
    (environment : Environment) (command : Command) (hidden : Hidden)
    (memoryActive : MemoryKey → Bool)
    (memoryScore : Hidden → MemoryKey → ℝ)
    (memoryValue : MemoryKey → MemoryValue)
    (readout : Hidden → MemoryValue → Readout)
    (pairing : Readout → Embedding → ℝ)
    (operatorEmbedding : Operator → Embedding)
    (bias : Operator → ℝ) (legal : Operator → Bool)
    (operator : Operator) :
    (sourcePolicyReadout memoryActive memoryScore memoryValue readout pairing
      operatorEmbedding bias legal (port.step environment command hidden)
      operator).isSome = legal operator := by
  exact sourcePolicyReadout_isSome memoryActive memoryScore memoryValue readout
    pairing operatorEmbedding bias legal (port.step environment command hidden)
    operator

end RecurrentPolicyPort

/-! ## Positive and negative executable fixtures -/

namespace RecurrentPolicyFixtures

/-- Metadata values chosen to exercise all three source clamps. -/
def clampedMetadata : RecurrentPolicyMetadata where
  previousAction := 1
  role := 2
  parent := 3
  argument := 9
  depth := 10
  openHoles := 11
  position := 4

theorem clamped_metadata_fields_exact :
    recurrentEmbeddingFields 8 6 id id id id id id id clampedMetadata =
      [1, 2, 3, 4, 8, 6, 4] := rfl

theorem position_boundary_is_rejected :
    ¬ recurrentPositionAdmissible 4 clampedMetadata := by
  norm_num [recurrentPositionAdmissible, clampedMetadata]

/-- Reordering the previous-action and role fields changes an
order-sensitive projection input. -/
theorem recurrent_field_order_is_observable :
    recurrentEmbeddingFields 8 6 id id id id id id id clampedMetadata ≠
      [2, 1, 3, 4, 8, 6, 4] := by
  decide

/-- A small genuinely moving recurrent port. -/
def scalarPort : RecurrentPolicyPort ℕ ℕ ℕ ℕ ℕ ℕ where
  summarize := id
  stateInput := id
  combineSummary := (· + ·)
  initialProjection := id
  initialActivation := id
  transition := fun input hidden ↦ hidden + input + 1
  policyReadout := fun environment hidden ↦ hidden + environment

theorem scalar_teacher_forced_exact :
    scalarPort.teacherForced 0 [1, 2] = [2, 5] := rfl

theorem scalar_incremental_matches_teacher_forced :
    scalarPort.teacherForced 0 ([1] ++ [2]) =
      scalarPort.teacherForced 0 [1] ++
        [scalarPort.step 0 2 (scalarPort.finalState 0 [1])] :=
  scalarPort.teacherForced_append_one 0 [1] 2

/-- Incorrect comparison path that resets the recurrent state before every
command. -/
def resetBeforeEveryCommand
    (port : RecurrentPolicyPort Environment Command Summary Input Hidden Policy)
    (environment : Environment) (commands : List Command) : List Hidden :=
  commands.map fun command ↦
    port.step environment command (port.initialState environment)

theorem resetting_between_commands_is_wrong :
    resetBeforeEveryCommand scalarPort 0 [1, 2] ≠
      scalarPort.teacherForced 0 [1, 2] := by
  decide

end RecurrentPolicyFixtures

#print axioms recurrentEmbeddingFields_length
#print axioms RecurrentPolicyPort.toCarrier_step_eq
#print axioms RecurrentPolicyPort.hiddenSequenceFrom_eq_trajectory_tail
#print axioms RecurrentPolicyPort.hiddenSequenceFrom_append
#print axioms RecurrentPolicyPort.teacherForced_append_one
#print axioms RecurrentPolicyPort.finalState_append
#print axioms RecurrentPolicyPort.sourcePolicyAfterStep_isSome
#print axioms RecurrentPolicyFixtures.clamped_metadata_fields_exact
#print axioms RecurrentPolicyFixtures.position_boundary_is_rejected
#print axioms RecurrentPolicyFixtures.recurrent_field_order_is_observable
#print axioms RecurrentPolicyFixtures.scalar_teacher_forced_exact
#print axioms RecurrentPolicyFixtures.scalar_incremental_matches_teacher_forced
#print axioms RecurrentPolicyFixtures.resetting_between_commands_is_wrong

end Mettapedia.MachineLearning.NeuralNetworks.Architecture
