import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Instances.BroadcastProxy

/-!
# Inverse targets, forward derivatives, and function evaluations

The three families in this module have different oracle access.  Target
propagation transports desired states through an inverse model.  Forward
gradients consume an exact directional derivative.  Zeroth-order updates
consume perturbed function values.  Algebraic coincidences on special
objectives do not identify these oracle classes.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace Instances

/-! ## Target propagation -/

namespace FeedbackMap2

def add (left right : FeedbackMap2) : FeedbackMap2 where
  row00 := left.row00 + right.row00
  row01 := left.row01 + right.row01
  row10 := left.row10 + right.row10
  row11 := left.row11 + right.row11

@[simp] theorem add_apply (left right : FeedbackMap2) (vector : CreditVec2) :
    (left.add right).apply vector =
      (left.apply vector).add (right.apply vector) := by
  ext <;> simp [add, apply, CreditVec2.add] <;> ring

def negIdentity : FeedbackMap2 where
  row00 := -1
  row01 := 0
  row10 := 0
  row11 := -1

@[simp] theorem negIdentity_apply (vector : CreditVec2) :
    negIdentity.apply vector = vector.scale (-1) := by
  ext <;> simp [negIdentity, apply, CreditVec2.scale]

end FeedbackMap2

structure TargetPropagationProblem where
  outputTarget : CreditVec2
  forward : FeedbackMap2
  inverse : FeedbackMap2

abbrev TargetPropagationParameter := CreditVec2

inductive TargetPropagationPhase where
  | ready
  | outputObserved
  | targetPropagated
  | creditRead
  deriving DecidableEq

inductive TargetPropagationEvent where
  | observeOutput
  | propagateTarget
  | readCredit
  deriving DecidableEq

structure TargetPropagationState where
  phase : TargetPropagationPhase
  output : CreditVec2
  hiddenTarget : CreditVec2
  update : CreditVec2

noncomputable def targetPropagationObjective
    (problem : TargetPropagationProblem)
    (parameter : TargetPropagationParameter) : ℝ :=
  ((problem.forward.apply parameter).sub problem.outputTarget).normSq / 2

def propagatedHiddenTarget
    (problem : TargetPropagationProblem) : CreditVec2 :=
  problem.inverse.apply problem.outputTarget

def targetPropagationUpdate
    (problem : TargetPropagationProblem)
    (parameter : TargetPropagationParameter) : CreditVec2 :=
  parameter.sub (propagatedHiddenTarget problem)

def initialTargetPropagationState : TargetPropagationState where
  phase := .ready
  output := CreditVec2.zero
  hiddenTarget := CreditVec2.zero
  update := CreditVec2.zero

def targetPropagationEnabled
    (_problem : TargetPropagationProblem)
    (_parameter : TargetPropagationParameter)
    (state : TargetPropagationState) (event : TargetPropagationEvent) : Prop :=
  match state.phase, event with
  | .ready, .observeOutput => True
  | .outputObserved, .propagateTarget => True
  | .targetPropagated, .readCredit => True
  | _, _ => False

def targetPropagationTransition
    (problem : TargetPropagationProblem)
    (parameter : TargetPropagationParameter)
    (event : TargetPropagationEvent)
    (state : TargetPropagationState) : TargetPropagationState :=
  match event with
  | .observeOutput =>
      { state with
        phase := .outputObserved
        output := problem.forward.apply parameter }
  | .propagateTarget =>
      let hiddenTarget := propagatedHiddenTarget problem
      { state with
        phase := .targetPropagated
        hiddenTarget := hiddenTarget
        update := parameter.sub hiddenTarget }
  | .readCredit =>
      { state with phase := .creditRead }

def targetPropagationEventCost
    (_problem : TargetPropagationProblem)
    (_parameter : TargetPropagationParameter)
    (_state : TargetPropagationState) (event : TargetPropagationEvent) :
    ResourceVector :=
  match event with
  | .observeOutput =>
      { scalarWork := 6, criticalPathSpan := 3, persistentMemory := 4 }
  | .propagateTarget =>
      { scalarWork := 8, criticalPathSpan := 4, persistentMemory := 4,
        localDerivativeCalls := 1 }
  | .readCredit =>
      { scalarWork := 2, criticalPathSpan := 1, persistentMemory := 4 }

def learnedInverseOracle : OracleAudit where
  accesses := [.learnedInverseTarget]
  teacherDependent := true

noncomputable def scalarTargetPropagation : CreditTransportSystem
    TargetPropagationProblem TargetPropagationParameter TargetPropagationState
    TargetPropagationEvent CreditVec2 CreditVec2 where
  objective := targetPropagationObjective
  initialState := fun _ _ => initialTargetPropagationState
  enabled := targetPropagationEnabled
  transition := targetPropagationTransition
  signal := fun _ _ state => state.update
  readUpdate := fun _ _ state => state.update
  eventCost := targetPropagationEventCost
  oracleAudit := learnedInverseOracle
  localityAudit := moduleLocality TargetPropagationEvent

def scalarTargetPropagationSchedule : List TargetPropagationEvent :=
  [.observeOutput, .propagateTarget, .readCredit]

theorem scalarTargetPropagationSchedule_enabled
    (problem : TargetPropagationProblem)
    (parameter : TargetPropagationParameter) :
    scalarTargetPropagation.ScheduleEnabled problem parameter
      scalarTargetPropagationSchedule := by
  simp [CreditTransportSystem.ScheduleEnabled,
    CreditTransportSystem.ScheduleEnabledFrom, scalarTargetPropagationSchedule,
    scalarTargetPropagation, initialTargetPropagationState,
    targetPropagationEnabled, targetPropagationTransition,
    propagatedHiddenTarget]

theorem scalarTargetPropagation_finalUpdate
    (problem : TargetPropagationProblem)
    (parameter : TargetPropagationParameter) :
    scalarTargetPropagation.finalUpdate problem parameter
      scalarTargetPropagationSchedule = targetPropagationUpdate problem parameter := by
  rfl

theorem scalarTargetPropagation_teacher_dependency :
    scalarTargetPropagation.oracleAudit.teacherDependent = true := by
  rfl

/-- An exact right inverse realizes every requested output target. -/
theorem exact_inverse_realizes_output_target
    (forward inverse : FeedbackMap2)
    (rightInverse : ∀ output, forward.apply (inverse.apply output) = output)
    (outputTarget : CreditVec2) :
    forward.apply (inverse.apply outputTarget) = outputTarget :=
  rightInverse outputTarget

/-- Adding an inverse-model error produces exactly the forward image of that
error after subtracting the requested displacement. -/
theorem approximate_inverse_error_decomposition
    (forward inverse inverseError : FeedbackMap2)
    (displacement : CreditVec2)
    (rightInverseAt : forward.apply (inverse.apply displacement) = displacement) :
    (forward.apply ((inverse.add inverseError).apply displacement)).sub displacement =
      forward.apply (inverseError.apply displacement) := by
  rw [FeedbackMap2.add_apply]
  have firstCoordinate := congrArg CreditVec2.first rightInverseAt
  have secondCoordinate := congrArg CreditVec2.second rightInverseAt
  ext <;>
    simp [FeedbackMap2.apply, CreditVec2.add, CreditVec2.sub] at firstCoordinate secondCoordinate ⊢ <;>
    linarith

/-- A rank-deficient forward block cannot realize a requested target outside
its image. -/
theorem noninjective_projection_target_unreachable :
    ¬ ∃ hidden,
      FeedbackMap2.firstCoordinateProjection.apply hidden =
        (⟨0, 1⟩ : CreditVec2) := by
  rintro ⟨hidden, equality⟩
  have secondCoordinate := congrArg CreditVec2.second equality
  norm_num [FeedbackMap2.firstCoordinateProjection, FeedbackMap2.apply] at secondCoordinate

/-- A sign-reversing inverse can turn a zero-loss current state into a
positive-loss target update. -/
theorem sign_reversing_inverse_can_worsen_output_target :
    let problem : TargetPropagationProblem :=
      { outputTarget := ⟨1, 0⟩
        forward := FeedbackMap2.identity
        inverse := FeedbackMap2.negIdentity }
    targetPropagationObjective problem (⟨1, 0⟩ : CreditVec2) = 0 ∧
      targetPropagationObjective problem (propagatedHiddenTarget problem) = 2 := by
  norm_num [targetPropagationObjective, propagatedHiddenTarget,
    FeedbackMap2.identity, FeedbackMap2.negIdentity, FeedbackMap2.apply,
    CreditVec2.sub, CreditVec2.normSq, CreditVec2.dot]

/-! ## Forward-gradient estimators -/

structure ForwardGradientProblem where
  target : CreditVec2
  direction : CreditVec2

abbrev ForwardGradientParameter := CreditVec2

inductive ForwardGradientPhase where
  | ready
  | derivativeEvaluated
  | estimateAssembled
  | creditRead
  deriving DecidableEq

inductive ForwardGradientEvent where
  | evaluateDirectionalDerivative
  | assembleEstimate
  | readCredit
  deriving DecidableEq

structure ForwardGradientState where
  phase : ForwardGradientPhase
  directionalDerivative : ℝ
  update : CreditVec2

noncomputable def forwardGradientObjective
    (problem : ForwardGradientProblem)
    (parameter : ForwardGradientParameter) : ℝ :=
  (parameter.sub problem.target).normSq / 2

def forwardGradientTrueGradient
    (problem : ForwardGradientProblem)
    (parameter : ForwardGradientParameter) : CreditVec2 :=
  parameter.sub problem.target

def forwardGradientEstimate
    (trueGradient direction : CreditVec2) : CreditVec2 :=
  direction.scale (trueGradient.dot direction)

def initialForwardGradientState : ForwardGradientState where
  phase := .ready
  directionalDerivative := 0
  update := CreditVec2.zero

def forwardGradientEnabled
    (_problem : ForwardGradientProblem)
    (_parameter : ForwardGradientParameter)
    (state : ForwardGradientState) (event : ForwardGradientEvent) : Prop :=
  match state.phase, event with
  | .ready, .evaluateDirectionalDerivative => True
  | .derivativeEvaluated, .assembleEstimate => True
  | .estimateAssembled, .readCredit => True
  | _, _ => False

def forwardGradientTransition
    (problem : ForwardGradientProblem)
    (parameter : ForwardGradientParameter)
    (event : ForwardGradientEvent)
    (state : ForwardGradientState) : ForwardGradientState :=
  match event with
  | .evaluateDirectionalDerivative =>
      { state with
        phase := .derivativeEvaluated
        directionalDerivative :=
          (forwardGradientTrueGradient problem parameter).dot problem.direction }
  | .assembleEstimate =>
      { state with
        phase := .estimateAssembled
        update := problem.direction.scale state.directionalDerivative }
  | .readCredit =>
      { state with phase := .creditRead }

def forwardGradientEventCost
    (_problem : ForwardGradientProblem)
    (_parameter : ForwardGradientParameter)
    (_state : ForwardGradientState) (event : ForwardGradientEvent) :
    ResourceVector :=
  match event with
  | .evaluateDirectionalDerivative =>
      { scalarWork := 4, criticalPathSpan := 2, localDerivativeCalls := 1 }
  | .assembleEstimate =>
      { scalarWork := 2, criticalPathSpan := 1 }
  | .readCredit =>
      { scalarWork := 2, criticalPathSpan := 1 }

def forwardDerivativeOracle : OracleAudit where
  accesses := [.forwardPerturbation]

def globalForwardLocality (Event : Type*) : LocalityAudit Event where
  scope := .globalForward
  dependsOn := fun _ _ => True

noncomputable def scalarForwardGradient : CreditTransportSystem
    ForwardGradientProblem ForwardGradientParameter ForwardGradientState
    ForwardGradientEvent CreditVec2 CreditVec2 where
  objective := forwardGradientObjective
  initialState := fun _ _ => initialForwardGradientState
  enabled := forwardGradientEnabled
  transition := forwardGradientTransition
  signal := fun _ _ state => state.update
  readUpdate := fun _ _ state => state.update
  eventCost := forwardGradientEventCost
  oracleAudit := forwardDerivativeOracle
  localityAudit := globalForwardLocality ForwardGradientEvent

def scalarForwardGradientSchedule : List ForwardGradientEvent :=
  [.evaluateDirectionalDerivative, .assembleEstimate, .readCredit]

theorem scalarForwardGradientSchedule_enabled
    (problem : ForwardGradientProblem)
    (parameter : ForwardGradientParameter) :
    scalarForwardGradient.ScheduleEnabled problem parameter
      scalarForwardGradientSchedule := by
  simp [CreditTransportSystem.ScheduleEnabled,
    CreditTransportSystem.ScheduleEnabledFrom, scalarForwardGradientSchedule,
    scalarForwardGradient, initialForwardGradientState,
    forwardGradientEnabled, forwardGradientTransition]

theorem scalarForwardGradient_finalUpdate
    (problem : ForwardGradientProblem)
    (parameter : ForwardGradientParameter) :
    scalarForwardGradient.finalUpdate problem parameter
        scalarForwardGradientSchedule =
      forwardGradientEstimate (forwardGradientTrueGradient problem parameter)
        problem.direction := by
  rfl

/-- Every exact forward-gradient sample is nonnegatively aligned with the true
gradient; finite-step failure can therefore come from zero information or an
oversized step rather than a negative first-order margin. -/
theorem forwardGradient_sample_alignment
    (trueGradient direction : CreditVec2) :
    trueGradient.dot (forwardGradientEstimate trueGradient direction) =
      (trueGradient.dot direction) ^ 2 := by
  simp [forwardGradientEstimate, CreditVec2.dot, CreditVec2.scale]
  ring

noncomputable def fourRademacherAverage (gradient : CreditVec2) : CreditVec2 :=
  (CreditVec2.add
    (CreditVec2.add
      (forwardGradientEstimate gradient ⟨1, 1⟩)
      (forwardGradientEstimate gradient ⟨1, -1⟩))
    (CreditVec2.add
      (forwardGradientEstimate gradient ⟨-1, 1⟩)
      (forwardGradientEstimate gradient ⟨-1, -1⟩))).scale (1 / 4)

/-- The full two-dimensional Rademacher ensemble averages exactly to the true
gradient. -/
theorem fourRademacherAverage_eq (gradient : CreditVec2) :
    fourRademacherAverage gradient = gradient := by
  ext <;>
    simp [fourRademacherAverage, forwardGradientEstimate, CreditVec2.add,
      CreditVec2.scale, CreditVec2.dot] <;>
    ring

/-- A covariance-deficient direction distribution estimates only a projection
and can erase a genuine coordinate. -/
theorem axis_one_direction_erases_second_coordinate :
    forwardGradientEstimate (⟨0, 1⟩ : CreditVec2) ⟨1, 0⟩ =
      CreditVec2.zero := by
  ext <;> norm_num [forwardGradientEstimate, CreditVec2.scale,
    CreditVec2.dot, CreditVec2.zero]

/-- Even an exact rank-one sample can increase a quadratic task when the step
is too large. -/
theorem forwardGradient_oversized_step_increases_quadratic :
    let problem : ForwardGradientProblem :=
      { target := ⟨0, 0⟩, direction := ⟨1, 0⟩ }
    let parameter : CreditVec2 := ⟨1, 0⟩
    let update := forwardGradientEstimate
      (forwardGradientTrueGradient problem parameter) problem.direction
    forwardGradientObjective problem (parameter.sub (update.scale 3)) >
      forwardGradientObjective problem parameter := by
  norm_num [forwardGradientObjective, forwardGradientTrueGradient,
    forwardGradientEstimate, CreditVec2.sub, CreditVec2.scale,
    CreditVec2.normSq, CreditVec2.dot]

/-! ## Zeroth-order two-point estimators -/

structure ZerothOrderProblem where
  loss : ℝ → ℝ
  epsilon : ℝ
  direction : ℝ

abbrev ZerothOrderParameter := ℝ

inductive ZerothOrderPhase where
  | ready
  | plusEvaluated
  | minusEvaluated
  | estimateAssembled
  | creditRead
  deriving DecidableEq

inductive ZerothOrderEvent where
  | evaluatePlus
  | evaluateMinus
  | assembleEstimate
  | readCredit
  deriving DecidableEq

structure ZerothOrderState where
  phase : ZerothOrderPhase
  plusValue : ℝ
  minusValue : ℝ
  update : ℝ

noncomputable def zerothOrderEstimate
    (problem : ZerothOrderProblem) (parameter : ZerothOrderParameter) : ℝ :=
  ((problem.loss (parameter + problem.epsilon * problem.direction) -
      problem.loss (parameter - problem.epsilon * problem.direction)) /
      (2 * problem.epsilon)) * problem.direction

def initialZerothOrderState : ZerothOrderState where
  phase := .ready
  plusValue := 0
  minusValue := 0
  update := 0

def zerothOrderEnabled
    (_problem : ZerothOrderProblem) (_parameter : ZerothOrderParameter)
    (state : ZerothOrderState) (event : ZerothOrderEvent) : Prop :=
  match state.phase, event with
  | .ready, .evaluatePlus => True
  | .plusEvaluated, .evaluateMinus => True
  | .minusEvaluated, .assembleEstimate => True
  | .estimateAssembled, .readCredit => True
  | _, _ => False

noncomputable def zerothOrderTransition
    (problem : ZerothOrderProblem) (parameter : ZerothOrderParameter)
    (event : ZerothOrderEvent) (state : ZerothOrderState) : ZerothOrderState :=
  match event with
  | .evaluatePlus =>
      { state with
        phase := .plusEvaluated
        plusValue :=
          problem.loss (parameter + problem.epsilon * problem.direction) }
  | .evaluateMinus =>
      { state with
        phase := .minusEvaluated
        minusValue :=
          problem.loss (parameter - problem.epsilon * problem.direction) }
  | .assembleEstimate =>
      { state with
        phase := .estimateAssembled
        update := ((state.plusValue - state.minusValue) /
          (2 * problem.epsilon)) * problem.direction }
  | .readCredit =>
      { state with phase := .creditRead }

def zerothOrderEventCost
    (_problem : ZerothOrderProblem) (_parameter : ZerothOrderParameter)
    (_state : ZerothOrderState) (event : ZerothOrderEvent) : ResourceVector :=
  match event with
  | .evaluatePlus | .evaluateMinus =>
      { scalarWork := 1, criticalPathSpan := 1, functionEvaluations := 1 }
  | .assembleEstimate =>
      { scalarWork := 4, criticalPathSpan := 3 }
  | .readCredit =>
      { scalarWork := 1, criticalPathSpan := 1 }

def functionEvaluationOracle : OracleAudit where
  accesses := [.functionEvaluation, .functionEvaluation]

def functionEvaluationLocality (Event : Type*) : LocalityAudit Event where
  scope := .functionEvaluationGlobal
  dependsOn := fun _ _ => True

noncomputable def scalarZerothOrder : CreditTransportSystem
    ZerothOrderProblem ZerothOrderParameter ZerothOrderState ZerothOrderEvent
    ℝ ℝ where
  objective := fun problem parameter => problem.loss parameter
  initialState := fun _ _ => initialZerothOrderState
  enabled := zerothOrderEnabled
  transition := zerothOrderTransition
  signal := fun _ _ state => state.update
  readUpdate := fun _ _ state => state.update
  eventCost := zerothOrderEventCost
  oracleAudit := functionEvaluationOracle
  localityAudit := functionEvaluationLocality ZerothOrderEvent

def scalarZerothOrderSchedule : List ZerothOrderEvent :=
  [.evaluatePlus, .evaluateMinus, .assembleEstimate, .readCredit]

theorem scalarZerothOrderSchedule_enabled
    (problem : ZerothOrderProblem) (parameter : ZerothOrderParameter) :
    scalarZerothOrder.ScheduleEnabled problem parameter
      scalarZerothOrderSchedule := by
  simp [CreditTransportSystem.ScheduleEnabled,
    CreditTransportSystem.ScheduleEnabledFrom, scalarZerothOrderSchedule,
    scalarZerothOrder, initialZerothOrderState, zerothOrderEnabled,
    zerothOrderTransition]

theorem scalarZerothOrder_finalUpdate
    (problem : ZerothOrderProblem) (parameter : ZerothOrderParameter) :
    scalarZerothOrder.finalUpdate problem parameter scalarZerothOrderSchedule =
      zerothOrderEstimate problem parameter := by
  rfl

theorem scalarZerothOrder_oracle_locality_consistent :
    OracleLocalityConsistent scalarZerothOrder.oracleAudit
      scalarZerothOrder.localityAudit := by
  simp [OracleLocalityConsistent, scalarZerothOrder,
    functionEvaluationOracle, OracleAudit.Declares]

/-- On a scalar quadratic, a two-point function-evaluation estimator equals
the corresponding exact directional-derivative sample. -/
theorem quadratic_zerothOrder_eq_forward_sample
    (parameter epsilon direction : ℝ) (epsilonNonzero : epsilon ≠ 0) :
    let loss := fun value : ℝ => value ^ 2 / 2
    (((loss (parameter + epsilon * direction) -
        loss (parameter - epsilon * direction)) / (2 * epsilon)) * direction) =
      (parameter * direction) * direction := by
  dsimp only
  field_simp
  ring

/-- At finite perturbation radius, the central estimator for a cubic differs
from the point derivative by an exact positive bias term. -/
theorem cubic_central_difference_bias
    (parameter epsilon : ℝ) (epsilonNonzero : epsilon ≠ 0) :
    let loss := fun value : ℝ => value ^ 3 / 3
    (loss (parameter + epsilon) - loss (parameter - epsilon)) /
        (2 * epsilon) =
      parameter ^ 2 + epsilon ^ 2 / 3 := by
  dsimp only
  field_simp
  ring

noncomputable def thresholdCheckerReward (parameter : ℝ) : ℝ :=
  if 1 ≤ parameter then 1 else 0

/-- A local two-point query can be completely flat although an accepted point
is reachable outside the perturbation radius. -/
theorem checker_plateau_zero_local_credit_but_acceptance_reachable :
    let problem : ZerothOrderProblem :=
      { loss := thresholdCheckerReward, epsilon := 1 / 4, direction := 1 }
    zerothOrderEstimate problem 0 = 0 ∧
      thresholdCheckerReward 1 = 1 := by
  norm_num [zerothOrderEstimate, thresholdCheckerReward]

#print axioms approximate_inverse_error_decomposition
#print axioms noninjective_projection_target_unreachable
#print axioms sign_reversing_inverse_can_worsen_output_target
#print axioms scalarTargetPropagation_finalUpdate
#print axioms forwardGradient_sample_alignment
#print axioms fourRademacherAverage_eq
#print axioms axis_one_direction_erases_second_coordinate
#print axioms forwardGradient_oversized_step_increases_quadratic
#print axioms scalarZerothOrder_finalUpdate
#print axioms quadratic_zerothOrder_eq_forward_sample
#print axioms cubic_central_difference_bias
#print axioms checker_plateau_zero_local_credit_but_acceptance_reachable

end Instances

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
