import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Core
import Mathlib.Tactic

/-!
# Broadcast and learned-proxy credit

This module places direct feedback alignment and synthetic gradients on the
common finite credit-transport interface.  Broadcast output error is classified
as broadcast-local.  A learned proxy is module-local when consumed, while its
teacher dependence remains explicit in the oracle audit.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace Instances

/-! ## Two-dimensional algebra shared by the fixtures -/

@[ext] structure CreditVec2 where
  first : ℝ
  second : ℝ

namespace CreditVec2

def zero : CreditVec2 := ⟨0, 0⟩

def add (left right : CreditVec2) : CreditVec2 :=
  ⟨left.first + right.first, left.second + right.second⟩

def sub (left right : CreditVec2) : CreditVec2 :=
  ⟨left.first - right.first, left.second - right.second⟩

def scale (scalar : ℝ) (vector : CreditVec2) : CreditVec2 :=
  ⟨scalar * vector.first, scalar * vector.second⟩

def hadamard (left right : CreditVec2) : CreditVec2 :=
  ⟨left.first * right.first, left.second * right.second⟩

def dot (left right : CreditVec2) : ℝ :=
  left.first * right.first + left.second * right.second

def normSq (vector : CreditVec2) : ℝ :=
  vector.dot vector

theorem normSq_nonneg (vector : CreditVec2) : 0 ≤ vector.normSq := by
  simp [normSq, dot]
  nlinarith [sq_nonneg vector.first, sq_nonneg vector.second]

theorem dot_sub_right (left right offset : CreditVec2) :
    left.dot (right.sub offset) = left.dot right - left.dot offset := by
  simp [dot, sub]
  ring

theorem dot_add_right (left first second : CreditVec2) :
    left.dot (first.add second) = left.dot first + left.dot second := by
  simp [dot, add]
  ring

theorem cauchy_squared (left right : CreditVec2) :
    (left.dot right) ^ 2 ≤ left.normSq * right.normSq := by
  have squareNonnegative :
      0 ≤ (left.first * right.second - left.second * right.first) ^ 2 :=
    sq_nonneg _
  simp [dot, normSq] at squareNonnegative ⊢
  nlinarith

/-- A proxy whose squared error is smaller than the squared true-gradient norm
has a strictly positive first-order task margin. -/
theorem positive_dot_of_proxy_error_normSq_lt
    (trueGradient proxy : CreditVec2)
    (errorBound : (proxy.sub trueGradient).normSq < trueGradient.normSq) :
    0 < trueGradient.dot proxy := by
  have trueNormNonnegative := trueGradient.normSq_nonneg
  have errorNormNonnegative := (proxy.sub trueGradient).normSq_nonneg
  have cauchy := trueGradient.cauchy_squared (proxy.sub trueGradient)
  have decomposition :
      trueGradient.dot proxy =
        trueGradient.normSq + trueGradient.dot (proxy.sub trueGradient) := by
    simp [dot, normSq, sub]
    ring
  by_contra notPositive
  have nonpositive : trueGradient.dot proxy ≤ 0 := le_of_not_gt notPositive
  nlinarith

end CreditVec2

/-! ## Direct feedback alignment -/

structure FeedbackMap2 where
  row00 : ℝ
  row01 : ℝ
  row10 : ℝ
  row11 : ℝ

namespace FeedbackMap2

def apply (feedback : FeedbackMap2) (error : CreditVec2) : CreditVec2 :=
  ⟨feedback.row00 * error.first + feedback.row01 * error.second,
    feedback.row10 * error.first + feedback.row11 * error.second⟩

def identity : FeedbackMap2 :=
  { row00 := 1, row01 := 0, row10 := 0, row11 := 1 }

def firstCoordinateProjection : FeedbackMap2 :=
  { row00 := 1, row01 := 0, row10 := 0, row11 := 0 }

@[simp] theorem identity_apply (error : CreditVec2) :
    identity.apply error = error := by
  ext <;> simp [identity, apply]

@[simp] theorem apply_zero (feedback : FeedbackMap2) :
    feedback.apply CreditVec2.zero = CreditVec2.zero := by
  ext <;> simp [apply, CreditVec2.zero]

theorem apply_sub (feedback : FeedbackMap2) (left right : CreditVec2) :
    feedback.apply (left.sub right) =
      (feedback.apply left).sub (feedback.apply right) := by
  ext <;> simp [apply, CreditVec2.sub] <;> ring

/-- A linear feedback map detects every nonzero output error exactly when its
kernel is trivial. -/
theorem injective_iff_kernel_trivial (feedback : FeedbackMap2) :
    Function.Injective feedback.apply ↔
      ∀ error, feedback.apply error = CreditVec2.zero →
        error = CreditVec2.zero := by
  constructor
  · intro injective error mappedZero
    exact injective (mappedZero.trans feedback.apply_zero.symm)
  · intro kernelTrivial left right imagesEqual
    have differenceMappedZero :
        feedback.apply (left.sub right) = CreditVec2.zero := by
      rw [feedback.apply_sub, imagesEqual]
      ext <;> simp [CreditVec2.sub, CreditVec2.zero]
    have differenceZero := kernelTrivial (left.sub right) differenceMappedZero
    have firstDifference :=
      congrArg (fun vector => vector.first) differenceZero
    have secondDifference :=
      congrArg (fun vector => vector.second) differenceZero
    ext
    · simpa [CreditVec2.sub, CreditVec2.zero] using sub_eq_zero.mp firstDifference
    · simpa [CreditVec2.sub, CreditVec2.zero] using sub_eq_zero.mp secondDifference

theorem identity_injective : Function.Injective identity.apply := by
  intro left right equality
  simpa using equality

/-- Rank loss can erase a real output error before it reaches a hidden site. -/
theorem projection_erases_nonzero_error :
    let error : CreditVec2 := ⟨0, 1⟩
    error ≠ CreditVec2.zero ∧
      firstCoordinateProjection.apply error = CreditVec2.zero := by
  norm_num [CreditVec2.zero, firstCoordinateProjection, apply]

end FeedbackMap2

structure DFAProblem where
  target : CreditVec2
  outputError : CreditVec2
  feedback : FeedbackMap2
  localDerivative : CreditVec2

abbrev DFAParameter := CreditVec2

inductive DFAPhase where
  | ready
  | errorBroadcast
  | locallyMultiplied
  | creditRead
  deriving DecidableEq

inductive DFAEvent where
  | broadcast
  | multiplyLocalDerivative
  | readCredit
  deriving DecidableEq

structure DFAState where
  phase : DFAPhase
  hiddenSignal : CreditVec2
  update : CreditVec2

noncomputable def dfaObjective
    (problem : DFAProblem) (parameter : DFAParameter) : ℝ :=
  (parameter.sub problem.target).normSq / 2

def dfaExactGradient
    (problem : DFAProblem) (parameter : DFAParameter) : CreditVec2 :=
  parameter.sub problem.target

def dfaUpdate (problem : DFAProblem) : CreditVec2 :=
  CreditVec2.hadamard (problem.feedback.apply problem.outputError)
    problem.localDerivative

def initialDFAState : DFAState where
  phase := .ready
  hiddenSignal := CreditVec2.zero
  update := CreditVec2.zero

def dfaEnabled
    (_problem : DFAProblem) (_parameter : DFAParameter)
    (state : DFAState) (event : DFAEvent) : Prop :=
  match state.phase, event with
  | .ready, .broadcast => True
  | .errorBroadcast, .multiplyLocalDerivative => True
  | .locallyMultiplied, .readCredit => True
  | _, _ => False

def dfaTransition
    (problem : DFAProblem) (_parameter : DFAParameter)
    (event : DFAEvent) (state : DFAState) : DFAState :=
  match event with
  | .broadcast =>
      { state with
        phase := .errorBroadcast
        hiddenSignal := problem.feedback.apply problem.outputError }
  | .multiplyLocalDerivative =>
      { state with
        phase := .locallyMultiplied
        update := CreditVec2.hadamard state.hiddenSignal
          problem.localDerivative }
  | .readCredit =>
      { state with phase := .creditRead }

def dfaEventCost
    (_problem : DFAProblem) (_parameter : DFAParameter)
    (_state : DFAState) (event : DFAEvent) : ResourceVector :=
  match event with
  | .broadcast =>
      { scalarWork := 6, criticalPathSpan := 3, bytesCommunicated := 16,
        synchronizationRounds := 1 }
  | .multiplyLocalDerivative =>
      { scalarWork := 2, criticalPathSpan := 1, localDerivativeCalls := 1 }
  | .readCredit =>
      { scalarWork := 2, criticalPathSpan := 1 }

def directBroadcastOracle : OracleAudit where
  accesses := [.broadcastOutputError]

def broadcastLocality (Event : Type*) : LocalityAudit Event where
  scope := .broadcastLocal
  dependsOn := fun _ _ => True

noncomputable def scalarDFA : CreditTransportSystem
    DFAProblem DFAParameter DFAState DFAEvent CreditVec2 CreditVec2 where
  objective := dfaObjective
  initialState := fun _ _ => initialDFAState
  enabled := dfaEnabled
  transition := dfaTransition
  signal := fun _ _ state => state.update
  readUpdate := fun _ _ state => state.update
  eventCost := dfaEventCost
  oracleAudit := directBroadcastOracle
  localityAudit := broadcastLocality DFAEvent

def scalarDFASchedule : List DFAEvent :=
  [.broadcast, .multiplyLocalDerivative, .readCredit]

theorem scalarDFASchedule_enabled
    (problem : DFAProblem) (parameter : DFAParameter) :
    scalarDFA.ScheduleEnabled problem parameter scalarDFASchedule := by
  simp [CreditTransportSystem.ScheduleEnabled,
    CreditTransportSystem.ScheduleEnabledFrom, scalarDFASchedule, scalarDFA,
    initialDFAState, dfaEnabled, dfaTransition]

theorem scalarDFA_finalUpdate
    (problem : DFAProblem) (parameter : DFAParameter) :
    scalarDFA.finalUpdate problem parameter scalarDFASchedule =
      dfaUpdate problem := by
  rfl

theorem scalarDFA_oracle_locality_consistent :
    OracleLocalityConsistent scalarDFA.oracleAudit scalarDFA.localityAudit := by
  simp [OracleLocalityConsistent, scalarDFA, directBroadcastOracle,
    OracleAudit.Declares]

/-- The exact first-order coefficient of the quadratic task along a declared
update is its inner product with the exact gradient. -/
theorem dfaObjective_step_expansion
    (problem : DFAProblem) (parameter update : CreditVec2) (step : ℝ) :
    dfaObjective problem (parameter.sub (update.scale step)) =
      dfaObjective problem parameter -
        step * (dfaExactGradient problem parameter).dot update +
        step ^ 2 * update.normSq / 2 := by
  simp [dfaObjective, dfaExactGradient, CreditVec2.sub, CreditVec2.scale,
    CreditVec2.normSq, CreditVec2.dot]
  ring

/-- Positive feedback alignment is exactly the first-order descent condition
for the pre-optimizer DFA direction. -/
theorem dfa_positive_alignment_gives_negative_linear_term
    (problem : DFAProblem) (parameter : DFAParameter)
    (aligned : 0 < (dfaExactGradient problem parameter).dot (dfaUpdate problem))
    (stepPositive : 0 < step) :
    -step * (dfaExactGradient problem parameter).dot (dfaUpdate problem) < 0 := by
  nlinarith

/-- A tied parameter still sums every local occurrence after broadcast credit
has arrived. -/
def tiedDFAUpdate
    (credit : CreditVec2) (sensitivities : List CreditVec2) : ℝ :=
  (sensitivities.map (credit.dot ·)).sum

theorem tiedDFAUpdate_two_occurrences
    (credit first second : CreditVec2) :
    tiedDFAUpdate credit [first, second] =
      credit.dot first + credit.dot second := by
  simp [tiedDFAUpdate]

theorem tiedDFA_single_occurrence_loses_credit :
    let credit : CreditVec2 := ⟨1, 1⟩
    let first : CreditVec2 := ⟨1, 0⟩
    let second : CreditVec2 := ⟨0, 1⟩
    tiedDFAUpdate credit [first] ≠ tiedDFAUpdate credit [first, second] := by
  norm_num [tiedDFAUpdate, CreditVec2.dot]

/-- Orthogonal update directions need not be behaviorally complementary: the
second direction lies in this readout's kernel. -/
theorem orthogonal_updates_need_not_be_behaviorally_complementary :
    let first : CreditVec2 := ⟨1, 0⟩
    let second : CreditVec2 := ⟨0, 1⟩
    first.dot second = 0 ∧
      first ≠ CreditVec2.zero ∧ second ≠ CreditVec2.zero ∧
      first.first = 1 ∧ second.first = 0 := by
  norm_num [CreditVec2.dot, CreditVec2.zero]

/-! ## Synthetic-gradient credit -/

structure SyntheticGradientProblem where
  target : CreditVec2
  proxy : CreditVec2

abbrev SyntheticGradientParameter := CreditVec2

inductive SyntheticGradientPhase where
  | ready
  | predicted
  | creditRead
  deriving DecidableEq

inductive SyntheticGradientEvent where
  | predict
  | readCredit
  deriving DecidableEq

structure SyntheticGradientState where
  phase : SyntheticGradientPhase
  update : CreditVec2

noncomputable def syntheticGradientObjective
    (problem : SyntheticGradientProblem)
    (parameter : SyntheticGradientParameter) : ℝ :=
  (parameter.sub problem.target).normSq / 2

def syntheticGradientTrueGradient
    (problem : SyntheticGradientProblem)
    (parameter : SyntheticGradientParameter) : CreditVec2 :=
  parameter.sub problem.target

def initialSyntheticGradientState : SyntheticGradientState where
  phase := .ready
  update := CreditVec2.zero

def syntheticGradientEnabled
    (_problem : SyntheticGradientProblem)
    (_parameter : SyntheticGradientParameter)
    (state : SyntheticGradientState) (event : SyntheticGradientEvent) : Prop :=
  match state.phase, event with
  | .ready, .predict => True
  | .predicted, .readCredit => True
  | _, _ => False

def syntheticGradientTransition
    (problem : SyntheticGradientProblem)
    (_parameter : SyntheticGradientParameter)
    (event : SyntheticGradientEvent)
    (state : SyntheticGradientState) : SyntheticGradientState :=
  match event with
  | .predict => { phase := .predicted, update := problem.proxy }
  | .readCredit => { state with phase := .creditRead }

def syntheticGradientEventCost
    (_problem : SyntheticGradientProblem)
    (_parameter : SyntheticGradientParameter)
    (_state : SyntheticGradientState) (event : SyntheticGradientEvent) :
    ResourceVector :=
  match event with
  | .predict =>
      { scalarWork := 4, criticalPathSpan := 2, persistentMemory := 2,
        peakTemporaryMemory := 2 }
  | .readCredit =>
      { scalarWork := 2, criticalPathSpan := 1, persistentMemory := 2 }

def learnedProxyOracle : OracleAudit where
  accesses := [.learnedCreditProxy]
  teacherDependent := true

def moduleLocality (Event : Type*) : LocalityAudit Event where
  scope := .moduleLocal
  dependsOn := fun _ _ => True

noncomputable def scalarSyntheticGradient : CreditTransportSystem
    SyntheticGradientProblem SyntheticGradientParameter SyntheticGradientState
    SyntheticGradientEvent CreditVec2 CreditVec2 where
  objective := syntheticGradientObjective
  initialState := fun _ _ => initialSyntheticGradientState
  enabled := syntheticGradientEnabled
  transition := syntheticGradientTransition
  signal := fun _ _ state => state.update
  readUpdate := fun _ _ state => state.update
  eventCost := syntheticGradientEventCost
  oracleAudit := learnedProxyOracle
  localityAudit := moduleLocality SyntheticGradientEvent

def scalarSyntheticGradientSchedule : List SyntheticGradientEvent :=
  [.predict, .readCredit]

theorem scalarSyntheticGradientSchedule_enabled
    (problem : SyntheticGradientProblem)
    (parameter : SyntheticGradientParameter) :
    scalarSyntheticGradient.ScheduleEnabled problem parameter
      scalarSyntheticGradientSchedule := by
  simp [CreditTransportSystem.ScheduleEnabled,
    CreditTransportSystem.ScheduleEnabledFrom, scalarSyntheticGradientSchedule,
    scalarSyntheticGradient, initialSyntheticGradientState,
    syntheticGradientEnabled, syntheticGradientTransition]

theorem scalarSyntheticGradient_finalUpdate
    (problem : SyntheticGradientProblem)
    (parameter : SyntheticGradientParameter) :
    scalarSyntheticGradient.finalUpdate problem parameter
      scalarSyntheticGradientSchedule = problem.proxy := by
  rfl

theorem scalarSyntheticGradient_teacher_dependency :
    scalarSyntheticGradient.oracleAudit.teacherDependent = true := by
  rfl

theorem scalarSyntheticGradient_oracle_locality_consistent :
    OracleLocalityConsistent scalarSyntheticGradient.oracleAudit
      scalarSyntheticGradient.localityAudit := by
  simp [OracleLocalityConsistent, scalarSyntheticGradient,
    learnedProxyOracle, OracleAudit.Declares]

theorem syntheticGradient_bounded_error_positive_margin
    (problem : SyntheticGradientProblem)
    (parameter : SyntheticGradientParameter)
    (errorBound :
      (problem.proxy.sub (syntheticGradientTrueGradient problem parameter)).normSq <
        (syntheticGradientTrueGradient problem parameter).normSq) :
    0 < (syntheticGradientTrueGradient problem parameter).dot problem.proxy :=
  CreditVec2.positive_dot_of_proxy_error_normSq_lt _ _ errorBound

/-- Any smoothness upper bound yields strict finite-step descent once its
quadratic remainder is smaller than the positive proxy margin. -/
theorem syntheticGradient_strict_descent_of_smooth_upper
    {current next step beta : ℝ} {trueGradient proxy : CreditVec2}
    (smoothUpper :
      next ≤ current - step * trueGradient.dot proxy +
        beta * step ^ 2 * proxy.normSq / 2)
    (remainderBelowMargin :
      beta * step ^ 2 * proxy.normSq / 2 <
        step * trueGradient.dot proxy) :
    next < current := by
  linarith

theorem syntheticGradient_bounded_error_positive :
    let trueGradient : CreditVec2 := ⟨1, 1⟩
    let proxy : CreditVec2 := ⟨1, 1 / 2⟩
    (proxy.sub trueGradient).normSq < trueGradient.normSq ∧
      0 < trueGradient.dot proxy := by
  norm_num [CreditVec2.sub, CreditVec2.normSq, CreditVec2.dot]

/-- A proxy exact before a sign-changing representation drift becomes a strict
ascent direction afterward. -/
theorem stale_proxy_representation_drift_can_reverse_margin :
    let oldGradient : CreditVec2 := ⟨1, 0⟩
    let newGradient : CreditVec2 := ⟨-1, 0⟩
    let staleProxy : CreditVec2 := ⟨1, 0⟩
    oldGradient.dot staleProxy = 1 ∧
      newGradient.dot staleProxy = -1 := by
  norm_num [CreditVec2.dot]

#print axioms CreditVec2.cauchy_squared
#print axioms CreditVec2.positive_dot_of_proxy_error_normSq_lt
#print axioms FeedbackMap2.injective_iff_kernel_trivial
#print axioms FeedbackMap2.projection_erases_nonzero_error
#print axioms scalarDFA_finalUpdate
#print axioms dfaObjective_step_expansion
#print axioms tiedDFAUpdate_two_occurrences
#print axioms tiedDFA_single_occurrence_loses_credit
#print axioms orthogonal_updates_need_not_be_behaviorally_complementary
#print axioms scalarSyntheticGradient_finalUpdate
#print axioms syntheticGradient_bounded_error_positive_margin
#print axioms syntheticGradient_strict_descent_of_smooth_upper
#print axioms stale_proxy_representation_drift_can_reverse_margin

end Instances

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
