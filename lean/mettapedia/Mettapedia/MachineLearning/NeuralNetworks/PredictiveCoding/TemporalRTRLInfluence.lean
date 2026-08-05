import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic

/-!
# Temporal predictive coding and exact recurrent influence

Potter and Rhodes, *Learning Long-Range Dependencies with Temporal Predictive
Coding* (2026), Equations (10), (11), and (16), use the recurrent influence
equation

`M_t = immediate_t + J_t M_(t-1)`.

The same recurrence is the temporal half of real-time recurrent learning
(RTRL).  This file formalizes it at arbitrary finite horizon for additive
endomorphisms, rather than only for scalar Jacobians:

* the chronological recurrence equals an independently expanded composition;
* processing a prefix and suffix separately is exactly compositional;
* dropping the transported previous influence has an exact omission term;
* injected approximation errors obey a finite propagated-error certificate.

The source's full predictive-coding/BPTT equivalence additionally requires an
exact spatial learning signal and its fixed-prediction assumptions.  Those
hypotheses are deliberately not inferred from the temporal recurrence here.
The negative fixtures show that the one-step truncation can erase or reverse a
long-range contribution.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding

namespace TemporalRTRLInfluence

/-! ## Operator-valued RTRL recurrence -/

/-- One recurrent influence update.  `transport` is the state Jacobian acting
on the previous parameter influence, while `immediate` is the direct
parameter derivative at the current time. -/
structure InfluenceStep (Influence : Type*) [AddCommMonoid Influence] where
  transport : Influence →+ Influence
  immediate : Influence

/-- Chronological recurrent influence.  The head of the list is the earliest
time step. -/
def rtrlInfluence
    {Influence : Type*} [AddCommMonoid Influence] :
    List (InfluenceStep Influence) → Influence → Influence
  | [], initial => initial
  | step :: rest, initial =>
      rtrlInfluence rest (step.immediate + step.transport initial)

/-- Ordered composition of all recurrent transports. -/
def chronologicalTransport
    {Influence : Type*} [AddCommMonoid Influence] :
    List (InfluenceStep Influence) → Influence →+ Influence
  | [] => AddMonoidHom.id Influence
  | step :: rest =>
      (chronologicalTransport rest).comp step.transport

/-- Sum of each immediate derivative transported through every later
Jacobian. -/
def transportedImmediate
    {Influence : Type*} [AddCommMonoid Influence] :
    List (InfluenceStep Influence) → Influence
  | [] => 0
  | step :: rest =>
      chronologicalTransport rest step.immediate +
        transportedImmediate rest

/-- Independently expanded finite-horizon influence. -/
def expandedInfluence
    {Influence : Type*} [AddCommMonoid Influence]
    (steps : List (InfluenceStep Influence)) (initial : Influence) :
    Influence :=
  transportedImmediate steps + chronologicalTransport steps initial

/-- RTRL can be evaluated in chunks without changing its result. -/
theorem rtrlInfluence_append
    {Influence : Type*} [AddCommMonoid Influence]
    (earlierSteps laterSteps : List (InfluenceStep Influence))
    (initial : Influence) :
    rtrlInfluence (earlierSteps ++ laterSteps) initial =
      rtrlInfluence laterSteps
        (rtrlInfluence earlierSteps initial) := by
  induction earlierSteps generalizing initial with
  | nil =>
      rfl
  | cons step rest inductionHypothesis =>
      simp only [List.cons_append, rtrlInfluence]
      exact inductionHypothesis _

/-- The recurrent equation equals the explicit sum of all transported direct
derivatives plus the transported initial influence. -/
theorem rtrlInfluence_eq_expandedInfluence
    {Influence : Type*} [AddCommMonoid Influence]
    (steps : List (InfluenceStep Influence)) (initial : Influence) :
    rtrlInfluence steps initial = expandedInfluence steps initial := by
  induction steps generalizing initial with
  | nil =>
      simp [rtrlInfluence, expandedInfluence, transportedImmediate,
        chronologicalTransport]
  | cons step rest inductionHypothesis =>
      rw [rtrlInfluence, inductionHypothesis]
      simp only [expandedInfluence, transportedImmediate,
        chronologicalTransport, AddMonoidHom.comp_apply, map_add]
      ac_rfl

/-- Equation (11): any additive instantaneous-gradient readout sees the same
result from the recurrence and from the explicit temporal expansion. -/
theorem instantaneousGradient_eq_expanded
    {Influence Gradient : Type*}
    [AddCommMonoid Influence] [AddCommMonoid Gradient]
    (readout : Influence →+ Gradient)
    (steps : List (InfluenceStep Influence)) (initial : Influence) :
    readout (rtrlInfluence steps initial) =
      readout (expandedInfluence steps initial) := by
  rw [rtrlInfluence_eq_expandedInfluence]

/-! ## Exact boundary of one-step temporal truncation -/

/-- Full influence after one recurrent step. -/
def fullOneStepInfluence
    {Influence : Type*} [AddCommMonoid Influence]
    (step : InfluenceStep Influence) (previous : Influence) :
    Influence :=
  step.immediate + step.transport previous

/-- The one-step temporal-PC approximation that retains only the direct
parameter derivative. -/
def oneStepTruncatedInfluence
    {Influence : Type*} [AddCommMonoid Influence]
    (step : InfluenceStep Influence) : Influence :=
  step.immediate

/-- The exact term omitted by one-step temporal truncation is the transported
previous influence. -/
theorem fullOneStep_sub_truncated
    {Influence : Type*} [AddCommGroup Influence]
    (step : InfluenceStep Influence) (previous : Influence) :
    fullOneStepInfluence step previous -
        oneStepTruncatedInfluence step =
      step.transport previous := by
  simp [fullOneStepInfluence, oneStepTruncatedInfluence]

/-- Scalar specialization used by the executable boundary fixtures. -/
def scalarInfluenceStep (jacobian immediate : ℝ) : InfluenceStep ℝ where
  transport :=
    { toFun := fun previous => jacobian * previous
      map_zero' := by simp
      map_add' := by
        intro left right
        ring }
  immediate := immediate

@[simp]
theorem scalarInfluenceStep_transport
    (jacobian immediate previous : ℝ) :
    (scalarInfluenceStep jacobian immediate).transport previous =
      jacobian * previous :=
  rfl

/-- A purely long-range influence is completely erased by the one-step
approximation. -/
theorem oneStep_truncation_erases_long_range :
    fullOneStepInfluence (scalarInfluenceStep 1 0) 1 = 1 ∧
      oneStepTruncatedInfluence (scalarInfluenceStep 1 0) = 0 := by
  norm_num [fullOneStepInfluence, oneStepTruncatedInfluence,
    scalarInfluenceStep]

/-- The omitted long-range term can reverse the sign of the temporal
influence. -/
theorem oneStep_truncation_can_reverse_sign :
    fullOneStepInfluence (scalarInfluenceStep 2 (-1)) 1 = 1 ∧
      oneStepTruncatedInfluence (scalarInfluenceStep 2 (-1)) = -1 := by
  norm_num [fullOneStepInfluence, oneStepTruncatedInfluence,
    scalarInfluenceStep]

/-! ## Approximate recurrent influence and finite error transport -/

/-- One approximate recurrent-influence step, with an explicit local error and
a certified operator-norm bound for its exact transport. -/
structure ApproximateInfluenceStep
    (Influence : Type*) [NormedAddCommGroup Influence] where
  exact : InfluenceStep Influence
  injectedError : Influence
  transportBound : ℝ
  transportBound_nonneg : 0 ≤ transportBound
  transport_norm_le :
    ∀ difference,
      ‖exact.transport difference‖ ≤ transportBound * ‖difference‖

/-- Approximate recurrence with a declared local influence error at each
step. -/
def approximateInfluence
    {Influence : Type*} [NormedAddCommGroup Influence] :
    List (ApproximateInfluenceStep Influence) → Influence → Influence
  | [], initial => initial
  | step :: rest, initial =>
      approximateInfluence rest
        (step.exact.immediate + step.exact.transport initial +
          step.injectedError)

/-- The exact recurrence corresponding to an approximate trace. -/
def exactInfluenceSteps
    {Influence : Type*} [NormedAddCommGroup Influence]
    (steps : List (ApproximateInfluenceStep Influence)) :
    List (InfluenceStep Influence) :=
  steps.map ApproximateInfluenceStep.exact

/-- Scalar error budget obtained by transporting the current error bound and
adding the next declared local error. -/
def propagatedInfluenceError
    {Influence : Type*} [NormedAddCommGroup Influence] :
    List (ApproximateInfluenceStep Influence) → ℝ → ℝ
  | [], initialBound => initialBound
  | step :: rest, initialBound =>
      propagatedInfluenceError rest
        (step.transportBound * initialBound + ‖step.injectedError‖)

theorem propagatedInfluenceError_nonnegative
    {Influence : Type*} [NormedAddCommGroup Influence]
    (steps : List (ApproximateInfluenceStep Influence))
    (initialBound : ℝ) (initialBound_nonneg : 0 ≤ initialBound) :
    0 ≤ propagatedInfluenceError steps initialBound := by
  induction steps generalizing initialBound with
  | nil =>
      exact initialBound_nonneg
  | cons step rest inductionHypothesis =>
      apply inductionHypothesis
      exact add_nonneg
        (mul_nonneg step.transportBound_nonneg initialBound_nonneg)
        (norm_nonneg step.injectedError)

/-- Finite-horizon RTRL error certificate.  It permits nonuniform Jacobian
bounds and nonuniform local approximation errors across time. -/
theorem approximateInfluence_error_le
    {Influence : Type*} [NormedAddCommGroup Influence]
    (steps : List (ApproximateInfluenceStep Influence))
    (approximateInitial exactInitial : Influence)
    (initialBound : ℝ)
    (initialError_le : ‖approximateInitial - exactInitial‖ ≤ initialBound) :
    ‖approximateInfluence steps approximateInitial -
        rtrlInfluence (exactInfluenceSteps steps) exactInitial‖ ≤
      propagatedInfluenceError steps initialBound := by
  induction steps generalizing approximateInitial exactInitial initialBound with
  | nil =>
      simpa [approximateInfluence, exactInfluenceSteps, rtrlInfluence,
        propagatedInfluenceError] using initialError_le
  | cons step rest inductionHypothesis =>
      simp only [approximateInfluence, exactInfluenceSteps, List.map_cons,
        rtrlInfluence, propagatedInfluenceError]
      apply inductionHypothesis
      have differenceIdentity :
          (step.exact.immediate +
                step.exact.transport approximateInitial +
              step.injectedError) -
              (step.exact.immediate +
                step.exact.transport exactInitial) =
            step.exact.transport (approximateInitial - exactInitial) +
              step.injectedError := by
        rw [map_sub]
        abel
      rw [differenceIdentity]
      calc
        ‖step.exact.transport (approximateInitial - exactInitial) +
            step.injectedError‖ ≤
            ‖step.exact.transport
                (approximateInitial - exactInitial)‖ +
              ‖step.injectedError‖ :=
          norm_add_le _ _
        _ ≤ step.transportBound *
                ‖approximateInitial - exactInitial‖ +
              ‖step.injectedError‖ :=
          add_le_add
            (step.transport_norm_le
              (approximateInitial - exactInitial))
            le_rfl
        _ ≤ step.transportBound * initialBound +
              ‖step.injectedError‖ :=
          add_le_add
            (mul_le_mul_of_nonneg_left initialError_le
              step.transportBound_nonneg)
            le_rfl

/-- The canonical certificate starts from the observed initial discrepancy. -/
theorem approximateInfluence_error_le_canonical
    {Influence : Type*} [NormedAddCommGroup Influence]
    (steps : List (ApproximateInfluenceStep Influence))
    (approximateInitial exactInitial : Influence) :
    ‖approximateInfluence steps approximateInitial -
        rtrlInfluence (exactInfluenceSteps steps) exactInitial‖ ≤
      propagatedInfluenceError steps
        ‖approximateInitial - exactInitial‖ := by
  exact approximateInfluence_error_le steps approximateInitial exactInitial
    ‖approximateInitial - exactInitial‖ le_rfl

/-- A scalar step constructor whose bound is the exact absolute Jacobian. -/
def scalarApproximateInfluenceStep
    (jacobian immediate injectedError : ℝ) :
    ApproximateInfluenceStep ℝ where
  exact := scalarInfluenceStep jacobian immediate
  injectedError := injectedError
  transportBound := |jacobian|
  transportBound_nonneg := abs_nonneg jacobian
  transport_norm_le := by
    intro difference
    simp [scalarInfluenceStep]

/-- Persistent local influence error accumulates exactly on an identity
transport, so a zero initial error does not make an approximate trace exact. -/
theorem persistent_local_error :
    let step := scalarApproximateInfluenceStep 1 0 1
    let steps := [step, step]
    approximateInfluence steps 0 = 2 ∧
      rtrlInfluence (exactInfluenceSteps steps) 0 = 0 ∧
      propagatedInfluenceError steps 0 = 2 := by
  norm_num [approximateInfluence, exactInfluenceSteps,
    propagatedInfluenceError, scalarApproximateInfluenceStep,
    scalarInfluenceStep, rtrlInfluence, abs_of_nonneg]

#print axioms rtrlInfluence_eq_expandedInfluence
#print axioms fullOneStep_sub_truncated
#print axioms approximateInfluence_error_le

end TemporalRTRLInfluence

end Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding
