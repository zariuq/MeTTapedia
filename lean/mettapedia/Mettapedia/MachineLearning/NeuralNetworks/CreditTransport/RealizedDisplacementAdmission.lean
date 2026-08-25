import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.ActionMemoryLocalPC
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.WorkNormalizedTruncation

/-!
# Admission at the realized optimizer displacement

An optimizer is a state-dependent map from a proposed gradient and optimizer
state to both a parameter displacement and a successor optimizer state.  A
certificate on the proposed gradient therefore does not, in general, certify
the transition that will execute.  This module places the authorization gate
after that map.

The operational model is pure: clone the complete snapshot, compute one trial,
measure the realized displacement and post-step loss, then either commit the
trial snapshot or return the original snapshot exactly.  No particular
optimizer formula is assumed.  Consequently the theorem applies to momentum,
adaptive preconditioning, decoupled regularization, and any later optimizer
whose realized displacement can be measured.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
namespace RealizedDisplacementAdmission

noncomputable section

open scoped InnerProductSpace
open DirectionalTaskDescent
open WorkNormalizedTruncation

universe uP uS uM

/-! ## Abstract state-dependent optimizer -/

structure OptimizerSnapshot (Parameter : Type uP) (OptimizerState : Type uS) where
  parameter : Parameter
  optimizerState : OptimizerState
deriving DecidableEq

/-- The output of one optimizer calculation before authorization. -/
structure OptimizerOutput (Parameter : Type uP) (OptimizerState : Type uS) where
  displacement : Parameter
  optimizerState : OptimizerState

/-- No optimizer internals are assumed: only its complete state-dependent
input/output behavior is exposed. -/
structure OptimizerTransform (Parameter : Type uP) (OptimizerState : Type uS) where
  apply : Parameter → OptimizerState → OptimizerOutput Parameter OptimizerState

def plainOptimizerStep
    {Parameter : Type uP} {OptimizerState : Type uS}
    [Sub Parameter]
    (optimizer : OptimizerTransform Parameter OptimizerState)
    (gradient : Parameter)
    (before : OptimizerSnapshot Parameter OptimizerState) :
    OptimizerSnapshot Parameter OptimizerState :=
  let output := optimizer.apply gradient before.optimizerState
  { parameter := before.parameter - output.displacement
    optimizerState := output.optimizerState }

def realizedDisplacement
    {Parameter : Type uP} {OptimizerState : Type uS}
    (optimizer : OptimizerTransform Parameter OptimizerState)
    (gradient : Parameter)
    (before : OptimizerSnapshot Parameter OptimizerState) : Parameter :=
  (optimizer.apply gradient before.optimizerState).displacement

/-! ## Direction, scale, and observed task behavior -/

/-- Geometry checked on two realized optimizer displacements.  This is kept
separate from task descent: optimizer-to-optimizer similarity is not itself a
loss certificate. -/
structure DirectionScaleGate
    (Parameter : Type uP)
    [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    (reference candidate : Parameter) where
  cosineFloor : ℝ
  minimumNormRatio : ℝ
  maximumNormRatio : ℝ
  reference_nonzero : ‖reference‖ ≠ 0
  candidate_nonzero : ‖candidate‖ ≠ 0
  direction_passes :
    cosineFloor * (‖candidate‖ * ‖reference‖) ≤ ⟪reference, candidate⟫_ℝ
  scale_lower_passes : minimumNormRatio * ‖reference‖ ≤ ‖candidate‖
  scale_upper_passes : ‖candidate‖ ≤ maximumNormRatio * ‖reference‖

/-- A complete admission certificate refers to the trial snapshot actually
produced by the optimizer and to a positive measured loss margin. -/
structure MeasuredTransitionAdmission
    (Parameter : Type uP) (OptimizerState : Type uS)
    [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    (loss : Parameter → ℝ)
    (before candidate : OptimizerSnapshot Parameter OptimizerState)
    (reference displacement : Parameter) where
  parameter_transition : candidate.parameter = before.parameter - displacement
  geometry : DirectionScaleGate Parameter reference displacement
  minimumDecrease : ℝ
  minimumDecrease_pos : 0 < minimumDecrease
  observedDecrease :
    minimumDecrease ≤ loss before.parameter - loss candidate.parameter

/-- The measured post-step margin certifies strict descent of the exact
snapshot that would be committed. -/
theorem MeasuredTransitionAdmission.strictTaskDescent
    {Parameter : Type uP} {OptimizerState : Type uS}
    [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    {loss : Parameter → ℝ}
    {before candidate : OptimizerSnapshot Parameter OptimizerState}
    {reference displacement : Parameter}
    (admission : MeasuredTransitionAdmission Parameter OptimizerState loss
      before candidate reference displacement) :
    loss candidate.parameter < loss before.parameter := by
  linarith [admission.minimumDecrease_pos, admission.observedDecrease]

/-- Admission simultaneously preserves the required realized-displacement
geometry and certifies descent of the exact candidate snapshot.  The geometry
is a policy boundary; the measured positive margin is the descent witness. -/
theorem MeasuredTransitionAdmission.sound
    {Parameter : Type uP} {OptimizerState : Type uS}
    [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    {loss : Parameter → ℝ}
    {before candidate : OptimizerSnapshot Parameter OptimizerState}
    {reference displacement : Parameter}
    (admission : MeasuredTransitionAdmission Parameter OptimizerState loss
      before candidate reference displacement) :
    Nonempty (DirectionScaleGate Parameter reference displacement) ∧
      loss candidate.parameter < loss before.parameter :=
  ⟨⟨admission.geometry⟩, admission.strictTaskDescent⟩

/-- The existing observable finite-credit theorem applies to the realized
displacement, not to the raw optimizer input. -/
theorem strictTaskDescent_of_realized_finiteCredit
    {Parameter : Type uP} {OptimizerState : Type uS}
    [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    (optimizer : OptimizerTransform Parameter OptimizerState)
    (proposedGradient taskGradient : Parameter)
    (before : OptimizerSnapshot Parameter OptimizerState)
    {loss : Parameter → ℝ} {error curvature : ℝ}
    (upper : HasDirectionalTaskUpperModelAt loss before.parameter taskGradient
      (realizedDisplacement optimizer proposedGradient before) curvature)
    (herror :
      ‖realizedDisplacement optimizer proposedGradient before - taskGradient‖ ≤ error)
    (htrust :
      curvature / 2 <
        ‖realizedDisplacement optimizer proposedGradient before‖ *
          (‖realizedDisplacement optimizer proposedGradient before‖ - error)) :
    loss (plainOptimizerStep optimizer proposedGradient before).parameter <
      loss before.parameter := by
  have descent := finiteCredit_strictTaskDescent
    (exact := taskGradient)
    (finite := realizedDisplacement optimizer proposedGradient before)
    (parameter := before.parameter) (step := (1 : ℝ))
    upper herror (by norm_num) (by simpa using htrust)
  simpa [plainOptimizerStep, realizedDisplacement] using descent

/-! ## Clone, trial, measurement, commit, and rollback -/

/-- The measurement may fail; when it succeeds it carries the complete
admission certificate for the exact trial snapshot. -/
abbrev TransitionMeasurement
    (Parameter : Type uP) (OptimizerState : Type uS)
    [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    (loss : Parameter → ℝ)
    (before candidate : OptimizerSnapshot Parameter OptimizerState)
    (reference displacement : Parameter) :=
  MeasuredTransitionAdmission Parameter OptimizerState loss before candidate
    reference displacement

/-- Trial one step on the cloned snapshot.  Commit exactly that snapshot when
measurement returns a certificate; otherwise return the original snapshot. -/
def cloneStepMeasureCommit
    {Parameter : Type uP} {OptimizerState : Type uS}
    [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    (optimizer : OptimizerTransform Parameter OptimizerState)
    (proposedGradient referenceDisplacement : Parameter)
    (loss : Parameter → ℝ)
    (measure :
      (before candidate : OptimizerSnapshot Parameter OptimizerState) →
      (displacement : Parameter) →
      Option (TransitionMeasurement Parameter OptimizerState loss before candidate
        referenceDisplacement displacement))
    (before : OptimizerSnapshot Parameter OptimizerState) :
    OptimizerSnapshot Parameter OptimizerState :=
  let output := optimizer.apply proposedGradient before.optimizerState
  let candidate : OptimizerSnapshot Parameter OptimizerState :=
    { parameter := before.parameter - output.displacement
      optimizerState := output.optimizerState }
  match measure before candidate output.displacement with
  | some _ => candidate
  | none => before

theorem cloneStepMeasureCommit_measurement_failure_is_exact_rollback
    {Parameter : Type uP} {OptimizerState : Type uS}
    [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    (optimizer : OptimizerTransform Parameter OptimizerState)
    (proposedGradient referenceDisplacement : Parameter)
    (loss : Parameter → ℝ)
    (measure :
      (before candidate : OptimizerSnapshot Parameter OptimizerState) →
      (displacement : Parameter) →
      Option (TransitionMeasurement Parameter OptimizerState loss before candidate
        referenceDisplacement displacement))
    (before : OptimizerSnapshot Parameter OptimizerState)
    (failed :
      measure before (plainOptimizerStep optimizer proposedGradient before)
        (realizedDisplacement optimizer proposedGradient before) = none) :
    cloneStepMeasureCommit optimizer proposedGradient referenceDisplacement loss
      measure before = before := by
  let output := optimizer.apply proposedGradient before.optimizerState
  let candidate : OptimizerSnapshot Parameter OptimizerState :=
    { parameter := before.parameter - output.displacement
      optimizerState := output.optimizerState }
  have failed' : measure before candidate output.displacement = none := by
    simpa [plainOptimizerStep, realizedDisplacement, output, candidate] using failed
  simp [cloneStepMeasureCommit, output, candidate, failed']

theorem cloneStepMeasureCommit_measurement_failure_preserves_parameter
    {Parameter : Type uP} {OptimizerState : Type uS}
    [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    (optimizer : OptimizerTransform Parameter OptimizerState)
    (proposedGradient referenceDisplacement : Parameter)
    (loss : Parameter → ℝ)
    (measure :
      (before candidate : OptimizerSnapshot Parameter OptimizerState) →
      (displacement : Parameter) →
      Option (TransitionMeasurement Parameter OptimizerState loss before candidate
        referenceDisplacement displacement))
    (before : OptimizerSnapshot Parameter OptimizerState)
    (failed :
      measure before (plainOptimizerStep optimizer proposedGradient before)
        (realizedDisplacement optimizer proposedGradient before) = none) :
    (cloneStepMeasureCommit optimizer proposedGradient referenceDisplacement loss
      measure before).parameter = before.parameter := by
  rw [cloneStepMeasureCommit_measurement_failure_is_exact_rollback
    optimizer proposedGradient referenceDisplacement loss measure before failed]

theorem cloneStepMeasureCommit_measurement_failure_preserves_optimizerState
    {Parameter : Type uP} {OptimizerState : Type uS}
    [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    (optimizer : OptimizerTransform Parameter OptimizerState)
    (proposedGradient referenceDisplacement : Parameter)
    (loss : Parameter → ℝ)
    (measure :
      (before candidate : OptimizerSnapshot Parameter OptimizerState) →
      (displacement : Parameter) →
      Option (TransitionMeasurement Parameter OptimizerState loss before candidate
        referenceDisplacement displacement))
    (before : OptimizerSnapshot Parameter OptimizerState)
    (failed :
      measure before (plainOptimizerStep optimizer proposedGradient before)
        (realizedDisplacement optimizer proposedGradient before) = none) :
    (cloneStepMeasureCommit optimizer proposedGradient referenceDisplacement loss
      measure before).optimizerState = before.optimizerState := by
  rw [cloneStepMeasureCommit_measurement_failure_is_exact_rollback
    optimizer proposedGradient referenceDisplacement loss measure before failed]

theorem cloneStepMeasureCommit_admitted_eq_plain_step
    {Parameter : Type uP} {OptimizerState : Type uS}
    [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    (optimizer : OptimizerTransform Parameter OptimizerState)
    (proposedGradient referenceDisplacement : Parameter)
    (loss : Parameter → ℝ)
    (measure :
      (before candidate : OptimizerSnapshot Parameter OptimizerState) →
      (displacement : Parameter) →
      Option (TransitionMeasurement Parameter OptimizerState loss before candidate
        referenceDisplacement displacement))
    (before : OptimizerSnapshot Parameter OptimizerState)
    (certificate : TransitionMeasurement Parameter OptimizerState loss before
      (plainOptimizerStep optimizer proposedGradient before) referenceDisplacement
      (realizedDisplacement optimizer proposedGradient before))
    (admitted :
      measure before (plainOptimizerStep optimizer proposedGradient before)
        (realizedDisplacement optimizer proposedGradient before) = some certificate) :
    cloneStepMeasureCommit optimizer proposedGradient referenceDisplacement loss
      measure before = plainOptimizerStep optimizer proposedGradient before := by
  let output := optimizer.apply proposedGradient before.optimizerState
  let candidate : OptimizerSnapshot Parameter OptimizerState :=
    { parameter := before.parameter - output.displacement
      optimizerState := output.optimizerState }
  have admitted' : measure before candidate output.displacement = some certificate := by
    simpa [plainOptimizerStep, realizedDisplacement, output, candidate] using admitted
  simp [cloneStepMeasureCommit, plainOptimizerStep, output, candidate, admitted']

theorem cloneStepMeasureCommit_admitted_strictTaskDescent
    {Parameter : Type uP} {OptimizerState : Type uS}
    [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    (optimizer : OptimizerTransform Parameter OptimizerState)
    (proposedGradient referenceDisplacement : Parameter)
    (loss : Parameter → ℝ)
    (measure :
      (before candidate : OptimizerSnapshot Parameter OptimizerState) →
      (displacement : Parameter) →
      Option (TransitionMeasurement Parameter OptimizerState loss before candidate
        referenceDisplacement displacement))
    (before : OptimizerSnapshot Parameter OptimizerState)
    (certificate : TransitionMeasurement Parameter OptimizerState loss before
      (plainOptimizerStep optimizer proposedGradient before) referenceDisplacement
      (realizedDisplacement optimizer proposedGradient before))
    (admitted :
      measure before (plainOptimizerStep optimizer proposedGradient before)
        (realizedDisplacement optimizer proposedGradient before) = some certificate) :
    loss (cloneStepMeasureCommit optimizer proposedGradient referenceDisplacement loss
      measure before).parameter < loss before.parameter := by
  rw [cloneStepMeasureCommit_admitted_eq_plain_step optimizer proposedGradient
    referenceDisplacement loss measure before certificate admitted]
  exact certificate.strictTaskDescent

/-! ## Positive and negative two-coordinate fixtures -/

abbrev FixturePlane := EuclideanSpace ℝ (Fin 2)

def plane (first second : ℝ) : FixturePlane :=
  (WithLp.equiv 2 (Fin 2 → ℝ)).symm ![first, second]

private theorem plane_norm_sq (vector : FixturePlane) :
    ‖vector‖ ^ 2 = vector 0 ^ 2 + vector 1 ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, Fin.sum_univ_two]
  ring

def diagonalRescale (firstScale secondScale : ℝ)
    (gradient : FixturePlane) : FixturePlane :=
  plane (firstScale * gradient 0) (secondScale * gradient 1)

def rawReference : FixturePlane := plane 4 3
def rawCandidate : FixturePlane := plane 4 (-3)
def realizedReference : FixturePlane := diagonalRescale 1 2 rawReference
def realizedCandidate : FixturePlane := diagonalRescale 1 2 rawCandidate

theorem raw_pair_passes_direction_and_scale :
    ∃ gate : DirectionScaleGate FixturePlane rawReference rawCandidate,
      gate.cosineFloor = 1 / 4 ∧
      gate.minimumNormRatio = 1 ∧ gate.maximumNormRatio = 1 := by
  have hrefSq : ‖rawReference‖ ^ 2 = 25 := by
    rw [plane_norm_sq]
    norm_num [rawReference, plane, WithLp.equiv]
  have hcandSq : ‖rawCandidate‖ ^ 2 = 25 := by
    rw [plane_norm_sq]
    norm_num [rawCandidate, plane, WithLp.equiv]
  have href : ‖rawReference‖ = 5 := by
    nlinarith [norm_nonneg rawReference]
  have hcand : ‖rawCandidate‖ = 5 := by
    nlinarith [norm_nonneg rawCandidate]
  refine ⟨{
    cosineFloor := 1 / 4
    minimumNormRatio := 1
    maximumNormRatio := 1
    reference_nonzero := by rw [href]; norm_num
    candidate_nonzero := by rw [hcand]; norm_num
    direction_passes := ?_
    scale_lower_passes := ?_
    scale_upper_passes := ?_ }, rfl, rfl, rfl⟩
  · rw [href, hcand]
    norm_num [rawReference, rawCandidate, plane, WithLp.equiv,
      PiLp.inner_apply, Fin.sum_univ_two]
  · rw [href, hcand]
    norm_num
  · rw [href, hcand]
    norm_num

/-- A positive diagonal preconditioner can destroy a direction certificate
that held for the raw gradients.  This is the two-coordinate obstruction to
authorizing a history-dependent optimizer from pre-transform geometry. -/
theorem positive_diagonal_rescaling_breaks_raw_direction_gate :
    0 < ⟪rawReference, rawCandidate⟫_ℝ ∧
      ⟪realizedReference, realizedCandidate⟫_ℝ < 0 := by
  constructor <;>
    norm_num [rawReference, rawCandidate, realizedReference, realizedCandidate,
      diagonalRescale, plane, WithLp.equiv, PiLp.inner_apply,
      Fin.sum_univ_two]

/-- Direction-and-scale similarity alone says nothing about the task loss
unless the reference is connected to task descent or the post-step loss is
measured. -/
theorem geometry_without_task_measurement_does_not_certify_descent :
    let direction : ℝ := 1
    let loss : ℝ → ℝ := fun parameter => -parameter
    (1 : ℝ) * |direction| ≤ |direction| ∧
      loss (0 - direction) > loss 0 := by
  norm_num

#print axioms MeasuredTransitionAdmission.strictTaskDescent
#print axioms MeasuredTransitionAdmission.sound
#print axioms strictTaskDescent_of_realized_finiteCredit
#print axioms cloneStepMeasureCommit_measurement_failure_is_exact_rollback
#print axioms cloneStepMeasureCommit_admitted_eq_plain_step
#print axioms cloneStepMeasureCommit_admitted_strictTaskDescent
#print axioms raw_pair_passes_direction_and_scale
#print axioms positive_diagonal_rescaling_breaks_raw_direction_gate
#print axioms geometry_without_task_measurement_does_not_certify_descent

end
end RealizedDisplacementAdmission
end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
