import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.ActionMemoryGroupedInformationObjective

/-!
# Detached slow-parameter credit for the nonlinear action-memory reasoner

State settling and slow-parameter learning are different derivatives.  This
module holds the settled active/evidence states fixed and differentiates the
same nonlinear residual-plus-grouped-task energy along every locally plastic
runtime parameter family.  No derivative is taken through the finite settling
unroll.

The common theorem works with certified hidden-input curves.  Concrete
corollaries then bind those curves to the dense drive maps, output projection,
output gate, and bounded raw coupling parameters of `Parameters`.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
namespace ActionMemoryNonlinearVectorPC

open scoped InnerProductSpace BigOperators
open InnerProduct
open ActionMemoryLocalPC

noncomputable section

local instance (priority := 2000) parameterCreditRealModule : Module ℝ ℝ :=
  RCLike.toInnerProductSpaceReal.toModule

private abbrev AlgebraRealHasDerivAt (function : ℝ → ℝ)
    (derivative point : ℝ) : Prop :=
  @HasDerivAt ℝ inferInstance ℝ
    Real.normedCommRing.toAddCommGroup
    (NormedAlgebra.toNormedSpace ℝ).toModule inferInstance inferInstance
    function derivative point

private theorem algebraHasDerivAt_to_exact {function : ℝ → ℝ}
    {derivative point : ℝ}
    (witness : AlgebraRealHasDerivAt function derivative point) :
    ExactRealHasDerivAt function derivative point := by
  have moduleEquality : (NormedAlgebra.toNormedSpace ℝ).toModule =
      RCLike.toInnerProductSpaceReal.toModule := by
    apply Module.ext
    rfl
  simpa only [AlgebraRealHasDerivAt, ExactRealHasDerivAt,
    moduleEquality] using witness

structure HiddenCurveWitness (width : ℕ) where
  curve : ℝ → Hidden width
  atZero : Hidden width
  derivative : Hidden width
  curve_zero : curve 0 = atZero
  coordinateDerivative : ∀ coordinate : Fin width,
    ExactRealHasDerivAt (fun time : ℝ => curve time coordinate)
      (derivative coordinate) 0

def HiddenCurveWitness.constant {width : ℕ} (value : Hidden width) :
    HiddenCurveWitness width where
  curve _ := value
  atZero := value
  derivative := 0
  curve_zero := rfl
  coordinateDerivative coordinate := by
    simpa using hasDerivAt_const (x := (0 : ℝ)) (c := value coordinate)

def HiddenCurveWitness.affine {width : ℕ}
    (base direction : Hidden width) : HiddenCurveWitness width where
  curve time := base + time • direction
  atZero := base
  derivative := direction
  curve_zero := by simp
  coordinateDerivative coordinate := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const
      (direction coordinate)).const_add (base coordinate)

def HiddenCurveWitness.tanhAffine {width : ℕ}
    (base direction : Hidden width) : HiddenCurveWitness width where
  curve time := coordinateTanh (base + time • direction)
  atZero := coordinateTanh base
  derivative := coordinateTanhSlope base direction
  curve_zero := by simp
  coordinateDerivative coordinate := by
    have affine : ExactRealHasDerivAt
        (fun time : ℝ => base coordinate + time * direction coordinate)
        (direction coordinate) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const
        (direction coordinate)).const_add (base coordinate)
    have composed :=
      (hasDerivAt_tanhExact (base coordinate + 0 * direction coordinate)).comp 0 affine
    have converted := algebraHasDerivAt_to_exact composed
    convert converted using 1
    · funext time
      rfl
    · simp only [zero_mul, add_zero, coordinateTanhSlope_apply]

def HiddenCurveWitness.add {width : ℕ}
    (left right : HiddenCurveWitness width) : HiddenCurveWitness width where
  curve time := left.curve time + right.curve time
  atZero := left.atZero + right.atZero
  derivative := left.derivative + right.derivative
  curve_zero := by rw [left.curve_zero, right.curve_zero]
  coordinateDerivative coordinate := by
    have combined := (left.coordinateDerivative coordinate).add
      (right.coordinateDerivative coordinate)
    have converted := algebraHasDerivAt_to_exact combined
    convert converted using 1
    · funext time
      rfl
    · rfl

def HiddenCurveWitness.smul {width : ℕ} (scalar : ℝ)
    (curve : HiddenCurveWitness width) : HiddenCurveWitness width where
  curve time := scalar • curve.curve time
  atZero := scalar • curve.atZero
  derivative := scalar • curve.derivative
  curve_zero := by rw [curve.curve_zero]
  coordinateDerivative coordinate := by
    simpa using (curve.coordinateDerivative coordinate).const_mul scalar

/-- The raw scalar is passed through the registered bounded-coupling map
`limit * tanh(raw)`, then multiplies a fixed hidden parent. -/
def HiddenCurveWitness.rawCoupling {width : ℕ}
    (limit raw rawDirection : ℝ) (parent : Hidden width) :
    HiddenCurveWitness width where
  curve time := (limit * Real.tanh (raw + time * rawDirection)) • parent
  atZero := (limit * Real.tanh raw) • parent
  derivative := (limit * tanhSlope raw * rawDirection) • parent
  curve_zero := by simp
  coordinateDerivative coordinate := by
    have affine : ExactRealHasDerivAt
        (fun time : ℝ => raw + time * rawDirection) rawDirection 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const rawDirection).const_add raw
    have tanhLine := (hasDerivAt_tanhExact
      (raw + 0 * rawDirection)).comp 0 affine
    have scaled := tanhLine.const_mul (limit * parent coordinate)
    have converted := algebraHasDerivAt_to_exact scaled
    convert converted using 1
    · funext time
      simp only [PiLp.smul_apply, Function.comp_apply]
      ring
    · simp only [zero_mul, add_zero, PiLp.smul_apply]
      ring

structure DetachedEnergyLine (width actions : ℕ) where
  activeInput : HiddenCurveWitness width
  evidenceInput : HiddenCurveWitness width
  logitsBase : PolicyRow actions
  logitsDirection : PolicyRow actions

def detachedEnergyAlong {width actions : ℕ}
    (parameters : Parameters width actions) (task : TaskFunctional actions)
    (frozenAuxiliary : ℝ) (state : State width)
    (line : DetachedEnergyLine width actions) (time : ℝ) : ℝ :=
  parameters.residualPrecision / 2 *
      ‖state.1 - coordinateTanh (line.activeInput.curve time)‖ ^ 2 +
    parameters.residualPrecision / 2 *
      ‖state.2 - coordinateTanh (line.evidenceInput.curve time)‖ ^ 2 +
    parameters.taskPrecision *
      task.value (line.logitsBase + time • line.logitsDirection) +
    frozenAuxiliary

def detachedParameterDirectionalCredit {width actions : ℕ}
    (parameters : Parameters width actions) (task : TaskFunctional actions)
    (state : State width) (line : DetachedEnergyLine width actions) : ℝ :=
  parameters.residualPrecision *
      ⟪state.1 - coordinateTanh line.activeInput.atZero,
        -(coordinateTanhSlope line.activeInput.atZero
          line.activeInput.derivative)⟫_ℝ +
    parameters.residualPrecision *
      ⟪state.2 - coordinateTanh line.evidenceInput.atZero,
        -(coordinateTanhSlope line.evidenceInput.atZero
          line.evidenceInput.derivative)⟫_ℝ +
    parameters.taskPrecision *
      ⟪task.gradient line.logitsBase, line.logitsDirection⟫_ℝ

/-- Exact detached directional derivative of the nonlinear local energy. -/
theorem hasDerivAt_detachedEnergyAlong {width actions : ℕ}
    (parameters : Parameters width actions) (task : TaskFunctional actions)
    (frozenAuxiliary : ℝ) (state : State width)
    (line : DetachedEnergyLine width actions) :
    HasDerivAt
      (detachedEnergyAlong parameters task frozenAuxiliary state line)
      (detachedParameterDirectionalCredit parameters task state line) 0 := by
  have activeLine := hasDerivAt_weightedTanhResidualCurve
    parameters.residualPrecision state.1 line.activeInput.curve
    line.activeInput.atZero line.activeInput.derivative
    line.activeInput.curve_zero line.activeInput.coordinateDerivative
  have evidenceLine := hasDerivAt_weightedTanhResidualCurve
    parameters.residualPrecision state.2 line.evidenceInput.curve
    line.evidenceInput.atZero line.evidenceInput.derivative
    line.evidenceInput.curve_zero line.evidenceInput.coordinateDerivative
  have taskLine := (task.directionalDerivative line.logitsBase
    line.logitsDirection).const_mul parameters.taskPrecision
  have frozenLine : HasDerivAt (fun _time : ℝ => frozenAuxiliary) 0 0 :=
    hasDerivAt_const _ _
  have combined := activeLine.add evidenceLine |>.add taskLine |>.add frozenLine
  apply combined.congr_deriv
  unfold detachedParameterDirectionalCredit
  ring

def detachedEvidenceInput {width actions : ℕ}
    (parameters : Parameters width actions) (inputs : Inputs actions)
    (dynamics : Dynamics) (state : State width) : Hidden width :=
  match dynamics with
  | .equilibrium => parameters.evidenceDrive inputs +
      parameters.evidenceCoupling • state.1
  | .feedforward => parameters.evidenceDrive inputs +
      parameters.evidenceCoupling • coordinateTanh (parameters.activeDrive inputs)

def detachedEvidenceParent {width actions : ℕ}
    (parameters : Parameters width actions) (inputs : Inputs actions)
    (dynamics : Dynamics) (state : State width) : Hidden width :=
  match dynamics with
  | .equilibrium => state.1
  | .feedforward => coordinateTanh (parameters.activeDrive inputs)

/-- A single reusable bridge from an exact parameter path in `localEnergy` to
its detached directional credit.  The hypotheses identify the actual active
input, evidence input, and masked readout along that path; the precision fields
must remain fixed. -/
theorem hasDerivAt_localEnergy_parameterPath {width actions : ℕ}
    (parameters : Parameters width actions) (inputs : Inputs actions)
    (task : TaskFunctional actions) (dynamics : Dynamics)
    (frozenAuxiliary : ℝ) (state : State width)
    (varied : ℝ → Parameters width actions)
    (line : DetachedEnergyLine width actions)
    (residualPrecision_fixed : ∀ time,
      (varied time).residualPrecision = parameters.residualPrecision)
    (taskPrecision_fixed : ∀ time,
      (varied time).taskPrecision = parameters.taskPrecision)
    (activeInput_exact : ∀ time,
      (varied time).activeDrive inputs +
          (varied time).activeCoupling • state.2 = line.activeInput.curve time)
    (evidenceInput_exact : ∀ time,
      detachedEvidenceInput (varied time) inputs dynamics state =
        line.evidenceInput.curve time)
    (readout_exact : ∀ time,
      patchedLogits (varied time) inputs state.1 =
        line.logitsBase + time • line.logitsDirection) :
    HasDerivAt
      (fun time : ℝ => localEnergy (varied time) inputs task dynamics
        frozenAuxiliary state)
      (detachedParameterDirectionalCredit parameters task state line) 0 := by
  have derivative := hasDerivAt_detachedEnergyAlong parameters task
    frozenAuxiliary state line
  have functionEquality :
      (fun time : ℝ => localEnergy (varied time) inputs task dynamics
        frozenAuxiliary state) =
      detachedEnergyAlong parameters task frozenAuxiliary state line := by
    funext time
    unfold localEnergy residualEnergy activeResidual evidenceResidual
      detachedEnergyAlong
    rw [residualPrecision_fixed time, taskPrecision_fixed time,
      activeInput_exact time, readout_exact time]
    cases dynamics
    · simp only [detachedEvidenceInput] at evidenceInput_exact
      rw [evidenceInput_exact time]
    · simp only [detachedEvidenceInput] at evidenceInput_exact
      rw [evidenceInput_exact time]
  rw [functionEquality]
  exact derivative

structure BatchDetachedEnergyLine (rows width actions : ℕ) where
  activeInput : Fin rows → HiddenCurveWitness width
  evidenceInput : Fin rows → HiddenCurveWitness width
  logitsBase : PolicyBatch rows actions
  logitsDirection : PolicyBatch rows actions

def batchDetachedEnergyAlong {rows width actions : ℕ}
    (parameters : Parameters width actions)
    (task : BatchTaskFunctional rows actions) (frozenAuxiliary : ℝ)
    (states : Fin rows → State width)
    (selected : Finset (Fin rows))
    (line : BatchDetachedEnergyLine rows width actions) (time : ℝ) : ℝ :=
  (if selected.Nonempty then
    (selected.card : ℝ)⁻¹ * ∑ row ∈ selected,
        (parameters.residualPrecision / 2 *
            ‖(states row).1 - coordinateTanh ((line.activeInput row).curve time)‖ ^ 2 +
          parameters.residualPrecision / 2 *
            ‖(states row).2 - coordinateTanh ((line.evidenceInput row).curve time)‖ ^ 2)
  else 0) +
    parameters.taskPrecision *
      task.value (line.logitsBase + time • line.logitsDirection) +
    frozenAuxiliary

def batchDetachedParameterDirectionalCredit {rows width actions : ℕ}
    (parameters : Parameters width actions)
    (task : BatchTaskFunctional rows actions) (states : Fin rows → State width)
    (selected : Finset (Fin rows))
    (line : BatchDetachedEnergyLine rows width actions) : ℝ :=
  (if selected.Nonempty then
    (selected.card : ℝ)⁻¹ * ∑ row ∈ selected,
        (parameters.residualPrecision *
            ⟪(states row).1 - coordinateTanh (line.activeInput row).atZero,
              -(coordinateTanhSlope (line.activeInput row).atZero
                (line.activeInput row).derivative)⟫_ℝ +
          parameters.residualPrecision *
            ⟪(states row).2 - coordinateTanh (line.evidenceInput row).atZero,
              -(coordinateTanhSlope (line.evidenceInput row).atZero
                (line.evidenceInput row).derivative)⟫_ℝ)
  else 0) +
    parameters.taskPrecision *
      ⟪task.gradient line.logitsBase, line.logitsDirection⟫_ℝ

/-- Exact aggregation theorem for shared slow parameters: residual credits are
averaged over routed rows and the task credit is differentiated once through
the exact grouped information functional. -/
theorem hasDerivAt_batchDetachedEnergyAlong {rows width actions : ℕ}
    (parameters : Parameters width actions)
    (task : BatchTaskFunctional rows actions) (frozenAuxiliary : ℝ)
    (states : Fin rows → State width)
    (selected : Finset (Fin rows))
    (line : BatchDetachedEnergyLine rows width actions) :
    HasDerivAt
      (batchDetachedEnergyAlong parameters task frozenAuxiliary states selected line)
      (batchDetachedParameterDirectionalCredit parameters task states selected line) 0 := by
  have rowDerivative (row : Fin rows) : HasDerivAt
      (fun time : ℝ =>
        parameters.residualPrecision / 2 *
            ‖(states row).1 - coordinateTanh ((line.activeInput row).curve time)‖ ^ 2 +
          parameters.residualPrecision / 2 *
            ‖(states row).2 - coordinateTanh ((line.evidenceInput row).curve time)‖ ^ 2)
      (parameters.residualPrecision *
          ⟪(states row).1 - coordinateTanh (line.activeInput row).atZero,
            -(coordinateTanhSlope (line.activeInput row).atZero
              (line.activeInput row).derivative)⟫_ℝ +
        parameters.residualPrecision *
          ⟪(states row).2 - coordinateTanh (line.evidenceInput row).atZero,
            -(coordinateTanhSlope (line.evidenceInput row).atZero
              (line.evidenceInput row).derivative)⟫_ℝ) 0 := by
    exact (hasDerivAt_weightedTanhResidualCurve parameters.residualPrecision
      (states row).1 (line.activeInput row).curve
      (line.activeInput row).atZero (line.activeInput row).derivative
      (line.activeInput row).curve_zero
      (line.activeInput row).coordinateDerivative).add
      (hasDerivAt_weightedTanhResidualCurve parameters.residualPrecision
        (states row).2 (line.evidenceInput row).curve
        (line.evidenceInput row).atZero (line.evidenceInput row).derivative
        (line.evidenceInput row).curve_zero
        (line.evidenceInput row).coordinateDerivative)
  have residualDerivative : HasDerivAt
      (fun time : ℝ => if selected.Nonempty then
        (selected.card : ℝ)⁻¹ * ∑ row ∈ selected,
          (parameters.residualPrecision / 2 *
              ‖(states row).1 - coordinateTanh ((line.activeInput row).curve time)‖ ^ 2 +
            parameters.residualPrecision / 2 *
              ‖(states row).2 - coordinateTanh ((line.evidenceInput row).curve time)‖ ^ 2)
        else 0)
      (if selected.Nonempty then
        (selected.card : ℝ)⁻¹ * ∑ row ∈ selected,
          (parameters.residualPrecision *
              ⟪(states row).1 - coordinateTanh (line.activeInput row).atZero,
                -(coordinateTanhSlope (line.activeInput row).atZero
                  (line.activeInput row).derivative)⟫_ℝ +
            parameters.residualPrecision *
              ⟪(states row).2 - coordinateTanh (line.evidenceInput row).atZero,
                -(coordinateTanhSlope (line.evidenceInput row).atZero
                  (line.evidenceInput row).derivative)⟫_ℝ)
        else 0) 0 := by
    by_cases nonempty : selected.Nonempty
    · simp only [nonempty, if_pos]
      exact (HasDerivAt.fun_sum (u := selected)
        (fun row _ => rowDerivative row)).const_mul ((selected.card : ℝ)⁻¹)
    · simp only [nonempty]
      exact hasDerivAt_const (x := (0 : ℝ)) (c := (0 : ℝ))
  have taskDerivative :=
    (task.directionalDerivative line.logitsBase line.logitsDirection).const_mul
      parameters.taskPrecision
  have frozenDerivative : HasDerivAt (fun _time : ℝ => frozenAuxiliary) 0 0 :=
    hasDerivAt_const _ _
  have combined := residualDerivative.add taskDerivative |>.add frozenDerivative
  apply combined.congr_deriv
  unfold batchDetachedParameterDirectionalCredit
  ring

/-- Connects a concrete shared-parameter path to the exact routed-row batch
energy.  Unlike row freezing, this theorem moves the parameter in every row
simultaneously and differentiates the grouped task once. -/
theorem hasDerivAt_routedBatch_parameterPath {rows width actions : ℕ}
    (parameters : Parameters width actions)
    (inputs : Fin rows → Inputs actions) (states : Fin rows → State width)
    (task : BatchTaskFunctional rows actions) (dynamics : Dynamics)
    (frozenAuxiliary : ℝ) (varied : ℝ → Parameters width actions)
    (line : BatchDetachedEnergyLine rows width actions)
    (residualPrecision_fixed : ∀ time,
      (varied time).residualPrecision = parameters.residualPrecision)
    (taskPrecision_fixed : ∀ time,
      (varied time).taskPrecision = parameters.taskPrecision)
    (activeInput_exact : ∀ time row,
      (varied time).activeDrive (inputs row) +
          (varied time).activeCoupling • (states row).2 =
        (line.activeInput row).curve time)
    (evidenceInput_exact : ∀ time row,
      detachedEvidenceInput (varied time) (inputs row) dynamics (states row) =
        (line.evidenceInput row).curve time)
    (readout_exact : ∀ time,
      patchedPolicyBatch (varied time) inputs states =
        line.logitsBase + time • line.logitsDirection) :
    HasDerivAt
      (fun time : ℝ => routedBatchEnergy (varied time) inputs states task
        dynamics frozenAuxiliary)
      (batchDetachedParameterDirectionalCredit parameters task states
        (routedRows inputs) line) 0 := by
  have derivative := hasDerivAt_batchDetachedEnergyAlong parameters task
    frozenAuxiliary states (routedRows inputs) line
  have functionEquality :
      (fun time : ℝ => routedBatchEnergy (varied time) inputs states task
        dynamics frozenAuxiliary) =
      batchDetachedEnergyAlong parameters task frozenAuxiliary states
        (routedRows inputs) line := by
    funext time
    unfold routedBatchEnergy routedResidualMean finiteSelectedMean
      batchDetachedEnergyAlong
    rw [taskPrecision_fixed time, readout_exact time]
    by_cases nonempty : (routedRows inputs).Nonempty
    · simp only [nonempty, if_pos]
      congr 2
      congr 1
      apply Finset.sum_congr rfl
      intro row _
      unfold residualEnergy activeResidual evidenceResidual
      rw [residualPrecision_fixed time, activeInput_exact time row]
      cases dynamics
      · simp only [detachedEvidenceInput] at evidenceInput_exact
        rw [evidenceInput_exact time row]
      · simp only [detachedEvidenceInput] at evidenceInput_exact
        rw [evidenceInput_exact time row]
    · simp [nonempty]
  rw [functionEquality]
  exact derivative

/-! ## Concrete parameter paths -/

def varyBaseDriveWeight {width actions : ℕ}
    (parameters : Parameters width actions)
    (direction : PolicyRow actions →L[ℝ] Hidden width) (time : ℝ) :
    Parameters width actions :=
  { parameters with baseDriveWeight := parameters.baseDriveWeight + time • direction }

def varyBaseDriveBias {width actions : ℕ}
    (parameters : Parameters width actions) (direction : Hidden width) (time : ℝ) :
    Parameters width actions :=
  { parameters with baseDriveBias := parameters.baseDriveBias + time • direction }

def varyEvidenceToActive {width actions : ℕ}
    (parameters : Parameters width actions)
    (direction : PolicyRow actions →L[ℝ] Hidden width) (time : ℝ) :
    Parameters width actions :=
  { parameters with evidenceToActive := parameters.evidenceToActive + time • direction }

def varyEvidenceDriveWeight {width actions : ℕ}
    (parameters : Parameters width actions)
    (direction : PolicyRow actions →L[ℝ] Hidden width) (time : ℝ) :
    Parameters width actions :=
  { parameters with evidenceDriveWeight := parameters.evidenceDriveWeight + time • direction }

def varyEvidenceDriveBias {width actions : ℕ}
    (parameters : Parameters width actions) (direction : Hidden width) (time : ℝ) :
    Parameters width actions :=
  { parameters with evidenceDriveBias := parameters.evidenceDriveBias + time • direction }

def varyOutputProjection {width actions : ℕ}
    (parameters : Parameters width actions)
    (direction : Hidden width →L[ℝ] PolicyRow actions) (time : ℝ) :
    Parameters width actions :=
  { parameters with outputProjection := parameters.outputProjection + time • direction }

def varyOutputGate {width actions : ℕ}
    (parameters : Parameters width actions) (direction time : ℝ) :
    Parameters width actions :=
  { parameters with outputGate := parameters.outputGate + time * direction }

def varyRawActiveCoupling {width actions : ℕ}
    (parameters : Parameters width actions) (direction time : ℝ) :
    Parameters width actions :=
  { parameters with rawActiveCoupling := parameters.rawActiveCoupling + time * direction }

def varyRawEvidenceCoupling {width actions : ℕ}
    (parameters : Parameters width actions) (direction time : ℝ) :
    Parameters width actions :=
  { parameters with rawEvidenceCoupling := parameters.rawEvidenceCoupling + time * direction }

def maskedReadoutDirection {actions : ℕ}
    (inputs : Inputs actions) (direction : PolicyRow actions) : PolicyRow actions :=
  maskedTaskGradient inputs direction

def equilibriumDetachedLine {width actions : ℕ}
    (parameters : Parameters width actions) (inputs : Inputs actions)
    (state : State width) (activeInput evidenceInput : HiddenCurveWitness width)
    (logitsDirection : PolicyRow actions) : DetachedEnergyLine width actions where
  activeInput := activeInput
  evidenceInput := evidenceInput
  logitsBase := patchedLogits parameters inputs state.1
  logitsDirection := logitsDirection

/-! The eight experiment-facing families are proved below. -/

theorem hasDerivAt_baseDriveWeight_equilibrium {width actions : ℕ}
    (parameters : Parameters width actions) (inputs : Inputs actions)
    (task : TaskFunctional actions) (frozenAuxiliary : ℝ) (state : State width)
    (direction : PolicyRow actions →L[ℝ] Hidden width) :
    HasDerivAt
      (fun time : ℝ => localEnergy (varyBaseDriveWeight parameters direction time)
        inputs task .equilibrium frozenAuxiliary state)
      (detachedParameterDirectionalCredit parameters task state
        (equilibriumDetachedLine parameters inputs state
          (HiddenCurveWitness.affine
            (parameters.activeDrive inputs + parameters.activeCoupling • state.2)
            (direction inputs.maskedBaseDistribution))
          (HiddenCurveWitness.constant
            (parameters.evidenceDrive inputs + parameters.evidenceCoupling • state.1))
          0)) 0 := by
  let line := equilibriumDetachedLine parameters inputs state
    (HiddenCurveWitness.affine
      (parameters.activeDrive inputs + parameters.activeCoupling • state.2)
      (direction inputs.maskedBaseDistribution))
    (HiddenCurveWitness.constant
      (parameters.evidenceDrive inputs + parameters.evidenceCoupling • state.1)) 0
  have derivative := hasDerivAt_detachedEnergyAlong parameters task
    frozenAuxiliary state line
  have functionEquality :
      (fun time : ℝ => localEnergy (varyBaseDriveWeight parameters direction time)
        inputs task .equilibrium frozenAuxiliary state) =
      detachedEnergyAlong parameters task frozenAuxiliary state line := by
    funext time
    have activeInputEquality :
        (varyBaseDriveWeight parameters direction time).activeDrive inputs +
            (varyBaseDriveWeight parameters direction time).activeCoupling • state.2 =
          line.activeInput.curve time := by
      simp [line, equilibriumDetachedLine, varyBaseDriveWeight,
        HiddenCurveWitness.affine, Parameters.activeDrive,
        Parameters.activeCoupling]
      module
    have evidenceInputEquality :
        (varyBaseDriveWeight parameters direction time).evidenceDrive inputs +
            (varyBaseDriveWeight parameters direction time).evidenceCoupling • state.1 =
          line.evidenceInput.curve time := by
      simp [line, equilibriumDetachedLine, varyBaseDriveWeight,
        HiddenCurveWitness.constant, Parameters.evidenceDrive,
        Parameters.evidenceCoupling]
    have logitsEquality :
        patchedLogits (varyBaseDriveWeight parameters direction time) inputs state.1 =
          line.logitsBase := by
      rfl
    simp only [localEnergy, residualEnergy, activeResidual, evidenceResidual]
    rw [activeInputEquality, evidenceInputEquality, logitsEquality]
    simp [detachedEnergyAlong, line, equilibriumDetachedLine,
      HiddenCurveWitness.affine, HiddenCurveWitness.constant,
      varyBaseDriveWeight]
  rw [functionEquality]
  exact derivative

theorem hasDerivAt_baseDriveBias_equilibrium {width actions : ℕ}
    (parameters : Parameters width actions) (inputs : Inputs actions)
    (task : TaskFunctional actions) (frozenAuxiliary : ℝ) (state : State width)
    (direction : Hidden width) :
    HasDerivAt
      (fun time : ℝ => localEnergy (varyBaseDriveBias parameters direction time)
        inputs task .equilibrium frozenAuxiliary state)
      (detachedParameterDirectionalCredit parameters task state
        (equilibriumDetachedLine parameters inputs state
          (HiddenCurveWitness.affine
            (parameters.activeDrive inputs + parameters.activeCoupling • state.2) direction)
          (HiddenCurveWitness.constant
            (parameters.evidenceDrive inputs + parameters.evidenceCoupling • state.1)) 0)) 0 := by
  let line := equilibriumDetachedLine parameters inputs state
    (HiddenCurveWitness.affine
      (parameters.activeDrive inputs + parameters.activeCoupling • state.2) direction)
    (HiddenCurveWitness.constant
      (parameters.evidenceDrive inputs + parameters.evidenceCoupling • state.1)) 0
  have derivative := hasDerivAt_detachedEnergyAlong parameters task
    frozenAuxiliary state line
  have functionEquality :
      (fun time : ℝ => localEnergy (varyBaseDriveBias parameters direction time)
        inputs task .equilibrium frozenAuxiliary state) =
      detachedEnergyAlong parameters task frozenAuxiliary state line := by
    funext time
    have activeInputEquality :
        (varyBaseDriveBias parameters direction time).activeDrive inputs +
            (varyBaseDriveBias parameters direction time).activeCoupling • state.2 =
          line.activeInput.curve time := by
      simp [line, equilibriumDetachedLine, varyBaseDriveBias,
        HiddenCurveWitness.affine, Parameters.activeDrive,
        Parameters.activeCoupling]
      module
    have evidenceInputEquality :
        (varyBaseDriveBias parameters direction time).evidenceDrive inputs +
            (varyBaseDriveBias parameters direction time).evidenceCoupling • state.1 =
          line.evidenceInput.curve time := by
      simp [line, equilibriumDetachedLine, varyBaseDriveBias,
        HiddenCurveWitness.constant, Parameters.evidenceDrive,
        Parameters.evidenceCoupling]
    have logitsEquality :
        patchedLogits (varyBaseDriveBias parameters direction time) inputs state.1 =
          line.logitsBase := by
      rfl
    simp only [localEnergy, residualEnergy, activeResidual, evidenceResidual]
    rw [activeInputEquality, evidenceInputEquality, logitsEquality]
    simp [detachedEnergyAlong, line, equilibriumDetachedLine,
      HiddenCurveWitness.affine, HiddenCurveWitness.constant,
      varyBaseDriveBias]
  rw [functionEquality]
  exact derivative

theorem hasDerivAt_evidenceToActive_equilibrium {width actions : ℕ}
    (parameters : Parameters width actions) (inputs : Inputs actions)
    (task : TaskFunctional actions) (frozenAuxiliary : ℝ) (state : State width)
    (direction : PolicyRow actions →L[ℝ] Hidden width) :
    HasDerivAt
      (fun time : ℝ => localEnergy (varyEvidenceToActive parameters direction time)
        inputs task .equilibrium frozenAuxiliary state)
      (detachedParameterDirectionalCredit parameters task state
        (equilibriumDetachedLine parameters inputs state
          (HiddenCurveWitness.affine
            (parameters.activeDrive inputs + parameters.activeCoupling • state.2)
            (direction inputs.normalizedLegalHistogram))
          (HiddenCurveWitness.constant
            (parameters.evidenceDrive inputs + parameters.evidenceCoupling • state.1)) 0)) 0 := by
  let line := equilibriumDetachedLine parameters inputs state
    (HiddenCurveWitness.affine
      (parameters.activeDrive inputs + parameters.activeCoupling • state.2)
      (direction inputs.normalizedLegalHistogram))
    (HiddenCurveWitness.constant
      (parameters.evidenceDrive inputs + parameters.evidenceCoupling • state.1)) 0
  have derivative := hasDerivAt_detachedEnergyAlong parameters task
    frozenAuxiliary state line
  have functionEquality :
      (fun time : ℝ => localEnergy (varyEvidenceToActive parameters direction time)
        inputs task .equilibrium frozenAuxiliary state) =
      detachedEnergyAlong parameters task frozenAuxiliary state line := by
    funext time
    have activeInputEquality :
        (varyEvidenceToActive parameters direction time).activeDrive inputs +
            (varyEvidenceToActive parameters direction time).activeCoupling • state.2 =
          line.activeInput.curve time := by
      simp [line, equilibriumDetachedLine, varyEvidenceToActive,
        HiddenCurveWitness.affine, Parameters.activeDrive,
        Parameters.activeCoupling]
      module
    have evidenceInputEquality :
        (varyEvidenceToActive parameters direction time).evidenceDrive inputs +
            (varyEvidenceToActive parameters direction time).evidenceCoupling • state.1 =
          line.evidenceInput.curve time := by
      simp [line, equilibriumDetachedLine, varyEvidenceToActive,
        HiddenCurveWitness.constant, Parameters.evidenceDrive,
        Parameters.evidenceCoupling]
    have logitsEquality :
        patchedLogits (varyEvidenceToActive parameters direction time) inputs state.1 =
          line.logitsBase := by
      rfl
    simp only [localEnergy, residualEnergy, activeResidual, evidenceResidual]
    rw [activeInputEquality, evidenceInputEquality, logitsEquality]
    simp [detachedEnergyAlong, line, equilibriumDetachedLine,
      HiddenCurveWitness.affine, HiddenCurveWitness.constant,
      varyEvidenceToActive]
  rw [functionEquality]
  exact derivative

def evidenceDriveWeightLine {width actions : ℕ}
    (parameters : Parameters width actions) (inputs : Inputs actions)
    (dynamics : Dynamics) (state : State width)
    (direction : PolicyRow actions →L[ℝ] Hidden width) :
    DetachedEnergyLine width actions :=
  equilibriumDetachedLine parameters inputs state
    (HiddenCurveWitness.constant
      (parameters.activeDrive inputs + parameters.activeCoupling • state.2))
    (HiddenCurveWitness.affine
      (detachedEvidenceInput parameters inputs dynamics state)
      (direction inputs.normalizedLegalHistogram)) 0

theorem hasDerivAt_evidenceDriveWeight {width actions : ℕ}
    (parameters : Parameters width actions) (inputs : Inputs actions)
    (task : TaskFunctional actions) (dynamics : Dynamics)
    (frozenAuxiliary : ℝ) (state : State width)
    (direction : PolicyRow actions →L[ℝ] Hidden width) :
    HasDerivAt
      (fun time : ℝ => localEnergy
        (varyEvidenceDriveWeight parameters direction time)
        inputs task dynamics frozenAuxiliary state)
      (detachedParameterDirectionalCredit parameters task state
        (evidenceDriveWeightLine parameters inputs dynamics state direction)) 0 := by
  apply hasDerivAt_localEnergy_parameterPath parameters inputs task dynamics
    frozenAuxiliary state (varyEvidenceDriveWeight parameters direction)
    (evidenceDriveWeightLine parameters inputs dynamics state direction)
  · intro time
    rfl
  · intro time
    rfl
  · intro time
    simp [evidenceDriveWeightLine, equilibriumDetachedLine,
      HiddenCurveWitness.constant, varyEvidenceDriveWeight,
      Parameters.activeDrive, Parameters.activeCoupling]
  · intro time
    cases dynamics <;>
      simp [detachedEvidenceInput, evidenceDriveWeightLine,
        equilibriumDetachedLine, HiddenCurveWitness.affine,
        varyEvidenceDriveWeight, Parameters.activeDrive,
        Parameters.evidenceDrive, Parameters.evidenceCoupling]
    all_goals module
  · intro time
    simp [evidenceDriveWeightLine, equilibriumDetachedLine,
      varyEvidenceDriveWeight, patchedLogits]

def evidenceDriveBiasLine {width actions : ℕ}
    (parameters : Parameters width actions) (inputs : Inputs actions)
    (dynamics : Dynamics) (state : State width) (direction : Hidden width) :
    DetachedEnergyLine width actions :=
  equilibriumDetachedLine parameters inputs state
    (HiddenCurveWitness.constant
      (parameters.activeDrive inputs + parameters.activeCoupling • state.2))
    (HiddenCurveWitness.affine
      (detachedEvidenceInput parameters inputs dynamics state) direction) 0

theorem hasDerivAt_evidenceDriveBias {width actions : ℕ}
    (parameters : Parameters width actions) (inputs : Inputs actions)
    (task : TaskFunctional actions) (dynamics : Dynamics)
    (frozenAuxiliary : ℝ) (state : State width) (direction : Hidden width) :
    HasDerivAt
      (fun time : ℝ => localEnergy
        (varyEvidenceDriveBias parameters direction time)
        inputs task dynamics frozenAuxiliary state)
      (detachedParameterDirectionalCredit parameters task state
        (evidenceDriveBiasLine parameters inputs dynamics state direction)) 0 := by
  apply hasDerivAt_localEnergy_parameterPath parameters inputs task dynamics
    frozenAuxiliary state (varyEvidenceDriveBias parameters direction)
    (evidenceDriveBiasLine parameters inputs dynamics state direction)
  · intro time
    rfl
  · intro time
    rfl
  · intro time
    simp [evidenceDriveBiasLine, equilibriumDetachedLine,
      HiddenCurveWitness.constant, varyEvidenceDriveBias,
      Parameters.activeDrive, Parameters.activeCoupling]
  · intro time
    cases dynamics <;>
      simp [detachedEvidenceInput, evidenceDriveBiasLine,
        equilibriumDetachedLine, HiddenCurveWitness.affine,
        varyEvidenceDriveBias, Parameters.activeDrive,
        Parameters.evidenceDrive, Parameters.evidenceCoupling]
    all_goals module
  · intro time
    simp [evidenceDriveBiasLine, equilibriumDetachedLine,
      varyEvidenceDriveBias, patchedLogits]

def constantResidualLine {width actions : ℕ}
    (parameters : Parameters width actions) (inputs : Inputs actions)
    (dynamics : Dynamics) (state : State width)
    (logitsDirection : PolicyRow actions) : DetachedEnergyLine width actions :=
  equilibriumDetachedLine parameters inputs state
    (HiddenCurveWitness.constant
      (parameters.activeDrive inputs + parameters.activeCoupling • state.2))
    (HiddenCurveWitness.constant
      (detachedEvidenceInput parameters inputs dynamics state))
    logitsDirection

def outputProjectionLogitsDirection {width actions : ℕ}
    (parameters : Parameters width actions) (inputs : Inputs actions)
    (state : State width) (direction : Hidden width →L[ℝ] PolicyRow actions) :
    PolicyRow actions :=
  maskedReadoutDirection inputs
    (parameters.outputGate • direction state.1)

theorem hasDerivAt_outputProjection {width actions : ℕ}
    (parameters : Parameters width actions) (inputs : Inputs actions)
    (task : TaskFunctional actions) (dynamics : Dynamics)
    (frozenAuxiliary : ℝ) (state : State width)
    (direction : Hidden width →L[ℝ] PolicyRow actions) :
    HasDerivAt
      (fun time : ℝ => localEnergy
        (varyOutputProjection parameters direction time)
        inputs task dynamics frozenAuxiliary state)
      (detachedParameterDirectionalCredit parameters task state
        (constantResidualLine parameters inputs dynamics state
          (outputProjectionLogitsDirection parameters inputs state direction))) 0 := by
  apply hasDerivAt_localEnergy_parameterPath parameters inputs task dynamics
    frozenAuxiliary state (varyOutputProjection parameters direction)
    (constantResidualLine parameters inputs dynamics state
      (outputProjectionLogitsDirection parameters inputs state direction))
  · intro time
    rfl
  · intro time
    rfl
  · intro time
    simp [constantResidualLine, equilibriumDetachedLine,
      HiddenCurveWitness.constant, varyOutputProjection,
      Parameters.activeDrive, Parameters.activeCoupling]
  · intro time
    cases dynamics <;>
      simp [detachedEvidenceInput, constantResidualLine,
        equilibriumDetachedLine, HiddenCurveWitness.constant,
        varyOutputProjection, Parameters.activeDrive,
        Parameters.evidenceDrive, Parameters.evidenceCoupling]
  · intro time
    ext action
    by_cases mutable : action ∈ mutableActions inputs
    · simp [constantResidualLine, equilibriumDetachedLine,
        outputProjectionLogitsDirection, maskedReadoutDirection,
        maskedTaskGradient, patchedLogits, mutable, varyOutputProjection]
      ring
    · simp [constantResidualLine, equilibriumDetachedLine,
        outputProjectionLogitsDirection, maskedReadoutDirection,
        maskedTaskGradient, patchedLogits, mutable, varyOutputProjection]

def outputGateLogitsDirection {width actions : ℕ}
    (parameters : Parameters width actions) (inputs : Inputs actions)
    (state : State width) (direction : ℝ) : PolicyRow actions :=
  maskedReadoutDirection inputs
    (direction • parameters.outputProjection state.1)

theorem hasDerivAt_outputGate {width actions : ℕ}
    (parameters : Parameters width actions) (inputs : Inputs actions)
    (task : TaskFunctional actions) (dynamics : Dynamics)
    (frozenAuxiliary : ℝ) (state : State width) (direction : ℝ) :
    HasDerivAt
      (fun time : ℝ => localEnergy
        (varyOutputGate parameters direction time)
        inputs task dynamics frozenAuxiliary state)
      (detachedParameterDirectionalCredit parameters task state
        (constantResidualLine parameters inputs dynamics state
          (outputGateLogitsDirection parameters inputs state direction))) 0 := by
  apply hasDerivAt_localEnergy_parameterPath parameters inputs task dynamics
    frozenAuxiliary state (varyOutputGate parameters direction)
    (constantResidualLine parameters inputs dynamics state
      (outputGateLogitsDirection parameters inputs state direction))
  · intro time
    rfl
  · intro time
    rfl
  · intro time
    simp [constantResidualLine, equilibriumDetachedLine,
      HiddenCurveWitness.constant, varyOutputGate,
      Parameters.activeDrive, Parameters.activeCoupling]
  · intro time
    cases dynamics <;>
      simp [detachedEvidenceInput, constantResidualLine,
        equilibriumDetachedLine, HiddenCurveWitness.constant,
        varyOutputGate, Parameters.activeDrive,
        Parameters.evidenceDrive, Parameters.evidenceCoupling]
  · intro time
    ext action
    by_cases mutable : action ∈ mutableActions inputs
    · simp [constantResidualLine, equilibriumDetachedLine,
        outputGateLogitsDirection, maskedReadoutDirection,
        maskedTaskGradient, patchedLogits, mutable, varyOutputGate]
      ring
    · simp [constantResidualLine, equilibriumDetachedLine,
        outputGateLogitsDirection, maskedReadoutDirection,
        maskedTaskGradient, patchedLogits, mutable, varyOutputGate]

def rawActiveCouplingLine {width actions : ℕ}
    (parameters : Parameters width actions) (inputs : Inputs actions)
    (dynamics : Dynamics) (state : State width) (direction : ℝ) :
    DetachedEnergyLine width actions :=
  equilibriumDetachedLine parameters inputs state
    (HiddenCurveWitness.add
      (HiddenCurveWitness.constant (parameters.activeDrive inputs))
      (HiddenCurveWitness.rawCoupling parameters.contractionLimit
        parameters.rawActiveCoupling direction state.2))
    (HiddenCurveWitness.constant
      (detachedEvidenceInput parameters inputs dynamics state)) 0

theorem hasDerivAt_rawActiveCoupling {width actions : ℕ}
    (parameters : Parameters width actions) (inputs : Inputs actions)
    (task : TaskFunctional actions) (dynamics : Dynamics)
    (frozenAuxiliary : ℝ) (state : State width) (direction : ℝ) :
    HasDerivAt
      (fun time : ℝ => localEnergy
        (varyRawActiveCoupling parameters direction time)
        inputs task dynamics frozenAuxiliary state)
      (detachedParameterDirectionalCredit parameters task state
        (rawActiveCouplingLine parameters inputs dynamics state direction)) 0 := by
  apply hasDerivAt_localEnergy_parameterPath parameters inputs task dynamics
    frozenAuxiliary state (varyRawActiveCoupling parameters direction)
    (rawActiveCouplingLine parameters inputs dynamics state direction)
  · intro time
    rfl
  · intro time
    rfl
  · intro time
    simp [rawActiveCouplingLine, equilibriumDetachedLine,
      HiddenCurveWitness.add, HiddenCurveWitness.constant,
      HiddenCurveWitness.rawCoupling, varyRawActiveCoupling,
      Parameters.activeDrive, Parameters.activeCoupling]
  · intro time
    cases dynamics <;>
      simp [detachedEvidenceInput, rawActiveCouplingLine,
        equilibriumDetachedLine, HiddenCurveWitness.constant,
        varyRawActiveCoupling, Parameters.activeDrive,
        Parameters.evidenceDrive, Parameters.evidenceCoupling]
  · intro time
    simp [rawActiveCouplingLine, equilibriumDetachedLine,
      varyRawActiveCoupling, patchedLogits]

def rawEvidenceCouplingLine {width actions : ℕ}
    (parameters : Parameters width actions) (inputs : Inputs actions)
    (dynamics : Dynamics) (state : State width) (direction : ℝ) :
    DetachedEnergyLine width actions :=
  equilibriumDetachedLine parameters inputs state
    (HiddenCurveWitness.constant
      (parameters.activeDrive inputs + parameters.activeCoupling • state.2))
    (HiddenCurveWitness.add
      (HiddenCurveWitness.constant (parameters.evidenceDrive inputs))
      (HiddenCurveWitness.rawCoupling parameters.contractionLimit
        parameters.rawEvidenceCoupling direction
        (detachedEvidenceParent parameters inputs dynamics state))) 0

theorem hasDerivAt_rawEvidenceCoupling {width actions : ℕ}
    (parameters : Parameters width actions) (inputs : Inputs actions)
    (task : TaskFunctional actions) (dynamics : Dynamics)
    (frozenAuxiliary : ℝ) (state : State width) (direction : ℝ) :
    HasDerivAt
      (fun time : ℝ => localEnergy
        (varyRawEvidenceCoupling parameters direction time)
        inputs task dynamics frozenAuxiliary state)
      (detachedParameterDirectionalCredit parameters task state
        (rawEvidenceCouplingLine parameters inputs dynamics state direction)) 0 := by
  apply hasDerivAt_localEnergy_parameterPath parameters inputs task dynamics
    frozenAuxiliary state (varyRawEvidenceCoupling parameters direction)
    (rawEvidenceCouplingLine parameters inputs dynamics state direction)
  · intro time
    rfl
  · intro time
    rfl
  · intro time
    simp [rawEvidenceCouplingLine, equilibriumDetachedLine,
      HiddenCurveWitness.constant, varyRawEvidenceCoupling,
      Parameters.activeDrive, Parameters.activeCoupling]
  · intro time
    cases dynamics <;>
      simp [detachedEvidenceInput, detachedEvidenceParent,
        rawEvidenceCouplingLine, equilibriumDetachedLine,
        HiddenCurveWitness.add, HiddenCurveWitness.constant,
        HiddenCurveWitness.rawCoupling, varyRawEvidenceCoupling,
        Parameters.activeDrive, Parameters.evidenceDrive,
        Parameters.evidenceCoupling]
  · intro time
    simp [rawEvidenceCouplingLine, equilibriumDetachedLine,
      varyRawEvidenceCoupling, patchedLogits]

def activeDriveFeedforwardLine {width actions : ℕ}
    (parameters : Parameters width actions) (inputs : Inputs actions)
    (state : State width) (direction : Hidden width) :
    DetachedEnergyLine width actions :=
  equilibriumDetachedLine parameters inputs state
    (HiddenCurveWitness.affine
      (parameters.activeDrive inputs + parameters.activeCoupling • state.2)
      direction)
    (HiddenCurveWitness.add
      (HiddenCurveWitness.constant (parameters.evidenceDrive inputs))
      (HiddenCurveWitness.smul parameters.evidenceCoupling
        (HiddenCurveWitness.tanhAffine (parameters.activeDrive inputs) direction))) 0

theorem hasDerivAt_baseDriveWeight_feedforward {width actions : ℕ}
    (parameters : Parameters width actions) (inputs : Inputs actions)
    (task : TaskFunctional actions) (frozenAuxiliary : ℝ)
    (state : State width)
    (direction : PolicyRow actions →L[ℝ] Hidden width) :
    HasDerivAt
      (fun time : ℝ => localEnergy
        (varyBaseDriveWeight parameters direction time)
        inputs task .feedforward frozenAuxiliary state)
      (detachedParameterDirectionalCredit parameters task state
        (activeDriveFeedforwardLine parameters inputs state
          (direction inputs.maskedBaseDistribution))) 0 := by
  apply hasDerivAt_localEnergy_parameterPath parameters inputs task .feedforward
    frozenAuxiliary state (varyBaseDriveWeight parameters direction)
    (activeDriveFeedforwardLine parameters inputs state
      (direction inputs.maskedBaseDistribution))
  · intro time
    rfl
  · intro time
    rfl
  · intro time
    simp [activeDriveFeedforwardLine, equilibriumDetachedLine,
      HiddenCurveWitness.affine, varyBaseDriveWeight,
      Parameters.activeDrive, Parameters.activeCoupling]
    module
  · intro time
    simp [detachedEvidenceInput, activeDriveFeedforwardLine,
      equilibriumDetachedLine, HiddenCurveWitness.add,
      HiddenCurveWitness.constant, HiddenCurveWitness.smul,
      HiddenCurveWitness.tanhAffine, varyBaseDriveWeight,
      Parameters.activeDrive, Parameters.evidenceDrive,
      Parameters.evidenceCoupling]
    apply congrArg (fun value : Hidden width =>
      parameters.evidenceCoupling • coordinateTanh value)
    module
  · intro time
    simp [activeDriveFeedforwardLine, equilibriumDetachedLine,
      varyBaseDriveWeight, patchedLogits]

theorem hasDerivAt_baseDriveBias_feedforward {width actions : ℕ}
    (parameters : Parameters width actions) (inputs : Inputs actions)
    (task : TaskFunctional actions) (frozenAuxiliary : ℝ)
    (state : State width) (direction : Hidden width) :
    HasDerivAt
      (fun time : ℝ => localEnergy
        (varyBaseDriveBias parameters direction time)
        inputs task .feedforward frozenAuxiliary state)
      (detachedParameterDirectionalCredit parameters task state
        (activeDriveFeedforwardLine parameters inputs state direction)) 0 := by
  apply hasDerivAt_localEnergy_parameterPath parameters inputs task .feedforward
    frozenAuxiliary state (varyBaseDriveBias parameters direction)
    (activeDriveFeedforwardLine parameters inputs state direction)
  · intro time
    rfl
  · intro time
    rfl
  · intro time
    simp [activeDriveFeedforwardLine, equilibriumDetachedLine,
      HiddenCurveWitness.affine, varyBaseDriveBias,
      Parameters.activeDrive, Parameters.activeCoupling]
    module
  · intro time
    simp [detachedEvidenceInput, activeDriveFeedforwardLine,
      equilibriumDetachedLine, HiddenCurveWitness.add,
      HiddenCurveWitness.constant, HiddenCurveWitness.smul,
      HiddenCurveWitness.tanhAffine, varyBaseDriveBias,
      Parameters.activeDrive, Parameters.evidenceDrive,
      Parameters.evidenceCoupling]
    apply congrArg (fun value : Hidden width =>
      parameters.evidenceCoupling • coordinateTanh value)
    module
  · intro time
    simp [activeDriveFeedforwardLine, equilibriumDetachedLine,
      varyBaseDriveBias, patchedLogits]

theorem hasDerivAt_evidenceToActive_feedforward {width actions : ℕ}
    (parameters : Parameters width actions) (inputs : Inputs actions)
    (task : TaskFunctional actions) (frozenAuxiliary : ℝ)
    (state : State width)
    (direction : PolicyRow actions →L[ℝ] Hidden width) :
    HasDerivAt
      (fun time : ℝ => localEnergy
        (varyEvidenceToActive parameters direction time)
        inputs task .feedforward frozenAuxiliary state)
      (detachedParameterDirectionalCredit parameters task state
        (activeDriveFeedforwardLine parameters inputs state
          (direction inputs.normalizedLegalHistogram))) 0 := by
  apply hasDerivAt_localEnergy_parameterPath parameters inputs task .feedforward
    frozenAuxiliary state (varyEvidenceToActive parameters direction)
    (activeDriveFeedforwardLine parameters inputs state
      (direction inputs.normalizedLegalHistogram))
  · intro time
    rfl
  · intro time
    rfl
  · intro time
    simp [activeDriveFeedforwardLine, equilibriumDetachedLine,
      HiddenCurveWitness.affine, varyEvidenceToActive,
      Parameters.activeDrive, Parameters.activeCoupling]
    module
  · intro time
    simp [detachedEvidenceInput, activeDriveFeedforwardLine,
      equilibriumDetachedLine, HiddenCurveWitness.add,
      HiddenCurveWitness.constant, HiddenCurveWitness.smul,
      HiddenCurveWitness.tanhAffine, varyEvidenceToActive,
      Parameters.activeDrive, Parameters.evidenceDrive,
      Parameters.evidenceCoupling]
    apply congrArg (fun value : Hidden width =>
      parameters.evidenceCoupling • coordinateTanh value)
    module
  · intro time
    simp [activeDriveFeedforwardLine, equilibriumDetachedLine,
      varyEvidenceToActive, patchedLogits]

theorem width32_baseDriveBias_credit_positive :
    0 < detachedParameterDirectionalCredit width32NonzeroParameters
      (zeroTaskFunctional 2) (0, 0)
      (equilibriumDetachedLine width32NonzeroParameters width32ZeroInputs (0, 0)
        (HiddenCurveWitness.affine
          (width32NonzeroParameters.activeDrive width32ZeroInputs +
            width32NonzeroParameters.activeCoupling • (0 : Hidden 32))
          width32Impulse)
        (HiddenCurveWitness.constant
          (width32NonzeroParameters.evidenceDrive width32ZeroInputs +
            width32NonzeroParameters.evidenceCoupling • (0 : Hidden 32))) 0) := by
  simp [detachedParameterDirectionalCredit, equilibriumDetachedLine,
    HiddenCurveWitness.affine, HiddenCurveWitness.constant,
    width32NonzeroParameters, width32ZeroParameters, width32ZeroInputs,
    width32Impulse, zeroTaskFunctional, Parameters.activeDrive,
    Parameters.evidenceDrive, Parameters.activeCoupling,
    Parameters.evidenceCoupling, coordinateTanh, coordinateTanhSlope,
    tanhSlope, PiLp.inner_apply, RCLike.inner_apply]
  have tanhPositive : 0 < Real.tanh (1 : ℝ) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    positivity
  positivity

#print axioms hasDerivAt_detachedEnergyAlong
#print axioms hasDerivAt_batchDetachedEnergyAlong
#print axioms hasDerivAt_routedBatch_parameterPath
#print axioms hasDerivAt_baseDriveWeight_equilibrium
#print axioms hasDerivAt_baseDriveBias_equilibrium
#print axioms hasDerivAt_evidenceToActive_equilibrium
#print axioms hasDerivAt_evidenceDriveWeight
#print axioms hasDerivAt_evidenceDriveBias
#print axioms hasDerivAt_outputProjection
#print axioms hasDerivAt_outputGate
#print axioms hasDerivAt_rawActiveCoupling
#print axioms hasDerivAt_rawEvidenceCoupling
#print axioms hasDerivAt_baseDriveWeight_feedforward
#print axioms hasDerivAt_baseDriveBias_feedforward
#print axioms hasDerivAt_evidenceToActive_feedforward
#print axioms width32_baseDriveBias_credit_positive

end
end ActionMemoryNonlinearVectorPC
end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
