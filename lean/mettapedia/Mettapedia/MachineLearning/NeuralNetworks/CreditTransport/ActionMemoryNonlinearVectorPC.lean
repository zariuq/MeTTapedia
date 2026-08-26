import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.ActionMemoryVectorPC
import Mathlib.Analysis.Calculus.FDeriv.WithLp

/-!
# Exact nonlinear vector local predictive coding for action memory

This module models the nonlinear two-node reasoner rather than the older
linear-quadratic surrogate.  Hidden and policy rows are finite Euclidean
spaces; the dense maps are continuous linear maps; both recurrent couplings
are bounded scalar `tanh` parameters; and the state transition applies
coordinatewise `tanh` followed by simultaneous damping.

The task boundary is explicit.  Only routed-and-legal logits are mutable, and
a differentiable task functional supplies the derivative of the registered
information objective at that exact patched row.  Slow-parameter credit is the
partial derivative of the same residual-plus-task energy with the settled
states held fixed.  Finite state settling remains distinct from the unique
forward-map equilibrium.

This is exact-real theory.  It makes no claim about a Python execution or a
floating-point fixture.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
namespace ActionMemoryNonlinearVectorPC

noncomputable section

open scoped InnerProductSpace
open InnerProduct
open ActionMemoryLocalPC

local instance (priority := 2000) nonlinearVectorRealModule : Module ℝ ℝ :=
  RCLike.toInnerProductSpaceReal.toModule

abbrev ExactRealHasDerivAt (function : ℝ → ℝ)
    (derivative point : ℝ) : Prop :=
  @HasDerivAt ℝ inferInstance ℝ
    Real.normedAddCommGroup.toAddCommGroup
    RCLike.toInnerProductSpaceReal.toModule inferInstance inferInstance
    function derivative point

abbrev ExactRealDeriv (function : ℝ → ℝ) (point : ℝ) : ℝ :=
  @deriv ℝ inferInstance ℝ Real.normedAddCommGroup.toAddCommGroup
    RCLike.toInnerProductSpaceReal.toModule inferInstance function point

universe uA

abbrev Hidden (width : ℕ) := PiLp 2 (fun _ : Fin width => ℝ)
abbrev PolicyRow (actions : ℕ) := PiLp 2 (fun _ : Fin actions => ℝ)
abbrev State (width : ℕ) := Hidden width × Hidden width

/-! ## Coordinatewise nonlinearity -/

def coordinateTanh {width : ℕ} (value : Hidden width) : Hidden width :=
  WithLp.toLp 2 fun coordinate => Real.tanh (value coordinate)

def coordinateTanhSlope {width : ℕ} (value direction : Hidden width) :
    Hidden width :=
  WithLp.toLp 2 fun coordinate =>
    tanhSlope (value coordinate) * direction coordinate

@[simp] theorem coordinateTanh_apply {width : ℕ} (value : Hidden width)
    (coordinate : Fin width) :
    coordinateTanh value coordinate = Real.tanh (value coordinate) := by
  rfl

@[simp] theorem coordinateTanhSlope_apply {width : ℕ}
    (value direction : Hidden width) (coordinate : Fin width) :
    coordinateTanhSlope value direction coordinate =
      tanhSlope (value coordinate) * direction coordinate := by
  rfl

theorem coordinateTanh_sub_norm_le {width : ℕ}
    (left right : Hidden width) :
    ‖coordinateTanh left - coordinateTanh right‖ ≤ ‖left - right‖ := by
  have coordinateBound : ∀ coordinate : Fin width,
      |(coordinateTanh left - coordinateTanh right) coordinate| ^ 2 ≤
        |(left - right) coordinate| ^ 2 := by
    intro coordinate
    have bound := tanh_sub_le (left coordinate) (right coordinate)
    exact (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).2 bound
  have sumBound :
      ∑ coordinate : Fin width,
          |(coordinateTanh left - coordinateTanh right) coordinate| ^ 2 ≤
        ∑ coordinate : Fin width, |(left - right) coordinate| ^ 2 :=
    Finset.sum_le_sum fun coordinate _ => coordinateBound coordinate
  have squareBound :
      ‖coordinateTanh left - coordinateTanh right‖ ^ 2 ≤
        ‖left - right‖ ^ 2 := by
    simpa [EuclideanSpace.real_norm_sq_eq, sq_abs] using sumBound
  nlinarith [norm_nonneg (coordinateTanh left - coordinateTanh right),
    norm_nonneg (left - right)]

/-! ## Exact parameterization and forward maps -/

structure Parameters (width actions : ℕ) where
  baseDriveWeight : PolicyRow actions →L[ℝ] Hidden width
  baseDriveBias : Hidden width
  evidenceToActive : PolicyRow actions →L[ℝ] Hidden width
  evidenceDriveWeight : PolicyRow actions →L[ℝ] Hidden width
  evidenceDriveBias : Hidden width
  outputProjection : Hidden width →L[ℝ] PolicyRow actions
  outputGate : ℝ
  rawActiveCoupling : ℝ
  rawEvidenceCoupling : ℝ
  contractionLimit : ℝ
  damping : ℝ
  finiteDepth : ℕ
  residualPrecision : ℝ
  taskPrecision : ℝ

structure Inputs (actions : ℕ) where
  maskedBaseDistribution : PolicyRow actions
  normalizedLegalHistogram : PolicyRow actions
  baseLogits : PolicyRow actions
  routed : Finset (Fin actions)
  legal : Finset (Fin actions)

def Parameters.activeCoupling {width actions : ℕ}
    (parameters : Parameters width actions) : ℝ :=
  parameters.contractionLimit * Real.tanh parameters.rawActiveCoupling

def Parameters.evidenceCoupling {width actions : ℕ}
    (parameters : Parameters width actions) : ℝ :=
  parameters.contractionLimit * Real.tanh parameters.rawEvidenceCoupling

def Parameters.activeDrive {width actions : ℕ}
    (parameters : Parameters width actions) (inputs : Inputs actions) :
    Hidden width :=
  parameters.baseDriveWeight inputs.maskedBaseDistribution +
    parameters.baseDriveBias +
    parameters.evidenceToActive inputs.normalizedLegalHistogram

def Parameters.evidenceDrive {width actions : ℕ}
    (parameters : Parameters width actions) (inputs : Inputs actions) :
    Hidden width :=
  parameters.evidenceDriveWeight inputs.normalizedLegalHistogram +
    parameters.evidenceDriveBias

def candidateMap {width actions : ℕ}
    (parameters : Parameters width actions) (inputs : Inputs actions)
    (state : State width) : State width :=
  (coordinateTanh (parameters.activeDrive inputs +
      parameters.activeCoupling • state.2),
    coordinateTanh (parameters.evidenceDrive inputs +
      parameters.evidenceCoupling • state.1))

def dampedMap {width actions : ℕ}
    (parameters : Parameters width actions) (inputs : Inputs actions)
    (state : State width) : State width :=
  let candidate := candidateMap parameters inputs state
  ((1 - parameters.damping) • state.1 + parameters.damping • candidate.1,
    (1 - parameters.damping) • state.2 + parameters.damping • candidate.2)

def initialState {width actions : ℕ}
    (parameters : Parameters width actions) (inputs : Inputs actions) :
    State width :=
  (coordinateTanh (parameters.activeDrive inputs),
    coordinateTanh (parameters.evidenceDrive inputs))

/-- Capacity-matched acyclic branch: evidence reads `tanh(activeDrive)` and
the final active state reads that evidence. -/
def feedforwardState {width actions : ℕ}
    (parameters : Parameters width actions) (inputs : Inputs actions) :
    State width :=
  let initialActive := coordinateTanh (parameters.activeDrive inputs)
  let evidence := coordinateTanh (parameters.evidenceDrive inputs +
    parameters.evidenceCoupling • initialActive)
  (coordinateTanh (parameters.activeDrive inputs +
    parameters.activeCoupling • evidence), evidence)

def iterateState {width actions : ℕ}
    (parameters : Parameters width actions) (inputs : Inputs actions) :
    ℕ → State width → State width
  | 0, state => state
  | steps + 1, state =>
      iterateState parameters inputs steps (dampedMap parameters inputs state)

def finiteEquilibriumState {width actions : ℕ}
    (parameters : Parameters width actions) (inputs : Inputs actions) :
    State width :=
  iterateState parameters inputs parameters.finiteDepth
    (initialState parameters inputs)

/-! ## Width-independent nonlinear contraction -/

def blockDistance {width : ℕ} (left right : State width) : ℝ :=
  max ‖left.1 - right.1‖ ‖left.2 - right.2‖

def couplingFactor {width actions : ℕ} (parameters : Parameters width actions) : ℝ :=
  max |parameters.activeCoupling| |parameters.evidenceCoupling|

def dampedFactor {width actions : ℕ} (parameters : Parameters width actions) : ℝ :=
  1 - parameters.damping + parameters.damping * couplingFactor parameters

theorem candidateMap_contracts {width actions : ℕ}
    (parameters : Parameters width actions) (inputs : Inputs actions)
    (left right : State width) :
    blockDistance (candidateMap parameters inputs left)
        (candidateMap parameters inputs right) ≤
      couplingFactor parameters * blockDistance left right := by
  apply max_le
  · calc
      _ ≤ ‖(parameters.activeDrive inputs + parameters.activeCoupling • left.2) -
          (parameters.activeDrive inputs + parameters.activeCoupling • right.2)‖ :=
        coordinateTanh_sub_norm_le _ _
      _ = |parameters.activeCoupling| * ‖left.2 - right.2‖ := by
        rw [show (parameters.activeDrive inputs + parameters.activeCoupling • left.2) -
            (parameters.activeDrive inputs + parameters.activeCoupling • right.2) =
            parameters.activeCoupling • (left.2 - right.2) by module,
          norm_smul, Real.norm_eq_abs]
      _ ≤ couplingFactor parameters * blockDistance left right := by
        calc
          _ ≤ couplingFactor parameters * ‖left.2 - right.2‖ :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
          _ ≤ couplingFactor parameters * blockDistance left right :=
            mul_le_mul_of_nonneg_left (le_max_right _ _)
              ((abs_nonneg _).trans (le_max_left _ _))
  · calc
      _ ≤ ‖(parameters.evidenceDrive inputs + parameters.evidenceCoupling • left.1) -
          (parameters.evidenceDrive inputs + parameters.evidenceCoupling • right.1)‖ :=
        coordinateTanh_sub_norm_le _ _
      _ = |parameters.evidenceCoupling| * ‖left.1 - right.1‖ := by
        rw [show (parameters.evidenceDrive inputs + parameters.evidenceCoupling • left.1) -
            (parameters.evidenceDrive inputs + parameters.evidenceCoupling • right.1) =
            parameters.evidenceCoupling • (left.1 - right.1) by module,
          norm_smul, Real.norm_eq_abs]
      _ ≤ couplingFactor parameters * blockDistance left right := by
        calc
          _ ≤ couplingFactor parameters * ‖left.1 - right.1‖ :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
          _ ≤ couplingFactor parameters * blockDistance left right :=
            mul_le_mul_of_nonneg_left (le_max_left _ _)
              ((abs_nonneg _).trans (le_max_left _ _))

theorem dampedMap_contracts {width actions : ℕ}
    (parameters : Parameters width actions) (inputs : Inputs actions)
    (hdamping0 : 0 ≤ parameters.damping)
    (hdamping1 : parameters.damping ≤ 1)
    (left right : State width) :
    blockDistance (dampedMap parameters inputs left)
        (dampedMap parameters inputs right) ≤
      dampedFactor parameters * blockDistance left right := by
  have candidateBound := candidateMap_contracts parameters inputs left right
  have couplingNonnegative : 0 ≤ couplingFactor parameters :=
    (abs_nonneg _).trans (le_max_left _ _)
  apply max_le
  · calc
      _ ≤ ‖(1 - parameters.damping) • (left.1 - right.1)‖ +
          ‖parameters.damping •
            ((candidateMap parameters inputs left).1 -
              (candidateMap parameters inputs right).1)‖ := by
        simpa [dampedMap, sub_eq_add_neg, add_assoc, add_left_comm,
          add_comm, smul_add, smul_neg] using
          norm_add_le ((1 - parameters.damping) • (left.1 - right.1))
            (parameters.damping • ((candidateMap parameters inputs left).1 -
              (candidateMap parameters inputs right).1))
      _ ≤ (1 - parameters.damping) * blockDistance left right +
          parameters.damping *
            (couplingFactor parameters * blockDistance left right) := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg hdamping0, abs_of_nonneg (sub_nonneg.mpr hdamping1)]
        gcongr
        · exact le_max_left _ _
        · exact (le_max_left _ _).trans candidateBound
      _ = dampedFactor parameters * blockDistance left right := by
        simp [dampedFactor]
        ring
  · calc
      _ ≤ ‖(1 - parameters.damping) • (left.2 - right.2)‖ +
          ‖parameters.damping •
            ((candidateMap parameters inputs left).2 -
              (candidateMap parameters inputs right).2)‖ := by
        simpa [dampedMap, sub_eq_add_neg, add_assoc, add_left_comm,
          add_comm, smul_add, smul_neg] using
          norm_add_le ((1 - parameters.damping) • (left.2 - right.2))
            (parameters.damping • ((candidateMap parameters inputs left).2 -
              (candidateMap parameters inputs right).2))
      _ ≤ (1 - parameters.damping) * blockDistance left right +
          parameters.damping *
            (couplingFactor parameters * blockDistance left right) := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg hdamping0, abs_of_nonneg (sub_nonneg.mpr hdamping1)]
        gcongr
        · exact le_max_right _ _
        · exact (le_max_right _ _).trans candidateBound
      _ = dampedFactor parameters * blockDistance left right := by
        simp [dampedFactor]
        ring

theorem dampedMap_contracting {width actions : ℕ}
    (parameters : Parameters width actions) (inputs : Inputs actions)
    (hdamping0 : 0 ≤ parameters.damping)
    (hdamping1 : parameters.damping ≤ 1)
    (hfactor0 : 0 ≤ dampedFactor parameters)
    (hfactor1 : dampedFactor parameters < 1) :
    ContractingWith ⟨dampedFactor parameters, hfactor0⟩
      (dampedMap parameters inputs) := by
  constructor
  · exact_mod_cast hfactor1
  · apply LipschitzWith.of_dist_le_mul
    intro left right
    change dist (dampedMap parameters inputs left)
        (dampedMap parameters inputs right) ≤
      dampedFactor parameters * dist left right
    simpa [Prod.dist_eq, dist_eq_norm, Prod.norm_def, blockDistance] using
      dampedMap_contracts parameters inputs hdamping0 hdamping1 left right

theorem dampedMap_existsUnique_equilibrium {width actions : ℕ}
    (parameters : Parameters width actions) (inputs : Inputs actions)
    (hdamping0 : 0 ≤ parameters.damping)
    (hdamping1 : parameters.damping ≤ 1)
    (hfactor0 : 0 ≤ dampedFactor parameters)
    (hfactor1 : dampedFactor parameters < 1) :
    ∃! state : State width, dampedMap parameters inputs state = state := by
  let factor : NNReal := ⟨dampedFactor parameters, hfactor0⟩
  have contracting : ContractingWith factor (dampedMap parameters inputs) :=
    dampedMap_contracting parameters inputs hdamping0 hdamping1 hfactor0 hfactor1
  obtain ⟨target, fixed, _converges, _bound⟩ :=
    contracting.exists_fixedPoint (0, 0) (edist_ne_top _ _)
  exact ⟨target, fixed, fun other otherFixed =>
    contracting.fixedPoint_unique' otherFixed fixed⟩

theorem effectiveCoupling_abs_lt_limit {width actions : ℕ}
    (parameters : Parameters width actions) (limitPositive : 0 < parameters.contractionLimit) :
    |parameters.activeCoupling| < parameters.contractionLimit ∧
      |parameters.evidenceCoupling| < parameters.contractionLimit := by
  constructor
  · simpa [Parameters.activeCoupling] using
      (boundedCoupling_lt (limit := parameters.contractionLimit)
        (raw := parameters.rawActiveCoupling) limitPositive)
  · simpa [Parameters.evidenceCoupling] using
      (boundedCoupling_lt (limit := parameters.contractionLimit)
        (raw := parameters.rawEvidenceCoupling) limitPositive)

/-! ## Exact residuals, patched readout, and task interface -/

inductive Dynamics where
  | feedforward
  | equilibrium
deriving DecidableEq

def activeResidual {width actions : ℕ}
    (parameters : Parameters width actions) (inputs : Inputs actions)
    (state : State width) : Hidden width :=
  state.1 - coordinateTanh (parameters.activeDrive inputs +
    parameters.activeCoupling • state.2)

def evidenceResidual {width actions : ℕ}
    (parameters : Parameters width actions) (inputs : Inputs actions)
    (dynamics : Dynamics) (state : State width) : Hidden width :=
  match dynamics with
  | .equilibrium =>
      state.2 - coordinateTanh (parameters.evidenceDrive inputs +
        parameters.evidenceCoupling • state.1)
  | .feedforward =>
      state.2 - coordinateTanh (parameters.evidenceDrive inputs +
        parameters.evidenceCoupling •
          coordinateTanh (parameters.activeDrive inputs))

def mutableActions {actions : ℕ} (inputs : Inputs actions) : Finset (Fin actions) :=
  inputs.routed ∩ inputs.legal

def patchedLogits {width actions : ℕ}
    (parameters : Parameters width actions) (inputs : Inputs actions)
    (active : Hidden width) : PolicyRow actions :=
  WithLp.toLp 2 fun action =>
    if action ∈ mutableActions inputs then
      inputs.baseLogits action +
        parameters.outputGate * parameters.outputProjection active action
    else inputs.baseLogits action

@[simp] theorem patchedLogits_outside_mutable {width actions : ℕ}
    (parameters : Parameters width actions) (inputs : Inputs actions)
    (active : Hidden width) (action : Fin actions)
    (outside : action ∉ mutableActions inputs) :
    patchedLogits parameters inputs active action = inputs.baseLogits action := by
  simp [patchedLogits, outside]

@[simp] theorem patchedLogits_illegal_eq_base {width actions : ℕ}
    (parameters : Parameters width actions) (inputs : Inputs actions)
    (active : Hidden width) (action : Fin actions)
    (illegal : action ∉ inputs.legal) :
    patchedLogits parameters inputs active action = inputs.baseLogits action := by
  apply patchedLogits_outside_mutable
  intro mutable
  exact illegal (Finset.mem_of_mem_inter_right mutable)

@[simp] theorem patchedLogits_unrouted_eq_base {width actions : ℕ}
    (parameters : Parameters width actions) (inputs : Inputs actions)
    (active : Hidden width) (action : Fin actions)
    (unrouted : action ∉ inputs.routed) :
    patchedLogits parameters inputs active action = inputs.baseLogits action := by
  apply patchedLogits_outside_mutable
  intro mutable
  exact unrouted (Finset.mem_of_mem_inter_left mutable)

@[simp] theorem patchedLogits_gate_zero {width actions : ℕ}
    (parameters : Parameters width actions) (inputs : Inputs actions)
    (active : Hidden width) (gateZero : parameters.outputGate = 0) :
    patchedLogits parameters inputs active = inputs.baseLogits := by
  ext action
  simp [patchedLogits, gateZero]

def maskedProbability {actions : ℕ}
    (legal : Finset (Fin actions)) (logits : PolicyRow actions)
    (action : Fin actions) : ℝ :=
  if action ∈ legal then
    Real.exp (logits action) /
      ∑ candidate ∈ legal, Real.exp (logits candidate)
  else 0

@[simp] theorem maskedProbability_illegal {actions : ℕ}
    (legal : Finset (Fin actions)) (logits : PolicyRow actions)
    (action : Fin actions) (illegal : action ∉ legal) :
    maskedProbability legal logits action = 0 := by
  simp [maskedProbability, illegal]

/-- A task functional with an exact Euclidean gradient at every policy row. -/
structure TaskFunctional (actions : ℕ) where
  value : PolicyRow actions → ℝ
  gradient : PolicyRow actions → PolicyRow actions
  directionalDerivative : ∀ logits direction,
    HasDerivAt (fun time : ℝ => value (logits + time • direction))
      ⟪gradient logits, direction⟫_ℝ 0

def residualEnergy {width actions : ℕ}
    (parameters : Parameters width actions) (inputs : Inputs actions)
    (dynamics : Dynamics) (state : State width) : ℝ :=
  parameters.residualPrecision / 2 * ‖activeResidual parameters inputs state‖ ^ 2 +
    parameters.residualPrecision / 2 *
      ‖evidenceResidual parameters inputs dynamics state‖ ^ 2

def localEnergy {width actions : ℕ}
    (parameters : Parameters width actions) (inputs : Inputs actions)
    (task : TaskFunctional actions) (dynamics : Dynamics)
    (frozenAuxiliary : ℝ) (state : State width) : ℝ :=
  residualEnergy parameters inputs dynamics state +
    parameters.taskPrecision * task.value (patchedLogits parameters inputs state.1) +
    frozenAuxiliary

theorem frozenAuxiliary_has_zero_local_derivative
    (frozenAuxiliary : ℝ) :
    HasDerivAt (fun _time : ℝ => frozenAuxiliary) 0 0 := by
  exact hasDerivAt_const (x := (0 : ℝ)) frozenAuxiliary

/-! ## Exact state gradients -/

def maskedTaskGradient {actions : ℕ} (inputs : Inputs actions)
    (gradient : PolicyRow actions) : PolicyRow actions :=
  WithLp.toLp 2 fun action =>
    if action ∈ mutableActions inputs then gradient action else 0

@[simp] theorem maskedTaskGradient_illegal {actions : ℕ}
    (inputs : Inputs actions) (gradient : PolicyRow actions)
    (action : Fin actions) (illegal : action ∉ inputs.legal) :
    maskedTaskGradient inputs gradient action = 0 := by
  simp only [maskedTaskGradient, PiLp.toLp_apply]
  split
  · rename_i mutable
    exact False.elim (illegal (Finset.mem_of_mem_inter_right mutable))
  · rfl

@[simp] theorem maskedTaskGradient_unrouted {actions : ℕ}
    (inputs : Inputs actions) (gradient : PolicyRow actions)
    (action : Fin actions) (unrouted : action ∉ inputs.routed) :
    maskedTaskGradient inputs gradient action = 0 := by
  simp only [maskedTaskGradient, PiLp.toLp_apply]
  split
  · rename_i mutable
    exact False.elim (unrouted (Finset.mem_of_mem_inter_left mutable))
  · rfl

theorem inner_maskedTaskGradient {actions : ℕ} (inputs : Inputs actions)
    (left right : PolicyRow actions) :
    ⟪left, maskedTaskGradient inputs right⟫_ℝ =
      ⟪maskedTaskGradient inputs left, right⟫_ℝ := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro action _
  by_cases mutable : action ∈ mutableActions inputs <;>
    simp [maskedTaskGradient, mutable, RCLike.inner_apply]

theorem coordinateTanhSlope_smul {width : ℕ} (value direction : Hidden width)
    (scalar : ℝ) :
    coordinateTanhSlope value (scalar • direction) =
      scalar • coordinateTanhSlope value direction := by
  ext coordinate
  simp [coordinateTanhSlope]
  ring

theorem inner_coordinateTanhSlope_comm {width : ℕ}
    (value left right : Hidden width) :
    ⟪left, coordinateTanhSlope value right⟫_ℝ =
      ⟪coordinateTanhSlope value left, right⟫_ℝ := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro coordinate _
  simp [coordinateTanhSlope, RCLike.inner_apply]
  ring

def activeStateGradient {width actions : ℕ}
    (parameters : Parameters width actions) (inputs : Inputs actions)
    (task : TaskFunctional actions) (dynamics : Dynamics)
    (state : State width) : Hidden width :=
  let evidenceInput := parameters.evidenceDrive inputs +
    parameters.evidenceCoupling • state.1
  let evidenceBack := coordinateTanhSlope evidenceInput
    (evidenceResidual parameters inputs dynamics state)
  let taskBack := parameters.outputProjection.adjoint
    (maskedTaskGradient inputs
      (task.gradient (patchedLogits parameters inputs state.1)))
  match dynamics with
  | .equilibrium =>
      parameters.residualPrecision •
          (activeResidual parameters inputs state -
            parameters.evidenceCoupling • evidenceBack) +
        (parameters.taskPrecision * parameters.outputGate) • taskBack
  | .feedforward =>
      parameters.residualPrecision • activeResidual parameters inputs state +
        (parameters.taskPrecision * parameters.outputGate) • taskBack

def evidenceStateGradient {width actions : ℕ}
    (parameters : Parameters width actions) (inputs : Inputs actions)
    (dynamics : Dynamics) (state : State width) : Hidden width :=
  let activeInput := parameters.activeDrive inputs +
    parameters.activeCoupling • state.2
  parameters.residualPrecision •
    (evidenceResidual parameters inputs dynamics state -
      parameters.activeCoupling • coordinateTanhSlope activeInput
        (activeResidual parameters inputs state))

private theorem hasDerivAt_weightedNormSq_line {width : ℕ}
    (precision : ℝ) (residual derivative : Hidden width) :
    HasDerivAt
      (fun time : ℝ => precision / 2 * ‖residual + time • derivative‖ ^ 2)
      (precision * ⟪residual, derivative⟫_ℝ) 0 := by
  have line : HasDerivAt (fun time : ℝ => residual + time • derivative)
      derivative 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const derivative).const_add residual
  have weighted := line.norm_sq.const_mul (precision / 2)
  apply weighted.congr_deriv
  simp only [zero_smul, add_zero]
  ring

theorem hasDerivAt_tanhExact (input : ℝ) :
    ExactRealHasDerivAt Real.tanh (tanhSlope input) input := by
  simpa [tanhSlope] using ActionMemoryLocalPC.hasDerivAt_tanh input

/-- Directional derivative of a precision-weighted nonlinear residual norm.
The `state` argument is held fixed while the prediction input moves. -/
theorem hasDerivAt_weightedTanhResidualLine {width : ℕ}
    (precision : ℝ) (state input inputDirection : Hidden width) :
    ExactRealHasDerivAt
      (fun time : ℝ => precision / 2 *
        ‖state - coordinateTanh (input + time • inputDirection)‖ ^ 2)
      (precision *
        ⟪state - coordinateTanh input,
          -(coordinateTanhSlope input inputDirection)⟫_ℝ) 0 := by
  let coordinateDerivative := fun coordinate : Fin width =>
    (((hasDerivAt_const (x := (0 : ℝ)) (state coordinate)).sub
      ((hasDerivAt_tanhExact
        (input coordinate + 0 * inputDirection coordinate)).comp 0
        (((hasDerivAt_id (0 : ℝ)).mul_const
          (inputDirection coordinate)).const_add (input coordinate)))).pow 2)
  have sumDerivative := HasDerivAt.fun_sum
    (u := Finset.univ) (fun coordinate _ => coordinateDerivative coordinate)
  have weighted := sumDerivative.const_mul (precision / 2)
  have functionEquality :
      (fun time : ℝ => precision / 2 *
        ‖state - coordinateTanh (input + time • inputDirection)‖ ^ 2) =
      (fun time : ℝ => precision / 2 *
        ∑ coordinate : Fin width,
          (state coordinate -
            Real.tanh (input coordinate + time * inputDirection coordinate)) ^ 2) := by
    funext time
    rw [EuclideanSpace.real_norm_sq_eq]
    rfl
  rw [functionEquality]
  convert weighted.congr_deriv ?_ using 1 <;>
    simp only [Function.comp_apply, Pi.sub_apply, Pi.pow_apply, id_eq]
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial, zero_mul, add_zero, one_mul,
    Nat.cast_ofNat, Nat.reduceSub, pow_one, zero_sub,
    coordinateTanhSlope_apply, PiLp.neg_apply, PiLp.sub_apply,
    coordinateTanh_apply]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro coordinate _
  ring

/-- Curve form of the nonlinear residual derivative.  This is needed for raw
coupling parameters: their effective coefficient is itself a `tanh` curve,
so the prediction input is differentiable but not affine in the raw
parameter. -/
theorem hasDerivAt_weightedTanhResidualCurve {width : ℕ}
    (precision : ℝ) (state : Hidden width)
    (inputCurve : ℝ → Hidden width) (inputAtZero inputDerivative : Hidden width)
    (curveAtZero : inputCurve 0 = inputAtZero)
    (coordinateDerivative : ∀ coordinate : Fin width,
      ExactRealHasDerivAt (fun time : ℝ => inputCurve time coordinate)
        (inputDerivative coordinate) 0) :
    ExactRealHasDerivAt
      (fun time : ℝ => precision / 2 *
        ‖state - coordinateTanh (inputCurve time)‖ ^ 2)
      (precision *
        ⟪state - coordinateTanh inputAtZero,
          -(coordinateTanhSlope inputAtZero inputDerivative)⟫_ℝ) 0 := by
  let coordinateEnergyDerivative := fun coordinate : Fin width =>
    (((hasDerivAt_const (x := (0 : ℝ)) (state coordinate)).sub
      ((hasDerivAt_tanhExact (inputCurve 0 coordinate)).comp 0
        (coordinateDerivative coordinate))).pow 2)
  have sumDerivative := HasDerivAt.fun_sum
    (u := Finset.univ) (fun coordinate _ => coordinateEnergyDerivative coordinate)
  have weighted := sumDerivative.const_mul (precision / 2)
  have functionEquality :
      (fun time : ℝ => precision / 2 *
        ‖state - coordinateTanh (inputCurve time)‖ ^ 2) =
      (fun time : ℝ => precision / 2 *
        ∑ coordinate : Fin width,
          (state coordinate - Real.tanh (inputCurve time coordinate)) ^ 2) := by
    funext time
    rw [EuclideanSpace.real_norm_sq_eq]
    rfl
  rw [functionEquality]
  convert weighted.congr_deriv ?_ using 1 <;>
    simp only [Function.comp_apply, Pi.sub_apply, Pi.pow_apply]
  rw [curveAtZero]
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial, Nat.cast_ofNat,
    Nat.reduceSub, pow_one, coordinateTanhSlope_apply, PiLp.neg_apply,
    PiLp.sub_apply, coordinateTanh_apply]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro coordinate _
  ring

private theorem patchedLogits_activeLine {width actions : ℕ}
    (parameters : Parameters width actions) (inputs : Inputs actions)
    (active direction : Hidden width) (time : ℝ) :
    patchedLogits parameters inputs (active + time • direction) =
      patchedLogits parameters inputs active +
        time • ((parameters.outputGate) •
          maskedTaskGradient inputs (parameters.outputProjection direction)) := by
  ext action
  by_cases mutable : action ∈ mutableActions inputs
  · simp [patchedLogits, maskedTaskGradient, mutable, map_add, map_smul]
    ring
  · simp [patchedLogits, maskedTaskGradient, mutable]

private theorem task_hasDerivAt_activeLine {width actions : ℕ}
    (parameters : Parameters width actions) (inputs : Inputs actions)
    (task : TaskFunctional actions) (active direction : Hidden width) :
    HasDerivAt
      (fun time : ℝ => task.value
        (patchedLogits parameters inputs (active + time • direction)))
      ⟪task.gradient (patchedLogits parameters inputs active),
        parameters.outputGate •
          maskedTaskGradient inputs (parameters.outputProjection direction)⟫_ℝ 0 := by
  convert task.directionalDerivative (patchedLogits parameters inputs active)
    (parameters.outputGate •
      maskedTaskGradient inputs (parameters.outputProjection direction)) using 1
  · funext time
    rw [patchedLogits_activeLine]

/-! The complete analytic state-gradient proofs are stated below after the
residual line identities, keeping feedforward and equilibrium cases separate. -/

@[simp] theorem activeResidual_activeLine {width actions : ℕ}
    (parameters : Parameters width actions) (inputs : Inputs actions)
    (state : State width) (direction : Hidden width) (time : ℝ) :
    activeResidual parameters inputs (state.1 + time • direction, state.2) =
      activeResidual parameters inputs state + time • direction := by
  simp [activeResidual]
  module

@[simp] theorem activeResidual_evidenceLine {width actions : ℕ}
    (parameters : Parameters width actions) (inputs : Inputs actions)
    (state : State width) (direction : Hidden width) (time : ℝ) :
    activeResidual parameters inputs (state.1, state.2 + time • direction) =
      state.1 - coordinateTanh
        ((parameters.activeDrive inputs + parameters.activeCoupling • state.2) +
          time • (parameters.activeCoupling • direction)) := by
  simp [activeResidual]
  congr 1
  module

@[simp] theorem evidenceResidual_equilibrium_evidenceLine {width actions : ℕ}
    (parameters : Parameters width actions) (inputs : Inputs actions)
    (state : State width) (direction : Hidden width) (time : ℝ) :
    evidenceResidual parameters inputs .equilibrium
        (state.1, state.2 + time • direction) =
      evidenceResidual parameters inputs .equilibrium state + time • direction := by
  simp [evidenceResidual]
  module

@[simp] theorem evidenceResidual_evidenceLine {width actions : ℕ}
    (parameters : Parameters width actions) (inputs : Inputs actions)
    (dynamics : Dynamics) (state : State width) (direction : Hidden width)
    (time : ℝ) :
    evidenceResidual parameters inputs dynamics
        (state.1, state.2 + time • direction) =
      evidenceResidual parameters inputs dynamics state + time • direction := by
  cases dynamics <;> simp [evidenceResidual] <;> module

@[simp] theorem evidenceResidual_equilibrium_activeLine {width actions : ℕ}
    (parameters : Parameters width actions) (inputs : Inputs actions)
    (state : State width) (direction : Hidden width) (time : ℝ) :
    evidenceResidual parameters inputs .equilibrium
        (state.1 + time • direction, state.2) =
      state.2 - coordinateTanh
        ((parameters.evidenceDrive inputs + parameters.evidenceCoupling • state.1) +
          time • (parameters.evidenceCoupling • direction)) := by
  simp [evidenceResidual]
  congr 1
  module

@[simp] theorem evidenceResidual_feedforward_activeLine {width actions : ℕ}
    (parameters : Parameters width actions) (inputs : Inputs actions)
    (state : State width) (direction : Hidden width) (time : ℝ) :
    evidenceResidual parameters inputs .feedforward
        (state.1 + time • direction, state.2) =
      evidenceResidual parameters inputs .feedforward state := by
  rfl

/-- The declared active gradient is the exact derivative of the nonlinear
equilibrium energy along every active-state line. -/
theorem hasDerivAt_localEnergy_equilibrium_activeLine {width actions : ℕ}
    (parameters : Parameters width actions) (inputs : Inputs actions)
    (task : TaskFunctional actions) (frozenAuxiliary : ℝ)
    (state : State width) (direction : Hidden width) :
    HasDerivAt
      (fun time : ℝ => localEnergy parameters inputs task .equilibrium
        frozenAuxiliary (state.1 + time • direction, state.2))
      ⟪activeStateGradient parameters inputs task .equilibrium state, direction⟫_ℝ 0 := by
  have activeLine := hasDerivAt_weightedNormSq_line parameters.residualPrecision
    (activeResidual parameters inputs state) direction
  have evidenceLine := hasDerivAt_weightedTanhResidualLine
    parameters.residualPrecision state.2
    (parameters.evidenceDrive inputs + parameters.evidenceCoupling • state.1)
    (parameters.evidenceCoupling • direction)
  have taskLine := (task_hasDerivAt_activeLine parameters inputs task state.1 direction).const_mul
    parameters.taskPrecision
  have frozenLine : HasDerivAt (fun _time : ℝ => frozenAuxiliary) 0 0 :=
    hasDerivAt_const _ _
  have combined := activeLine.add evidenceLine |>.add taskLine |>.add frozenLine
  have functionEquality :
      (fun time : ℝ => localEnergy parameters inputs task .equilibrium
        frozenAuxiliary (state.1 + time • direction, state.2)) =
      (fun time : ℝ =>
        parameters.residualPrecision / 2 *
            ‖activeResidual parameters inputs state + time • direction‖ ^ 2 +
          parameters.residualPrecision / 2 *
            ‖state.2 - coordinateTanh
              ((parameters.evidenceDrive inputs +
                  parameters.evidenceCoupling • state.1) +
                time • (parameters.evidenceCoupling • direction))‖ ^ 2 +
          parameters.taskPrecision * task.value
            (patchedLogits parameters inputs (state.1 + time • direction)) +
          frozenAuxiliary) := by
    funext time
    simp only [localEnergy, residualEnergy, activeResidual_activeLine,
      evidenceResidual_equilibrium_activeLine]
  rw [functionEquality]
  apply combined.congr_deriv
  have evidenceCross :
      ⟪state.2 - coordinateTanh
          (parameters.evidenceDrive inputs + parameters.evidenceCoupling • state.1),
        -(coordinateTanhSlope
          (parameters.evidenceDrive inputs + parameters.evidenceCoupling • state.1)
          (parameters.evidenceCoupling • direction))⟫_ℝ =
      ⟪-(parameters.evidenceCoupling • coordinateTanhSlope
          (parameters.evidenceDrive inputs + parameters.evidenceCoupling • state.1)
          (state.2 - coordinateTanh
            (parameters.evidenceDrive inputs + parameters.evidenceCoupling • state.1))),
        direction⟫_ℝ := by
    rw [coordinateTanhSlope_smul, inner_neg_right, inner_neg_left,
      real_inner_smul_right, real_inner_smul_left,
      inner_coordinateTanhSlope_comm]
  have taskCross :
      ⟪task.gradient (patchedLogits parameters inputs state.1),
        parameters.outputGate •
          maskedTaskGradient inputs (parameters.outputProjection direction)⟫_ℝ =
      parameters.outputGate *
        ⟪parameters.outputProjection.adjoint
            (maskedTaskGradient inputs
              (task.gradient (patchedLogits parameters inputs state.1))),
          direction⟫_ℝ := by
    rw [real_inner_smul_right, inner_maskedTaskGradient,
      ← ContinuousLinearMap.adjoint_inner_left]
  unfold activeStateGradient
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left,
    evidenceCross, taskCross]
  rw [inner_sub_left, inner_neg_left, real_inner_smul_left]
  simp only [evidenceResidual]
  rw [real_inner_smul_left]
  ring

/-- In the feedforward cell the evidence residual is independent of the live
active state, so the active derivative has no recurrent evidence-back term. -/
theorem hasDerivAt_localEnergy_feedforward_activeLine {width actions : ℕ}
    (parameters : Parameters width actions) (inputs : Inputs actions)
    (task : TaskFunctional actions) (frozenAuxiliary : ℝ)
    (state : State width) (direction : Hidden width) :
    HasDerivAt
      (fun time : ℝ => localEnergy parameters inputs task .feedforward
        frozenAuxiliary (state.1 + time • direction, state.2))
      ⟪activeStateGradient parameters inputs task .feedforward state, direction⟫_ℝ 0 := by
  have activeLine := hasDerivAt_weightedNormSq_line parameters.residualPrecision
    (activeResidual parameters inputs state) direction
  have evidenceLine : HasDerivAt
      (fun _time : ℝ => parameters.residualPrecision / 2 *
        ‖evidenceResidual parameters inputs .feedforward state‖ ^ 2) 0 0 :=
    hasDerivAt_const _ _
  have taskLine := (task_hasDerivAt_activeLine parameters inputs task state.1 direction).const_mul
    parameters.taskPrecision
  have frozenLine : HasDerivAt (fun _time : ℝ => frozenAuxiliary) 0 0 :=
    hasDerivAt_const _ _
  have combined := activeLine.add evidenceLine |>.add taskLine |>.add frozenLine
  have functionEquality :
      (fun time : ℝ => localEnergy parameters inputs task .feedforward
        frozenAuxiliary (state.1 + time • direction, state.2)) =
      (fun time : ℝ =>
        parameters.residualPrecision / 2 *
            ‖activeResidual parameters inputs state + time • direction‖ ^ 2 +
          parameters.residualPrecision / 2 *
            ‖evidenceResidual parameters inputs .feedforward state‖ ^ 2 +
          parameters.taskPrecision * task.value
            (patchedLogits parameters inputs (state.1 + time • direction)) +
          frozenAuxiliary) := by
    funext time
    simp only [localEnergy, residualEnergy, activeResidual_activeLine,
      evidenceResidual_feedforward_activeLine]
  rw [functionEquality]
  apply combined.congr_deriv
  have taskCross :
      ⟪task.gradient (patchedLogits parameters inputs state.1),
        parameters.outputGate •
          maskedTaskGradient inputs (parameters.outputProjection direction)⟫_ℝ =
      parameters.outputGate *
        ⟪parameters.outputProjection.adjoint
            (maskedTaskGradient inputs
              (task.gradient (patchedLogits parameters inputs state.1))),
          direction⟫_ℝ := by
    rw [real_inner_smul_right, inner_maskedTaskGradient,
      ← ContinuousLinearMap.adjoint_inner_left]
  unfold activeStateGradient
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, taskCross]
  ring

/-- The evidence-state gradient is exact for both dynamics: the evidence
residual is affine in evidence, while the active residual contributes through
the coordinatewise `tanh` Jacobian. -/
theorem hasDerivAt_localEnergy_evidenceLine {width actions : ℕ}
    (parameters : Parameters width actions) (inputs : Inputs actions)
    (task : TaskFunctional actions) (dynamics : Dynamics)
    (frozenAuxiliary : ℝ) (state : State width) (direction : Hidden width) :
    HasDerivAt
      (fun time : ℝ => localEnergy parameters inputs task dynamics
        frozenAuxiliary (state.1, state.2 + time • direction))
      ⟪evidenceStateGradient parameters inputs dynamics state, direction⟫_ℝ 0 := by
  have activeLine := hasDerivAt_weightedTanhResidualLine
    parameters.residualPrecision state.1
    (parameters.activeDrive inputs + parameters.activeCoupling • state.2)
    (parameters.activeCoupling • direction)
  have evidenceLine := hasDerivAt_weightedNormSq_line parameters.residualPrecision
    (evidenceResidual parameters inputs dynamics state) direction
  have taskLine : HasDerivAt
      (fun _time : ℝ => parameters.taskPrecision *
        task.value (patchedLogits parameters inputs state.1)) 0 0 :=
    hasDerivAt_const _ _
  have frozenLine : HasDerivAt (fun _time : ℝ => frozenAuxiliary) 0 0 :=
    hasDerivAt_const _ _
  have combined := activeLine.add evidenceLine |>.add taskLine |>.add frozenLine
  have functionEquality :
      (fun time : ℝ => localEnergy parameters inputs task dynamics
        frozenAuxiliary (state.1, state.2 + time • direction)) =
      (fun time : ℝ =>
        parameters.residualPrecision / 2 *
            ‖state.1 - coordinateTanh
              ((parameters.activeDrive inputs + parameters.activeCoupling • state.2) +
                time • (parameters.activeCoupling • direction))‖ ^ 2 +
          parameters.residualPrecision / 2 *
            ‖evidenceResidual parameters inputs dynamics state + time • direction‖ ^ 2 +
          parameters.taskPrecision *
            task.value (patchedLogits parameters inputs state.1) + frozenAuxiliary) := by
    funext time
    simp only [localEnergy, residualEnergy, activeResidual_evidenceLine,
      evidenceResidual_evidenceLine]
  rw [functionEquality]
  apply combined.congr_deriv
  have activeCross :
      ⟪state.1 - coordinateTanh
          (parameters.activeDrive inputs + parameters.activeCoupling • state.2),
        -(coordinateTanhSlope
          (parameters.activeDrive inputs + parameters.activeCoupling • state.2)
          (parameters.activeCoupling • direction))⟫_ℝ =
      ⟪-(parameters.activeCoupling • coordinateTanhSlope
          (parameters.activeDrive inputs + parameters.activeCoupling • state.2)
          (state.1 - coordinateTanh
            (parameters.activeDrive inputs + parameters.activeCoupling • state.2))),
        direction⟫_ℝ := by
    rw [coordinateTanhSlope_smul, inner_neg_right, inner_neg_left,
      real_inner_smul_right, real_inner_smul_left,
      inner_coordinateTanhSlope_comm]
  unfold evidenceStateGradient
  rw [activeCross, real_inner_smul_left, inner_sub_left, inner_neg_left,
    real_inner_smul_left]
  simp only [activeResidual]
  rw [real_inner_smul_left]
  ring

/-! ## Finite state settling with explicit work -/

structure SettlingWork where
  objectiveEvaluations : ℕ
  rejectedProposals : ℕ
deriving DecidableEq

structure SettlingResult (width : ℕ) where
  state : State width
  work : SettlingWork
  solverFailed : Bool

def acceptedStateStep {width : ℕ}
    (energy : State width → ℝ) (current proposal : State width) : State width :=
  if energy proposal ≤ energy current then proposal else current

theorem acceptedStateStep_energy_nonincreasing {width : ℕ}
    (energy : State width → ℝ) (current proposal : State width) :
    energy (acceptedStateStep energy current proposal) ≤ energy current := by
  unfold acceptedStateStep
  split
  · assumption
  · exact le_rfl

theorem failedStateStep_is_identity {width : ℕ}
    (energy : State width → ℝ) (current proposal : State width)
    (rejected : ¬ energy proposal ≤ energy current) :
    acceptedStateStep energy current proposal = current := by
  simp [acceptedStateStep, rejected]

def oneBacktrackingAttempt {width : ℕ}
    (energy : State width → ℝ) (current proposal : State width) :
    SettlingResult width :=
  if energy proposal ≤ energy current then
    ⟨proposal, ⟨2, 0⟩, false⟩
  else
    ⟨current, ⟨2, 1⟩, true⟩

theorem oneBacktrackingAttempt_charges_both_objectives {width : ℕ}
    (energy : State width → ℝ) (current proposal : State width) :
    (oneBacktrackingAttempt energy current proposal).work.objectiveEvaluations = 2 := by
  unfold oneBacktrackingAttempt
  split <;> rfl

def SettlingWork.add (left right : SettlingWork) : SettlingWork :=
  ⟨left.objectiveEvaluations + right.objectiveEvaluations,
    left.rejectedProposals + right.rejectedProposals⟩

/-- A finite settling schedule.  Every proposed state is measured against the
current state.  Rejection retains the current state, but its two energy
evaluations remain charged. -/
def runSettlingSchedule {width : ℕ}
    (energy : State width → ℝ) (proposal : ℕ → State width → State width) :
    ℕ → State width → SettlingResult width
  | 0, current => ⟨current, ⟨0, 0⟩, false⟩
  | steps + 1, current =>
      let attempt := oneBacktrackingAttempt energy current (proposal steps current)
      let remainder := runSettlingSchedule energy proposal steps attempt.state
      ⟨remainder.state, attempt.work.add remainder.work,
        attempt.solverFailed || remainder.solverFailed⟩

theorem runSettlingSchedule_energy_nonincreasing {width : ℕ}
    (energy : State width → ℝ) (proposal : ℕ → State width → State width)
    (steps : ℕ) (initial : State width) :
    energy (runSettlingSchedule energy proposal steps initial).state ≤
      energy initial := by
  induction steps generalizing initial with
  | zero => exact le_rfl
  | succ steps induction =>
      unfold runSettlingSchedule
      let attempt := oneBacktrackingAttempt energy initial (proposal steps initial)
      have remainder := induction attempt.state
      apply remainder.trans
      unfold attempt oneBacktrackingAttempt
      split
      · assumption
      · exact le_rfl

theorem runSettlingSchedule_charges_every_proposal {width : ℕ}
    (energy : State width → ℝ) (proposal : ℕ → State width → State width)
    (steps : ℕ) (initial : State width) :
    (runSettlingSchedule energy proposal steps initial).work.objectiveEvaluations =
      2 * steps := by
  induction steps generalizing initial with
  | zero => rfl
  | succ steps induction =>
      unfold runSettlingSchedule
      let attempt := oneBacktrackingAttempt energy initial (proposal steps initial)
      have charged : attempt.work.objectiveEvaluations = 2 := by
        exact oneBacktrackingAttempt_charges_both_objectives _ _ _
      simp only [SettlingWork.add]
      rw [charged, induction attempt.state]
      omega

theorem runSettlingSchedule_rejections_le_steps {width : ℕ}
    (energy : State width → ℝ) (proposal : ℕ → State width → State width)
    (steps : ℕ) (initial : State width) :
    (runSettlingSchedule energy proposal steps initial).work.rejectedProposals ≤ steps := by
  induction steps generalizing initial with
  | zero => exact Nat.le_refl 0
  | succ steps induction =>
      unfold runSettlingSchedule
      let attempt := oneBacktrackingAttempt energy initial (proposal steps initial)
      have attemptBound : attempt.work.rejectedProposals ≤ 1 := by
        unfold attempt oneBacktrackingAttempt
        split <;> simp
      simp only [SettlingWork.add]
      calc
        attempt.work.rejectedProposals +
              (runSettlingSchedule energy proposal steps attempt.state).work.rejectedProposals ≤
            1 + steps := Nat.add_le_add attemptBound (induction attempt.state)
        _ = steps + 1 := Nat.add_comm 1 steps

/-! ## Exact-real gradient settling and finite backtracking

`runSettlingSchedule` above is a reusable acceptance skeleton.  The following
transition fixes the proposal to the actual local-energy gradient and searches
the registered geometric rate schedule.  Its work ledger counts the initial
energy, every per-step baseline, every rejected or accepted candidate, and the
final energy. -/

def localStateGradient {width actions : ℕ}
    (parameters : Parameters width actions) (inputs : Inputs actions)
    (task : TaskFunctional actions) (dynamics : Dynamics)
    (state : State width) : State width :=
  (activeStateGradient parameters inputs task dynamics state,
    evidenceStateGradient parameters inputs dynamics state)

def gradientStateProposal {width : ℕ}
    (rate : ℝ) (gradient state : State width) : State width :=
  (state.1 - rate • gradient.1, state.2 - rate • gradient.2)

structure BacktrackingResult (width : ℕ) where
  state : State width
  work : SettlingWork
  acceptedRate : Option ℝ
  solverFailed : Bool

/-- Try `maximumBacktracks + 1` rates: `rate`, `rate/2`, ... .  The baseline
energy is supplied by the caller because the runtime computes it once before
the candidate loop. -/
def tryGradientBacktracking {width : ℕ}
    (energy : State width → ℝ) (current gradient : State width)
    (baseline rate : ℝ) : ℕ → BacktrackingResult width
  | 0 =>
      let candidate := gradientStateProposal rate gradient current
      if energy candidate ≤ baseline then
        ⟨candidate, ⟨1, 0⟩, some rate, false⟩
      else
        ⟨current, ⟨1, 1⟩, none, true⟩
  | remaining + 1 =>
      let candidate := gradientStateProposal rate gradient current
      if energy candidate ≤ baseline then
        ⟨candidate, ⟨1, 0⟩, some rate, false⟩
      else
        let later := tryGradientBacktracking energy current gradient baseline
          (rate / 2) remaining
        ⟨later.state, ⟨later.work.objectiveEvaluations + 1,
          later.work.rejectedProposals + 1⟩,
          later.acceptedRate, later.solverFailed⟩

theorem tryGradientBacktracking_energy_nonincreasing {width : ℕ}
    (energy : State width → ℝ) (current gradient : State width)
    (baseline rate : ℝ) (baselineExact : baseline = energy current)
    (maximumBacktracks : ℕ) :
    energy (tryGradientBacktracking energy current gradient baseline rate
      maximumBacktracks).state ≤ energy current := by
  subst baseline
  induction maximumBacktracks generalizing rate with
  | zero =>
      simp only [tryGradientBacktracking]
      split
      · assumption
      · exact le_rfl
  | succ remaining induction =>
      simp only [tryGradientBacktracking]
      split
      · assumption
      · exact induction (rate / 2)

theorem tryGradientBacktracking_failure_is_identity {width : ℕ}
    (energy : State width → ℝ) (current gradient : State width)
    (baseline rate : ℝ) (maximumBacktracks : ℕ)
    (failed : (tryGradientBacktracking energy current gradient baseline rate
      maximumBacktracks).solverFailed = true) :
    (tryGradientBacktracking energy current gradient baseline rate
      maximumBacktracks).state = current := by
  induction maximumBacktracks generalizing rate with
  | zero =>
      by_cases accepted :
          energy (gradientStateProposal rate gradient current) ≤ baseline <;>
        simp [tryGradientBacktracking, accepted] at failed ⊢
  | succ remaining induction =>
      by_cases accepted :
          energy (gradientStateProposal rate gradient current) ≤ baseline
      · simp [tryGradientBacktracking, accepted] at failed
      · simp only [tryGradientBacktracking, accepted, ↓reduceIte] at failed ⊢
        exact induction (rate / 2) failed

theorem tryGradientBacktracking_charges_every_candidate {width : ℕ}
    (energy : State width → ℝ) (current gradient : State width)
    (baseline rate : ℝ) (maximumBacktracks : ℕ) :
    (tryGradientBacktracking energy current gradient baseline rate
      maximumBacktracks).work.objectiveEvaluations =
      (tryGradientBacktracking energy current gradient baseline rate
        maximumBacktracks).work.rejectedProposals +
        if (tryGradientBacktracking energy current gradient baseline rate
          maximumBacktracks).solverFailed then 0 else 1 := by
  induction maximumBacktracks generalizing rate with
  | zero =>
      by_cases accepted :
          energy (gradientStateProposal rate gradient current) ≤ baseline <;>
        simp [tryGradientBacktracking, accepted]
  | succ remaining induction =>
      by_cases accepted :
          energy (gradientStateProposal rate gradient current) ≤ baseline
      · simp [tryGradientBacktracking, accepted]
      · simp only [tryGradientBacktracking, accepted, ↓reduceIte]
        rw [induction (rate / 2)]
        cases (tryGradientBacktracking energy current gradient baseline
          (rate / 2) remaining).solverFailed <;> simp

structure GradientSettlingResult (width : ℕ) where
  state : State width
  work : SettlingWork
  acceptedRates : List ℝ
  solverFailed : Bool

def runGradientSettlingCore {width : ℕ}
    (energy : State width → ℝ) (gradient : State width → State width)
    (initialRate : ℝ) (maximumBacktracks : ℕ) :
    ℕ → State width → GradientSettlingResult width
  | 0, current => ⟨current, ⟨0, 0⟩, [], false⟩
  | steps + 1, current =>
      let attempt := tryGradientBacktracking energy current (gradient current)
        (energy current) initialRate maximumBacktracks
      if attempt.solverFailed then
        ⟨current, ⟨attempt.work.objectiveEvaluations + 1,
          attempt.work.rejectedProposals⟩, [], true⟩
      else
        let remainder := runGradientSettlingCore energy gradient initialRate
          maximumBacktracks steps attempt.state
        ⟨remainder.state,
          ⟨attempt.work.objectiveEvaluations + 1 +
              remainder.work.objectiveEvaluations,
            attempt.work.rejectedProposals + remainder.work.rejectedProposals⟩,
          attempt.acceptedRate.toList ++ remainder.acceptedRates,
          remainder.solverFailed⟩

theorem runGradientSettlingCore_energy_nonincreasing {width : ℕ}
    (energy : State width → ℝ) (gradient : State width → State width)
    (initialRate : ℝ) (maximumBacktracks steps : ℕ) (initial : State width) :
    energy (runGradientSettlingCore energy gradient initialRate
      maximumBacktracks steps initial).state ≤ energy initial := by
  induction steps generalizing initial with
  | zero => exact le_rfl
  | succ steps induction =>
      simp only [runGradientSettlingCore]
      let attempt := tryGradientBacktracking energy initial (gradient initial)
        (energy initial) initialRate maximumBacktracks
      by_cases failed : attempt.solverFailed = true
      · rw [if_pos failed]
      · rw [if_neg failed]
        exact (induction attempt.state).trans
          (tryGradientBacktracking_energy_nonincreasing energy initial
            (gradient initial) (energy initial) initialRate rfl maximumBacktracks)

/-- Exact accounting wrapper: one initial and one final objective evaluation
surround all baseline and candidate evaluations performed by the core. -/
def runGradientSettling {width : ℕ}
    (energy : State width → ℝ) (gradient : State width → State width)
    (initialRate : ℝ) (maximumBacktracks steps : ℕ) (initial : State width) :
    GradientSettlingResult width :=
  let core := runGradientSettlingCore energy gradient initialRate
    maximumBacktracks steps initial
  ⟨core.state, ⟨core.work.objectiveEvaluations + 2,
    core.work.rejectedProposals⟩, core.acceptedRates, core.solverFailed⟩

theorem runGradientSettling_energy_nonincreasing {width : ℕ}
    (energy : State width → ℝ) (gradient : State width → State width)
    (initialRate : ℝ) (maximumBacktracks steps : ℕ) (initial : State width) :
    energy (runGradientSettling energy gradient initialRate maximumBacktracks
      steps initial).state ≤ energy initial := by
  exact runGradientSettlingCore_energy_nonincreasing energy gradient initialRate
    maximumBacktracks steps initial

theorem runGradientSettling_charges_initial_and_final {width : ℕ}
    (energy : State width → ℝ) (gradient : State width → State width)
    (initialRate : ℝ) (maximumBacktracks steps : ℕ) (initial : State width) :
    (runGradientSettling energy gradient initialRate maximumBacktracks steps
      initial).work.objectiveEvaluations =
      (runGradientSettlingCore energy gradient initialRate maximumBacktracks
        steps initial).work.objectiveEvaluations + 2 := by
  rfl

def runExactLocalPCSettling {width actions : ℕ}
    (parameters : Parameters width actions) (inputs : Inputs actions)
    (task : TaskFunctional actions) (dynamics : Dynamics)
    (frozenAuxiliary initialRate : ℝ) (maximumBacktracks steps : ℕ)
    (initial : State width) : GradientSettlingResult width :=
  runGradientSettling
    (localEnergy parameters inputs task dynamics frozenAuxiliary)
    (localStateGradient parameters inputs task dynamics)
    initialRate maximumBacktracks steps initial

theorem runExactLocalPCSettling_energy_nonincreasing {width actions : ℕ}
    (parameters : Parameters width actions) (inputs : Inputs actions)
    (task : TaskFunctional actions) (dynamics : Dynamics)
    (frozenAuxiliary initialRate : ℝ) (maximumBacktracks steps : ℕ)
    (initial : State width) :
    localEnergy parameters inputs task dynamics frozenAuxiliary
        (runExactLocalPCSettling parameters inputs task dynamics frozenAuxiliary
          initialRate maximumBacktracks steps initial).state ≤
      localEnergy parameters inputs task dynamics frozenAuxiliary initial := by
  exact runGradientSettling_energy_nonincreasing _ _ initialRate
    maximumBacktracks steps initial

theorem runExactLocalPCSettling_charges_initial_and_final {width actions : ℕ}
    (parameters : Parameters width actions) (inputs : Inputs actions)
    (task : TaskFunctional actions) (dynamics : Dynamics)
    (frozenAuxiliary initialRate : ℝ) (maximumBacktracks steps : ℕ)
    (initial : State width) :
    (runExactLocalPCSettling parameters inputs task dynamics frozenAuxiliary
      initialRate maximumBacktracks steps initial).work.objectiveEvaluations =
      (runGradientSettlingCore
        (localEnergy parameters inputs task dynamics frozenAuxiliary)
        (localStateGradient parameters inputs task dynamics)
        initialRate maximumBacktracks steps initial).work.objectiveEvaluations + 2 := by
  rfl

theorem finite_depth_not_equilibrium_fixture :
    let parameters : Parameters 1 1 := {
      baseDriveWeight := 0,
      baseDriveBias := WithLp.toLp 2 fun _ => 1,
      evidenceToActive := 0,
      evidenceDriveWeight := 0, evidenceDriveBias := 0,
      outputProjection := 0, outputGate := 0,
      rawActiveCoupling := 0, rawEvidenceCoupling := 1,
      contractionLimit := 1 / 2, damping := 1 / 2, finiteDepth := 0,
      residualPrecision := 1, taskPrecision := 0 }
    let inputs : Inputs 1 := {
      maskedBaseDistribution := 0, normalizedLegalHistogram := 0,
      baseLogits := 0, routed := ∅, legal := ∅ }
    let endpoint := finiteEquilibriumState parameters inputs
    endpoint = initialState parameters inputs ∧
      dampedMap parameters inputs endpoint ≠ endpoint := by
  dsimp only
  constructor
  · rfl
  · intro equality
    have coordinate := congrArg (fun pair => pair.2 (0 : Fin 1)) equality
    simp only [finiteEquilibriumState, iterateState, initialState,
      dampedMap, candidateMap, Parameters.activeDrive,
      Parameters.evidenceDrive, Parameters.activeCoupling,
      Parameters.evidenceCoupling, coordinateTanh] at coordinate
    norm_num at coordinate
    have tanhOnePositive : 0 < Real.tanh (1 : ℝ) := by
      rw [Real.tanh_eq_sinh_div_cosh]
      positivity
    have nestedPositive :
        0 < Real.tanh ((1 / 2 : ℝ) * Real.tanh 1 * Real.tanh 1) := by
      rw [Real.tanh_eq_sinh_div_cosh]
      positivity
    linarith

/-! ## Exact width-32 and negative-model fixtures -/

def width32ZeroParameters : Parameters 32 2 := {
  baseDriveWeight := 0
  baseDriveBias := 0
  evidenceToActive := 0
  evidenceDriveWeight := 0
  evidenceDriveBias := 0
  outputProjection := 0
  outputGate := 0
  rawActiveCoupling := 0
  rawEvidenceCoupling := 0
  contractionLimit := 1 / 2
  damping := 1 / 2
  finiteDepth := 8
  residualPrecision := 20
  taskPrecision := 1 }

def width32ZeroInputs : Inputs 2 := {
  maskedBaseDistribution := 0
  normalizedLegalHistogram := 0
  baseLogits := 0
  routed := {0}
  legal := {0} }

def width32Impulse : Hidden 32 :=
  WithLp.toLp 2 fun coordinate => if coordinate = 0 then 1 else 0

def width32NonzeroParameters : Parameters 32 2 :=
  { width32ZeroParameters with baseDriveBias := width32Impulse }

def width32CoupledParameters : Parameters 32 2 :=
  { width32NonzeroParameters with
    rawActiveCoupling := 1
    rawEvidenceCoupling := 1 }

def width32FiniteDepthParameters : Parameters 32 2 :=
  { width32CoupledParameters with finiteDepth := 0 }

def zeroTaskFunctional (actions : ℕ) : TaskFunctional actions where
  value _ := 0
  gradient _ := 0
  directionalDerivative _ _ := by
    simpa using hasDerivAt_const (x := (0 : ℝ)) (c := (0 : ℝ))

def width1GradientFixtureParameters : Parameters 1 1 := {
  baseDriveWeight := 0
  baseDriveBias := 0
  evidenceToActive := 0
  evidenceDriveWeight := 0
  evidenceDriveBias := 0
  outputProjection := 0
  outputGate := 0
  rawActiveCoupling := 0
  rawEvidenceCoupling := 1
  contractionLimit := 1
  damping := 1 / 2
  finiteDepth := 1
  residualPrecision := 1
  taskPrecision := 0 }

def width1GradientFixtureInputs : Inputs 1 := {
  maskedBaseDistribution := 0
  normalizedLegalHistogram := 0
  baseLogits := 0
  routed := ∅
  legal := ∅ }

def width1GradientFixtureState : State 1 :=
  (0, WithLp.toLp 2 fun _ => 1)

theorem width32_zero_fixture_is_fixed :
    dampedMap width32ZeroParameters width32ZeroInputs (0, 0) = (0, 0) ∧
      activeResidual width32ZeroParameters width32ZeroInputs (0, 0) = 0 ∧
      evidenceResidual width32ZeroParameters width32ZeroInputs .equilibrium
        (0, 0) = 0 := by
  constructor
  · ext <;> simp [dampedMap, candidateMap, width32ZeroParameters,
      width32ZeroInputs, Parameters.activeDrive, Parameters.evidenceDrive,
      Parameters.activeCoupling, Parameters.evidenceCoupling, coordinateTanh]
  constructor <;>
    ext coordinate <;>
    simp [activeResidual, evidenceResidual, width32ZeroParameters,
      width32ZeroInputs, Parameters.activeDrive, Parameters.evidenceDrive,
      Parameters.activeCoupling, Parameters.evidenceCoupling, coordinateTanh]

theorem width32_nonzero_candidate_fixture :
    candidateMap width32NonzeroParameters width32ZeroInputs (0, 0) ≠ (0, 0) ∧
      couplingFactor width32NonzeroParameters = 0 := by
  constructor
  · intro equality
    have coordinate := congrArg (fun pair => pair.1 (0 : Fin 32)) equality
    simp [candidateMap, width32NonzeroParameters, width32ZeroParameters,
      width32ZeroInputs, width32Impulse, Parameters.activeDrive,
      Parameters.activeCoupling, coordinateTanh] at coordinate
    have positive : 0 < Real.tanh (1 : ℝ) := by
      rw [Real.tanh_eq_sinh_div_cosh]
      positivity
    linarith
  · norm_num [couplingFactor, width32NonzeroParameters, width32ZeroParameters,
      Parameters.activeCoupling, Parameters.evidenceCoupling]

theorem width32_nonlinear_contraction_fixture :
    couplingFactor width32CoupledParameters < 1 ∧
      dampedFactor width32CoupledParameters < 1 := by
  have bounds := effectiveCoupling_abs_lt_limit width32CoupledParameters (by
    norm_num [width32CoupledParameters, width32NonzeroParameters,
      width32ZeroParameters])
  have factorHalf : couplingFactor width32CoupledParameters < 1 / 2 := by
    exact max_lt bounds.1 bounds.2
  constructor
  · linarith
  · change 1 - 1 / 2 + 1 / 2 * couplingFactor width32CoupledParameters < 1
    linarith

theorem width32_nonzero_residual_energy_fixture :
    0 < residualEnergy width32NonzeroParameters width32ZeroInputs .equilibrium
      (0, 0) := by
  have activeNonzero :
      activeResidual width32NonzeroParameters width32ZeroInputs (0, 0) ≠ 0 := by
    intro equality
    have coordinate := congrArg (fun vector => vector (0 : Fin 32)) equality
    simp [activeResidual, width32NonzeroParameters, width32ZeroParameters,
      width32ZeroInputs, width32Impulse, Parameters.activeDrive,
      Parameters.activeCoupling, coordinateTanh] at coordinate
    have positive : 0 < Real.tanh (1 : ℝ) := by
      rw [Real.tanh_eq_sinh_div_cosh]
      positivity
    linarith
  have normPositive :
      0 < ‖activeResidual width32NonzeroParameters width32ZeroInputs (0, 0)‖ :=
    norm_pos_iff.mpr activeNonzero
  unfold residualEnergy
  norm_num [width32NonzeroParameters, width32ZeroParameters]
  positivity

theorem width32_state_gradient_nonzero_fixture :
    activeStateGradient width32NonzeroParameters width32ZeroInputs
      (zeroTaskFunctional 2) .equilibrium (0, 0) ≠ 0 := by
  intro equality
  have coordinate := congrArg (fun vector => vector (0 : Fin 32)) equality
  simp [activeStateGradient, activeResidual, evidenceResidual,
    width32NonzeroParameters, width32ZeroParameters, width32ZeroInputs,
    width32Impulse, zeroTaskFunctional, patchedLogits, maskedTaskGradient,
    Parameters.activeDrive, Parameters.evidenceDrive,
    Parameters.activeCoupling, Parameters.evidenceCoupling,
    coordinateTanh, coordinateTanhSlope, tanhSlope] at coordinate
  have positive : 0 < Real.tanh (1 : ℝ) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    positivity
  linarith

theorem width32_legality_support_fixture :
    patchedLogits width32NonzeroParameters width32ZeroInputs width32Impulse 1 =
        width32ZeroInputs.baseLogits 1 ∧
      maskedProbability width32ZeroInputs.legal
        (patchedLogits width32NonzeroParameters width32ZeroInputs width32Impulse) 1 = 0 := by
  constructor
  · apply patchedLogits_illegal_eq_base
    simp [width32ZeroInputs]
  · apply maskedProbability_illegal
    simp [width32ZeroInputs]

theorem width32_finite_depth_endpoint_is_not_equilibrium :
    let endpoint := finiteEquilibriumState width32FiniteDepthParameters
      width32ZeroInputs
    endpoint = initialState width32FiniteDepthParameters width32ZeroInputs ∧
      dampedMap width32FiniteDepthParameters width32ZeroInputs endpoint ≠ endpoint := by
  dsimp only
  constructor
  · rfl
  · change dampedMap width32FiniteDepthParameters width32ZeroInputs
      (initialState width32FiniteDepthParameters width32ZeroInputs) ≠
        initialState width32FiniteDepthParameters width32ZeroInputs
    intro equality
    have coordinate := congrArg (fun pair => pair.2 (0 : Fin 32)) equality
    simp only [initialState, dampedMap, candidateMap, Parameters.activeDrive,
      Parameters.evidenceDrive, Parameters.activeCoupling,
      Parameters.evidenceCoupling, coordinateTanh] at coordinate
    norm_num [width32FiniteDepthParameters, width32CoupledParameters,
      width32NonzeroParameters, width32ZeroParameters, width32ZeroInputs,
      width32Impulse] at coordinate
    have tanhOnePositive : 0 < Real.tanh (1 : ℝ) := by
      rw [Real.tanh_eq_sinh_div_cosh]
      positivity
    have nestedPositive :
        0 < Real.tanh ((1 / 2 : ℝ) * Real.tanh 1 * Real.tanh 1) := by
      rw [Real.tanh_eq_sinh_div_cosh]
      positivity
    linarith

theorem feedforward_and_equilibrium_state_gradients_differ_fixture :
    activeStateGradient width1GradientFixtureParameters width1GradientFixtureInputs
        (zeroTaskFunctional 1) .feedforward width1GradientFixtureState ≠
      activeStateGradient width1GradientFixtureParameters width1GradientFixtureInputs
        (zeroTaskFunctional 1) .equilibrium width1GradientFixtureState := by
  intro equality
  have coordinate := congrArg (fun vector => vector (0 : Fin 1)) equality
  simp [activeStateGradient, activeResidual, evidenceResidual,
    width1GradientFixtureParameters, width1GradientFixtureInputs,
    width1GradientFixtureState, zeroTaskFunctional, patchedLogits,
    maskedTaskGradient, Parameters.activeDrive, Parameters.evidenceDrive,
    Parameters.activeCoupling, Parameters.evidenceCoupling,
    coordinateTanh, coordinateTanhSlope, tanhSlope] at coordinate
  have tanhPositive : 0 < Real.tanh (1 : ℝ) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    positivity
  have coshPositive : 0 < Real.cosh (0 : ℝ) := Real.cosh_pos 0
  nlinarith

theorem linear_surrogate_differs_from_nonlinear_tanh :
    let value : Hidden 1 := WithLp.toLp 2 fun _ => 1
    coordinateTanh value ≠ value := by
  dsimp only
  intro equality
  have coordinate := congrArg (fun vector => vector (0 : Fin 1)) equality
  simp [coordinateTanh] at coordinate
  have upper := Real.tanh_lt_one (1 : ℝ)
  linarith

theorem output_gate_zero_does_not_force_gate_derivative_zero :
    let base : ℝ := 0
    let projected : ℝ := 2
    let loss : ℝ → ℝ := fun gate =>
      (1 / 2 : ℝ) * (base + gate * projected - 1) ^ 2
    loss 0 = 1 / 2 ∧ HasDerivAt loss (-2) 0 := by
  constructor
  · norm_num
  · have affine : HasDerivAt (fun gate : ℝ => gate * 2 - 1) 2 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (2 : ℝ)).sub_const 1
    have square := affine.pow 2
    have scaled := square.const_mul (1 / 2 : ℝ)
    simpa using scaled

#print axioms coordinateTanh_sub_norm_le
#print axioms dampedMap_contracts
#print axioms dampedMap_existsUnique_equilibrium
#print axioms patchedLogits_outside_mutable
#print axioms patchedLogits_illegal_eq_base
#print axioms patchedLogits_unrouted_eq_base
#print axioms patchedLogits_gate_zero
#print axioms maskedProbability_illegal
#print axioms maskedTaskGradient_illegal
#print axioms maskedTaskGradient_unrouted
#print axioms acceptedStateStep_energy_nonincreasing
#print axioms failedStateStep_is_identity
#print axioms runSettlingSchedule_energy_nonincreasing
#print axioms runSettlingSchedule_charges_every_proposal
#print axioms runSettlingSchedule_rejections_le_steps
#print axioms tryGradientBacktracking_energy_nonincreasing
#print axioms tryGradientBacktracking_failure_is_identity
#print axioms tryGradientBacktracking_charges_every_candidate
#print axioms runGradientSettlingCore_energy_nonincreasing
#print axioms runGradientSettling_energy_nonincreasing
#print axioms runGradientSettling_charges_initial_and_final
#print axioms runExactLocalPCSettling_energy_nonincreasing
#print axioms runExactLocalPCSettling_charges_initial_and_final
#print axioms finite_depth_not_equilibrium_fixture
#print axioms width32_zero_fixture_is_fixed
#print axioms width32_nonzero_candidate_fixture
#print axioms width32_nonlinear_contraction_fixture
#print axioms width32_nonzero_residual_energy_fixture
#print axioms width32_state_gradient_nonzero_fixture
#print axioms width32_legality_support_fixture
#print axioms width32_finite_depth_endpoint_is_not_equilibrium
#print axioms feedforward_and_equilibrium_state_gradients_differ_fixture
#print axioms linear_surrogate_differs_from_nonlinear_tanh
#print axioms output_gate_zero_does_not_force_gate_derivative_zero

end
end ActionMemoryNonlinearVectorPC
end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
