import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.ErrorCoordinateResidualSemantics
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.SpectralPolynomialAcceleration

/-!
# Active-subspace acceleration for deep error-coordinate inference

Deep error-coordinate inference stores one error tensor at each of three
hidden adapter sites.  Padding coordinates are masked before both task
propagation and the quadratic error penalty.  Positive precision therefore
does not make the full stored tensor space strongly convex: inactive
directions are flat.  The correct acceleration domain is the compacted
three-site active subspace.

This file gives that source-facing geometry and then lifts the finite-spectrum
two-rate theorem to an error-coordinate energy gradient carrying an explicit
modal task-curvature certificate.  The certificate states an independently
checkable equation for task-gradient differences; it is not inferred from
positive precision or from one decreasing energy trace.  A uniformly
approximate nonlinear block inherits the existing explicit error floor.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace DeepErrorCoordinateAcceleration

open scoped InnerProductSpace
open NonlinearResolvent
open ErrorCoordinateResidualSemantics
open SpectralPolynomialAcceleration
open InexactForwardBackward
open AmortizedInitialization

noncomputable section

/-! ## Three-site active and stored error geometry -/

/-- The compacted active coordinates of the three hidden error sites. -/
abbrev ThreeSiteActiveError (ActiveCoord : Type*) [Fintype ActiveCoord] :=
  EuclideanSpace ℝ (Fin 3 × ActiveCoord)

/-- Inactive padding coordinates retained by the tensor representation. -/
abbrev ThreeSiteInactiveError (InactiveCoord : Type*)
    [Fintype InactiveCoord] :=
  EuclideanSpace ℝ (Fin 3 × InactiveCoord)

/-- An exact Euclidean split of stored errors into active and inactive
coordinates.  A concrete tensor mask must supply the finite reindexing that
produces this split. -/
abbrev ThreeSiteStoredError (ActiveCoord InactiveCoord : Type*)
    [Fintype ActiveCoord] [Fintype InactiveCoord] :=
  WithLp 2
    (ThreeSiteActiveError ActiveCoord ×
      ThreeSiteInactiveError InactiveCoord)

/-- Embed an active error while setting every stored padding coordinate to
zero. -/
def storeActive
    {ActiveCoord InactiveCoord : Type*}
    [Fintype ActiveCoord] [Fintype InactiveCoord]
    (active : ThreeSiteActiveError ActiveCoord) :
    ThreeSiteStoredError ActiveCoord InactiveCoord :=
  WithLp.toLp 2 (active, 0)

/-- Embed a pure padding error. -/
def storeInactive
    {ActiveCoord InactiveCoord : Type*}
    [Fintype ActiveCoord] [Fintype InactiveCoord]
    (inactive : ThreeSiteInactiveError InactiveCoord) :
    ThreeSiteStoredError ActiveCoord InactiveCoord :=
  WithLp.toLp 2 (0, inactive)

@[simp] theorem storeActive_fst
    {ActiveCoord InactiveCoord : Type*}
    [Fintype ActiveCoord] [Fintype InactiveCoord]
    (active : ThreeSiteActiveError ActiveCoord) :
    (storeActive (InactiveCoord := InactiveCoord) active).fst = active :=
  rfl

@[simp] theorem storeActive_snd
    {ActiveCoord InactiveCoord : Type*}
    [Fintype ActiveCoord] [Fintype InactiveCoord]
    (active : ThreeSiteActiveError ActiveCoord) :
    (storeActive (InactiveCoord := InactiveCoord) active).snd = 0 :=
  rfl

@[simp] theorem storeInactive_fst
    {ActiveCoord InactiveCoord : Type*}
    [Fintype ActiveCoord] [Fintype InactiveCoord]
    (inactive : ThreeSiteInactiveError InactiveCoord) :
    (storeInactive (ActiveCoord := ActiveCoord) inactive).fst = 0 :=
  rfl

@[simp] theorem storeInactive_snd
    {ActiveCoord InactiveCoord : Type*}
    [Fintype ActiveCoord] [Fintype InactiveCoord]
    (inactive : ThreeSiteInactiveError InactiveCoord) :
    (storeInactive (ActiveCoord := ActiveCoord) inactive).snd = inactive :=
  rfl

@[simp] theorem norm_storeActive
    {ActiveCoord InactiveCoord : Type*}
    [Fintype ActiveCoord] [Fintype InactiveCoord]
    (active : ThreeSiteActiveError ActiveCoord) :
    ‖storeActive (InactiveCoord := InactiveCoord) active‖ = ‖active‖ := by
  exact WithLp.norm_toLp_fst 2 _ _ active

@[simp] theorem norm_storeInactive
    {ActiveCoord InactiveCoord : Type*}
    [Fintype ActiveCoord] [Fintype InactiveCoord]
    (inactive : ThreeSiteInactiveError InactiveCoord) :
    ‖storeInactive (ActiveCoord := ActiveCoord) inactive‖ = ‖inactive‖ := by
  exact WithLp.norm_toLp_snd 2 _ _ inactive

@[simp] theorem storeActive_zero
    {ActiveCoord InactiveCoord : Type*}
    [Fintype ActiveCoord] [Fintype InactiveCoord] :
    storeActive (ActiveCoord := ActiveCoord) (InactiveCoord := InactiveCoord) 0 = 0 :=
  rfl

/-- The masked stored energy depends only on compacted active coordinates. -/
def maskedStoredEnergy
    {ActiveCoord InactiveCoord : Type*}
    [Fintype ActiveCoord] [Fintype InactiveCoord]
    (task : ThreeSiteActiveError ActiveCoord → ℝ)
    (precision : ℝ)
    (stored : ThreeSiteStoredError ActiveCoord InactiveCoord) : ℝ :=
  task stored.fst + precision * ‖stored.fst‖ ^ 2 / 2

/-- The corresponding stored gradient has zero padding component. -/
def maskedStoredEnergyGradient
    {ActiveCoord InactiveCoord : Type*}
    [Fintype ActiveCoord] [Fintype InactiveCoord]
    (precision : ℝ)
    (taskGradient :
      ThreeSiteActiveError ActiveCoord → ThreeSiteActiveError ActiveCoord)
    (stored : ThreeSiteStoredError ActiveCoord InactiveCoord) :
    ThreeSiteStoredError ActiveCoord InactiveCoord :=
  storeActive (InactiveCoord := InactiveCoord)
    (errorCoordinateEnergyGradient precision taskGradient stored.fst)

theorem maskedStoredEnergy_storeInactive
    {ActiveCoord InactiveCoord : Type*}
    [Fintype ActiveCoord] [Fintype InactiveCoord]
    (task : ThreeSiteActiveError ActiveCoord → ℝ)
    (precision : ℝ)
    (inactive : ThreeSiteInactiveError InactiveCoord) :
    maskedStoredEnergy task precision
        (storeInactive (ActiveCoord := ActiveCoord) inactive) =
      task 0 := by
  simp [maskedStoredEnergy]

theorem maskedStoredGradient_storeInactive
    {ActiveCoord InactiveCoord : Type*}
    [Fintype ActiveCoord] [Fintype InactiveCoord]
    (precision : ℝ)
    (taskGradient :
      ThreeSiteActiveError ActiveCoord → ThreeSiteActiveError ActiveCoord)
    (inactive : ThreeSiteInactiveError InactiveCoord) :
    maskedStoredEnergyGradient precision taskGradient
        (storeInactive (ActiveCoord := ActiveCoord) inactive) =
      storeActive (InactiveCoord := InactiveCoord)
        (errorCoordinateEnergyGradient precision taskGradient 0) := by
  rfl

/-! ## Padding is a genuine flat direction -/

abbrev UnitStoredError := ThreeSiteStoredError (Fin 1) (Fin 1)

def unitInactiveError : ThreeSiteInactiveError (Fin 1) :=
  EuclideanSpace.single (0, 0) 1

def unitInactiveStored : UnitStoredError :=
  storeInactive (ActiveCoord := Fin 1) unitInactiveError

theorem unitInactiveStored_norm : ‖unitInactiveStored‖ = 1 := by
  simp [unitInactiveStored, unitInactiveError]

theorem unitInactiveStored_ne_zero : unitInactiveStored ≠ 0 := by
  intro hzero
  have hnorm := congrArg norm hzero
  rw [unitInactiveStored_norm, norm_zero] at hnorm
  norm_num at hnorm

def zeroActiveTaskGradient
    (_error : ThreeSiteActiveError (Fin 1)) : ThreeSiteActiveError (Fin 1) :=
  0

/-- Any positive claimed strong-monotonicity modulus on the full stored space
is refuted by a nonzero padding-only error. -/
theorem maskedStoredGradient_not_stronglyMonotone
    (precision modulus : ℝ) (hmodulus : 0 < modulus) :
    ¬ StronglyMonotoneMap modulus
      (maskedStoredEnergyGradient
        (InactiveCoord := Fin 1) precision zeroActiveTaskGradient) := by
  intro claimed
  have hflat := claimed unitInactiveStored 0
  have hgradientUnit :
      maskedStoredEnergyGradient
          (InactiveCoord := Fin 1) precision zeroActiveTaskGradient
          unitInactiveStored = 0 := by
    simp [maskedStoredEnergyGradient, unitInactiveStored,
      zeroActiveTaskGradient, errorCoordinateEnergyGradient]
  have hgradientZero :
      maskedStoredEnergyGradient
          (InactiveCoord := Fin 1) precision zeroActiveTaskGradient 0 = 0 := by
    simp [maskedStoredEnergyGradient, zeroActiveTaskGradient,
      errorCoordinateEnergyGradient]
  rw [hgradientUnit, hgradientZero] at hflat
  have : modulus ≤ 0 := by
    simpa [unitInactiveStored_norm] using hflat
  linarith

/-! ## Modal task-curvature certificate on the active space -/

variable {ActiveCoord Mode : Type*}
  [Fintype ActiveCoord] [Fintype Mode]

/-- An exact modal certificate for task-gradient differences on the compacted
active error space.  It is appropriate for a quadratic reference model.  A
nonlinear implementation must additionally provide a uniform approximation
or local remainder certificate. -/
structure ModalTaskGradientCertificate
    (taskGradient :
      ThreeSiteActiveError ActiveCoord → ThreeSiteActiveError ActiveCoord)
    (rho smooth : ℝ) where
  coordinates :
    ThreeSiteActiveError ActiveCoord ≃ₗᵢ[ℝ] ModalState Mode
  taskCurvature : Mode → ℝ
  taskCurvature_lower : ∀ mode, -rho ≤ taskCurvature mode
  taskCurvature_upper : ∀ mode, taskCurvature mode ≤ smooth
  gradient_difference : ∀ left right,
    coordinates (taskGradient left - taskGradient right) =
      WithLp.toLp 2 (fun mode =>
        taskCurvature mode * coordinates (left - right) mode)

/-- Curvature of task plus the isotropic active error penalty. -/
def combinedCurvature
    {taskGradient :
      ThreeSiteActiveError ActiveCoord → ThreeSiteActiveError ActiveCoord}
    {rho smooth : ℝ}
    (certificate : ModalTaskGradientCertificate (Mode := Mode)
      taskGradient rho smooth)
    (precision : ℝ) (mode : Mode) : ℝ :=
  precision + certificate.taskCurvature mode

/-- One explicit gradient step on the active error-coordinate energy. -/
def activeErrorGradientStep
    (precision rate : ℝ)
    (taskGradient :
      ThreeSiteActiveError ActiveCoord → ThreeSiteActiveError ActiveCoord)
    (error : ThreeSiteActiveError ActiveCoord) :
    ThreeSiteActiveError ActiveCoord :=
  error - rate •
    errorCoordinateEnergyGradient precision taskGradient error

theorem ModalTaskGradientCertificate.combinedCurvature_mem
    {taskGradient :
      ThreeSiteActiveError ActiveCoord → ThreeSiteActiveError ActiveCoord}
    {rho smooth precision : ℝ}
    (certificate : ModalTaskGradientCertificate (Mode := Mode)
      taskGradient rho smooth)
    (mode : Mode) :
    precision - rho ≤ combinedCurvature certificate precision mode ∧
      combinedCurvature certificate precision mode ≤ precision + smooth := by
  constructor
  · dsimp [combinedCurvature]
    linarith [certificate.taskCurvature_lower mode]
  · dsimp [combinedCurvature]
    linarith [certificate.taskCurvature_upper mode]

/-- The modal equation for one active energy-gradient step. -/
theorem ModalTaskGradientCertificate.coordinates_gradientStep_sub
    {taskGradient :
      ThreeSiteActiveError ActiveCoord → ThreeSiteActiveError ActiveCoord}
    {rho smooth : ℝ}
    (certificate : ModalTaskGradientCertificate (Mode := Mode)
      taskGradient rho smooth)
    (precision rate : ℝ)
    (left right : ThreeSiteActiveError ActiveCoord) :
    certificate.coordinates
        (activeErrorGradientStep precision rate taskGradient left -
          activeErrorGradientStep precision rate taskGradient right) =
      diagonalStep rate (combinedCurvature certificate precision)
        (certificate.coordinates (left - right)) := by
  ext mode
  have htask := congrArg (fun state => state mode)
    (certificate.gradient_difference left right)
  simp [activeErrorGradientStep, errorCoordinateEnergyGradient,
    diagonalStep, combinedCurvature] at htask ⊢
  linear_combination -rate * htask

/-- Two rationally placed active energy-gradient sweeps. -/
def activeTwoRateBlock
    (precision rho smooth : ℝ)
    (taskGradient :
      ThreeSiteActiveError ActiveCoord → ThreeSiteActiveError ActiveCoord)
    (error : ThreeSiteActiveError ActiveCoord) :
    ThreeSiteActiveError ActiveCoord :=
  activeErrorGradientStep precision
    (secondRate (precision - rho) (precision + smooth)) taskGradient
    (activeErrorGradientStep precision
      (firstRate (precision - rho) (precision + smooth)) taskGradient error)

/-- The full two-sweep source map is exactly the transported spectral
polynomial whenever the modal task-gradient equation holds. -/
theorem ModalTaskGradientCertificate.coordinates_twoRateBlock_sub
    {taskGradient :
      ThreeSiteActiveError ActiveCoord → ThreeSiteActiveError ActiveCoord}
    {rho smooth : ℝ}
    (certificate : ModalTaskGradientCertificate (Mode := Mode)
      taskGradient rho smooth)
    (precision : ℝ)
    (left right : ThreeSiteActiveError ActiveCoord) :
    certificate.coordinates
        (activeTwoRateBlock precision rho smooth taskGradient left -
          activeTwoRateBlock precision rho smooth taskGradient right) =
      twoRateSweep (precision - rho) (precision + smooth)
        (combinedCurvature certificate precision)
        (certificate.coordinates (left - right)) := by
  simp only [activeTwoRateBlock]
  rw [certificate.coordinates_gradientStep_sub,
    certificate.coordinates_gradientStep_sub]
  rfl

/-- Source-bound pairwise contraction of the active two-rate block. -/
theorem ModalTaskGradientCertificate.twoRateBlock_distance_le
    {taskGradient :
      ThreeSiteActiveError ActiveCoord → ThreeSiteActiveError ActiveCoord}
    {rho smooth precision : ℝ}
    (certificate : ModalTaskGradientCertificate (Mode := Mode)
      taskGradient rho smooth)
    (hrho : 0 ≤ rho) (hsmooth : 0 ≤ smooth)
    (hdominates : rho < precision)
    (left right : ThreeSiteActiveError ActiveCoord) :
    ‖activeTwoRateBlock precision rho smooth taskGradient left -
        activeTwoRateBlock precision rho smooth taskGradient right‖ ≤
      twoRateBound (precision - rho) (precision + smooth) *
        ‖left - right‖ := by
  have hlower : 0 < precision - rho := sub_pos.mpr hdominates
  have hle : precision - rho ≤ precision + smooth := by linarith
  have hmodal := twoRateSweep_norm_le hlower hle
    (fun mode => certificate.combinedCurvature_mem mode)
    (certificate.coordinates (left - right))
  calc
    ‖activeTwoRateBlock precision rho smooth taskGradient left -
        activeTwoRateBlock precision rho smooth taskGradient right‖ =
        ‖certificate.coordinates
          (activeTwoRateBlock precision rho smooth taskGradient left -
            activeTwoRateBlock precision rho smooth taskGradient right)‖ :=
      (certificate.coordinates.norm_map _).symm
    _ = ‖twoRateSweep (precision - rho) (precision + smooth)
          (combinedCurvature certificate precision)
          (certificate.coordinates (left - right))‖ := by
      rw [certificate.coordinates_twoRateBlock_sub]
    _ ≤ twoRateBound (precision - rho) (precision + smooth) *
          ‖certificate.coordinates (left - right)‖ := hmodal
    _ = twoRateBound (precision - rho) (precision + smooth) *
          ‖left - right‖ := by
      rw [certificate.coordinates.norm_map]

/-- Proof-carrying contraction certificate for the active error block. -/
def ModalTaskGradientCertificate.twoRateBlockCertificate
    {taskGradient :
      ThreeSiteActiveError ActiveCoord → ThreeSiteActiveError ActiveCoord}
    {rho smooth precision : ℝ}
    (certificate : ModalTaskGradientCertificate (Mode := Mode)
      taskGradient rho smooth)
    (hrho : 0 ≤ rho) (hsmooth : 0 ≤ smooth)
    (hdominates : rho < precision) :
    ContractionCertificate
      (activeTwoRateBlock precision rho smooth taskGradient) where
  factor := twoRateBound (precision - rho) (precision + smooth)
  factor_nonneg := twoRateBound_nonneg (sub_pos.mpr hdominates) (by linarith)
  factor_lt_one := twoRateBound_lt_one (sub_pos.mpr hdominates) (by linarith)
  contracts := certificate.twoRateBlock_distance_le hrho hsmooth hdominates

theorem activeTwoRateBlock_fixed_of_stationary
    {taskGradient :
      ThreeSiteActiveError ActiveCoord → ThreeSiteActiveError ActiveCoord}
    {rho smooth precision : ℝ}
    {target : ThreeSiteActiveError ActiveCoord}
    (stationary :
      errorCoordinateEnergyGradient precision taskGradient target = 0) :
    IsFixedPoint
      (activeTwoRateBlock precision rho smooth taskGradient) target := by
  simp [IsFixedPoint, activeTwoRateBlock, activeErrorGradientStep, stationary]

/-- A nonlinear or approximate source block inherits the explicit transient
and error floor after supplying a uniform block-approximation certificate. -/
theorem ModalTaskGradientCertificate.inexact_iterate_to_errorFloor_le
    {taskGradient :
      ThreeSiteActiveError ActiveCoord → ThreeSiteActiveError ActiveCoord}
    {rho smooth precision : ℝ}
    (certificate : ModalTaskGradientCertificate (Mode := Mode)
      taskGradient rho smooth)
    (hrho : 0 ≤ rho) (hsmooth : 0 ≤ smooth)
    (hdominates : rho < precision)
    {approximate :
      ThreeSiteActiveError ActiveCoord → ThreeSiteActiveError ActiveCoord}
    (approximation : InexactMapCertificate
      (activeTwoRateBlock precision rho smooth taskGradient) approximate)
    (target initial : ThreeSiteActiveError ActiveCoord)
    (stationary :
      errorCoordinateEnergyGradient precision taskGradient target = 0)
    (steps : ℕ) :
    ‖approximate^[steps] initial - target‖ ≤
      twoRateBound (precision - rho) (precision + smooth) ^ steps *
          ‖initial - target‖ +
        approximation.error /
          (1 - twoRateBound (precision - rho) (precision + smooth)) := by
  simpa [ModalTaskGradientCertificate.twoRateBlockCertificate] using
    InexactForwardBackward.inexact_iterate_to_errorFloor_le
      (certificate.twoRateBlockCertificate hrho hsmooth hdominates)
      approximation target initial
      (activeTwoRateBlock_fixed_of_stationary stationary) steps

/-! ## Nondegenerate three-site endpoint fixture -/

abbrev EndpointActiveError := ThreeSiteActiveError (Fin 2)

def endpointTaskCurvature (index : Fin 3 × Fin 2) : ℝ :=
  if index.2 = 0 then -1 else 7

def endpointTaskGradient (error : EndpointActiveError) : EndpointActiveError :=
  WithLp.toLp 2 fun index => endpointTaskCurvature index * error index

def endpointTaskCertificate :
    ModalTaskGradientCertificate (Mode := Fin 3 × Fin 2)
      endpointTaskGradient 1 7 where
  coordinates := LinearIsometryEquiv.refl ℝ EndpointActiveError
  taskCurvature := endpointTaskCurvature
  taskCurvature_lower := by
    intro index
    by_cases h : index.2 = 0 <;>
      norm_num [endpointTaskCurvature, h]
  taskCurvature_upper := by
    intro index
    by_cases h : index.2 = 0 <;>
      norm_num [endpointTaskCurvature, h]
  gradient_difference := by
    intro left right
    ext index
    simp [endpointTaskGradient]
    ring

theorem endpointTask_combinedCurvature (index : Fin 3 × Fin 2) :
    combinedCurvature endpointTaskCertificate 2 index =
      if index.2 = 0 then 1 else 9 := by
  by_cases h : index.2 = 0 <;>
    simp [combinedCurvature, endpointTaskCertificate,
      endpointTaskCurvature, h] <;> norm_num

/-- All three sites carry both endpoint modes, and the exact active block
contracts every stored active error by the sharp factor `4/7`. -/
theorem endpointThreeSite_twoRateBlock_exact (error : EndpointActiveError) :
    activeTwoRateBlock 2 1 7 endpointTaskGradient error =
      (4 / 7 : ℝ) • error := by
  ext index
  rcases index with ⟨site, coordinate⟩
  fin_cases coordinate <;>
    norm_num [activeTwoRateBlock, activeErrorGradientStep,
      errorCoordinateEnergyGradient, endpointTaskGradient,
      endpointTaskCurvature, firstRate, secondRate] <;>
    ring

theorem endpointThreeSite_norm_exact (error : EndpointActiveError) :
    ‖activeTwoRateBlock 2 1 7 endpointTaskGradient error‖ =
      (4 / 7 : ℝ) * ‖error‖ := by
  rw [endpointThreeSite_twoRateBlock_exact, norm_smul, Real.norm_eq_abs]
  norm_num

#print axioms maskedStoredGradient_not_stronglyMonotone
#print axioms ModalTaskGradientCertificate.coordinates_gradientStep_sub
#print axioms ModalTaskGradientCertificate.twoRateBlock_distance_le
#print axioms ModalTaskGradientCertificate.twoRateBlockCertificate
#print axioms ModalTaskGradientCertificate.inexact_iterate_to_errorFloor_le
#print axioms endpointThreeSite_twoRateBlock_exact
#print axioms endpointThreeSite_norm_exact

end

end DeepErrorCoordinateAcceleration

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
