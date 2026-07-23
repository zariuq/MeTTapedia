import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.ConditionalAcceleration
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.InexactForwardBackward

/-!
# Spectrum-wide polynomial acceleration

The scalar acceleration fixture does not by itself license a multi-mode
solver.  This file supplies the first spectrum-wide rung for a finite
Euclidean error space whose quadratic energy has a declared diagonal spectral
representation.  For every curvature in `[lower, upper]`, two rationally
placed Richardson steps contract by a common polynomial factor.  The proof is
simultaneous over all modes, not an endpoint-only calculation.

The two-step map is packaged as a contraction certificate, so the existing
inexact-solver theory transports approximation error to an explicit error
floor.  A high-curvature fixture also shows why individual-sweep energy
monotonicity cannot be required: the first sweep expands that mode even though
the certified two-sweep composition contracts it.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace SpectralPolynomialAcceleration

open AmortizedInitialization
open InexactForwardBackward

noncomputable section

variable {Mode : Type*} [Fintype Mode]

/-- Finite Euclidean coordinates supplied by a diagonalization of an SPD
quadratic energy. -/
abbrev ModalState (Mode : Type*) [Fintype Mode] := EuclideanSpace ℝ Mode

/-- One Richardson/gradient step on every diagonal curvature mode. -/
noncomputable def diagonalStep
    (rate : ℝ) (curvature : Mode → ℝ) (state : ModalState Mode) :
    ModalState Mode :=
  WithLp.toLp 2 fun mode =>
    (1 - rate * curvature mode) * state mode

@[simp] theorem diagonalStep_apply
    (rate : ℝ) (curvature : Mode → ℝ) (state : ModalState Mode)
    (mode : Mode) :
    diagonalStep rate curvature state mode =
      (1 - rate * curvature mode) * state mode :=
  rfl

/-- Modal Nesterov state, included to state the exact zero-momentum boundary
in the same Hilbert coordinates as the polynomial result. -/
@[ext] structure ModalMomentumState (Mode : Type*) [Fintype Mode] where
  previous : ModalState Mode
  current : ModalState Mode

/-- Look-ahead momentum step on a diagonal quadratic energy. -/
noncomputable def diagonalMomentumStep
    (rate momentum : ℝ) (curvature : Mode → ℝ)
    (state : ModalMomentumState Mode) : ModalMomentumState Mode :=
  { previous := state.current
    current := WithLp.toLp 2 fun mode =>
      (1 - rate * curvature mode) *
        (state.current mode +
          momentum * (state.current mode - state.previous mode)) }

/-- Momentum zero is exactly the ordinary diagonal step, in every mode. -/
@[simp] theorem diagonalMomentumStep_zero_current
    (rate : ℝ) (curvature : Mode → ℝ)
    (state : ModalMomentumState Mode) :
    (diagonalMomentumStep rate 0 curvature state).current =
      diagonalStep rate curvature state.current := by
  ext mode
  simp [diagonalMomentumStep]

/-! ## A rational two-sweep spectrum polynomial -/

/-- First rate, whose reciprocal is the lower quartile of the spectral
interval. -/
noncomputable def firstRate (lower upper : ℝ) : ℝ :=
  4 / (3 * lower + upper)

/-- Second rate, whose reciprocal is the upper quartile of the spectral
interval. -/
noncomputable def secondRate (lower upper : ℝ) : ℝ :=
  4 / (lower + 3 * upper)

/-- Scalar residual polynomial produced by the two rationally placed steps. -/
noncomputable def twoRateFactor
    (lower upper curvature : ℝ) : ℝ :=
  (1 - firstRate lower upper * curvature) *
    (1 - secondRate lower upper * curvature)

/-- Uniform two-sweep factor over the full spectral interval. -/
noncomputable def twoRateBound (lower upper : ℝ) : ℝ :=
  3 * (upper - lower) ^ 2 /
    ((3 * lower + upper) * (lower + 3 * upper))

/-- Two consecutive polynomial-settling sweeps. -/
noncomputable def twoRateSweep
    (lower upper : ℝ) (curvature : Mode → ℝ)
    (state : ModalState Mode) : ModalState Mode :=
  diagonalStep (secondRate lower upper) curvature
    (diagonalStep (firstRate lower upper) curvature state)

@[simp] theorem twoRateSweep_apply
    (lower upper : ℝ) (curvature : Mode → ℝ)
    (state : ModalState Mode) (mode : Mode) :
    twoRateSweep lower upper curvature state mode =
      twoRateFactor lower upper (curvature mode) * state mode := by
  simp [twoRateSweep, twoRateFactor]
  ring

theorem spectralDenominator_pos
    {lower upper : ℝ} (hlower : 0 < lower) (hle : lower ≤ upper) :
    0 < (3 * lower + upper) * (lower + 3 * upper) := by
  have hupper : 0 < upper := lt_of_lt_of_le hlower hle
  positivity

/-- Every eigenmode in the declared interval is bounded by the same residual
polynomial factor. -/
theorem abs_twoRateFactor_le
    {lower upper curvature : ℝ}
    (hlower : 0 < lower)
    (hcurvatureLower : lower ≤ curvature)
    (hcurvatureUpper : curvature ≤ upper) :
    |twoRateFactor lower upper curvature| ≤
      twoRateBound lower upper := by
  have hle : lower ≤ upper := hcurvatureLower.trans hcurvatureUpper
  have hdenominator := spectralDenominator_pos hlower hle
  have hleft : 0 ≤ curvature - lower := sub_nonneg.mpr hcurvatureLower
  have hright : 0 ≤ upper - curvature := sub_nonneg.mpr hcurvatureUpper
  have hspectralSquare :
      (2 * curvature - lower - upper) ^ 2 ≤
        (upper - lower) ^ 2 := by
    nlinarith [mul_nonneg hleft hright]
  have hproductBounds :
      |(3 * lower + upper - 4 * curvature) *
          (lower + 3 * upper - 4 * curvature)| ≤
        3 * (upper - lower) ^ 2 := by
    rw [abs_le]
    constructor <;>
      nlinarith [sq_nonneg (2 * curvature - lower - upper),
        sq_nonneg (upper - lower)]
  have hfactor :
      twoRateFactor lower upper curvature =
        ((3 * lower + upper - 4 * curvature) *
            (lower + 3 * upper - 4 * curvature)) /
          ((3 * lower + upper) * (lower + 3 * upper)) := by
    have hfirst : 0 < 3 * lower + upper := by
      have hupper : 0 < upper := lt_of_lt_of_le hlower hle
      positivity
    have hsecond : 0 < lower + 3 * upper := by
      have hupper : 0 < upper := lt_of_lt_of_le hlower hle
      positivity
    dsimp [twoRateFactor, firstRate, secondRate]
    field_simp [ne_of_gt hfirst, ne_of_gt hsecond]
  rw [hfactor, abs_div, abs_of_pos hdenominator, twoRateBound]
  exact (div_le_div_iff_of_pos_right hdenominator).2 hproductBounds

theorem twoRateBound_nonneg
    {lower upper : ℝ} (hlower : 0 < lower) (hle : lower ≤ upper) :
    0 ≤ twoRateBound lower upper := by
  exact div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
    (le_of_lt (spectralDenominator_pos hlower hle))

theorem twoRateBound_lt_one
    {lower upper : ℝ} (hlower : 0 < lower) (hle : lower ≤ upper) :
    twoRateBound lower upper < 1 := by
  have hupper : 0 < upper := lt_of_lt_of_le hlower hle
  have hdenominator := spectralDenominator_pos hlower hle
  rw [twoRateBound, div_lt_one hdenominator]
  nlinarith [mul_pos hlower hupper]

/-! ## Simultaneous Hilbert-norm contraction -/

/-- A diagonal multiplier bounded in every mode contracts the Euclidean norm
by the same factor. -/
theorem diagonalMultiplier_norm_le
    (multiplier : Mode → ℝ) (bound : ℝ)
    (hbound : 0 ≤ bound)
    (hmode : ∀ mode, |multiplier mode| ≤ bound)
    (state : ModalState Mode) :
    ‖WithLp.toLp 2 (fun mode => multiplier mode * state mode)‖ ≤
      bound * ‖state‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg hbound (norm_nonneg state))]
  rw [EuclideanSpace.real_norm_sq_eq, mul_pow,
    EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro mode _
  have hsq : multiplier mode ^ 2 ≤ bound ^ 2 :=
    sq_le_sq.mpr (by simpa [abs_of_nonneg hbound] using hmode mode)
  calc
    (multiplier mode * state mode) ^ 2 =
        multiplier mode ^ 2 * state mode ^ 2 := by ring
    _ ≤ bound ^ 2 * state mode ^ 2 :=
      mul_le_mul_of_nonneg_right hsq (sq_nonneg _)

/-- The two-rate schedule contracts every finite collection of SPD modes at
once. -/
theorem twoRateSweep_norm_le
    {lower upper : ℝ} (hlower : 0 < lower)
    (hle : lower ≤ upper)
    {curvature : Mode → ℝ}
    (hcurvature : ∀ mode, lower ≤ curvature mode ∧ curvature mode ≤ upper)
    (state : ModalState Mode) :
    ‖twoRateSweep lower upper curvature state‖ ≤
      twoRateBound lower upper * ‖state‖ := by
  have hnonneg := twoRateBound_nonneg hlower hle
  have heq :
      twoRateSweep lower upper curvature state =
        WithLp.toLp 2 (fun mode =>
          twoRateFactor lower upper (curvature mode) * state mode) := by
    ext mode
    simp
  rw [heq]
  exact diagonalMultiplier_norm_le
      (fun mode => twoRateFactor lower upper (curvature mode))
      (twoRateBound lower upper) hnonneg
      (fun mode => abs_twoRateFactor_le hlower
        (hcurvature mode).1 (hcurvature mode).2)
      state

/-- Difference form needed by the contraction interface. -/
theorem twoRateSweep_distance_le
    {lower upper : ℝ} (hlower : 0 < lower)
    (hle : lower ≤ upper)
    {curvature : Mode → ℝ}
    (hcurvature : ∀ mode, lower ≤ curvature mode ∧ curvature mode ≤ upper)
    (left right : ModalState Mode) :
    ‖twoRateSweep lower upper curvature left -
        twoRateSweep lower upper curvature right‖ ≤
      twoRateBound lower upper * ‖left - right‖ := by
  have hlinear :
      twoRateSweep lower upper curvature left -
          twoRateSweep lower upper curvature right =
        twoRateSweep lower upper curvature (left - right) := by
    ext mode
    simp [twoRateSweep_apply]
    ring
  rw [hlinear]
  exact twoRateSweep_norm_le hlower hle hcurvature (left - right)

/-- Proof-carrying spectrum-wide contraction certificate. -/
noncomputable def twoRateContractionCertificate
    {lower upper : ℝ} (hlower : 0 < lower)
    (hle : lower ≤ upper)
    {curvature : Mode → ℝ}
    (hcurvature : ∀ mode, lower ≤ curvature mode ∧ curvature mode ≤ upper) :
    ContractionCertificate (twoRateSweep lower upper curvature) where
  factor := twoRateBound lower upper
  factor_nonneg := twoRateBound_nonneg hlower hle
  factor_lt_one := twoRateBound_lt_one hlower hle
  contracts := twoRateSweep_distance_le hlower hle hcurvature

@[simp] theorem twoRateSweep_zero
    (lower upper : ℝ) (curvature : Mode → ℝ) :
    twoRateSweep lower upper curvature 0 = 0 := by
  ext mode
  simp

/-! ## Coordinate-free transport -/

variable {State : Type*} [NormedAddCommGroup State] [NormedSpace ℝ State]

/-- Transport the modal solver through an explicit linear-isometric spectral
coordinate system.  Supplying this equivalence is the diagonalization
certificate required to apply the theorem to an arbitrary finite Hilbert
representation. -/
noncomputable def liftedTwoRateSweep
    (coordinates : State ≃ₗᵢ[ℝ] ModalState Mode)
    (lower upper : ℝ) (curvature : Mode → ℝ) (state : State) : State :=
  coordinates.symm
    (twoRateSweep lower upper curvature (coordinates state))

@[simp] theorem coordinates_liftedTwoRateSweep
    (coordinates : State ≃ₗᵢ[ℝ] ModalState Mode)
    (lower upper : ℝ) (curvature : Mode → ℝ) (state : State) :
    coordinates (liftedTwoRateSweep coordinates lower upper curvature state) =
      twoRateSweep lower upper curvature (coordinates state) := by
  simp [liftedTwoRateSweep]

/-- The spectrum-wide contraction is invariant under orthogonal change of
coordinates. -/
theorem liftedTwoRateSweep_distance_le
    (coordinates : State ≃ₗᵢ[ℝ] ModalState Mode)
    {lower upper : ℝ} (hlower : 0 < lower) (hle : lower ≤ upper)
    {curvature : Mode → ℝ}
    (hcurvature : ∀ mode, lower ≤ curvature mode ∧ curvature mode ≤ upper)
    (left right : State) :
    ‖liftedTwoRateSweep coordinates lower upper curvature left -
        liftedTwoRateSweep coordinates lower upper curvature right‖ ≤
      twoRateBound lower upper * ‖left - right‖ := by
  have hmodal := twoRateSweep_distance_le hlower hle hcurvature
    (coordinates left) (coordinates right)
  simpa only [liftedTwoRateSweep, ← map_sub,
    LinearIsometryEquiv.norm_map] using hmodal

/-- Coordinate-free contraction certificate for any state space carrying an
explicit linear-isometric diagonalization. -/
noncomputable def liftedTwoRateContractionCertificate
    (coordinates : State ≃ₗᵢ[ℝ] ModalState Mode)
    {lower upper : ℝ} (hlower : 0 < lower) (hle : lower ≤ upper)
    {curvature : Mode → ℝ}
    (hcurvature : ∀ mode, lower ≤ curvature mode ∧ curvature mode ≤ upper) :
    ContractionCertificate
      (liftedTwoRateSweep coordinates lower upper curvature) where
  factor := twoRateBound lower upper
  factor_nonneg := twoRateBound_nonneg hlower hle
  factor_lt_one := twoRateBound_lt_one hlower hle
  contracts := liftedTwoRateSweep_distance_le coordinates hlower hle hcurvature

@[simp] theorem liftedTwoRateSweep_zero
    (coordinates : State ≃ₗᵢ[ℝ] ModalState Mode)
    (lower upper : ℝ) (curvature : Mode → ℝ) :
    liftedTwoRateSweep coordinates lower upper curvature 0 = 0 := by
  apply coordinates.injective
  simp

/-! ## Inexact two-sweep solver -/

/-- A uniformly approximate implementation inherits an explicit transient
plus error-floor bound from the exact spectrum-wide contraction. -/
theorem inexact_twoRate_iterate_to_errorFloor_le
    {lower upper : ℝ} (hlower : 0 < lower)
    (hle : lower ≤ upper)
    {curvature : Mode → ℝ}
    (hcurvature : ∀ mode, lower ≤ curvature mode ∧ curvature mode ≤ upper)
    {approximate : ModalState Mode → ModalState Mode}
    (approximation : InexactMapCertificate
      (twoRateSweep lower upper curvature) approximate)
    (initial : ModalState Mode) (steps : ℕ) :
    ‖approximate^[steps] initial‖ ≤
      twoRateBound lower upper ^ steps * ‖initial‖ +
        approximation.error / (1 - twoRateBound lower upper) := by
  have hfixed : IsFixedPoint (twoRateSweep lower upper curvature)
      (0 : ModalState Mode) := by
    simp [IsFixedPoint]
  simpa [twoRateContractionCertificate] using inexact_iterate_to_errorFloor_le
    (twoRateContractionCertificate hlower hle hcurvature)
    approximation (0 : ModalState Mode) initial hfixed steps

/-! ## Comparison and safeguard boundaries -/

/-- The two-rate uniform factor is strictly smaller than two repeated `1/L`
steps whenever the spectrum is nondegenerate.  This compares certified worst-
case factors, not every individual mode. -/
theorem twoRateBound_lt_repeatedUpperRate
    {lower upper : ℝ} (hlower : 0 < lower) (hlt : lower < upper) :
    twoRateBound lower upper < ((upper - lower) / upper) ^ 2 := by
  have hupper : 0 < upper := hlower.trans hlt
  have hdenominator := spectralDenominator_pos hlower hlt.le
  have hdifferenceSq : 0 < (upper - lower) ^ 2 :=
    sq_pos_of_pos (sub_pos.mpr hlt)
  have hbase :
      3 * upper ^ 2 < (3 * lower + upper) * (lower + 3 * upper) := by
    nlinarith [mul_pos hlower hupper, sq_pos_of_pos hlower]
  have hscaled := mul_lt_mul_of_pos_left hbase hdifferenceSq
  rw [twoRateBound, div_pow]
  apply (div_lt_div_iff₀ hdenominator (sq_pos_of_pos hupper)).2
  nlinarith

theorem unitNine_twoRateBound :
    twoRateBound 1 9 = 4 / 7 := by
  norm_num [twoRateBound]

theorem unitNine_twoRate_improves_repeatedUpperRate :
    twoRateBound 1 9 < ((9 - 1) / 9) ^ 2 := by
  exact twoRateBound_lt_repeatedUpperRate (by norm_num) (by norm_num)

/-- Explicit two-mode SPD spectrum attaining both endpoints of `[1,9]`. -/
def endpointCurvature : Fin 2 → ℝ
  | 0 => 1
  | 1 => 9

theorem endpointCurvature_mem_interval (mode : Fin 2) :
    1 ≤ endpointCurvature mode ∧ endpointCurvature mode ≤ 9 := by
  fin_cases mode <;> norm_num [endpointCurvature]

/-- On the nondegenerate two-mode endpoint spectrum, both modes attain the
uniform factor exactly. -/
theorem endpointSpectrum_twoRateSweep_exact
    (state : ModalState (Fin 2)) :
    twoRateSweep 1 9 endpointCurvature state = (4 / 7 : ℝ) • state := by
  ext mode
  fin_cases mode <;>
    norm_num [twoRateSweep, twoRateFactor, firstRate, secondRate,
      endpointCurvature] <;>
    ring

theorem endpointSpectrum_norm_exact
    (state : ModalState (Fin 2)) :
    ‖twoRateSweep 1 9 endpointCurvature state‖ =
      (4 / 7 : ℝ) * ‖state‖ := by
  rw [endpointSpectrum_twoRateSweep_exact, norm_smul, Real.norm_eq_abs]
  norm_num

/-- The first scheduled sweep expands the high mode by a factor of two on the
`[1,9]` fixture.  A sound safeguard therefore evaluates the composed solver,
not a false per-sweep monotonicity requirement. -/
theorem unitNine_firstSweep_expands_highMode (state : ℝ) :
    (1 - firstRate 1 9 * 9) * state = -2 * state := by
  norm_num [firstRate]

#print axioms diagonalMomentumStep_zero_current
#print axioms abs_twoRateFactor_le
#print axioms twoRateSweep_norm_le
#print axioms twoRateContractionCertificate
#print axioms liftedTwoRateSweep_distance_le
#print axioms liftedTwoRateContractionCertificate
#print axioms inexact_twoRate_iterate_to_errorFloor_le
#print axioms twoRateBound_lt_repeatedUpperRate
#print axioms endpointSpectrum_twoRateSweep_exact
#print axioms endpointSpectrum_norm_exact
#print axioms unitNine_firstSweep_expands_highMode

end

end SpectralPolynomialAcceleration

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
