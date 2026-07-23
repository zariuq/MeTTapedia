import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.DeepErrorCoordinateAcceleration

/-!
# Finite-horizon acceleration under curvature drift

The spectrum-wide two-rate block is exact for one fixed quadratic curvature
operator.  A nonlinear solver generally presents a different local Hessian at
the second sweep.  This file makes that time ordering explicit.

For each mode, the difference from the fixed-curvature polynomial splits into
two first-order terms and one quadratic interaction term.  A proof-carrying
pointwise drift budget then lifts to a simultaneous Euclidean contraction
bound.  Local sampled Ritz values do not supply that budget: the certificate
requires a bound for every declared mode and both ordered sweeps.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace CurvatureDriftAcceleration

open SpectralPolynomialAcceleration
open DeepErrorCoordinateAcceleration
open AmortizedInitialization

noncomputable section

variable {Mode : Type*} [Fintype Mode]

/-! ## Exact scalar time-ordered discrepancy -/

/-- Residual multiplier when the first and second sweeps see different local
curvatures. -/
def varyingTwoRateFactor
    (lower upper firstCurvature secondCurvature : ℝ) : ℝ :=
  (1 - firstRate lower upper * firstCurvature) *
    (1 - secondRate lower upper * secondCurvature)

/-- The two terms linear in the ordered curvature perturbations. -/
def curvatureDriftFirstOrder
    (lower upper base firstCurvature secondCurvature : ℝ) : ℝ :=
  -firstRate lower upper * (firstCurvature - base) *
      (1 - secondRate lower upper * base) -
    secondRate lower upper * (secondCurvature - base) *
      (1 - firstRate lower upper * base)

/-- The interaction of the two ordered curvature perturbations. -/
def curvatureDriftRemainder
    (lower upper base firstCurvature secondCurvature : ℝ) : ℝ :=
  firstRate lower upper * secondRate lower upper *
    (firstCurvature - base) * (secondCurvature - base)

/-- Absolute first-order gain plus the quadratic interaction. -/
def curvatureDriftEnvelope
    (lower upper base firstCurvature secondCurvature : ℝ) : ℝ :=
  |firstRate lower upper * (firstCurvature - base) *
      (1 - secondRate lower upper * base)| +
    |secondRate lower upper * (secondCurvature - base) *
      (1 - firstRate lower upper * base)| +
    |firstRate lower upper * secondRate lower upper *
      (firstCurvature - base) * (secondCurvature - base)|

/-- Exact time-ordered perturbation identity. -/
theorem varyingTwoRateFactor_sub_fixed
    (lower upper base firstCurvature secondCurvature : ℝ) :
    varyingTwoRateFactor lower upper firstCurvature secondCurvature -
        twoRateFactor lower upper base =
      curvatureDriftFirstOrder lower upper base
          firstCurvature secondCurvature +
        curvatureDriftRemainder lower upper base
          firstCurvature secondCurvature := by
  simp [varyingTwoRateFactor, twoRateFactor,
    curvatureDriftFirstOrder, curvatureDriftRemainder]
  ring

theorem curvatureDriftEnvelope_nonneg
    (lower upper base firstCurvature secondCurvature : ℝ) :
    0 ≤ curvatureDriftEnvelope lower upper base
      firstCurvature secondCurvature := by
  exact add_nonneg
    (add_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _)

/-- The envelope bounds the exact discrepancy without discarding the
time-ordered quadratic term. -/
theorem abs_varyingTwoRateFactor_sub_fixed_le
    (lower upper base firstCurvature secondCurvature : ℝ) :
    |varyingTwoRateFactor lower upper firstCurvature secondCurvature -
        twoRateFactor lower upper base| ≤
      curvatureDriftEnvelope lower upper base
        firstCurvature secondCurvature := by
  rw [varyingTwoRateFactor_sub_fixed]
  calc
    |curvatureDriftFirstOrder lower upper base firstCurvature secondCurvature +
        curvatureDriftRemainder lower upper base firstCurvature secondCurvature| ≤
        |curvatureDriftFirstOrder lower upper base firstCurvature secondCurvature| +
          |curvatureDriftRemainder lower upper base firstCurvature secondCurvature| :=
      abs_add_le _ _
    _ ≤ curvatureDriftEnvelope lower upper base
          firstCurvature secondCurvature := by
      dsimp [curvatureDriftFirstOrder, curvatureDriftRemainder,
        curvatureDriftEnvelope]
      have hlinear :
          |-firstRate lower upper * (firstCurvature - base) *
                (1 - secondRate lower upper * base) -
              secondRate lower upper * (secondCurvature - base) *
                (1 - firstRate lower upper * base)| ≤
            |firstRate lower upper * (firstCurvature - base) *
                (1 - secondRate lower upper * base)| +
              |secondRate lower upper * (secondCurvature - base) *
                (1 - firstRate lower upper * base)| := by
        calc
          |-firstRate lower upper * (firstCurvature - base) *
                (1 - secondRate lower upper * base) -
              secondRate lower upper * (secondCurvature - base) *
                (1 - firstRate lower upper * base)| =
              |(-(firstRate lower upper * (firstCurvature - base) *
                    (1 - secondRate lower upper * base))) +
                (-(secondRate lower upper * (secondCurvature - base) *
                    (1 - firstRate lower upper * base)))| := by
                congr 1
                ring
          _ ≤ |-(firstRate lower upper * (firstCurvature - base) *
                    (1 - secondRate lower upper * base))| +
                |-(secondRate lower upper * (secondCurvature - base) *
                    (1 - firstRate lower upper * base))| := abs_add_le _ _
          _ = |firstRate lower upper * (firstCurvature - base) *
                    (1 - secondRate lower upper * base)| +
                |secondRate lower upper * (secondCurvature - base) *
                    (1 - firstRate lower upper * base)| := by simp
      exact add_le_add_left hlinear
        |firstRate lower upper * secondRate lower upper *
          (firstCurvature - base) * (secondCurvature - base)|

@[simp] theorem curvatureDriftEnvelope_self
    (lower upper base : ℝ) :
    curvatureDriftEnvelope lower upper base base base = 0 := by
  simp [curvatureDriftEnvelope]

@[simp] theorem varyingTwoRateFactor_self
    (lower upper base : ℝ) :
    varyingTwoRateFactor lower upper base base =
      twoRateFactor lower upper base := by
  simp [varyingTwoRateFactor, twoRateFactor]

/-! ## Proof-carrying finite modal drift -/

/-- Two ordered sweeps with potentially different modal curvatures. -/
def varyingTwoRateSweep
    (lower upper : ℝ)
    (firstCurvature secondCurvature : Mode → ℝ)
    (state : ModalState Mode) : ModalState Mode :=
  diagonalStep (secondRate lower upper) secondCurvature
    (diagonalStep (firstRate lower upper) firstCurvature state)

@[simp] theorem varyingTwoRateSweep_apply
    (lower upper : ℝ)
    (firstCurvature secondCurvature : Mode → ℝ)
    (state : ModalState Mode) (mode : Mode) :
    varyingTwoRateSweep lower upper firstCurvature secondCurvature state mode =
      varyingTwoRateFactor lower upper
        (firstCurvature mode) (secondCurvature mode) * state mode := by
  simp [varyingTwoRateSweep, varyingTwoRateFactor]
  ring

/-- A finite-horizon certificate around one fixed reference spectrum.  The
drift budget is pointwise over all modes; sampled local Ritz values do not
construct this object. -/
structure CurvatureDriftCertificate
    (lower upper : ℝ)
    (base firstCurvature secondCurvature : Mode → ℝ) where
  base_mem : ∀ mode, lower ≤ base mode ∧ base mode ≤ upper
  driftBound : ℝ
  driftBound_nonneg : 0 ≤ driftBound
  envelope_le : ∀ mode,
    curvatureDriftEnvelope lower upper (base mode)
      (firstCurvature mode) (secondCurvature mode) ≤ driftBound

omit [Fintype Mode] in
theorem CurvatureDriftCertificate.abs_varyingFactor_le
    {lower upper : ℝ}
    {base firstCurvature secondCurvature : Mode → ℝ}
    (certificate : CurvatureDriftCertificate lower upper
      base firstCurvature secondCurvature)
    (hlower : 0 < lower) (mode : Mode) :
    |varyingTwoRateFactor lower upper
        (firstCurvature mode) (secondCurvature mode)| ≤
      twoRateBound lower upper + certificate.driftBound := by
  have hbase := abs_twoRateFactor_le hlower
    (certificate.base_mem mode).1 (certificate.base_mem mode).2
  have hdelta := abs_varyingTwoRateFactor_sub_fixed_le
    lower upper (base mode) (firstCurvature mode) (secondCurvature mode)
  have htriangle :
      |varyingTwoRateFactor lower upper
          (firstCurvature mode) (secondCurvature mode)| ≤
        |twoRateFactor lower upper (base mode)| +
          |varyingTwoRateFactor lower upper
              (firstCurvature mode) (secondCurvature mode) -
            twoRateFactor lower upper (base mode)| := by
    have hsum :
        twoRateFactor lower upper (base mode) +
            (varyingTwoRateFactor lower upper
                (firstCurvature mode) (secondCurvature mode) -
              twoRateFactor lower upper (base mode)) =
          varyingTwoRateFactor lower upper
            (firstCurvature mode) (secondCurvature mode) := by
      ring
    calc
      |varyingTwoRateFactor lower upper
          (firstCurvature mode) (secondCurvature mode)| =
          |twoRateFactor lower upper (base mode) +
            (varyingTwoRateFactor lower upper
                (firstCurvature mode) (secondCurvature mode) -
              twoRateFactor lower upper (base mode))| := congrArg abs hsum.symm
      _ ≤ |twoRateFactor lower upper (base mode)| +
          |varyingTwoRateFactor lower upper
              (firstCurvature mode) (secondCurvature mode) -
            twoRateFactor lower upper (base mode)| := abs_add_le _ _
  calc
    |varyingTwoRateFactor lower upper
        (firstCurvature mode) (secondCurvature mode)| ≤
        |twoRateFactor lower upper (base mode)| +
          |varyingTwoRateFactor lower upper
              (firstCurvature mode) (secondCurvature mode) -
            twoRateFactor lower upper (base mode)| := htriangle
    _ ≤ twoRateBound lower upper +
          curvatureDriftEnvelope lower upper (base mode)
            (firstCurvature mode) (secondCurvature mode) :=
      add_le_add hbase hdelta
    _ ≤ twoRateBound lower upper + certificate.driftBound :=
      add_le_add_right (certificate.envelope_le mode)
        (twoRateBound lower upper)

/-- A certified pointwise curvature-drift budget gives a simultaneous modal
norm bound for the ordered two-sweep block. -/
theorem CurvatureDriftCertificate.varyingSweep_norm_le
    {lower upper : ℝ}
    {base firstCurvature secondCurvature : Mode → ℝ}
    (certificate : CurvatureDriftCertificate lower upper
      base firstCurvature secondCurvature)
    (hlower : 0 < lower) (hle : lower ≤ upper)
    (state : ModalState Mode) :
    ‖varyingTwoRateSweep lower upper
        firstCurvature secondCurvature state‖ ≤
      (twoRateBound lower upper + certificate.driftBound) * ‖state‖ := by
  have hbound : 0 ≤ twoRateBound lower upper + certificate.driftBound :=
    add_nonneg (twoRateBound_nonneg hlower hle) certificate.driftBound_nonneg
  have heq :
      varyingTwoRateSweep lower upper firstCurvature secondCurvature state =
        WithLp.toLp 2 (fun mode =>
          varyingTwoRateFactor lower upper
            (firstCurvature mode) (secondCurvature mode) * state mode) := by
    ext mode
    simp
  rw [heq]
  exact diagonalMultiplier_norm_le
    (fun mode => varyingTwoRateFactor lower upper
      (firstCurvature mode) (secondCurvature mode))
    (twoRateBound lower upper + certificate.driftBound)
    hbound (certificate.abs_varyingFactor_le hlower) state

theorem CurvatureDriftCertificate.varyingSweep_distance_le
    {lower upper : ℝ}
    {base firstCurvature secondCurvature : Mode → ℝ}
    (certificate : CurvatureDriftCertificate lower upper
      base firstCurvature secondCurvature)
    (hlower : 0 < lower) (hle : lower ≤ upper)
    (left right : ModalState Mode) :
    ‖varyingTwoRateSweep lower upper firstCurvature secondCurvature left -
        varyingTwoRateSweep lower upper firstCurvature secondCurvature right‖ ≤
      (twoRateBound lower upper + certificate.driftBound) *
        ‖left - right‖ := by
  have hlinear :
      varyingTwoRateSweep lower upper firstCurvature secondCurvature left -
          varyingTwoRateSweep lower upper firstCurvature secondCurvature right =
        varyingTwoRateSweep lower upper firstCurvature secondCurvature
          (left - right) := by
    ext mode
    simp
    ring
  rw [hlinear]
  exact certificate.varyingSweep_norm_le hlower hle (left - right)

/-- The time-varying block is contractive only when the fixed-spectrum factor
plus the certified drift budget remains strictly below one. -/
def CurvatureDriftCertificate.toContractionCertificate
    {lower upper : ℝ}
    {base firstCurvature secondCurvature : Mode → ℝ}
    (certificate : CurvatureDriftCertificate lower upper
      base firstCurvature secondCurvature)
    (hlower : 0 < lower) (hle : lower ≤ upper)
    (hadmissible :
      twoRateBound lower upper + certificate.driftBound < 1) :
    ContractionCertificate
      (varyingTwoRateSweep lower upper firstCurvature secondCurvature) where
  factor := twoRateBound lower upper + certificate.driftBound
  factor_nonneg :=
    add_nonneg (twoRateBound_nonneg hlower hle) certificate.driftBound_nonneg
  factor_lt_one := hadmissible
  contracts := certificate.varyingSweep_distance_le hlower hle

/-! ## Isometric transport to the active error state -/

variable {State : Type*} [NormedAddCommGroup State] [NormedSpace ℝ State]

def liftedVaryingTwoRateSweep
    (coordinates : State ≃ₗᵢ[ℝ] ModalState Mode)
    (lower upper : ℝ)
    (firstCurvature secondCurvature : Mode → ℝ)
    (state : State) : State :=
  coordinates.symm
    (varyingTwoRateSweep lower upper firstCurvature secondCurvature
      (coordinates state))

theorem CurvatureDriftCertificate.liftedVaryingSweep_distance_le
    (coordinates : State ≃ₗᵢ[ℝ] ModalState Mode)
    {lower upper : ℝ}
    {base firstCurvature secondCurvature : Mode → ℝ}
    (certificate : CurvatureDriftCertificate lower upper
      base firstCurvature secondCurvature)
    (hlower : 0 < lower) (hle : lower ≤ upper)
    (left right : State) :
    ‖liftedVaryingTwoRateSweep coordinates lower upper
        firstCurvature secondCurvature left -
      liftedVaryingTwoRateSweep coordinates lower upper
        firstCurvature secondCurvature right‖ ≤
      (twoRateBound lower upper + certificate.driftBound) *
        ‖left - right‖ := by
  have hmodal := certificate.varyingSweep_distance_le hlower hle
    (coordinates left) (coordinates right)
  simpa only [liftedVaryingTwoRateSweep, ← map_sub,
    LinearIsometryEquiv.norm_map] using hmodal

/-! ## Positive and negative three-site fixtures -/

abbrev EndpointMode := Fin 3 × Fin 2

def threeSiteEndpointCurvature (index : EndpointMode) : ℝ :=
  if index.2 = 0 then 1 else 9

theorem threeSiteEndpointCurvature_mem (index : EndpointMode) :
    1 ≤ threeSiteEndpointCurvature index ∧
      threeSiteEndpointCurvature index ≤ 9 := by
  by_cases h : index.2 = 0 <;>
    norm_num [threeSiteEndpointCurvature, h]

def unchangedThreeSiteCertificate :
    CurvatureDriftCertificate 1 9
      threeSiteEndpointCurvature
      threeSiteEndpointCurvature
      threeSiteEndpointCurvature where
  base_mem := threeSiteEndpointCurvature_mem
  driftBound := 0
  driftBound_nonneg := by norm_num
  envelope_le := by
    intro mode
    simp

theorem unchangedThreeSite_varyingSweep_exact
    (state : ModalState EndpointMode) :
    varyingTwoRateSweep 1 9
        threeSiteEndpointCurvature threeSiteEndpointCurvature state =
      (4 / 7 : ℝ) • state := by
  ext index
  by_cases h : index.2 = 0 <;>
    norm_num [varyingTwoRateSweep, varyingTwoRateFactor,
      threeSiteEndpointCurvature, h, firstRate, secondRate] <;>
    ring

/-- A fixed-curvature terminal factor of `4/7` does not protect the schedule
against a sufficiently large second-sweep curvature change. -/
theorem unitNine_secondCurvatureDrift_expands (state : ℝ) :
    varyingTwoRateFactor 1 9 1 20 * state = (-26 / 21 : ℝ) * state := by
  norm_num [varyingTwoRateFactor, firstRate, secondRate]

theorem unitNine_secondCurvatureDrift_factor_gt_one :
    1 < |varyingTwoRateFactor 1 9 1 20| := by
  norm_num [varyingTwoRateFactor, firstRate, secondRate]

#print axioms varyingTwoRateFactor_sub_fixed
#print axioms abs_varyingTwoRateFactor_sub_fixed_le
#print axioms CurvatureDriftCertificate.abs_varyingFactor_le
#print axioms CurvatureDriftCertificate.varyingSweep_norm_le
#print axioms CurvatureDriftCertificate.toContractionCertificate
#print axioms CurvatureDriftCertificate.liftedVaryingSweep_distance_le
#print axioms unchangedThreeSite_varyingSweep_exact
#print axioms unitNine_secondCurvatureDrift_factor_gt_one

end

end CurvatureDriftAcceleration

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
