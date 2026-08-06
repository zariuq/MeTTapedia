import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.MinimumInterferenceCredit
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.WorkNormalizedTruncation
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.CoordinatewiseNormalizedTransport

/-!
# Robust and work-normalized conditional credit advantage

The ideal minimum-interference boundary is first-order and exact.  A realized
predictive direction can differ from that ideal because settling is finite,
the local field is nonlinear, or an optimizer transports the raw credit.
This file charges all such effects as norm-certified direction error, adds the
directional curvature price of a finite step, and finally compares certified
progress under a common work budget.

The resulting gate is sufficient, not magical: it certifies a stronger lower
bound for the retention-weighted objective.  It does not turn a lower-bound
comparison into a claim about realized discovery yield.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace ConditionalCreditAdvantage

noncomputable section

open scoped InnerProductSpace
open DirectionalTaskDescent
open WorkNormalizedTruncation
open MinimumInterferenceCredit
open AmortizedInitialization
open AmortizedCreditReadout

variable {Parameter : Type*}
  [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]

/-- Gradient of the retention-weighted local objective. -/
def combinedGradient
    (current replay : Parameter) (retentionWeight : ℝ) : Parameter :=
  current + retentionWeight • replay

/-- The retention-weighted score is the inner product with the combined
gradient. -/
theorem retentionWeightedScore_eq_inner_combined
    (current replay candidate : Parameter) (retentionWeight : ℝ) :
    retentionWeightedScore current replay retentionWeight candidate =
      ⟪combinedGradient current replay retentionWeight, candidate⟫_ℝ := by
  rw [retentionWeightedScore, combinedGradient, inner_add_left,
    real_inner_smul_left]

/-! ## Recovering norm error from logged mechanism telemetry -/

/-- Cosine convention used by the mechanism telemetry when both norms are
nonzero. -/
def telemetryCosine (subject reference : Parameter) : ℝ :=
  ⟪subject, reference⟫_ℝ / (‖subject‖ * ‖reference‖)

/-- Squared distance reconstructed from the two norms and their cosine. -/
def telemetrySquaredDistance
    (subjectNorm referenceNorm cosine : ℝ) : ℝ :=
  subjectNorm ^ 2 + referenceNorm ^ 2 -
    2 * subjectNorm * referenceNorm * cosine

/-- The logged subject norm, reference norm, and cosine determine the exact
norm-error charge required by the robust gate. -/
theorem norm_sub_sq_eq_telemetrySquaredDistance
    (subject reference : Parameter)
    (subject_norm_pos : 0 < ‖subject‖)
    (reference_norm_pos : 0 < ‖reference‖) :
    ‖subject - reference‖ ^ 2 =
      telemetrySquaredDistance ‖subject‖ ‖reference‖
        (telemetryCosine subject reference) := by
  have denominator_ne : ‖subject‖ * ‖reference‖ ≠ 0 :=
    mul_ne_zero (ne_of_gt subject_norm_pos) (ne_of_gt reference_norm_pos)
  have product_cosine :
      ‖subject‖ * ‖reference‖ * telemetryCosine subject reference =
        ⟪subject, reference⟫_ℝ := by
    rw [telemetryCosine]
    field_simp [denominator_ne]
  rw [norm_sub_sq_real]
  unfold telemetrySquaredDistance
  nlinarith [product_cosine]

namespace TelemetryWitness

theorem identical_has_zero_squaredDistance :
    telemetrySquaredDistance ‖(1 : ℝ)‖ ‖(1 : ℝ)‖
        (telemetryCosine (1 : ℝ) 1) = 0 := by
  norm_num [telemetrySquaredDistance, telemetryCosine, Real.norm_eq_abs]

theorem opposite_has_four_squaredDistance :
    telemetrySquaredDistance ‖(-1 : ℝ)‖ ‖(1 : ℝ)‖
        (telemetryCosine (-1 : ℝ) 1) = 4 := by
  norm_num [telemetrySquaredDistance, telemetryCosine, Real.norm_eq_abs]

end TelemetryWitness

/-- Exact ideal score gain over raw backpropagation in the conflicting
branch. -/
theorem ideal_score_gap_eq_of_conflict
    (current replay : Parameter) (retentionWeight : ℝ)
    (conflict : ⟪replay, current⟫_ℝ < 0) :
    retentionWeightedScore current replay retentionWeight
          (direction current replay) -
        retentionWeightedScore current replay retentionWeight current =
      -⟪replay, current⟫_ℝ ^ 2 / ‖replay‖ ^ 2 -
        retentionWeight * ⟪replay, current⟫_ℝ := by
  rw [retentionWeightedScore_direction_eq_of_conflict
      current replay retentionWeight conflict,
    retentionWeightedScore_current]
  ring

/-- A norm ball around an ideal direction gives a lower bound on the realized
retention-weighted score. -/
theorem retentionWeightedScore_realized_lower
    (current replay ideal realized : Parameter)
    (retentionWeight error : ℝ)
    (error_bound : ‖realized - ideal‖ ≤ error) :
    retentionWeightedScore current replay retentionWeight ideal -
        ‖combinedGradient current replay retentionWeight‖ * error ≤
      retentionWeightedScore current replay retentionWeight realized := by
  rw [retentionWeightedScore_eq_inner_combined,
    retentionWeightedScore_eq_inner_combined]
  let joint := combinedGradient current replay retentionWeight
  have decomposition : realized = ideal + (realized - ideal) := by abel
  rw [decomposition, inner_add_right]
  have cauchy :
      -(‖joint‖ * ‖realized - ideal‖) ≤
        ⟪joint, realized - ideal⟫_ℝ :=
    neg_le_of_abs_le (abs_real_inner_le_norm joint (realized - ideal))
  have scaled :
      ‖joint‖ * ‖realized - ideal‖ ≤ ‖joint‖ * error :=
    mul_le_mul_of_nonneg_left error_bound (norm_nonneg joint)
  dsimp only [joint] at cauchy scaled ⊢
  linarith

omit [InnerProductSpace ℝ Parameter] in
/-- Settling error followed by optimizer-transport error adds by the triangle
inequality.  The names describe the intended decomposition; the theorem is
valid for any two successive approximations. -/
theorem realized_error_le_settling_add_optimizer
    (ideal settled realized : Parameter)
    (settlingError optimizerError : ℝ)
    (settling_bound : ‖settled - ideal‖ ≤ settlingError)
    (optimizer_bound : ‖realized - settled‖ ≤ optimizerError) :
    ‖realized - ideal‖ ≤ settlingError + optimizerError := by
  calc
    ‖realized - ideal‖ =
        ‖(realized - settled) + (settled - ideal)‖ := by
      congr 1
      abel
    _ ≤ ‖realized - settled‖ + ‖settled - ideal‖ := norm_add_le _ _
    _ ≤ optimizerError + settlingError :=
      add_le_add optimizer_bound settling_bound
    _ = settlingError + optimizerError := add_comm _ _

/-! ## A concrete coordinatewise optimizer-error certificate -/

open CoordinatewiseNormalizedTransport
open SettledCreditSpectralGeometry

section CoordinateOptimizer

variable {ι : Type*} [Fintype ι]

/-- Bundle logged finite coordinates as a Euclidean vector. -/
noncomputable def toEuclidean (value : ι → ℝ) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 value

omit [Fintype ι] in
@[simp] theorem toEuclidean_apply (value : ι → ℝ) (index : ι) :
    toEuclidean value index = value index := rfl

theorem toEuclidean_norm_sq (value : ι → ℝ) :
    ‖toEuclidean value‖ ^ 2 = coordinateNormSq value := by
  rw [EuclideanSpace.real_norm_sq_eq, coordinateNormSq_apply]
  rfl

/-- The inverse-root moment divergence bound becomes a Euclidean norm-error
certificate suitable for the robust admission theorem. -/
theorem optimizer_transport_error_le
    (stabilizer : ℝ) (first second credit : ι → ℝ)
    (divergence : ℝ) (divergence_nonneg : 0 ≤ divergence)
    (moment_divergence :
      InverseRootDivergenceAtMost stabilizer first second divergence) :
    ‖toEuclidean
          (normalizedDisplacement stabilizer first credit) -
        toEuclidean
          (normalizedDisplacement stabilizer second credit)‖ ≤
      divergence * ‖toEuclidean credit‖ := by
  have squared := normalizedDisplacement_sub_normSq_le stabilizer first
    second credit divergence divergence_nonneg moment_divergence
  have rhs_nonneg : 0 ≤ divergence * ‖toEuclidean credit‖ :=
    mul_nonneg divergence_nonneg (norm_nonneg _)
  apply (sq_le_sq₀ (norm_nonneg _) rhs_nonneg).mp
  rw [show toEuclidean
        (normalizedDisplacement stabilizer first credit) -
      toEuclidean
        (normalizedDisplacement stabilizer second credit) =
      toEuclidean
        (normalizedDisplacement stabilizer first credit -
          normalizedDisplacement stabilizer second credit) by
        ext index
        simp]
  rw [toEuclidean_norm_sq, mul_pow, toEuclidean_norm_sq]
  exact squared

end CoordinateOptimizer

/-- A realized approximate direction still beats BP at first order whenever
its score-error charge fits strictly inside the ideal advantage gap. -/
theorem realized_score_gt_bp_of_error_lt_gap
    (current replay realized : Parameter) (retentionWeight error : ℝ)
    (error_bound :
      ‖realized - direction current replay‖ ≤ error)
    (error_lt_gap :
      ‖combinedGradient current replay retentionWeight‖ * error <
        retentionWeightedScore current replay retentionWeight
            (direction current replay) -
          retentionWeightedScore current replay retentionWeight current) :
    retentionWeightedScore current replay retentionWeight realized >
      retentionWeightedScore current replay retentionWeight current := by
  have lower := retentionWeightedScore_realized_lower current replay
    (direction current replay) realized retentionWeight error error_bound
  linarith

/-- Observable conflicting-branch form of the robust first-order gate. -/
theorem realized_score_gt_bp_of_observable_gate
    (current replay realized : Parameter) (retentionWeight error : ℝ)
    (conflict : ⟪replay, current⟫_ℝ < 0)
    (error_bound :
      ‖realized - direction current replay‖ ≤ error)
    (gate :
      ‖combinedGradient current replay retentionWeight‖ * error <
        -⟪replay, current⟫_ℝ ^ 2 / ‖replay‖ ^ 2 -
          retentionWeight * ⟪replay, current⟫_ℝ) :
    retentionWeightedScore current replay retentionWeight realized >
      retentionWeightedScore current replay retentionWeight current := by
  apply realized_score_gt_bp_of_error_lt_gap current replay realized
    retentionWeight error error_bound
  simpa [ideal_score_gap_eq_of_conflict current replay retentionWeight
    conflict] using gate

/-! ## Finite-step nonlinear curvature -/

/-- If the ideal advantage pays both the direction-error charge and the extra
directional-curvature charge, the realized direction has a strictly stronger
one-step decrease guarantee than BP. -/
theorem realized_decreaseLower_gt_bp_of_gate
    (current replay realized : Parameter)
    (retentionWeight error step pcCurvature bpCurvature : ℝ)
    (error_bound :
      ‖realized - direction current replay‖ ≤ error)
    (step_pos : 0 < step)
    (gate :
      ‖combinedGradient current replay retentionWeight‖ * error +
          step * (pcCurvature - bpCurvature) / 2 <
        retentionWeightedScore current replay retentionWeight
            (direction current replay) -
          retentionWeightedScore current replay retentionWeight current) :
    directionalDecreaseLower step
          (retentionWeightedScore current replay retentionWeight current)
          bpCurvature <
      directionalDecreaseLower step
          (retentionWeightedScore current replay retentionWeight realized)
          pcCurvature := by
  have lower := retentionWeightedScore_realized_lower current replay
    (direction current replay) realized retentionWeight error error_bound
  unfold directionalDecreaseLower
  have scaled := mul_lt_mul_of_pos_left gate step_pos
  nlinarith

/-- A nonnegative BP guarantee plus the robust comparative gate certifies a
genuine finite-step decrease of the retention-weighted nonlinear objective
along the realized predictive direction. -/
theorem realized_strict_descent_of_gate
    {loss : Parameter → ℝ} {parameter current replay realized : Parameter}
    {retentionWeight error step pcCurvature bpCurvature : ℝ}
    (certificate :
      HasDirectionalTaskUpperModelAt loss parameter
        (combinedGradient current replay retentionWeight) realized pcCurvature)
    (error_bound :
      ‖realized - direction current replay‖ ≤ error)
    (step_pos : 0 < step)
    (bp_guarantee_nonneg :
      0 ≤ directionalDecreaseLower step
        (retentionWeightedScore current replay retentionWeight current)
        bpCurvature)
    (gate :
      ‖combinedGradient current replay retentionWeight‖ * error +
          step * (pcCurvature - bpCurvature) / 2 <
        retentionWeightedScore current replay retentionWeight
            (direction current replay) -
          retentionWeightedScore current replay retentionWeight current) :
    loss (parameter - step • realized) < loss parameter := by
  have comparison := realized_decreaseLower_gt_bp_of_gate current replay
    realized retentionWeight error step pcCurvature bpCurvature error_bound
    step_pos gate
  have positiveMargin :
      0 < directionalDecreaseLower step
        (retentionWeightedScore current replay retentionWeight realized)
        pcCurvature :=
    lt_of_le_of_lt bp_guarantee_nonneg comparison
  apply directionalTask_strict_descent certificate step_pos
  unfold directionalDecreaseLower at positiveMargin
  rw [← retentionWeightedScore_eq_inner_combined]
  nlinarith

/-! ## Work normalization -/

/-- Certified cumulative decrease lower bound under a discrete work budget. -/
def workNormalizedGuarantee
    (budget fixedCost sweepCost depth : ℕ)
    (step alignment curvature : ℝ) : ℝ :=
  cumulativeDecreaseLower
    (roundsWithin budget fixedCost sweepCost depth)
    (directionalDecreaseLower step alignment curvature)

/-- Replacing an alignment by a lower bound can only lower the
work-normalized guarantee. -/
theorem workNormalizedGuarantee_mono_alignment
    (budget fixedCost sweepCost depth : ℕ)
    (step curvature lower actual : ℝ)
    (step_nonneg : 0 ≤ step) (alignment_lower : lower ≤ actual) :
    workNormalizedGuarantee budget fixedCost sweepCost depth
        step lower curvature ≤
      workNormalizedGuarantee budget fixedCost sweepCost depth
        step actual curvature := by
  unfold workNormalizedGuarantee cumulativeDecreaseLower
  have rounds_nonneg :
      0 ≤ (roundsWithin budget fixedCost sweepCost depth : ℝ) := by positivity
  have margin_le :
      directionalDecreaseLower step lower curvature ≤
        directionalDecreaseLower step actual curvature := by
    unfold directionalDecreaseLower
    exact sub_le_sub_right
      (mul_le_mul_of_nonneg_left alignment_lower step_nonneg)
      (step ^ 2 * curvature / 2)
  exact mul_le_mul_of_nonneg_left margin_le rounds_nonneg

/-- Complete observable admission gate.  The PC side uses the conservative
alignment after charging its certified direction error.  If that robust,
work-normalized guarantee beats BP, then the guarantee computed with the
actual realized PC score also beats BP. -/
theorem workNormalized_pc_gt_bp_of_admission
    (current replay realized : Parameter)
    (retentionWeight error step pcCurvature bpCurvature : ℝ)
    (budget : ℕ)
    (pcFixed pcSweep pcDepth bpFixed bpSweep bpDepth : ℕ)
    (error_bound :
      ‖realized - direction current replay‖ ≤ error)
    (step_nonneg : 0 ≤ step)
    (admission :
      workNormalizedGuarantee budget bpFixed bpSweep bpDepth step
          (retentionWeightedScore current replay retentionWeight current)
          bpCurvature <
        workNormalizedGuarantee budget pcFixed pcSweep pcDepth step
          (retentionWeightedScore current replay retentionWeight
              (direction current replay) -
            ‖combinedGradient current replay retentionWeight‖ * error)
          pcCurvature) :
    workNormalizedGuarantee budget bpFixed bpSweep bpDepth step
          (retentionWeightedScore current replay retentionWeight current)
          bpCurvature <
      workNormalizedGuarantee budget pcFixed pcSweep pcDepth step
          (retentionWeightedScore current replay retentionWeight realized)
          pcCurvature := by
  have alignment_lower := retentionWeightedScore_realized_lower current replay
    (direction current replay) realized retentionWeight error error_bound
  have pc_mono := workNormalizedGuarantee_mono_alignment budget pcFixed
    pcSweep pcDepth step pcCurvature
    (retentionWeightedScore current replay retentionWeight
        (direction current replay) -
      ‖combinedGradient current replay retentionWeight‖ * error)
    (retentionWeightedScore current replay retentionWeight realized)
    step_nonneg alignment_lower
  exact admission.trans_le pc_mono

/-- The work gate can be discharged directly from separate settling and
optimizer error certificates. -/
theorem workNormalized_pc_gt_bp_of_component_errors
    (current replay settled realized : Parameter)
    (retentionWeight settlingError optimizerError step
      pcCurvature bpCurvature : ℝ)
    (budget : ℕ)
    (pcFixed pcSweep pcDepth bpFixed bpSweep bpDepth : ℕ)
    (settling_bound :
      ‖settled - direction current replay‖ ≤ settlingError)
    (optimizer_bound : ‖realized - settled‖ ≤ optimizerError)
    (step_nonneg : 0 ≤ step)
    (admission :
      workNormalizedGuarantee budget bpFixed bpSweep bpDepth step
          (retentionWeightedScore current replay retentionWeight current)
          bpCurvature <
        workNormalizedGuarantee budget pcFixed pcSweep pcDepth step
          (retentionWeightedScore current replay retentionWeight
              (direction current replay) -
            ‖combinedGradient current replay retentionWeight‖ *
              (settlingError + optimizerError))
          pcCurvature) :
    workNormalizedGuarantee budget bpFixed bpSweep bpDepth step
          (retentionWeightedScore current replay retentionWeight current)
          bpCurvature <
      workNormalizedGuarantee budget pcFixed pcSweep pcDepth step
          (retentionWeightedScore current replay retentionWeight realized)
          pcCurvature := by
  apply workNormalized_pc_gt_bp_of_admission current replay realized
    retentionWeight (settlingError + optimizerError) step pcCurvature
    bpCurvature budget pcFixed pcSweep pcDepth bpFixed bpSweep bpDepth
  · exact realized_error_le_settling_add_optimizer
      (direction current replay) settled realized settlingError optimizerError
      settling_bound optimizer_bound
  · exact step_nonneg
  · exact admission

section ResidualOptimizer

variable {State : Type*} [NormedAddCommGroup State]

/-- Residual-certified settling plus a separately certified optimizer
transport error discharges the complete work-normalized admission theorem.
The residual and optimizer error can be reconstructed from existing telemetry;
the contraction factor, readout constant, and equilibrium mismatch remain
explicit certificate obligations. -/
theorem workNormalized_pc_gt_bp_of_residual_and_optimizer
    (current replay realized : Parameter)
    (retentionWeight optimizerError step pcCurvature bpCurvature : ℝ)
    (budget : ℕ)
    (pcFixed pcSweep pcDepth bpFixed bpSweep bpDepth : ℕ)
    {solver : State → State}
    (certificate : ContractionCertificate solver)
    (target state : State) (target_fixed : IsFixedPoint solver target)
    (readout : State → Parameter)
    (readoutConstant : ℝ) (readoutConstant_nonneg : 0 ≤ readoutConstant)
    (readout_lipschitz :
      CreditReadoutLipschitzAt readout target readoutConstant)
    (optimizer_bound : ‖realized - readout state‖ ≤ optimizerError)
    (step_nonneg : 0 ≤ step)
    (admission :
      let settlingError :=
        readoutConstant *
            (‖state - solver state‖ / (1 - certificate.factor)) +
          ‖readout target - direction current replay‖
      workNormalizedGuarantee budget bpFixed bpSweep bpDepth step
          (retentionWeightedScore current replay retentionWeight current)
          bpCurvature <
        workNormalizedGuarantee budget pcFixed pcSweep pcDepth step
          (retentionWeightedScore current replay retentionWeight
              (direction current replay) -
            ‖combinedGradient current replay retentionWeight‖ *
              (settlingError + optimizerError))
          pcCurvature) :
    workNormalizedGuarantee budget bpFixed bpSweep bpDepth step
          (retentionWeightedScore current replay retentionWeight current)
          bpCurvature <
      workNormalizedGuarantee budget pcFixed pcSweep pcDepth step
          (retentionWeightedScore current replay retentionWeight realized)
          pcCurvature := by
  let settlingError :=
    readoutConstant *
        (‖state - solver state‖ / (1 - certificate.factor)) +
      ‖readout target - direction current replay‖
  have settling_bound :
      ‖readout state - direction current replay‖ ≤ settlingError := by
    simpa [settlingError] using
      creditError_le_residual_plus_equilibriumMismatch certificate target state
        target_fixed readout (direction current replay) readoutConstant
        readoutConstant_nonneg readout_lipschitz
  apply workNormalized_pc_gt_bp_of_component_errors current replay
    (readout state) realized retentionWeight settlingError optimizerError step
    pcCurvature bpCurvature budget pcFixed pcSweep pcDepth bpFixed bpSweep
    bpDepth settling_bound optimizer_bound step_nonneg
  simpa [settlingError] using admission

end ResidualOptimizer

/-! ## Positive and negative work boundaries -/

/-- A two-sweep direction with three units of certified progress per update
beats a one-sweep BP direction with one unit under budget eight. -/
theorem extra_margin_can_pay_for_settling :
    workNormalizedGuarantee 8 0 1 1 1 1 0 <
      workNormalizedGuarantee 8 0 1 2 1 3 0 := by
  norm_num [workNormalizedGuarantee, roundsWithin, settlingWork,
    cumulativeDecreaseLower, directionalDecreaseLower]

/-- The same per-update margin cannot pay for four settling sweeps under that
budget; work normalization reverses the ranking. -/
theorem excess_settling_erases_margin_advantage :
    workNormalizedGuarantee 8 0 1 4 1 3 0 <
      workNormalizedGuarantee 8 0 1 1 1 1 0 := by
  norm_num [workNormalizedGuarantee, roundsWithin, settlingWork,
    cumulativeDecreaseLower, directionalDecreaseLower]

#print axioms retentionWeightedScore_realized_lower
#print axioms norm_sub_sq_eq_telemetrySquaredDistance
#print axioms TelemetryWitness.identical_has_zero_squaredDistance
#print axioms TelemetryWitness.opposite_has_four_squaredDistance
#print axioms realized_error_le_settling_add_optimizer
#print axioms optimizer_transport_error_le
#print axioms realized_score_gt_bp_of_observable_gate
#print axioms realized_decreaseLower_gt_bp_of_gate
#print axioms realized_strict_descent_of_gate
#print axioms workNormalized_pc_gt_bp_of_admission
#print axioms workNormalized_pc_gt_bp_of_component_errors
#print axioms workNormalized_pc_gt_bp_of_residual_and_optimizer
#print axioms extra_margin_can_pay_for_settling
#print axioms excess_settling_erases_margin_advantage

end

end ConditionalCreditAdvantage

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
