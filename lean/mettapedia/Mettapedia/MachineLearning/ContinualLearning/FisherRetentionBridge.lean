import Mettapedia.MachineLearning.ContinualLearning.MinimumChangeUpdate
import Mettapedia.MachineLearning.NeuralNetworks.PredictiveCoding.Frontier.FisherDiagnostic

/-!
# Fisher-metric bridge for local continual learning

Under a stated local Laplace/quadratic model, old-predictive KL, the mean-shift
part of VCL, EWC, and curvature-aware replay use the same Fisher quadratic.
This file proves that algebraic identification and connects it to the existing
positive-metric minimum-change update.  It also gives an explicit
noncommuting-projector counterexample: curvature preconditioning and retention
projection cannot in general be reordered.

Nothing here identifies the exact nonlinear objectives away from the local
quadratic model; a cubic fixture records that boundary.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

open scoped InnerProductSpace

section LocalQuadraticBridge

variable {Parameter Task : Type*} [NormedAddCommGroup Parameter]
  [InnerProductSpace ℝ Parameter]

/-- Local second-order old-predictive KL. -/
noncomputable def oldPredictiveKLLocal
    (metric : AdapterMetric Parameter) (update : Parameter) : ℝ :=
  metric.pair update update / 2

/-- Mean-shift part of the equal-covariance Gaussian/Laplace VCL objective. -/
noncomputable def vclLaplaceMeanShiftLocal
    (metric : AdapterMetric Parameter) (oldParameter newParameter : Parameter) : ℝ :=
  metric.pair (newParameter - oldParameter)
    (newParameter - oldParameter) / 2

/-- EWC quadratic penalty written in Fisher coordinates. -/
noncomputable def ewcFisherPenaltyLocal
    (metric : AdapterMetric Parameter) (update : Parameter) : ℝ :=
  (1 / 2 : ℝ) * metric.pair update update

/-- Curvature-aware replay trust cost in its local KL model. -/
noncomputable def curvatureReplayKLLocal
    (metric : AdapterMetric Parameter) (update : Parameter) : ℝ :=
  metric.pair update update * (1 / 2 : ℝ)

/-- The four local objectives coincide for the same parameter displacement. -/
theorem localLaplace_retention_objectives_coincide
    (metric : AdapterMetric Parameter) (oldParameter update : Parameter) :
    vclLaplaceMeanShiftLocal metric oldParameter (oldParameter + update) =
        oldPredictiveKLLocal metric update ∧
    oldPredictiveKLLocal metric update = ewcFisherPenaltyLocal metric update ∧
      ewcFisherPenaltyLocal metric update = curvatureReplayKLLocal metric update := by
  have hupdate : oldParameter + update - oldParameter = update := by abel
  constructor
  · simp [vclLaplaceMeanShiftLocal, oldPredictiveKLLocal, hupdate]
  constructor <;>
    simp [oldPredictiveKLLocal, ewcFisherPenaltyLocal,
      curvatureReplayKLLocal] <;> ring

/-- Local minimum predicate independent of any particular optimizer name. -/
def IsLocalPenaltyMinimum
    (penalty : Parameter → ℝ) (feasible : Parameter → Prop)
    (chosen : Parameter) : Prop :=
  feasible chosen ∧ ∀ candidate, feasible candidate →
    penalty chosen ≤ penalty candidate

omit [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter] in
theorem localPenaltyMinimum_congr
    (first second : Parameter → ℝ) (feasible : Parameter → Prop)
    (chosen : Parameter) (hequal : ∀ update, first update = second update) :
    IsLocalPenaltyMinimum first feasible chosen ↔
      IsLocalPenaltyMinimum second feasible chosen := by
  constructor
  · rintro ⟨hfeasible, hminimum⟩
    refine ⟨hfeasible, ?_⟩
    intro candidate hcandidate
    simpa [hequal] using hminimum candidate hcandidate
  · rintro ⟨hfeasible, hminimum⟩
    refine ⟨hfeasible, ?_⟩
    intro candidate hcandidate
    simpa [hequal] using hminimum candidate hcandidate

/-- VCL/Laplace, EWC, and curvature-aware replay induce exactly the same local
minimum problem after all are restricted to the shared Fisher quadratic. -/
theorem vcl_ewc_curvatureReplay_same_local_minimum
    (metric : AdapterMetric Parameter) (oldParameter : Parameter)
    (feasible : Parameter → Prop) (chosen : Parameter) :
    IsLocalPenaltyMinimum
        (fun update => vclLaplaceMeanShiftLocal metric oldParameter
          (oldParameter + update)) feasible chosen ↔
      IsLocalPenaltyMinimum
        (fun update => ewcFisherPenaltyLocal metric update) feasible chosen ∧
      IsLocalPenaltyMinimum
        (fun update => curvatureReplayKLLocal metric update) feasible chosen := by
  have hvcl : ∀ update,
      vclLaplaceMeanShiftLocal metric oldParameter (oldParameter + update) =
        oldPredictiveKLLocal metric update := fun update =>
    (localLaplace_retention_objectives_coincide metric oldParameter update).1
  have hewc : ∀ update,
      oldPredictiveKLLocal metric update = ewcFisherPenaltyLocal metric update :=
    fun update =>
      (localLaplace_retention_objectives_coincide metric oldParameter update).2.1
  have hreplay : ∀ update,
      ewcFisherPenaltyLocal metric update = curvatureReplayKLLocal metric update :=
    fun update =>
      (localLaplace_retention_objectives_coincide metric oldParameter update).2.2
  have hvclEwc : ∀ update,
      vclLaplaceMeanShiftLocal metric oldParameter (oldParameter + update) =
        ewcFisherPenaltyLocal metric update := fun update =>
    (hvcl update).trans (hewc update)
  constructor
  · intro hminimum
    constructor
    · exact (localPenaltyMinimum_congr _ _ feasible chosen hvclEwc).mp hminimum
    · exact (localPenaltyMinimum_congr _ _ feasible chosen
        (fun update => (hvclEwc update).trans (hreplay update))).mp hminimum
  · rintro ⟨hewcMinimum, _hreplayMinimum⟩
    exact (localPenaltyMinimum_congr _ _ feasible chosen hvclEwc).mpr
      hewcMinimum

/-- Existing metric minimum-change certificates minimize the shared local KL
displacement from the proposed update. -/
theorem MetricProjectionCertificate.minimizesOldPredictiveKLLocal
    (metric : AdapterMetric Parameter)
    (retentionGradients : Task → Parameter)
    (radius : ℝ) (proposed chosen candidate : Parameter)
    (certificate : MetricProjectionCertificate metric retentionGradients
      radius proposed chosen)
    (hcandidate : MetricUpdateFeasible retentionGradients radius candidate) :
    oldPredictiveKLLocal metric (chosen - proposed) ≤
      oldPredictiveKLLocal metric (candidate - proposed) := by
  have hminimum := certificate.minimumChange metric retentionGradients
    radius proposed chosen candidate hcandidate
  change metric.pair (chosen - proposed) (chosen - proposed) ≤
    metric.pair (candidate - proposed) (candidate - proposed) at hminimum
  change metric.pair (chosen - proposed) (chosen - proposed) / 2 ≤
    metric.pair (candidate - proposed) (candidate - proposed) / 2
  linarith

end LocalQuadraticBridge

/-! ## Scope boundary -/

noncomputable def nonlinearPredictiveKLFixture (update : ℝ) : ℝ :=
  update ^ 2 / 2 + update ^ 3

noncomputable def scalarFisherQuadraticFixture (update : ℝ) : ℝ :=
  update ^ 2 / 2

/-- Equality of the local quadratic models is not equality of a nonlinear KL
objective away from the expansion point. -/
theorem nonlinearKL_not_equal_localQuadratic_fixture :
    nonlinearPredictiveKLFixture 1 ≠ scalarFisherQuadraticFixture 1 := by
  norm_num [nonlinearPredictiveKLFixture, scalarFisherQuadraticFixture]

/-! ## Curvature/projection order -/

abbrev RetentionPlane := Fin 2 → ℝ

noncomputable def curvaturePreconditioner2D
    (vector : RetentionPlane) : RetentionPlane :=
  fun coordinate => if coordinate = 0 then 2 * vector 0 else vector 1

/-- Euclidean projection onto the diagonal retention subspace. -/
noncomputable def diagonalRetentionProjection
    (vector : RetentionPlane) : RetentionPlane :=
  fun _ => (vector 0 + vector 1) / 2

noncomputable def retentionAxis0 : RetentionPlane :=
  fun coordinate => if coordinate = 0 then 1 else 0

/-- Curvature preconditioning and retention projection do not commute, even
for a positive diagonal preconditioner and an orthogonal projection. -/
theorem curvature_then_projection_ne_projection_then_curvature :
    diagonalRetentionProjection
        (curvaturePreconditioner2D retentionAxis0) ≠
      curvaturePreconditioner2D
        (diagonalRetentionProjection retentionAxis0) := by
  intro h
  have hcoordinate := congrFun h (1 : Fin 2)
  norm_num [diagonalRetentionProjection, curvaturePreconditioner2D,
    retentionAxis0] at hcoordinate

/-- Scalar/isotropic preconditioning is the positive commuting fixture. -/
theorem scalarPreconditioner_commutes_with_retentionProjection
    (scale : ℝ) (vector : RetentionPlane) :
    diagonalRetentionProjection (scale • vector) =
      scale • diagonalRetentionProjection vector := by
  funext coordinate
  simp only [diagonalRetentionProjection, Pi.smul_apply, smul_eq_mul]
  ring

end Mettapedia.MachineLearning.ContinualLearning
