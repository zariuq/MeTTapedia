import Mettapedia.MachineLearning.ContinualLearning.RetentionSafeUpdate

/-!
# Minimum-change retention-constrained adapter updates

This file gives a finite-dimensional positive-metric projection problem for a
proposed adapter update subject to any finite family of replay-gradient
half-spaces and an adapter trust region.  A variational-inequality certificate
is proved sufficient for global minimum change.  The file then recovers the
corresponding BP+/single-constraint GEM update, the OGD/nullspace formula, and
the exact incompatibility between spanning retention constraints and
plasticity.

The scalar projection is not presented as a solution of every nonlinear
continual-learning problem.  It is the exact local quadratic subproblem that
the online optimizer must solve at one adapter step.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

open scoped InnerProductSpace

/-! ## General finite-dimensional metric projection -/

section MetricProjection

variable {Adapter : Type*} [NormedAddCommGroup Adapter]
  [InnerProductSpace ℝ Adapter]

/-- A symmetric positive-semidefinite adapter metric.  Positive definiteness,
when needed for uniqueness, is stated separately. -/
structure AdapterMetric (Adapter : Type*) [NormedAddCommGroup Adapter]
    [InnerProductSpace ℝ Adapter] where
  operator : Adapter →L[ℝ] Adapter
  symmetric : ∀ x y,
    ⟪operator x, y⟫_ℝ = ⟪operator y, x⟫_ℝ
  nonnegative : ∀ x, 0 ≤ ⟪operator x, x⟫_ℝ

namespace AdapterMetric

/-- Bilinear pairing induced by an adapter metric. -/
noncomputable def pair (metric : AdapterMetric Adapter)
    (x y : Adapter) : ℝ :=
  ⟪metric.operator x, y⟫_ℝ

/-- Squared metric distance from a candidate update to the unconstrained task
update. -/
noncomputable def deviationSq (metric : AdapterMetric Adapter)
    (candidate proposed : Adapter) : ℝ :=
  metric.pair (candidate - proposed) (candidate - proposed)

/-- A metric is positive definite when only the zero direction has zero
squared metric length. -/
def PositiveDefinite (metric : AdapterMetric Adapter) : Prop :=
  ∀ x, x ≠ 0 → 0 < metric.pair x x

theorem pair_symmetric (metric : AdapterMetric Adapter) (x y : Adapter) :
    metric.pair x y = metric.pair y x :=
  metric.symmetric x y

theorem pair_add_left (metric : AdapterMetric Adapter) (x y z : Adapter) :
    metric.pair (x + y) z = metric.pair x z + metric.pair y z := by
  simp [pair, inner_add_left]

theorem pair_add_right (metric : AdapterMetric Adapter) (x y z : Adapter) :
    metric.pair x (y + z) = metric.pair x y + metric.pair x z := by
  simp [pair, inner_add_right]

theorem pair_smul_right (metric : AdapterMetric Adapter)
    (x y : Adapter) (scalar : ℝ) :
    metric.pair x (scalar • y) = scalar * metric.pair x y := by
  simp [pair, inner_smul_right]

theorem pair_smul_self (metric : AdapterMetric Adapter)
    (x : Adapter) (scalar : ℝ) :
    metric.pair (scalar • x) (scalar • x) =
      scalar ^ 2 * metric.pair x x := by
  simp [pair, inner_smul_left, inner_smul_right]
  ring

theorem deviationSq_nonnegative (metric : AdapterMetric Adapter)
    (candidate proposed : Adapter) :
    0 ≤ metric.deviationSq candidate proposed :=
  metric.nonnegative _

/-- Exact polarization identity behind the minimum-change proof. -/
theorem deviationSq_expansion (metric : AdapterMetric Adapter)
    (chosen candidate proposed : Adapter) :
    metric.deviationSq candidate proposed =
      metric.deviationSq chosen proposed +
        2 * metric.pair (chosen - proposed) (candidate - chosen) +
        metric.pair (candidate - chosen) (candidate - chosen) := by
  have hdecompose : candidate - proposed =
      (chosen - proposed) + (candidate - chosen) := by abel
  unfold deviationSq
  rw [hdecompose, pair_add_left, pair_add_right,
    pair_add_right]
  rw [pair_symmetric metric (candidate - chosen) (chosen - proposed)]
  ring

end AdapterMetric

variable {Task : Type*}

/-- The simultaneous local constraints: every replay-gradient linearization
must be non-increasing, and the adapter update must remain inside its trust
radius. -/
def MetricUpdateFeasible
    (retentionGradients : Task → Adapter) (radius : ℝ)
    (update : Adapter) : Prop :=
  (∀ task, ⟪retentionGradients task, update⟫_ℝ ≤ 0) ∧
    ‖update‖ ≤ radius

/-- The concrete replay-halfspace/trust-ball feasible set is closed under
line segments. -/
theorem MetricUpdateFeasible.segment
    (retentionGradients : Task → Adapter) (radius : ℝ)
    (chosen candidate : Adapter)
    (hchosen : MetricUpdateFeasible retentionGradients radius chosen)
    (hcandidate : MetricUpdateFeasible retentionGradients radius candidate)
    (scalar : ℝ) (hscalar0 : 0 ≤ scalar) (hscalar1 : scalar ≤ 1) :
    MetricUpdateFeasible retentionGradients radius
      (chosen + scalar • (candidate - chosen)) := by
  constructor
  · intro task
    have hchosenTask := hchosen.1 task
    have hcandidateTask := hcandidate.1 task
    rw [inner_add_right, inner_smul_right, inner_sub_right]
    have honeMinus : 0 ≤ 1 - scalar := by linarith
    have hleft := mul_nonpos_of_nonneg_of_nonpos honeMinus hchosenTask
    have hright := mul_nonpos_of_nonneg_of_nonpos hscalar0 hcandidateTask
    nlinarith
  · have hline : chosen + scalar • (candidate - chosen) =
        (1 - scalar) • chosen + scalar • candidate := by
      module
    rw [hline]
    calc
      ‖(1 - scalar) • chosen + scalar • candidate‖ ≤
          ‖(1 - scalar) • chosen‖ + ‖scalar • candidate‖ := norm_add_le _ _
      _ = (1 - scalar) * ‖chosen‖ + scalar * ‖candidate‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (by linarith), abs_of_nonneg hscalar0]
      _ ≤ (1 - scalar) * radius + scalar * radius := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hchosen.2 (by linarith))
          (mul_le_mul_of_nonneg_left hcandidate.2 hscalar0)
      _ = radius := by ring

/-- First-order optimality certificate for the constrained metric projection.
Unlike the desired minimum statement, this is a local variational inequality
that can be discharged by KKT multipliers or a concrete projection formula. -/
structure MetricProjectionCertificate
    (metric : AdapterMetric Adapter)
    (retentionGradients : Task → Adapter)
    (radius : ℝ) (proposed chosen : Adapter) : Prop where
  feasible : MetricUpdateFeasible retentionGradients radius chosen
  variationalInequality : ∀ candidate,
    MetricUpdateFeasible retentionGradients radius candidate →
      0 ≤ metric.pair (chosen - proposed) (candidate - chosen)

/-- Global formulation of the constrained metric projection. -/
structure IsMetricProjectionMinimum
    (metric : AdapterMetric Adapter)
    (retentionGradients : Task → Adapter)
    (radius : ℝ) (proposed chosen : Adapter) : Prop where
  feasible : MetricUpdateFeasible retentionGradients radius chosen
  minimumChange : ∀ candidate,
    MetricUpdateFeasible retentionGradients radius candidate →
      metric.deviationSq chosen proposed ≤
        metric.deviationSq candidate proposed

/-- A variational-inequality certificate gives the global minimum-change
update over all replay-safe, trust-region-feasible candidates. -/
theorem MetricProjectionCertificate.minimumChange
    (metric : AdapterMetric Adapter)
    (retentionGradients : Task → Adapter)
    (radius : ℝ) (proposed chosen : Adapter)
    (certificate : MetricProjectionCertificate metric retentionGradients
      radius proposed chosen) :
    ∀ candidate, MetricUpdateFeasible retentionGradients radius candidate →
      metric.deviationSq chosen proposed ≤
        metric.deviationSq candidate proposed := by
  intro candidate hcandidate
  have hvariation := certificate.variationalInequality candidate hcandidate
  have hremainder := metric.nonnegative (candidate - chosen)
  change 0 ≤ metric.pair (candidate - chosen) (candidate - chosen) at hremainder
  rw [metric.deviationSq_expansion chosen candidate proposed]
  nlinarith

/-- Exact characterization: for the convex replay-halfspace/trust-ball
feasible set, global metric minimum change is equivalent to the local
variational inequality. -/
theorem metricProjectionCertificate_iff_minimum
    (metric : AdapterMetric Adapter)
    (retentionGradients : Task → Adapter)
    (radius : ℝ) (proposed chosen : Adapter) :
    MetricProjectionCertificate metric retentionGradients radius proposed chosen ↔
      IsMetricProjectionMinimum metric retentionGradients radius proposed chosen := by
  constructor
  · intro certificate
    exact ⟨certificate.feasible,
      certificate.minimumChange metric retentionGradients radius proposed chosen⟩
  · intro minimum
    constructor
    · exact minimum.feasible
    · intro candidate hcandidate
      let p := metric.pair (chosen - proposed) (candidate - chosen)
      let q := metric.pair (candidate - chosen) (candidate - chosen)
      have hq : 0 ≤ q := metric.nonnegative _
      by_contra hpnot
      have hp : p < 0 := lt_of_not_ge hpnot
      let scalar := min (1 / 2 : ℝ) (-p / (q + 1))
      have hqone : 0 < q + 1 := by linarith
      have hratio : 0 < -p / (q + 1) := div_pos (by linarith) hqone
      have hscalar0 : 0 < scalar := lt_min (by norm_num) hratio
      have hscalar1 : scalar ≤ 1 :=
        (min_le_left _ _).trans (by norm_num)
      have hscalarRatio : scalar ≤ -p / (q + 1) := min_le_right _ _
      have hscaled : scalar * (q + 1) ≤ -p :=
        (le_div_iff₀ hqone).mp hscalarRatio
      let line := chosen + scalar • (candidate - chosen)
      have hlineFeasible :
          MetricUpdateFeasible retentionGradients radius line := by
        exact MetricUpdateFeasible.segment retentionGradients radius chosen candidate
          minimum.feasible hcandidate scalar (le_of_lt hscalar0) hscalar1
      have hminimum := minimum.minimumChange line hlineFeasible
      have hlineDifference : line - chosen =
          scalar • (candidate - chosen) := by
        dsimp [line]
        abel
      rw [metric.deviationSq_expansion chosen line proposed,
        hlineDifference, metric.pair_smul_right,
        metric.pair_smul_self] at hminimum
      dsimp [p, q] at hminimum hscaled hp hq hscalar0
      have hstrict : scalar * q < -p := by linarith
      have hnegative : 2 * (scalar * p) + scalar ^ 2 * q < 0 := by
        nlinarith [mul_pos hscalar0 (sub_pos.mpr hstrict)]
      linarith

/-- Positive definiteness makes the certified minimum unique. -/
theorem MetricProjectionCertificate.unique
    (metric : AdapterMetric Adapter)
    (retentionGradients : Task → Adapter)
    (radius : ℝ) (proposed chosen other : Adapter)
    (hpositive : metric.PositiveDefinite)
    (certificate : MetricProjectionCertificate metric retentionGradients
      radius proposed chosen)
    (hother : MetricUpdateFeasible retentionGradients radius other)
    (hequalCost : metric.deviationSq other proposed =
      metric.deviationSq chosen proposed) :
    other = chosen := by
  have hvariation := certificate.variationalInequality other hother
  have hexpansion := metric.deviationSq_expansion chosen other proposed
  by_contra hne
  have hdiff : other - chosen ≠ 0 := sub_ne_zero.mpr hne
  have hremainder := hpositive (other - chosen) hdiff
  nlinarith

end MetricProjection

/-! ## Scalar metric projection -/

/-- Projection of a proposed scalar update onto the retention-gradient
half-space. -/
noncomputable def scalarRetentionProjection
    (retentionGradient proposed : ℝ) : ℝ :=
  if retentionGradient * proposed ≤ 0 then proposed else 0

/-- Scalar positive-metric change from the proposed task update. -/
noncomputable def scalarMetricDeviation
    (metric candidate proposed : ℝ) : ℝ :=
  metric * (candidate - proposed) ^ 2

theorem scalarRetentionProjection_feasible
    (retentionGradient proposed : ℝ) :
    retentionGradient *
      scalarRetentionProjection retentionGradient proposed ≤ 0 := by
  unfold scalarRetentionProjection
  split_ifs with h
  · exact h
  · simp

theorem scalarRetentionProjection_minimumChange
    (metric retentionGradient proposed candidate : ℝ)
    (hmetric : 0 ≤ metric)
    (hcandidate : retentionGradient * candidate ≤ 0) :
    scalarMetricDeviation metric
        (scalarRetentionProjection retentionGradient proposed) proposed ≤
      scalarMetricDeviation metric candidate proposed := by
  unfold scalarRetentionProjection
  split_ifs with hproposed
  · unfold scalarMetricDeviation
    simpa using mul_nonneg hmetric (sq_nonneg (candidate - proposed))
  · have htask : 0 < retentionGradient * proposed := lt_of_not_ge hproposed
    have hgradient : retentionGradient ≠ 0 := by
      intro hzero
      simp [hzero] at htask
    have hopposite : proposed * candidate ≤ 0 := by
      rcases (mul_pos_iff.mp htask) with hpositive | hnegative
      · have hc : candidate ≤ 0 := by
          by_contra hcnot
          have hcpos : 0 < candidate := lt_of_not_ge hcnot
          have : 0 < retentionGradient * candidate :=
            mul_pos hpositive.1 hcpos
          linarith
        exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt hpositive.2) hc
      · have hc : 0 ≤ candidate := by
          by_contra hcnot
          have hcneg : candidate < 0 := lt_of_not_ge hcnot
          have : 0 < retentionGradient * candidate :=
            mul_pos_of_neg_of_neg hnegative.1 hcneg
          linarith
        exact mul_nonpos_of_nonpos_of_nonneg (le_of_lt hnegative.2) hc
    unfold scalarMetricDeviation
    have hsquares : proposed ^ 2 ≤ (candidate - proposed) ^ 2 := by
      nlinarith [sq_nonneg candidate]
    have := mul_le_mul_of_nonneg_left hsquares hmetric
    simpa using this

/-- If the proposed update was clipped to the adapter trust radius, its
retention projection remains within the same radius. -/
theorem scalarRetentionProjection_preserves_trustRegion
    (retentionGradient proposed radius : ℝ)
    (hradius : 0 ≤ radius)
    (hproposed : |proposed| ≤ radius) :
    |scalarRetentionProjection retentionGradient proposed| ≤ radius := by
  unfold scalarRetentionProjection
  split_ifs
  · exact hproposed
  · simpa using hradius

/-- Complete certificate for the local scalar constrained subproblem. -/
structure ScalarMinimumChangeCertificate
    (metric retentionGradient proposed radius chosen : ℝ) : Prop where
  retentionFeasible : retentionGradient * chosen ≤ 0
  trustRegionFeasible : |chosen| ≤ radius
  minimumChange : ∀ candidate,
    retentionGradient * candidate ≤ 0 → |candidate| ≤ radius →
      scalarMetricDeviation metric chosen proposed ≤
        scalarMetricDeviation metric candidate proposed

theorem scalarRetentionProjection_certificate
    (metric retentionGradient proposed radius : ℝ)
    (hmetric : 0 ≤ metric)
    (hradius : 0 ≤ radius)
    (hproposed : |proposed| ≤ radius) :
    ScalarMinimumChangeCertificate metric retentionGradient proposed radius
      (scalarRetentionProjection retentionGradient proposed) := by
  refine ⟨scalarRetentionProjection_feasible retentionGradient proposed,
    scalarRetentionProjection_preserves_trustRegion retentionGradient proposed
      radius hradius hproposed, ?_⟩
  intro candidate hretention _htrust
  exact scalarRetentionProjection_minimumChange metric retentionGradient
    proposed candidate hmetric hretention

/-! The scalar rule is not parallel infrastructure: it instantiates the
general metric projection with one replay constraint. -/

/-- Multiplication by a nonnegative scalar is the one-dimensional adapter
metric. -/
noncomputable def scalarAdapterMetric
    (metric : ℝ) (hmetric : 0 ≤ metric) : AdapterMetric ℝ where
  operator := metric • ContinuousLinearMap.id ℝ ℝ
  symmetric := by
    intro x y
    simp
    ring
  nonnegative := by
    intro x
    simp
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      mul_nonneg hmetric (mul_self_nonneg x)

@[simp] theorem scalarAdapterMetric_pair
    (metric : ℝ) (hmetric : 0 ≤ metric) (x y : ℝ) :
    (scalarAdapterMetric metric hmetric).pair x y = metric * x * y := by
  simp [AdapterMetric.pair, scalarAdapterMetric]
  ring

theorem scalarMetricUpdateFeasible_iff
    (retentionGradient radius update : ℝ) :
    MetricUpdateFeasible (Task := PUnit)
        (fun _ => retentionGradient) radius update ↔
      retentionGradient * update ≤ 0 ∧ |update| ≤ radius := by
  simp [MetricUpdateFeasible, Real.norm_eq_abs, mul_comm]

/-- The explicit scalar prospective/BP+/GEM update carries the general
variational-inequality certificate, including its adapter trust region. -/
theorem scalarRetentionProjection_generalCertificate
    (metric retentionGradient proposed radius : ℝ)
    (hmetric : 0 ≤ metric)
    (hradius : 0 ≤ radius)
    (hproposed : |proposed| ≤ radius) :
    MetricProjectionCertificate
      (scalarAdapterMetric metric hmetric)
      (fun _ : PUnit => retentionGradient) radius proposed
      (scalarRetentionProjection retentionGradient proposed) := by
  constructor
  · rw [scalarMetricUpdateFeasible_iff]
    exact ⟨scalarRetentionProjection_feasible retentionGradient proposed,
      scalarRetentionProjection_preserves_trustRegion retentionGradient
        proposed radius hradius hproposed⟩
  · intro candidate hcandidate
    rw [scalarMetricUpdateFeasible_iff] at hcandidate
    unfold scalarRetentionProjection
    split_ifs with hcompatible
    · simp
    · have htask : 0 < retentionGradient * proposed :=
        lt_of_not_ge hcompatible
      have hopposite : proposed * candidate ≤ 0 := by
        rcases (mul_pos_iff.mp htask) with hpositive | hnegative
        · have hc : candidate ≤ 0 := by
            by_contra hcnot
            have hcpos : 0 < candidate := lt_of_not_ge hcnot
            have : 0 < retentionGradient * candidate :=
              mul_pos hpositive.1 hcpos
            linarith [hcandidate.1]
          exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt hpositive.2) hc
        · have hc : 0 ≤ candidate := by
            by_contra hcnot
            have hcneg : candidate < 0 := lt_of_not_ge hcnot
            have : 0 < retentionGradient * candidate :=
              mul_pos_of_neg_of_neg hnegative.1 hcneg
            linarith [hcandidate.1]
          exact mul_nonpos_of_nonpos_of_nonneg (le_of_lt hnegative.2) hc
      rw [scalarAdapterMetric_pair]
      have hnonnegative : 0 ≤ metric * (-(proposed * candidate)) :=
        mul_nonneg hmetric (neg_nonneg.mpr hopposite)
      nlinarith

/-! ## BP+ and GEM are the same local projection -/

/-- BP plus one exact replay-gradient constraint. -/
noncomputable def bpPlusScalarUpdate
    (retentionGradient proposed : ℝ) : ℝ :=
  scalarRetentionProjection retentionGradient proposed

/-- Single-constraint scalar GEM update. -/
noncomputable def gemSingleConstraintScalarUpdate
    (retentionGradient proposed : ℝ) : ℝ :=
  scalarRetentionProjection retentionGradient proposed

theorem bpPlus_eq_singleConstraintGEM
    (retentionGradient proposed : ℝ) :
    bpPlusScalarUpdate retentionGradient proposed =
      gemSingleConstraintScalarUpdate retentionGradient proposed := rfl

/-! ## OGD/nullspace recovery -/

section FiniteAdapter

variable {Index : Type*} [Fintype Index]

/-- Euclidean projection of a proposed update onto the nullspace of one old
task gradient. -/
noncomputable def ogdSingleGradientUpdate
    (retentionGradient proposed : Index → ℝ) : Index → ℝ :=
  proposed -
    ((retentionGradient ⬝ᵥ proposed) /
      (retentionGradient ⬝ᵥ retentionGradient)) • retentionGradient

theorem ogdSingleGradientUpdate_exactRetention
    (retentionGradient proposed : Index → ℝ)
    (hnonzero : retentionGradient ⬝ᵥ retentionGradient ≠ 0) :
    retentionGradient ⬝ᵥ
      ogdSingleGradientUpdate retentionGradient proposed = 0 := by
  unfold ogdSingleGradientUpdate
  rw [dotProduct_sub, dotProduct_smul]
  simp only [smul_eq_mul]
  field_simp
  ring

/-- Euclidean squared deviation used by the one-gradient OGD projection. -/
noncomputable def euclideanDeviationSq
    (candidate proposed : Index → ℝ) : ℝ :=
  (candidate - proposed) ⬝ᵥ (candidate - proposed)

theorem dotProduct_self_nonnegative (x : Index → ℝ) :
    0 ≤ x ⬝ᵥ x := by
  unfold dotProduct
  exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (x i))

/-- The OGD/nullspace formula is not merely retention-exact: it is the
minimum-Euclidean-change update among all candidates satisfying the same
linearized retention equality. -/
theorem ogdSingleGradientUpdate_minimumChange
    (retentionGradient proposed candidate : Index → ℝ)
    (hnonzero : retentionGradient ⬝ᵥ retentionGradient ≠ 0)
    (hcandidate : retentionGradient ⬝ᵥ candidate = 0) :
    euclideanDeviationSq
        (ogdSingleGradientUpdate retentionGradient proposed) proposed ≤
      euclideanDeviationSq candidate proposed := by
  let chosen := ogdSingleGradientUpdate retentionGradient proposed
  let coefficient :=
    (retentionGradient ⬝ᵥ proposed) /
      (retentionGradient ⬝ᵥ retentionGradient)
  have hchosen : retentionGradient ⬝ᵥ chosen = 0 := by
    exact ogdSingleGradientUpdate_exactRetention
      retentionGradient proposed hnonzero
  have hchosenSub : chosen - proposed =
      (-coefficient) • retentionGradient := by
    funext i
    simp [chosen, coefficient, ogdSingleGradientUpdate]
  have horthogonal :
      (candidate - chosen) ⬝ᵥ (chosen - proposed) = 0 := by
    rw [hchosenSub, dotProduct_smul]
    rw [dotProduct_comm (candidate - chosen) retentionGradient]
    rw [dotProduct_sub, hcandidate, hchosen]
    simp
  have hdecompose : candidate - proposed =
      (candidate - chosen) + (chosen - proposed) := by
    abel
  unfold euclideanDeviationSq
  rw [hdecompose, add_dotProduct, dotProduct_add, dotProduct_add]
  have hreverse :
      (chosen - proposed) ⬝ᵥ (candidate - chosen) = 0 := by
    rw [dotProduct_comm]
    exact horthogonal
  rw [horthogonal, hreverse]
  simp only [add_zero, zero_add]
  exact le_add_of_nonneg_left (dotProduct_self_nonnegative (candidate - chosen))

/-- Exact retention against a family of replay gradients. -/
def PreservesAllLinearizedTasks
    {Task : Type*} (retentionGradients : Task → Index → ℝ)
    (update : Index → ℝ) : Prop :=
  ∀ task, retentionGradients task ⬝ᵥ update = 0

/-- The retention constraints exhaust all useful task directions when every
exactly preserving update has zero current-task directional derivative. -/
def RetentionConstraintsExhaustUsefulDirections
    {Task : Type*} (retentionGradients : Task → Index → ℝ)
    (currentGradient : Index → ℝ) : Prop :=
  ∀ update, PreservesAllLinearizedTasks retentionGradients update →
    currentGradient ⬝ᵥ update = 0

/-- For a fixed update, the gradients orthogonal to it form a linear
subspace.  This lets the exhaustion theorem speak about the actual span of
replay gradients rather than only a hand-written coordinate family. -/
noncomputable def dotOrthogonalSubmodule
    (update : Index → ℝ) : Submodule ℝ (Index → ℝ) where
  carrier := {gradient | gradient ⬝ᵥ update = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change (x + y) ⬝ᵥ update = 0
    change x ⬝ᵥ update = 0 at hx
    change y ⬝ᵥ update = 0 at hy
    rw [add_dotProduct]
    simp [hx, hy]
  smul_mem' := by
    intro scalar x hx
    change (scalar • x) ⬝ᵥ update = 0
    change x ⬝ᵥ update = 0 at hx
    rw [smul_dotProduct]
    simp [hx]

/-- If the current-task gradient lies in the linear span of the retained-task
gradients, every exactly-retaining update has zero current-task derivative.
This is the precise span/rank form of plasticity exhaustion. -/
theorem retentionGradientSpan_exhaustsUsefulDirections
    {Task : Type*} (retentionGradients : Task → Index → ℝ)
    (currentGradient : Index → ℝ)
    (hspan : currentGradient ∈
      Submodule.span ℝ (Set.range retentionGradients)) :
    RetentionConstraintsExhaustUsefulDirections
      retentionGradients currentGradient := by
  intro update hpreserves
  have hrange : Set.range retentionGradients ⊆
      (dotOrthogonalSubmodule update : Set (Index → ℝ)) := by
    rintro gradient ⟨task, rfl⟩
    exact hpreserves task
  exact (Submodule.span_le.mpr hrange) hspan

theorem exactRetention_implies_no_strictPlasticity
    {Task : Type*} (retentionGradients : Task → Index → ℝ)
    (currentGradient : Index → ℝ)
    (hexhausted : RetentionConstraintsExhaustUsefulDirections
      retentionGradients currentGradient) :
    ¬ ∃ update,
      PreservesAllLinearizedTasks retentionGradients update ∧
        currentGradient ⬝ᵥ update < 0 := by
  rintro ⟨update, hpreserves, himproves⟩
  have hzero := hexhausted update hpreserves
  linarith

theorem retentionGradientSpan_no_strictPlasticity
    {Task : Type*} (retentionGradients : Task → Index → ℝ)
    (currentGradient : Index → ℝ)
    (hspan : currentGradient ∈
      Submodule.span ℝ (Set.range retentionGradients)) :
    ¬ ∃ update,
      PreservesAllLinearizedTasks retentionGradients update ∧
        currentGradient ⬝ᵥ update < 0 := by
  exact exactRetention_implies_no_strictPlasticity _ currentGradient
    (retentionGradientSpan_exhaustsUsefulDirections
      retentionGradients currentGradient hspan)

/-! A concrete full-coordinate retention family. -/

noncomputable def coordinateRetentionGradient [DecidableEq Index]
    (coordinate : Index) : Index → ℝ :=
  fun i => if i = coordinate then 1 else 0

theorem preservesAllCoordinateTasks_iff_zero
    [DecidableEq Index] (update : Index → ℝ) :
    PreservesAllLinearizedTasks
        (fun coordinate : Index => coordinateRetentionGradient coordinate) update ↔
      update = 0 := by
  constructor
  · intro hpreserves
    funext coordinate
    have hcoordinate := hpreserves coordinate
    simpa [coordinateRetentionGradient, dotProduct] using hcoordinate
  · rintro rfl
    simp [PreservesAllLinearizedTasks]

theorem fullCoordinateRetention_exhausts_every_direction
    [DecidableEq Index] (currentGradient : Index → ℝ) :
    RetentionConstraintsExhaustUsefulDirections
      (fun coordinate : Index => coordinateRetentionGradient coordinate)
      currentGradient := by
  intro update hpreserves
  have hzero :=
    (preservesAllCoordinateTasks_iff_zero (Index := Index) update).mp hpreserves
  simp [hzero]

theorem fullCoordinateRetention_no_strictPlasticity_negative_example
    [DecidableEq Index] (currentGradient : Index → ℝ) :
    ¬ ∃ update,
      PreservesAllLinearizedTasks
        (fun coordinate : Index => coordinateRetentionGradient coordinate) update ∧
      currentGradient ⬝ᵥ update < 0 := by
  exact exactRetention_implies_no_strictPlasticity _ currentGradient
    (fullCoordinateRetention_exhausts_every_direction currentGradient)

end FiniteAdapter

/-! ## Scalar fixtures -/

theorem conflictingScalarUpdate_projectsToZero_positive_example :
    scalarRetentionProjection 1 1 = 0 := by
  norm_num [scalarRetentionProjection]

theorem compatibleScalarUpdate_is_unchanged_positive_example :
    scalarRetentionProjection 1 (-1) = -1 := by
  norm_num [scalarRetentionProjection]

end Mettapedia.MachineLearning.ContinualLearning
