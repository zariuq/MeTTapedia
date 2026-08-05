import Mettapedia.MachineLearning.ContinualLearning.SynapticIntelligence
import Mathlib.Tactic

/-!
# Riemannian-walk path importance

Chaudhry, Dokania, Ajanthan, and Torr,
*Riemannian Walk for Incremental Learning: Understanding Forgetting and
Intransigence* (2018, arXiv:1801.10112), Section 4.1, define a
online diagonal-Fisher update and per-coordinate path-importance score.  The
Fisher estimate is an exponential moving average.  Each logged loss
contribution is divided by the local diagonal-Fisher approximation to KL
displacement plus positive damping; the ratios are accumulated along the
optimizer path and negative final scores are clipped to zero.  The resulting
path importance is added to the diagonal Fisher in the quadratic retention
penalty.

This file gives that finite scalar construction an exact semantics.  It proves
that Fisher-normalized step sensitivity is invariant under a nonzero linear
reparameterization when gradients, displacements, and Fisher entries transform
covariantly.  The analogous Euclidean normalization is not invariant.

It also exposes a separate measurement boundary.  Summing ratios is not
invariant under regrouping optimizer events: one displacement of size two and
two displacements of size one have the same endpoint but different importance.
Thus trace interval, damping, clipping, and the actual post-optimizer
displacement are part of the estimator, not reporting details.

The final averaging rule is recency weighted rather than a permutation-
invariant mean.  No theorem here identifies an empirical diagonal Fisher with
the exact Fisher, validates a finite nonlinear KL approximation, or proves the
paper's empirical continual-learning results.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

namespace RiemannianWalk

/-! ## Online diagonal-Fisher update -/

/-- Equation (6)'s online diagonal-Fisher update for one coordinate. -/
noncomputable def movingFisher
    (rate fresh previous : ℝ) : ℝ :=
  rate * fresh + (1 - rate) * previous

theorem movingFisher_nonnegative
    {rate fresh previous : ℝ}
    (rate_nonnegative : 0 ≤ rate)
    (rate_le_one : rate ≤ 1)
    (fresh_nonnegative : 0 ≤ fresh)
    (previous_nonnegative : 0 ≤ previous) :
    0 ≤ movingFisher rate fresh previous := by
  unfold movingFisher
  exact add_nonneg
    (mul_nonneg rate_nonnegative fresh_nonnegative)
    (mul_nonneg (sub_nonneg.mpr rate_le_one) previous_nonnegative)

theorem movingFisher_mem_Icc
    {rate fresh previous : ℝ}
    (rate_mem : rate ∈ Set.Icc (0 : ℝ) 1)
    (fresh_mem : fresh ∈ Set.Icc (0 : ℝ) 1)
    (previous_mem : previous ∈ Set.Icc (0 : ℝ) 1) :
    movingFisher rate fresh previous ∈ Set.Icc (0 : ℝ) 1 := by
  rcases rate_mem with ⟨rate_nonnegative, rate_le_one⟩
  rcases fresh_mem with ⟨fresh_nonnegative, fresh_le_one⟩
  rcases previous_mem with ⟨previous_nonnegative, previous_le_one⟩
  constructor
  · exact movingFisher_nonnegative rate_nonnegative rate_le_one
      fresh_nonnegative previous_nonnegative
  · unfold movingFisher
    nlinarith

@[simp] theorem movingFisher_rate_zero (fresh previous : ℝ) :
    movingFisher 0 fresh previous = previous := by
  simp [movingFisher]

@[simp] theorem movingFisher_rate_one (fresh previous : ℝ) :
    movingFisher 1 fresh previous = fresh := by
  simp [movingFisher]

/-- The online update is chronological: at rate one half, presenting scores
`1, 0` and `0, 1` gives different final Fisher values. -/
theorem movingFisher_not_permutationInvariant :
    movingFisher (1 / 2) 0 (movingFisher (1 / 2) 1 0) = 1 / 4 ∧
      movingFisher (1 / 2) 1 (movingFisher (1 / 2) 0 0) = 1 / 2 := by
  norm_num [movingFisher]

/-! ## Per-step Riemannian sensitivity -/

/-- One coordinate of one logged optimizer interval.  `update` is the actual
post-optimizer parameter displacement. -/
structure Step where
  gradient : ℝ
  update : ℝ
  fisher : ℝ

/-- Equation (7)'s first-order loss decrease attributed to one coordinate. -/
noncomputable def linearizedLossDecrease (step : Step) : ℝ :=
  -(step.gradient * step.update)

/-- Half the diagonal-Fisher quadratic displacement used as the local KL
approximation in the source score. -/
noncomputable def localMetricCost (step : Step) : ℝ :=
  step.fisher / 2 * step.update ^ 2

/-- One summand of the source path-importance score. -/
noncomputable def stepSensitivity (damping : ℝ) (step : Step) : ℝ :=
  linearizedLossDecrease step / (localMetricCost step + damping)

/-- The unclipped sum of per-interval sensitivities. -/
noncomputable def rawPathImportance
    (damping : ℝ) (trace : List Step) : ℝ :=
  (trace.map (stepSensitivity damping)).sum

/-- The source retains only positive accumulated influence. -/
noncomputable def pathImportance
    (damping : ℝ) (trace : List Step) : ℝ :=
  max (rawPathImportance damping trace) 0

/-- Net parameter displacement represented by a trace. -/
noncomputable def netDisplacement (trace : List Step) : ℝ :=
  (trace.map Step.update).sum

@[simp] theorem rawPathImportance_nil (damping : ℝ) :
    rawPathImportance damping [] = 0 := by
  rfl

@[simp] theorem rawPathImportance_cons
    (damping : ℝ) (step : Step) (trace : List Step) :
    rawPathImportance damping (step :: trace) =
      stepSensitivity damping step + rawPathImportance damping trace := by
  rfl

@[simp] theorem rawPathImportance_append
    (damping : ℝ) (first second : List Step) :
    rawPathImportance damping (first ++ second) =
      rawPathImportance damping first + rawPathImportance damping second := by
  simp [rawPathImportance, List.map_append]

@[simp] theorem netDisplacement_nil :
    netDisplacement [] = 0 := by
  rfl

@[simp] theorem netDisplacement_cons (step : Step) (trace : List Step) :
    netDisplacement (step :: trace) =
      step.update + netDisplacement trace := by
  rfl

@[simp] theorem netDisplacement_append (first second : List Step) :
    netDisplacement (first ++ second) =
      netDisplacement first + netDisplacement second := by
  simp [netDisplacement, List.map_append]

theorem localMetricCost_nonnegative
    (step : Step) (fisher_nonnegative : 0 ≤ step.fisher) :
    0 ≤ localMetricCost step := by
  unfold localMetricCost
  positivity

theorem metricDenominator_positive
    (step : Step) {damping : ℝ}
    (fisher_nonnegative : 0 ≤ step.fisher)
    (damping_positive : 0 < damping) :
    0 < localMetricCost step + damping := by
  have cost_nonnegative :=
    localMetricCost_nonnegative step fisher_nonnegative
  linarith

theorem stepSensitivity_nonnegative
    (step : Step) {damping : ℝ}
    (decrease_nonnegative : 0 ≤ linearizedLossDecrease step)
    (fisher_nonnegative : 0 ≤ step.fisher)
    (damping_positive : 0 < damping) :
    0 ≤ stepSensitivity damping step := by
  exact div_nonneg decrease_nonnegative
    (le_of_lt <| metricDenominator_positive step fisher_nonnegative
      damping_positive)

theorem pathImportance_nonnegative
    (damping : ℝ) (trace : List Step) :
    0 ≤ pathImportance damping trace := by
  exact le_max_right _ _

/-! ## Coordinate invariance and its Euclidean boundary -/

/-- Change coordinates by `newParameter = scale * oldParameter`.
Gradients and Fisher entries transform contravariantly; displacements
transform covariantly. -/
noncomputable def reparameterize (scale : ℝ) (step : Step) : Step where
  gradient := step.gradient / scale
  update := scale * step.update
  fisher := step.fisher / scale ^ 2

theorem linearizedLossDecrease_reparameterize
    (step : Step) {scale : ℝ} (scale_ne : scale ≠ 0) :
    linearizedLossDecrease (reparameterize scale step) =
      linearizedLossDecrease step := by
  unfold linearizedLossDecrease reparameterize
  field_simp [scale_ne]

theorem localMetricCost_reparameterize
    (step : Step) {scale : ℝ} (scale_ne : scale ≠ 0) :
    localMetricCost (reparameterize scale step) =
      localMetricCost step := by
  unfold localMetricCost reparameterize
  field_simp [scale_ne]

/-- The source's Fisher-normalized scalar sensitivity is invariant under a
nonzero linear coordinate rescaling. -/
theorem stepSensitivity_reparameterize
    (damping : ℝ) (step : Step) {scale : ℝ} (scale_ne : scale ≠ 0) :
    stepSensitivity damping (reparameterize scale step) =
      stepSensitivity damping step := by
  rw [stepSensitivity, stepSensitivity,
    linearizedLossDecrease_reparameterize step scale_ne,
    localMetricCost_reparameterize step scale_ne]

/-- The Euclidean-distance analogue mentioned by the source. -/
noncomputable def euclideanSensitivity
    (damping : ℝ) (step : Step) : ℝ :=
  linearizedLossDecrease step / (step.update ^ 2 / 2 + damping)

/-- A unit descent event with unit diagonal Fisher. -/
def unitDescentStep : Step :=
  ⟨-1, 1, 1⟩

theorem unitDescent_riemannianSensitivity :
    stepSensitivity 1 unitDescentStep = 2 / 3 := by
  norm_num [stepSensitivity, linearizedLossDecrease, localMetricCost,
    unitDescentStep]

theorem doubledCoordinate_riemannianSensitivity :
    stepSensitivity 1 (reparameterize 2 unitDescentStep) = 2 / 3 := by
  rw [stepSensitivity_reparameterize 1 unitDescentStep (by norm_num)]
  exact unitDescent_riemannianSensitivity

theorem unitDescent_euclideanSensitivity :
    euclideanSensitivity 1 unitDescentStep = 2 / 3 := by
  norm_num [euclideanSensitivity, linearizedLossDecrease, unitDescentStep]

/-- Euclidean normalization does not inherit the Fisher metric's coordinate
invariance. -/
theorem doubledCoordinate_euclideanSensitivity :
    euclideanSensitivity 1 (reparameterize 2 unitDescentStep) = 1 / 3 := by
  norm_num [euclideanSensitivity, linearizedLossDecrease, reparameterize,
    unitDescentStep]

theorem euclideanSensitivity_not_reparameterizationInvariant :
    euclideanSensitivity 1 (reparameterize 2 unitDescentStep) ≠
      euclideanSensitivity 1 unitDescentStep := by
  rw [doubledCoordinate_euclideanSensitivity,
    unitDescent_euclideanSensitivity]
  norm_num

/-! ## Trace-granularity boundary -/

/-- One logged interval moving two units. -/
def oneLargeStep : List Step :=
  [⟨-1, 2, 1⟩]

/-- Two logged intervals with the same net displacement. -/
def twoSmallSteps : List Step :=
  [⟨-1, 1, 1⟩, ⟨-1, 1, 1⟩]

theorem oneLarge_twoSmall_same_netDisplacement :
    netDisplacement oneLargeStep = netDisplacement twoSmallSteps := by
  norm_num [oneLargeStep, twoSmallSteps, netDisplacement]

theorem oneLarge_rawPathImportance :
    rawPathImportance 1 oneLargeStep = 2 / 3 := by
  norm_num [oneLargeStep, rawPathImportance, stepSensitivity,
    linearizedLossDecrease, localMetricCost]

theorem twoSmall_rawPathImportance :
    rawPathImportance 1 twoSmallSteps = 4 / 3 := by
  norm_num [twoSmallSteps, rawPathImportance, stepSensitivity,
    linearizedLossDecrease, localMetricCost]

theorem oneLarge_pathImportance :
    pathImportance 1 oneLargeStep = 2 / 3 := by
  rw [pathImportance, oneLarge_rawPathImportance]
  norm_num

theorem twoSmall_pathImportance :
    pathImportance 1 twoSmallSteps = 4 / 3 := by
  rw [pathImportance, twoSmall_rawPathImportance]
  norm_num

/-- Identical parameter endpoints do not determine the source estimator:
splitting one interval into two changes the accumulated ratio. -/
theorem same_endpoint_different_pathImportance :
    netDisplacement oneLargeStep = netDisplacement twoSmallSteps ∧
      pathImportance 1 oneLargeStep ≠ pathImportance 1 twoSmallSteps := by
  constructor
  · exact oneLarge_twoSmall_same_netDisplacement
  · rw [oneLarge_pathImportance, twoSmall_pathImportance]
    norm_num

/-! ## Combined retention coefficient and continual averaging -/

/-- Equation (8)'s unnormalized diagonal retention coefficient. -/
noncomputable def combinedImportance
    (fisher pathScore : ℝ) : ℝ :=
  fisher + max pathScore 0

/-- Scalar form of the source's quadratic retention term. -/
noncomputable def retentionPenalty
    (strength fisher pathScore anchor parameter : ℝ) : ℝ :=
  strength * combinedImportance fisher pathScore *
    (parameter - anchor) ^ 2

theorem combinedImportance_nonnegative
    {fisher : ℝ} (pathScore : ℝ) (fisher_nonnegative : 0 ≤ fisher) :
    0 ≤ combinedImportance fisher pathScore := by
  unfold combinedImportance
  exact add_nonneg fisher_nonnegative (le_max_right _ _)

theorem retentionPenalty_nonnegative
    {strength fisher : ℝ} (pathScore anchor parameter : ℝ)
    (strength_nonnegative : 0 ≤ strength)
    (fisher_nonnegative : 0 ≤ fisher) :
    0 ≤ retentionPenalty strength fisher pathScore anchor parameter := by
  unfold retentionPenalty
  exact mul_nonneg
    (mul_nonneg strength_nonnegative
      (combinedImportance_nonnegative pathScore fisher_nonnegative))
    (sq_nonneg (parameter - anchor))

@[simp] theorem combinedImportance_zeroPath (fisher : ℝ) :
    combinedImportance fisher 0 = fisher := by
  simp [combinedImportance]

@[simp] theorem combinedImportance_zeroFisher (pathScore : ℝ) :
    combinedImportance 0 pathScore = max pathScore 0 := by
  simp [combinedImportance]

theorem positivePath_strictly_augments_fisher
    (fisher pathScore : ℝ) (path_positive : 0 < pathScore) :
    fisher < combinedImportance fisher pathScore := by
  simp [combinedImportance, max_eq_left (le_of_lt path_positive),
    path_positive]

/-- The task-boundary averaging rule used for accumulated path importance. -/
noncomputable def averageImportance (old fresh : ℝ) : ℝ :=
  (old + fresh) / 2

@[simp] theorem averageImportance_self (score : ℝ) :
    averageImportance score score = score := by
  simp [averageImportance]

theorem averageImportance_between
    {old fresh : ℝ} (old_le_fresh : old ≤ fresh) :
    old ≤ averageImportance old fresh ∧
      averageImportance old fresh ≤ fresh := by
  constructor <;> unfold averageImportance <;> linarith

/-- Three successive scores receive weights `1/4, 1/4, 1/2`; the rule is a
recency-weighted fold rather than their arithmetic mean. -/
theorem averageImportance_three
    (first second third : ℝ) :
    averageImportance (averageImportance first second) third =
      first / 4 + second / 4 + third / 2 := by
  unfold averageImportance
  ring

/-- Swapping the oldest and newest scores can change the retained
importance. -/
theorem averageImportance_not_permutationInvariant :
    averageImportance (averageImportance 1 0) 0 ≠
      averageImportance (averageImportance 0 0) 1 := by
  norm_num [averageImportance]

#print axioms stepSensitivity_reparameterize
#print axioms movingFisher_mem_Icc
#print axioms movingFisher_not_permutationInvariant
#print axioms euclideanSensitivity_not_reparameterizationInvariant
#print axioms same_endpoint_different_pathImportance
#print axioms retentionPenalty_nonnegative
#print axioms averageImportance_three
#print axioms averageImportance_not_permutationInvariant

end RiemannianWalk

end Mettapedia.MachineLearning.ContinualLearning
