import Mettapedia.MachineLearning.ContinualLearning.ElasticWeightConsolidation

/-!
# Synaptic intelligence: online path ledgers and discrete curvature

Zenke, Poole, and Ganguli, *Continual Learning Through Synaptic Intelligence*
(2017), Equations (1)--(5), assign each parameter an online contribution
`-gradient * parameterUpdate`.  At a task boundary, the contribution is
divided by squared net displacement plus a positive damping term and added to
the importance accumulated from earlier tasks.  The resulting coefficient
weights a quadratic consolidation penalty.

This file formalizes that per-coordinate construction.  It separates three
objects which have different correctness conditions:

* an exactly-once online ledger of gradient/update products;
* a task-boundary normalization whose denominator must be positive;
* the quadratic retention penalty, shared with elastic-weight consolidation.

For a scalar quadratic loss, the source's continuous path argument admits a
stronger finite-step statement.  A left-endpoint gradient ledger equals the
actual endpoint loss drop plus an explicit curvature remainder.  Consequently
the practical discrete estimator can overestimate the conservative path
integral even without stochastic noise.  An exact geometric-descent formula
quantifies the learning-rate correction and recovers the continuous-rate
coefficient at rate zero.

No theorem identifies this path-dependent importance with an endpoint Hessian
for a general nonlinear loss.  The source explicitly warns that such an
identification requires special quadratic structure.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

namespace SynapticIntelligence

/-! ## Online per-parameter ledger -/

/-- One logged optimizer event for a single parameter.  `update` is the actual
post-optimizer displacement, not an assumed multiple of the raw gradient. -/
structure OnlineStep where
  gradient : ℝ
  update : ℝ

/-- Equation (3)'s online contribution for one parameter and one optimizer
event.  The sign is chosen so descent contributes positively. -/
noncomputable def stepContribution (step : OnlineStep) : ℝ :=
  -(step.gradient * step.update)

/-- Exactly-once sum of the online contributions in one task segment. -/
noncomputable def pathContribution (trace : List OnlineStep) : ℝ :=
  (trace.map stepContribution).sum

/-- Net parameter displacement over one task segment. -/
noncomputable def netDisplacement (trace : List OnlineStep) : ℝ :=
  (trace.map OnlineStep.update).sum

/-- Sum of squared optimizer displacements.  This is the finite-step
curvature remainder's sufficient statistic. -/
noncomputable def squaredVariation (trace : List OnlineStep) : ℝ :=
  (trace.map fun step => step.update ^ 2).sum

/-- Parameter reached after replaying the logged displacements. -/
noncomputable def endpoint (start : ℝ) (trace : List OnlineStep) : ℝ :=
  start + netDisplacement trace

@[simp] theorem pathContribution_nil :
    pathContribution [] = 0 := by
  rfl

@[simp] theorem pathContribution_cons (step : OnlineStep)
    (trace : List OnlineStep) :
    pathContribution (step :: trace) =
      stepContribution step + pathContribution trace := by
  rfl

@[simp] theorem pathContribution_append
    (first second : List OnlineStep) :
    pathContribution (first ++ second) =
      pathContribution first + pathContribution second := by
  simp [pathContribution, List.map_append]

@[simp] theorem netDisplacement_nil :
    netDisplacement [] = 0 := by
  rfl

@[simp] theorem netDisplacement_cons (step : OnlineStep)
    (trace : List OnlineStep) :
    netDisplacement (step :: trace) =
      step.update + netDisplacement trace := by
  rfl

@[simp] theorem netDisplacement_append
    (first second : List OnlineStep) :
    netDisplacement (first ++ second) =
      netDisplacement first + netDisplacement second := by
  simp [netDisplacement, List.map_append]

@[simp] theorem squaredVariation_nil :
    squaredVariation [] = 0 := by
  rfl

@[simp] theorem squaredVariation_cons (step : OnlineStep)
    (trace : List OnlineStep) :
    squaredVariation (step :: trace) =
      step.update ^ 2 + squaredVariation trace := by
  rfl

@[simp] theorem squaredVariation_append
    (first second : List OnlineStep) :
    squaredVariation (first ++ second) =
      squaredVariation first + squaredVariation second := by
  simp [squaredVariation, List.map_append]

@[simp] theorem endpoint_nil (start : ℝ) :
    endpoint start [] = start := by
  simp [endpoint]

@[simp] theorem endpoint_cons (start : ℝ) (step : OnlineStep)
    (trace : List OnlineStep) :
    endpoint start (step :: trace) =
      endpoint (start + step.update) trace := by
  simp [endpoint]
  ring

/-- Segmenting a trace and assimilating both pieces exactly once does not
change its endpoint. -/
theorem endpoint_append (start : ℝ)
    (first second : List OnlineStep) :
    endpoint start (first ++ second) =
      endpoint (endpoint start first) second := by
  simp [endpoint]
  ring

/-! ## Task-boundary normalization -/

/-- The two sufficient statistics retained from one completed task. -/
structure TaskRecord where
  contribution : ℝ
  displacement : ℝ

/-- Close one task segment into the sufficient statistics used by Equation
(5). -/
noncomputable def recordTrace
    (trace : List OnlineStep) : TaskRecord :=
  ⟨pathContribution trace, netDisplacement trace⟩

/-- One summand of Equation (5). -/
noncomputable def normalizedImportance
    (record : TaskRecord) (damping : ℝ) : ℝ :=
  record.contribution / (record.displacement ^ 2 + damping)

/-- Equation (5)'s cumulative importance over completed task records. -/
noncomputable def cumulativeImportance
    (records : List TaskRecord) (damping : ℝ) : ℝ :=
  (records.map fun record => normalizedImportance record damping).sum

/-- The semantic precondition hidden by totalized real division. -/
def AdmissibleNormalization
    (record : TaskRecord) (damping : ℝ) : Prop :=
  0 < record.displacement ^ 2 + damping

theorem admissibleNormalization_of_positiveDamping
    (record : TaskRecord) {damping : ℝ}
    (dampingPositive : 0 < damping) :
    AdmissibleNormalization record damping := by
  unfold AdmissibleNormalization
  nlinarith [sq_nonneg record.displacement]

theorem admissibleNormalization_zeroDamping_iff
    (record : TaskRecord) :
    AdmissibleNormalization record 0 ↔
      record.displacement ≠ 0 := by
  unfold AdmissibleNormalization
  simp [sq_pos_iff]

theorem normalizedImportance_nonnegative
    (record : TaskRecord) {damping : ℝ}
    (contributionNonnegative : 0 ≤ record.contribution)
    (admissible : AdmissibleNormalization record damping) :
    0 ≤ normalizedImportance record damping := by
  exact div_nonneg contributionNonnegative (le_of_lt admissible)

/-- Positive damping bounds a nonnegative task contribution even when net
parameter motion is arbitrarily small. -/
theorem normalizedImportance_le_contribution_div_damping
    (record : TaskRecord) {damping : ℝ}
    (contributionNonnegative : 0 ≤ record.contribution)
    (dampingPositive : 0 < damping) :
    normalizedImportance record damping ≤
      record.contribution / damping := by
  unfold normalizedImportance
  have denominatorPositive :
      0 < record.displacement ^ 2 + damping :=
    admissibleNormalization_of_positiveDamping record dampingPositive
  apply (div_le_div_iff₀ denominatorPositive dampingPositive).2
  nlinarith [sq_nonneg record.displacement]

@[simp] theorem cumulativeImportance_nil (damping : ℝ) :
    cumulativeImportance [] damping = 0 := by
  rfl

@[simp] theorem cumulativeImportance_append
    (first second : List TaskRecord) (damping : ℝ) :
    cumulativeImportance (first ++ second) damping =
      cumulativeImportance first damping +
        cumulativeImportance second damping := by
  simp [cumulativeImportance, List.map_append]

/-- If every completed task supplied a nonnegative path contribution, positive
damping makes the accumulated importance nonnegative. -/
theorem cumulativeImportance_nonnegative
    (records : List TaskRecord) {damping : ℝ}
    (dampingPositive : 0 < damping)
    (allNonnegative :
      ∀ record ∈ records, 0 ≤ record.contribution) :
    0 ≤ cumulativeImportance records damping := by
  induction records with
  | nil =>
      simp
  | cons record records inductionHypothesis =>
      simp only [cumulativeImportance, List.map_cons, List.sum_cons]
      apply add_nonneg
      · exact normalizedImportance_nonnegative record
          (allNonnegative record (by simp))
          (admissibleNormalization_of_positiveDamping
            record dampingPositive)
      · exact inductionHypothesis (by
          intro later laterMem
          exact allNonnegative later (by simp [laterMem]))

/-! ## Exact finite-step quadratic correspondence -/

/-- One-coordinate quadratic loss used for the source's Hessian analysis. -/
noncomputable def quadraticEnergy
    (curvature anchor parameter : ℝ) : ℝ :=
  curvature / 2 * (parameter - anchor) ^ 2

/-- Its exact scalar gradient. -/
noncomputable def quadraticGradient
    (curvature anchor parameter : ℝ) : ℝ :=
  curvature * (parameter - anchor)

/-- A logged trace uses the exact left-endpoint quadratic gradient.  Updates
remain arbitrary, so this predicate also covers momentum and adaptive
optimizers when their actual displacements are logged. -/
def FollowsQuadratic
    (curvature anchor start : ℝ) :
    List OnlineStep → Prop
  | [] => True
  | step :: trace =>
      step.gradient = quadraticGradient curvature anchor start ∧
        FollowsQuadratic curvature anchor
          (start + step.update) trace

/-- Exact Taylor identity for one logged displacement. -/
theorem quadratic_stepContribution_eq_energyDrop_add_remainder
    (curvature anchor parameter update : ℝ) :
    stepContribution
        ⟨quadraticGradient curvature anchor parameter, update⟩ =
      quadraticEnergy curvature anchor parameter -
        quadraticEnergy curvature anchor (parameter + update) +
        curvature / 2 * update ^ 2 := by
  unfold stepContribution quadraticGradient quadraticEnergy
  ring

/-- Finite, source-strengthened path theorem.  The online left-gradient ledger
is the endpoint loss drop plus an exact curvature remainder.  Thus finite
updates can overestimate the conservative path integral even without
stochastic gradient noise. -/
theorem pathContribution_eq_energyDrop_add_curvatureRemainder
    (curvature anchor start : ℝ) (trace : List OnlineStep)
    (follows : FollowsQuadratic curvature anchor start trace) :
    pathContribution trace =
      quadraticEnergy curvature anchor start -
        quadraticEnergy curvature anchor (endpoint start trace) +
        curvature / 2 * squaredVariation trace := by
  induction trace generalizing start with
  | nil =>
      simp
  | cons step trace inductionHypothesis =>
      rcases follows with ⟨gradientExact, restFollows⟩
      rw [pathContribution_cons, endpoint_cons,
        squaredVariation_cons]
      have localIdentity :
          stepContribution step =
            quadraticEnergy curvature anchor start -
              quadraticEnergy curvature anchor (start + step.update) +
              curvature / 2 * step.update ^ 2 := by
        unfold stepContribution
        rw [gradientExact]
        unfold quadraticGradient quadraticEnergy
        ring
      rw [localIdentity,
        inductionHypothesis (start := start + step.update)
          restFollows]
      ring

/-- The source's continuous path equality is recovered exactly when the
finite-step curvature remainder vanishes. -/
theorem pathContribution_eq_energyDrop_of_zero_squaredVariation
    (curvature anchor start : ℝ) (trace : List OnlineStep)
    (follows : FollowsQuadratic curvature anchor start trace)
    (zeroVariation : squaredVariation trace = 0) :
    pathContribution trace =
      quadraticEnergy curvature anchor start -
        quadraticEnergy curvature anchor (endpoint start trace) := by
  rw [
    pathContribution_eq_energyDrop_add_curvatureRemainder
      curvature anchor start trace follows,
    zeroVariation
  ]
  ring

/-- At nonnegative curvature, the discrete ledger is at least the actual
quadratic endpoint loss drop. -/
theorem energyDrop_le_pathContribution
    {curvature : ℝ} (anchor start : ℝ) (trace : List OnlineStep)
    (curvatureNonnegative : 0 ≤ curvature)
    (follows : FollowsQuadratic curvature anchor start trace) :
    quadraticEnergy curvature anchor start -
        quadraticEnergy curvature anchor (endpoint start trace) ≤
      pathContribution trace := by
  rw [
    pathContribution_eq_energyDrop_add_curvatureRemainder
      curvature anchor start trace follows
  ]
  have variationNonnegative : 0 ≤ squaredVariation trace := by
    unfold squaredVariation
    exact List.sum_nonneg (by
      intro value valueMem
      obtain ⟨step, _, rfl⟩ := List.mem_map.mp valueMem
      exact sq_nonneg step.update)
  nlinarith

/-! ## Gradient-descent specialization and exact discrete correction -/

/-- One exact gradient-descent event. -/
noncomputable def gradientDescentStep
    (rate curvature anchor parameter : ℝ) : OnlineStep :=
  let gradient := quadraticGradient curvature anchor parameter
  ⟨gradient, -(rate * gradient)⟩

/-- A finite exact gradient-descent trace. -/
noncomputable def gradientDescentTrace
    (rate curvature anchor : ℝ) :
    ℝ → ℕ → List OnlineStep
  | _, 0 => []
  | parameter, steps + 1 =>
      let step := gradientDescentStep rate curvature anchor parameter
      step ::
        gradientDescentTrace rate curvature anchor
          (parameter + step.update) steps

theorem gradientDescentTrace_followsQuadratic
    (rate curvature anchor parameter : ℝ) (steps : ℕ) :
    FollowsQuadratic curvature anchor parameter
      (gradientDescentTrace rate curvature anchor parameter steps) := by
  induction steps generalizing parameter with
  | zero =>
      simp [gradientDescentTrace, FollowsQuadratic]
  | succ steps inductionHypothesis =>
      simp only [gradientDescentTrace, FollowsQuadratic]
      constructor
      · rfl
      · exact inductionHypothesis
          (parameter +
            (gradientDescentStep rate curvature anchor parameter).update)

theorem gradientDescentStep_contribution
    (rate curvature anchor parameter : ℝ) :
    stepContribution
        (gradientDescentStep rate curvature anchor parameter) =
      rate * quadraticGradient curvature anchor parameter ^ 2 := by
  simp [gradientDescentStep, stepContribution]
  ring

theorem gradientDescentStep_error
    (rate curvature anchor parameter : ℝ) :
    parameter +
          (gradientDescentStep rate curvature anchor parameter).update -
        anchor =
      (1 - rate * curvature) * (parameter - anchor) := by
  simp [gradientDescentStep, quadraticGradient]
  ring

/-- Recursively oriented finite geometric sum:
`1 + ratio + ... + ratio^(steps-1)`. -/
noncomputable def geometricPartial (ratio : ℝ) : ℕ → ℝ
  | 0 => 0
  | steps + 1 => 1 + ratio * geometricPartial ratio steps

theorem one_sub_mul_geometricPartial
    (ratio : ℝ) (steps : ℕ) :
    (1 - ratio) * geometricPartial ratio steps =
      1 - ratio ^ steps := by
  induction steps with
  | zero =>
      simp [geometricPartial]
  | succ steps inductionHypothesis =>
      rw [geometricPartial, pow_succ]
      calc
        (1 - ratio) *
              (1 + ratio * geometricPartial ratio steps) =
            (1 - ratio) +
              ratio * ((1 - ratio) *
                geometricPartial ratio steps) := by ring
        _ = (1 - ratio) + ratio * (1 - ratio ^ steps) := by
          rw [inductionHypothesis]
        _ = 1 - ratio ^ steps * ratio := by ring

theorem geometricPartial_eq_div
    (ratio : ℝ) (steps : ℕ)
    (ratioNeOne : ratio ≠ 1) :
    geometricPartial ratio steps =
      (1 - ratio ^ steps) / (1 - ratio) := by
  have denominatorNonzero : 1 - ratio ≠ 0 :=
    sub_ne_zero.mpr ratioNeOne.symm
  apply (eq_div_iff denominatorNonzero).2
  simpa [mul_comm] using one_sub_mul_geometricPartial ratio steps

/-- Closed endpoint of the exact scalar gradient-descent trace. -/
theorem gradientDescentTrace_endpoint
    (rate curvature anchor parameter : ℝ) (steps : ℕ) :
    endpoint parameter
        (gradientDescentTrace rate curvature anchor parameter steps) =
      anchor +
        (1 - rate * curvature) ^ steps * (parameter - anchor) := by
  induction steps generalizing parameter with
  | zero =>
      simp [gradientDescentTrace]
  | succ steps inductionHypothesis =>
      rw [gradientDescentTrace, endpoint_cons,
        inductionHypothesis]
      rw [gradientDescentStep_error, pow_succ]
      ring

/-- Exact accumulated SI ledger for finite scalar quadratic gradient descent.
It exposes both the active curvature and the optimizer rate. -/
theorem gradientDescentTrace_pathContribution
    (rate curvature anchor parameter : ℝ) (steps : ℕ) :
    pathContribution
        (gradientDescentTrace rate curvature anchor parameter steps) =
      rate * curvature ^ 2 * (parameter - anchor) ^ 2 *
        geometricPartial ((1 - rate * curvature) ^ 2) steps := by
  induction steps generalizing parameter with
  | zero =>
      simp [gradientDescentTrace, geometricPartial]
  | succ steps inductionHypothesis =>
      rw [gradientDescentTrace, pathContribution_cons,
        gradientDescentStep_contribution,
        inductionHypothesis]
      rw [gradientDescentStep_error]
      simp only [quadraticGradient]
      rw [geometricPartial]
      ring

/-- Finite closed form.  The denominator reveals the sharp scalar stability
boundary `rate * curvature = 2`. -/
theorem gradientDescentTrace_pathContribution_closed
    (rate curvature anchor parameter : ℝ) (steps : ℕ)
    (rateNonzero : rate ≠ 0)
    (curvatureNonzero : curvature ≠ 0)
    (belowBoundary : 2 - rate * curvature ≠ 0) :
    pathContribution
        (gradientDescentTrace rate curvature anchor parameter steps) =
      curvature * (parameter - anchor) ^ 2 /
          (2 - rate * curvature) *
        (1 - (1 - rate * curvature) ^ (2 * steps)) := by
  let ratio : ℝ := (1 - rate * curvature) ^ 2
  have ratioNeOne : ratio ≠ 1 := by
    intro ratioEq
    have factorNonzero :
        rate * curvature * (2 - rate * curvature) ≠ 0 :=
      mul_ne_zero (mul_ne_zero rateNonzero curvatureNonzero)
        belowBoundary
    have factorZero :
        rate * curvature * (2 - rate * curvature) = 0 := by
      dsimp [ratio] at ratioEq
      nlinarith
    exact factorNonzero factorZero
  have geometricDenominatorNonzero :
      1 - (1 - rate * curvature) ^ 2 ≠ 0 := by
    change 1 - ratio ≠ 0
    exact sub_ne_zero.mpr ratioNeOne.symm
  rw [gradientDescentTrace_pathContribution,
    geometricPartial_eq_div ratio steps ratioNeOne]
  change
    rate * curvature ^ 2 * (parameter - anchor) ^ 2 *
        ((1 - ((1 - rate * curvature) ^ 2) ^ steps) /
          (1 - (1 - rate * curvature) ^ 2)) =
      _
  rw [← pow_mul]
  field_simp [geometricDenominatorNonzero, belowBoundary]
  ring

/-- The infinite-horizon normalized coefficient suggested by the exact finite
geometric formula.  It is only a quadratic-gradient-descent quantity. -/
noncomputable def asymptoticNormalizedImportance
    (rate curvature : ℝ) : ℝ :=
  curvature / (2 - rate * curvature)

/-- The continuous-rate endpoint is half the scalar curvature under this
left-gradient contribution convention. -/
@[simp] theorem asymptoticNormalizedImportance_zeroRate
    (curvature : ℝ) :
    asymptoticNormalizedImportance 0 curvature =
      curvature / 2 := by
  simp [asymptoticNormalizedImportance]

/-- Exact finite-rate inflation over the continuous-rate coefficient. -/
theorem asymptoticNormalizedImportance_sub_continuous
    (rate curvature : ℝ)
    (belowBoundary : 2 - rate * curvature ≠ 0) :
    asymptoticNormalizedImportance rate curvature -
        curvature / 2 =
      rate * curvature ^ 2 /
        (2 * (2 - rate * curvature)) := by
  unfold asymptoticNormalizedImportance
  have commutedBoundary : 2 - curvature * rate ≠ 0 := by
    simpa [mul_comm] using belowBoundary
  field_simp [belowBoundary, commutedBoundary]
  ring

theorem asymptoticNormalizedImportance_gt_continuous
    {rate curvature : ℝ}
    (ratePositive : 0 < rate)
    (curvaturePositive : 0 < curvature)
    (stable : rate * curvature < 2) :
    curvature / 2 <
      asymptoticNormalizedImportance rate curvature := by
  rw [← sub_pos]
  rw [
    asymptoticNormalizedImportance_sub_continuous
      rate curvature (ne_of_gt (sub_pos.mpr stable))
  ]
  positivity

/-! ## Shared penalty algebra and sharp boundaries -/

/-- Equation (4)'s scalar consolidation term, including its user-selected
strength. -/
noncomputable def consolidationPenalty
    (strength importance anchor parameter : ℝ) : ℝ :=
  strength * importance * (parameter - anchor) ^ 2

/-- SI and EWC share the same quadratic penalty algebra; they differ in how
the diagonal importance/precision is estimated. -/
theorem consolidationPenalty_eq_ewcPenalty
    (strength importance anchor parameter : ℝ) :
    consolidationPenalty strength importance anchor parameter =
      ElasticWeightConsolidation.penalty
        (2 * strength * importance) anchor parameter := by
  unfold consolidationPenalty ElasticWeightConsolidation.penalty
  ring

theorem consolidationPenalty_nonnegative
    {strength importance : ℝ} (anchor parameter : ℝ)
    (strengthNonnegative : 0 ≤ strength)
    (importanceNonnegative : 0 ≤ importance) :
    0 ≤ consolidationPenalty strength importance anchor parameter := by
  unfold consolidationPenalty
  positivity

/-- A negative online importance does not define a retention penalty. -/
theorem negativeImportance_lowers_penalty :
    consolidationPenalty 1 (-1) 0 2 <
      consolidationPenalty 1 (-1) 0 0 := by
  norm_num [consolidationPenalty]

/-- A round trip can have zero net displacement but positive discrete path
importance.  Therefore zero damping is not admissible merely because the
online ledger is nonzero. -/
def roundTripTrace : List OnlineStep :=
  [⟨0, 1⟩, ⟨1, -1⟩]

theorem roundTrip_pathContribution :
    pathContribution roundTripTrace = 1 := by
  norm_num [roundTripTrace, pathContribution, stepContribution]

theorem roundTrip_netDisplacement :
    netDisplacement roundTripTrace = 0 := by
  norm_num [roundTripTrace, netDisplacement]

theorem roundTrip_zeroDamping_not_admissible :
    ¬ AdmissibleNormalization (recordTrace roundTripTrace) 0 := by
  norm_num [
    AdmissibleNormalization,
    recordTrace,
    roundTripTrace,
    netDisplacement
  ]

/-- A one-step scalar quadratic fixture realizes the exact positive
curvature remainder: the ledger reports one while the loss drops by one half. -/
theorem quadratic_discrete_overestimate :
    pathContribution [⟨1, -1⟩] = 1 ∧
      quadraticEnergy 1 0 1 -
          quadraticEnergy 1 0 (endpoint 1 [⟨1, -1⟩]) =
        1 / 2 := by
  norm_num [
    pathContribution,
    stepContribution,
    quadraticEnergy,
    endpoint,
    netDisplacement
  ]

#print axioms pathContribution_append
#print axioms cumulativeImportance_nonnegative
#print axioms pathContribution_eq_energyDrop_add_curvatureRemainder
#print axioms energyDrop_le_pathContribution
#print axioms gradientDescentTrace_pathContribution
#print axioms gradientDescentTrace_pathContribution_closed
#print axioms asymptoticNormalizedImportance_gt_continuous
#print axioms consolidationPenalty_eq_ewcPenalty
#print axioms roundTrip_zeroDamping_not_admissible
#print axioms quadratic_discrete_overestimate

end SynapticIntelligence

end Mettapedia.MachineLearning.ContinualLearning
