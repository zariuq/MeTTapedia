import Mettapedia.MachineLearning.ContinualLearning.EvidenceLedger
import Mathlib.Tactic

/-!
# Variational continual learning in a linear-Gaussian model

Nguyen, Li, Bui, and Turner, *Variational Continual Learning* (2018,
arXiv:1710.10628), Section 2, Algorithm 1, and Appendix F, derive an online
Bayesian recursion, a coreset message schedule, and a specialization to
diagonal-Gaussian Bayesian linear regression.

This file gives the finite-dimensional update an exact semantics.  The mean
update is written in its Sherman--Morrison form and proved to solve the source
normal equation, while each diagonal precision receives the source's additive
feature-square contribution.  Exact full Gaussian information packets commute.

The diagonal projection has a different boundary.  Two concrete observations
produce the same final diagonal precision in either order but different means.
Thus exact evidence fusion may be scheduled as a set, while a sequence of
diagonal posterior projections generally may not.

No theorem here identifies a mean-field approximation with a general neural
posterior, bounds repeated variational-projection error, validates Monte Carlo
gradient estimates, or proves the source's empirical results.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

namespace VariationalContinualLearning

universe uIndex

/-- Mean and diagonal precision of a Gaussian approximation. -/
structure DiagonalGaussianState (Index : Type uIndex) where
  mean : Index → ℝ
  precision : Index → ℝ

/-- One scalar-output linear-regression observation. -/
structure Observation (Index : Type uIndex) where
  feature : Index → ℝ
  target : ℝ

variable {Index : Type uIndex} [Fintype Index]

/-- Finite feature/parameter pairing. -/
noncomputable def featureDot
    (feature parameter : Index → ℝ) : ℝ :=
  ∑ coordinate, feature coordinate * parameter coordinate

/-- Predictive variance contributed by a diagonal parameter covariance. -/
noncomputable def varianceMass
    (state : DiagonalGaussianState Index)
    (observation : Observation Index) : ℝ :=
  ∑ coordinate,
    observation.feature coordinate ^ 2 / state.precision coordinate

/-- Observation-noise variance plus parameter-induced predictive variance. -/
noncomputable def predictionDenominator
    (noiseVariance : ℝ)
    (state : DiagonalGaussianState Index)
    (observation : Observation Index) : ℝ :=
  noiseVariance + varianceMass state observation

/-- Prediction residual before incorporating the observation. -/
noncomputable def innovation
    (state : DiagonalGaussianState Index)
    (observation : Observation Index) : ℝ :=
  observation.target - featureDot observation.feature state.mean

/-- Equation (6), rewritten with the diagonal-covariance Kalman gain. -/
noncomputable def updatedMean
    (noiseVariance : ℝ)
    (state : DiagonalGaussianState Index)
    (observation : Observation Index) : Index → ℝ :=
  fun coordinate =>
    state.mean coordinate +
      ((observation.feature coordinate / state.precision coordinate) /
        predictionDenominator noiseVariance state observation) *
        innovation state observation

/-- Equation (7), the additive diagonal-precision update. -/
noncomputable def updatedPrecision
    (noiseVariance : ℝ)
    (state : DiagonalGaussianState Index)
    (observation : Observation Index) : Index → ℝ :=
  fun coordinate =>
    state.precision coordinate +
      observation.feature coordinate ^ 2 / noiseVariance

/-- One online diagonal-Gaussian projection step. -/
noncomputable def update
    (noiseVariance : ℝ)
    (state : DiagonalGaussianState Index)
    (observation : Observation Index) :
    DiagonalGaussianState Index where
  mean := updatedMean noiseVariance state observation
  precision := updatedPrecision noiseVariance state observation

theorem varianceMass_nonnegative
    (state : DiagonalGaussianState Index)
    (observation : Observation Index)
    (precision_positive : ∀ coordinate, 0 < state.precision coordinate) :
    0 ≤ varianceMass state observation := by
  unfold varianceMass
  exact Finset.sum_nonneg fun coordinate _ =>
    div_nonneg (sq_nonneg _) (le_of_lt <| precision_positive coordinate)

theorem predictionDenominator_positive
    {noiseVariance : ℝ}
    (state : DiagonalGaussianState Index)
    (observation : Observation Index)
    (noise_positive : 0 < noiseVariance)
    (precision_positive : ∀ coordinate, 0 < state.precision coordinate) :
    0 < predictionDenominator noiseVariance state observation := by
  unfold predictionDenominator
  exact add_pos_of_pos_of_nonneg noise_positive
    (varianceMass_nonnegative state observation precision_positive)

omit [Fintype Index] in
theorem updatedPrecision_positive
    {noiseVariance : ℝ}
    (state : DiagonalGaussianState Index)
    (observation : Observation Index)
    (noise_positive : 0 < noiseVariance)
    (precision_positive : ∀ coordinate, 0 < state.precision coordinate) :
    ∀ coordinate,
      0 < updatedPrecision noiseVariance state observation coordinate := by
  intro coordinate
  unfold updatedPrecision
  exact add_pos_of_pos_of_nonneg (precision_positive coordinate)
    (div_nonneg (sq_nonneg _) (le_of_lt noise_positive))

omit [Fintype Index] in
theorem updatedPrecision_sub_previous
    (noiseVariance : ℝ)
    (state : DiagonalGaussianState Index)
    (observation : Observation Index)
    (coordinate : Index) :
    updatedPrecision noiseVariance state observation coordinate -
        state.precision coordinate =
      observation.feature coordinate ^ 2 / noiseVariance := by
  unfold updatedPrecision
  ring

omit [Fintype Index] in
theorem updatedPrecision_mono
    {noiseVariance : ℝ}
    (state : DiagonalGaussianState Index)
    (observation : Observation Index)
    (noise_positive : 0 < noiseVariance) :
    ∀ coordinate,
      state.precision coordinate ≤
        updatedPrecision noiseVariance state observation coordinate := by
  intro coordinate
  unfold updatedPrecision
  exact le_add_of_nonneg_right
    (div_nonneg (sq_nonneg _) (le_of_lt noise_positive))

/-- Feature prediction after the mean update. -/
theorem featureDot_updatedMean
    (noiseVariance : ℝ)
    (state : DiagonalGaussianState Index)
    (observation : Observation Index) :
    featureDot observation.feature
        (updatedMean noiseVariance state observation) =
      featureDot observation.feature state.mean +
        varianceMass state observation *
          (innovation state observation /
            predictionDenominator noiseVariance state observation) := by
  classical
  unfold featureDot updatedMean
  simp only [mul_add, Finset.sum_add_distrib]
  congr 1
  calc
    ∑ coordinate,
        observation.feature coordinate *
          (((observation.feature coordinate /
              state.precision coordinate) /
              predictionDenominator noiseVariance state observation) *
            innovation state observation) =
        ∑ coordinate,
          (observation.feature coordinate ^ 2 /
            state.precision coordinate) *
            (innovation state observation /
              predictionDenominator noiseVariance state observation) := by
          apply Finset.sum_congr rfl
          intro coordinate _
          ring
    _ = (∑ coordinate,
          observation.feature coordinate ^ 2 /
            state.precision coordinate) *
          (innovation state observation /
            predictionDenominator noiseVariance state observation) := by
          rw [Finset.sum_mul]
    _ = varianceMass state observation *
          (innovation state observation /
            predictionDenominator noiseVariance state observation) := by
          rfl

/-- Matrix-free statement of Equation (6):
`(I + V x xᵀ / noise) m⁺ = m + V x y / noise`. -/
def SatisfiesSourceMeanEquation
    (noiseVariance : ℝ)
    (state : DiagonalGaussianState Index)
    (observation : Observation Index)
    (candidate : Index → ℝ) : Prop :=
  ∀ coordinate,
    candidate coordinate +
        (observation.feature coordinate / state.precision coordinate) *
          featureDot observation.feature candidate / noiseVariance =
      state.mean coordinate +
        (observation.feature coordinate / state.precision coordinate) *
          observation.target / noiseVariance

theorem updatedMean_satisfies_sourceEquation
    {noiseVariance : ℝ}
    (state : DiagonalGaussianState Index)
    (observation : Observation Index)
    (noise_ne : noiseVariance ≠ 0)
    (precision_ne : ∀ coordinate, state.precision coordinate ≠ 0)
    (denominator_ne :
      predictionDenominator noiseVariance state observation ≠ 0) :
    SatisfiesSourceMeanEquation noiseVariance state observation
      (updatedMean noiseVariance state observation) := by
  have denominator_expanded_ne :
      noiseVariance + varianceMass state observation ≠ 0 := by
    exact denominator_ne
  intro coordinate
  rw [featureDot_updatedMean]
  unfold updatedMean innovation predictionDenominator
  field_simp [noise_ne, denominator_expanded_ne, precision_ne coordinate]
  ring

/-! ## Exact information fusion versus repeated diagonal projection -/

/-- Full Gaussian information contributed by one observation. -/
noncomputable def observationEvidence
    (noiseVariance : ℝ)
    (observation : Observation Index) :
    GaussianEvidence Index where
  precision := fun row column =>
    observation.feature row * observation.feature column / noiseVariance
  naturalParameter := fun coordinate =>
    observation.feature coordinate * observation.target / noiseVariance

omit [Fintype Index] in
/-- Exact Gaussian information packets commute. -/
theorem exactEvidence_order_independent
    (prior : GaussianEvidence Index)
    (noiseVariance : ℝ)
    (first second : Observation Index) :
    (prior.update (observationEvidence noiseVariance first)).update
        (observationEvidence noiseVariance second) =
      (prior.update (observationEvidence noiseVariance second)).update
        (observationEvidence noiseVariance first) := by
  rw [GaussianEvidence.sequential_update_eq_additive,
    GaussianEvidence.sequential_update_eq_additive,
    GaussianEvidence.add_comm
      (observationEvidence noiseVariance first)
      (observationEvidence noiseVariance second)]

/-! ## Two-coordinate projection-order boundary -/

abbrev TwoCoordinate := Fin 2

def unitPrior : DiagonalGaussianState TwoCoordinate where
  mean := fun _ => 0
  precision := fun _ => 1

def axisObservation : Observation TwoCoordinate where
  feature := fun coordinate => if coordinate = 0 then 1 else 0
  target := 1

def jointObservation : Observation TwoCoordinate where
  feature := fun _ => 1
  target := 1

noncomputable def axisThenJoint : DiagonalGaussianState TwoCoordinate :=
  update 1 (update 1 unitPrior axisObservation) jointObservation

noncomputable def jointThenAxis : DiagonalGaussianState TwoCoordinate :=
  update 1 (update 1 unitPrior jointObservation) axisObservation

theorem axisThenJoint_mean :
    axisThenJoint.mean =
      fun coordinate => if coordinate = 0 then 3 / 5 else 1 / 5 := by
  funext coordinate
  fin_cases coordinate <;>
    norm_num [axisThenJoint, update, updatedMean, updatedPrecision,
      predictionDenominator, varianceMass, innovation, featureDot,
      unitPrior, axisObservation, jointObservation]

theorem jointThenAxis_mean :
    jointThenAxis.mean =
      fun coordinate => if coordinate = 0 then 5 / 9 else 1 / 3 := by
  funext coordinate
  fin_cases coordinate <;>
    norm_num [jointThenAxis, update, updatedMean, updatedPrecision,
      predictionDenominator, varianceMass, innovation, featureDot,
      unitPrior, axisObservation, jointObservation]

theorem axisThenJoint_precision_eq_jointThenAxis :
    axisThenJoint.precision = jointThenAxis.precision := by
  funext coordinate
  fin_cases coordinate <;>
    norm_num [axisThenJoint, jointThenAxis, update, updatedPrecision,
      unitPrior, axisObservation, jointObservation]

/-- Repeated diagonal projection loses the exact information ledger's order
independence: the two orders have equal precision but unequal means. -/
theorem diagonalProjection_order_changes_mean :
    axisThenJoint.precision = jointThenAxis.precision ∧
      axisThenJoint.mean ≠ jointThenAxis.mean := by
  constructor
  · exact axisThenJoint_precision_eq_jointThenAxis
  · rw [axisThenJoint_mean, jointThenAxis_mean]
    intro equalMeans
    have coordinateZero := congrFun equalMeans 0
    norm_num at coordinateZero

/-! ## Coreset message scheduling

Algorithm 1 separates the available packets `C_(t-1) ∪ D_t` into the packets
used for propagation and the new coreset used only for prediction.  The set
difference is load bearing: every available packet is scheduled exactly once.
-/

section CoresetScheduling

variable {Datum : Type*} [DecidableEq Datum]

/-- Packets available when advancing from task `t - 1` to task `t`. -/
def availablePackets
    (previousCoreset currentData : Finset Datum) : Finset Datum :=
  previousCoreset ∪ currentData

/-- Equation (2): packets incorporated into the propagated approximation. -/
def propagationPackets
    (previousCoreset currentData newCoreset : Finset Datum) : Finset Datum :=
  availablePackets previousCoreset currentData \ newCoreset

/-- Equation (3): packets held out of propagation and incorporated for
prediction. -/
def predictionPackets (newCoreset : Finset Datum) : Finset Datum :=
  newCoreset

/-- Number of times one packet is used across propagation and prediction. -/
def scheduledMultiplicity
    (previousCoreset currentData newCoreset : Finset Datum)
    (datum : Datum) : ℕ :=
  (if datum ∈ propagationPackets previousCoreset currentData newCoreset
    then 1 else 0) +
  (if datum ∈ predictionPackets newCoreset then 1 else 0)

theorem propagation_prediction_disjoint
    (previousCoreset currentData newCoreset : Finset Datum) :
    Disjoint
      (propagationPackets previousCoreset currentData newCoreset)
      (predictionPackets newCoreset) := by
  refine Finset.disjoint_left.mpr ?_
  intro datum inPropagation inPrediction
  have notNew :
      datum ∉ newCoreset :=
    (Finset.mem_sdiff.mp
      (show datum ∈
        availablePackets previousCoreset currentData \ newCoreset by
        exact inPropagation)).2
  exact notNew (by simpa [predictionPackets] using inPrediction)

theorem propagation_union_prediction_eq_available
    (previousCoreset currentData newCoreset : Finset Datum)
    (newCoreset_available :
      newCoreset ⊆ availablePackets previousCoreset currentData) :
    propagationPackets previousCoreset currentData newCoreset ∪
        predictionPackets newCoreset =
      availablePackets previousCoreset currentData := by
  exact Finset.sdiff_union_of_subset newCoreset_available

/-- Algorithm 1 schedules each available data packet exactly once and every
unavailable packet zero times. -/
theorem coreset_schedule_exactly_once
    (previousCoreset currentData newCoreset : Finset Datum)
    (newCoreset_available :
      newCoreset ⊆ availablePackets previousCoreset currentData)
    (datum : Datum) :
    scheduledMultiplicity previousCoreset currentData newCoreset datum =
      if datum ∈ availablePackets previousCoreset currentData then 1 else 0 := by
  by_cases inNew : datum ∈ newCoreset
  · have inAvailable := newCoreset_available inNew
    simp [scheduledMultiplicity, propagationPackets, predictionPackets,
      inNew, inAvailable]
  · simp [scheduledMultiplicity, propagationPackets, predictionPackets, inNew]

/-- Exact scheduling preserves the sum of arbitrary commutative evidence
weights, not only packet cardinality. -/
theorem coreset_schedule_preserves_evidence
    {Weight : Type*} [AddCommMonoid Weight]
    (previousCoreset currentData newCoreset : Finset Datum)
    (newCoreset_available :
      newCoreset ⊆ availablePackets previousCoreset currentData)
    (evidence : Datum → Weight) :
    (∑ datum ∈ propagationPackets previousCoreset currentData newCoreset,
        evidence datum) +
        ∑ datum ∈ predictionPackets newCoreset, evidence datum =
      ∑ datum ∈ availablePackets previousCoreset currentData, evidence datum := by
  rw [← Finset.sum_union
    (propagation_prediction_disjoint previousCoreset currentData newCoreset)]
  rw [propagation_union_prediction_eq_available
    previousCoreset currentData newCoreset newCoreset_available]

/-! A tempting implementation that propagates every available packet and then
uses the coreset again for prediction double counts retained packets. -/

def reusedCoresetMultiplicity
    (previousCoreset currentData newCoreset : Finset Datum)
    (datum : Datum) : ℕ :=
  (if datum ∈ availablePackets previousCoreset currentData then 1 else 0) +
  (if datum ∈ newCoreset then 1 else 0)

theorem retained_packet_reuse_is_double_counting
    (previousCoreset currentData newCoreset : Finset Datum)
    (newCoreset_available :
      newCoreset ⊆ availablePackets previousCoreset currentData)
    {datum : Datum}
    (retained : datum ∈ newCoreset) :
    reusedCoresetMultiplicity previousCoreset currentData newCoreset datum = 2 := by
  have available := newCoreset_available retained
  simp [reusedCoresetMultiplicity, retained, available]

/-! Omitting old coreset packets that leave the coreset loses evidence. -/

def currentOnlyMultiplicity
    (currentData newCoreset : Finset Datum)
    (datum : Datum) : ℕ :=
  (if datum ∈ currentData \ newCoreset then 1 else 0) +
  (if datum ∈ newCoreset then 1 else 0)

theorem released_old_packet_is_lost_without_transfer
    (previousCoreset currentData newCoreset : Finset Datum)
    {datum : Datum}
    (old : datum ∈ previousCoreset)
    (notCurrent : datum ∉ currentData)
    (released : datum ∉ newCoreset) :
    datum ∈ availablePackets previousCoreset currentData ∧
      currentOnlyMultiplicity currentData newCoreset datum = 0 := by
  constructor
  · simp [availablePackets, old]
  · simp [currentOnlyMultiplicity, notCurrent, released]

/-- Concrete positive and negative scheduling fixture. -/
theorem three_packet_coreset_schedule :
    let previous : Finset (Fin 3) := {0, 1}
    let current : Finset (Fin 3) := {2}
    let retained : Finset (Fin 3) := {1, 2}
    (∀ datum,
      scheduledMultiplicity previous current retained datum = 1) ∧
      reusedCoresetMultiplicity previous current retained 1 = 2 ∧
      currentOnlyMultiplicity current retained 0 = 0 := by
  decide

end CoresetScheduling

#print axioms updatedMean_satisfies_sourceEquation
#print axioms exactEvidence_order_independent
#print axioms diagonalProjection_order_changes_mean
#print axioms coreset_schedule_exactly_once
#print axioms coreset_schedule_preserves_evidence
#print axioms retained_packet_reuse_is_double_counting
#print axioms released_old_packet_is_lost_without_transfer
#print axioms three_packet_coreset_schedule

end VariationalContinualLearning

end Mettapedia.MachineLearning.ContinualLearning
