import Mettapedia.MachineLearning.NeuralNetworks.TwoTimescaleAdaptation.Model
import Mathlib.Algebra.Order.Floor.Div

/-!
# Two-timescale adaptation: capacity deadlines and cadence

Bounded fast state admits at most `capacity` evidence units.  At a declared
integer arrival rate, ceiling division gives the first saturation time.  The
second half of the file retains a declared continuous quadratic approximation:
early consolidation discards remaining refinement headroom, while late
consolidation accumulates saturation exposure.  Its unique optimum is correct
for that quadratic, but the functional form is not derived from the evidence
accounting above.

`DerivedCadence.lean` derives the actual counted-update/hinge-loss objective
from these primitives and proves that it generally has a different optimum.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.TwoTimescaleAdaptation

/-! ## T2: bounded fast-state capacity -/

/-- Evidence presented by `time` at a constant per-period arrival rate. -/
def arrivedEvidence (arrivalRate time : ℕ) : ℕ :=
  arrivalRate * time

/-- A bounded fast state admits all presented evidence up to its capacity. -/
def admittedEvidence (capacity arrivalRate time : ℕ) : ℕ :=
  min capacity (arrivedEvidence arrivalRate time)

/-- Presented evidence not admitted by the bounded fast state. -/
def lostEvidence (capacity arrivalRate time : ℕ) : ℕ :=
  arrivedEvidence arrivalRate time - admittedEvidence capacity arrivalRate time

/-- First period at which constant-rate arrivals reach or exceed capacity. -/
def saturationDeadline (capacity arrivalRate : ℕ) : ℕ :=
  capacity ⌈/⌉ arrivalRate

/-- The ceiling-division deadline has accumulated at least capacity whenever
the declared arrival rate is positive. -/
theorem capacity_le_arrivedEvidence_at_deadline
    (capacity arrivalRate : ℕ) (hrate : 0 < arrivalRate) :
    capacity ≤ arrivedEvidence arrivalRate
      (saturationDeadline capacity arrivalRate) := by
  unfold arrivedEvidence saturationDeadline
  exact (ceilDiv_le_iff_le_mul hrate).1 le_rfl

/-- Every earlier period is strictly below capacity. -/
theorem arrivedEvidence_lt_capacity_before_deadline
    (capacity arrivalRate time : ℕ) (hrate : 0 < arrivalRate)
    (hbefore : time < saturationDeadline capacity arrivalRate) :
    arrivedEvidence arrivalRate time < capacity := by
  unfold saturationDeadline at hbefore
  have hnot : ¬ capacity ≤ arrivalRate * time := by
    intro hcapacity
    have hdeadline : capacity ⌈/⌉ arrivalRate ≤ time :=
      (ceilDiv_le_iff_le_mul hrate).2 hcapacity
    omega
  unfold arrivedEvidence
  omega

/-- At the deadline and afterward, admitted evidence is pinned exactly at
capacity. -/
theorem admittedEvidence_eq_capacity_at_or_after_deadline
    (capacity arrivalRate time : ℕ) (hrate : 0 < arrivalRate)
    (hdeadline : saturationDeadline capacity arrivalRate ≤ time) :
    admittedEvidence capacity arrivalRate time = capacity := by
  have hat := capacity_le_arrivedEvidence_at_deadline capacity arrivalRate hrate
  have hmono :
      arrivedEvidence arrivalRate (saturationDeadline capacity arrivalRate) ≤
        arrivedEvidence arrivalRate time := by
    unfold arrivedEvidence
    exact Nat.mul_le_mul_left arrivalRate hdeadline
  unfold admittedEvidence
  rw [min_eq_left]
  exact hat.trans hmono

/-- Before the deadline every evidence unit is admitted and none is lost. -/
theorem admitted_and_lost_before_deadline
    (capacity arrivalRate time : ℕ) (hrate : 0 < arrivalRate)
    (hbefore : time < saturationDeadline capacity arrivalRate) :
    admittedEvidence capacity arrivalRate time =
        arrivedEvidence arrivalRate time ∧
      lostEvidence capacity arrivalRate time = 0 := by
  have hlt := arrivedEvidence_lt_capacity_before_deadline
    capacity arrivalRate time hrate hbefore
  constructor
  · exact min_eq_right hlt.le
  · simp [lostEvidence, admittedEvidence, min_eq_right hlt.le]

/-- At and after saturation, loss is exactly arrivals beyond capacity. -/
theorem admitted_and_lost_at_or_after_deadline
    (capacity arrivalRate time : ℕ) (hrate : 0 < arrivalRate)
    (hdeadline : saturationDeadline capacity arrivalRate ≤ time) :
    admittedEvidence capacity arrivalRate time = capacity ∧
      lostEvidence capacity arrivalRate time =
        arrivedEvidence arrivalRate time - capacity := by
  have hadmitted := admittedEvidence_eq_capacity_at_or_after_deadline
    capacity arrivalRate time hrate hdeadline
  exact ⟨hadmitted, by simp [lostEvidence, hadmitted]⟩

/-- Positive deadline fixture: capacity ten at rate three saturates at period
four; period three admits nine with no loss, while period four loses two. -/
theorem capacityTen_rateThree_deadline :
    saturationDeadline 10 3 = 4 ∧
      admittedEvidence 10 3 3 = 9 ∧
      lostEvidence 10 3 3 = 0 ∧
      admittedEvidence 10 3 4 = 10 ∧
      lostEvidence 10 3 4 = 2 := by
  norm_num [saturationDeadline, Nat.ceilDiv_eq_add_pred_div,
    admittedEvidence, arrivedEvidence, lostEvidence]

/-- Negative boundary: a zero arrival rate never fills positive capacity. -/
theorem zeroArrival_never_saturates
    (capacity time : ℕ) :
    admittedEvidence capacity 0 time = 0 ∧
      lostEvidence capacity 0 time = 0 := by
  simp [admittedEvidence, arrivedEvidence, lostEvidence]

/-! ## A retained quadratic approximation -/

/-- Continuous saturation deadline corresponding to capacity divided by
arrival rate. -/
noncomputable def realSaturationDeadline
    (arrivalRate capacity : ℝ) : ℝ :=
  capacity / arrivalRate

/-- Generic quadratic balance: `frequentCost` penalizes unused refinement
headroom `deadline - period`, while `rareCost` penalizes long exposure. -/
noncomputable def quadraticCadenceObjective
    (frequentCost rareCost deadline period : ℝ) : ℝ :=
  frequentCost * (deadline - period) ^ 2 + rareCost * period ^ 2

/-- Algebraically derived critical period for the quadratic balance. -/
noncomputable def quadraticOptimalPeriod
    (frequentCost rareCost deadline : ℝ) : ℝ :=
  frequentCost * deadline / (frequentCost + rareCost)

/-- Exact completed-square identity behind optimality. -/
theorem quadraticCadenceObjective_sub_optimal_exact
    (frequentCost rareCost deadline period : ℝ)
    (hsum : frequentCost + rareCost ≠ 0) :
    quadraticCadenceObjective frequentCost rareCost deadline period -
        quadraticCadenceObjective frequentCost rareCost deadline
          (quadraticOptimalPeriod frequentCost rareCost deadline) =
      (frequentCost + rareCost) *
        (period - quadraticOptimalPeriod frequentCost rareCost deadline) ^ 2 := by
  unfold quadraticCadenceObjective quadraticOptimalPeriod
  field_simp
  ring

/-- Positive costs give global minimality. -/
theorem quadraticOptimalPeriod_minimizes
    (frequentCost rareCost deadline period : ℝ)
    (hfrequent : 0 < frequentCost) (hrare : 0 < rareCost) :
    quadraticCadenceObjective frequentCost rareCost deadline
        (quadraticOptimalPeriod frequentCost rareCost deadline) ≤
      quadraticCadenceObjective frequentCost rareCost deadline period := by
  have hsum : frequentCost + rareCost ≠ 0 := ne_of_gt (add_pos hfrequent hrare)
  have hexact := quadraticCadenceObjective_sub_optimal_exact
    frequentCost rareCost deadline period hsum
  nlinarith [mul_nonneg (le_of_lt (add_pos hfrequent hrare))
    (sq_nonneg (period - quadraticOptimalPeriod
      frequentCost rareCost deadline))]

/-- Positive costs also make the minimizer unique. -/
theorem quadraticCadenceObjective_eq_optimal_iff
    (frequentCost rareCost deadline period : ℝ)
    (hfrequent : 0 < frequentCost) (hrare : 0 < rareCost) :
    quadraticCadenceObjective frequentCost rareCost deadline period =
        quadraticCadenceObjective frequentCost rareCost deadline
          (quadraticOptimalPeriod frequentCost rareCost deadline) ↔
      period = quadraticOptimalPeriod frequentCost rareCost deadline := by
  have hsumPos : 0 < frequentCost + rareCost := add_pos hfrequent hrare
  have hsum : frequentCost + rareCost ≠ 0 := ne_of_gt hsumPos
  constructor
  · intro hequal
    have hexact := quadraticCadenceObjective_sub_optimal_exact
      frequentCost rareCost deadline period hsum
    have hsquare :
        (period - quadraticOptimalPeriod frequentCost rareCost deadline) ^ 2 = 0 := by
      nlinarith
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsquare)
  · rintro rfl
    rfl

/-- When the deadline and both costs are positive, the unique optimum is
strictly interior: neither immediate consolidation nor waiting to saturation. -/
theorem quadraticOptimalPeriod_strictly_interior
    (frequentCost rareCost deadline : ℝ)
    (hfrequent : 0 < frequentCost) (hrare : 0 < rareCost)
    (hdeadline : 0 < deadline) :
    0 < quadraticOptimalPeriod frequentCost rareCost deadline ∧
      quadraticOptimalPeriod frequentCost rareCost deadline < deadline := by
  have hsum : 0 < frequentCost + rareCost := add_pos hfrequent hrare
  constructor
  · exact div_pos (mul_pos hfrequent hdeadline) hsum
  · rw [quadraticOptimalPeriod, div_lt_iff₀ hsum]
    nlinarith [mul_pos hrare hdeadline]

/-- Declared quadratic approximation.  Saturation pressure is normalized as
arrival rate per unit capacity; this term is not derived from `lostEvidence`. -/
noncomputable def cadenceObjective
    (arrivalRate capacity updateCost period : ℝ) : ℝ :=
  quadraticCadenceObjective updateCost (arrivalRate / capacity)
    (realSaturationDeadline arrivalRate capacity) period

/-- The optimizer of the declared quadratic approximation. -/
noncomputable def optimalConsolidationPeriod
    (arrivalRate capacity updateCost : ℝ) : ℝ :=
  quadraticOptimalPeriod updateCost (arrivalRate / capacity)
    (realSaturationDeadline arrivalRate capacity)

/-- Approximation theorem: the declared two-sided quadratic has one and only one
minimizer, and it lies strictly between immediate consolidation and capacity
saturation. -/
theorem optimalConsolidationPeriod_unique_interior
    (arrivalRate capacity updateCost : ℝ)
    (harrival : 0 < arrivalRate) (hcapacity : 0 < capacity)
    (hcost : 0 < updateCost) :
    (∀ period : ℝ,
      cadenceObjective arrivalRate capacity updateCost
          (optimalConsolidationPeriod arrivalRate capacity updateCost) ≤
        cadenceObjective arrivalRate capacity updateCost period) ∧
      (∀ period : ℝ,
        cadenceObjective arrivalRate capacity updateCost period =
            cadenceObjective arrivalRate capacity updateCost
              (optimalConsolidationPeriod arrivalRate capacity updateCost) ↔
          period = optimalConsolidationPeriod arrivalRate capacity updateCost) ∧
      0 < optimalConsolidationPeriod arrivalRate capacity updateCost ∧
      optimalConsolidationPeriod arrivalRate capacity updateCost <
        realSaturationDeadline arrivalRate capacity := by
  have hrare : 0 < arrivalRate / capacity := div_pos harrival hcapacity
  have hdeadline : 0 < realSaturationDeadline arrivalRate capacity :=
    div_pos hcapacity harrival
  refine ⟨?_, ?_, ?_⟩
  · intro period
    exact quadraticOptimalPeriod_minimizes _ _ _ _ hcost hrare
  · intro period
    exact quadraticCadenceObjective_eq_optimal_iff _ _ _ _ hcost hrare
  · exact quadraticOptimalPeriod_strictly_interior _ _ _ hcost hrare hdeadline

/-- Positive numeric fixture for the declared two-period quadratic optimum before the
four-period saturation deadline. -/
theorem cadence_rateTwo_capacityEight :
    realSaturationDeadline 2 8 = 4 ∧
      optimalConsolidationPeriod 2 8 (1 / 4) = 2 ∧
      (∀ period : ℝ,
        cadenceObjective 2 8 (1 / 4) 2 ≤
          cadenceObjective 2 8 (1 / 4) period) := by
  constructor
  · norm_num [realSaturationDeadline]
  constructor
  · norm_num [optimalConsolidationPeriod, quadraticOptimalPeriod,
      realSaturationDeadline]
  · intro period
    have h := (optimalConsolidationPeriod_unique_interior 2 8 (1 / 4)
      (by norm_num) (by norm_num) (by norm_num)).1 period
    norm_num [optimalConsolidationPeriod, quadraticOptimalPeriod,
      realSaturationDeadline] at h
    exact h

/-- Negative boundary: zero update cost puts the quadratic point at immediate
consolidation, so strict interior optimality genuinely needs positive cost. -/
theorem zeroUpdateCost_not_interior
    (arrivalRate capacity : ℝ) :
    optimalConsolidationPeriod arrivalRate capacity 0 = 0 := by
  simp [optimalConsolidationPeriod, quadraticOptimalPeriod,
    realSaturationDeadline]

#print axioms admitted_and_lost_at_or_after_deadline
#print axioms optimalConsolidationPeriod_unique_interior
#print axioms cadence_rateTwo_capacityEight
#print axioms zeroUpdateCost_not_interior

end Mettapedia.MachineLearning.NeuralNetworks.TwoTimescaleAdaptation
