import Mettapedia.MachineLearning.NeuralNetworks.TwoTimescaleAdaptation.Cadence

/-!
# Cadence derived from counted updates and exact evidence loss

This module replaces the former mission-level use of a symmetric quadratic.
One periodic cycle incurs one explicitly counted consolidation cost and the
exact evidence loss already defined in `Cadence`.  Dividing repeated-cycle
cost by elapsed time yields an update term proportional to `1 / period` and a
hinge loss: zero before capacity and linear after capacity.

The resulting objective is solved exactly.  Under a transparent condition
that losing a full register costs more than one update, its unique optimum is
the saturation deadline itself.  A numerical theorem proves that the old
quadratic selects a different, interior period on the existing fixture.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.TwoTimescaleAdaptation

/-! ## B1: every cost term traced to accounting primitives -/

/-- Continuous hinge corresponding to the integer `lostEvidence` primitive. -/
noncomputable def realEvidenceLoss
    (capacity arrivalRate period : ℝ) : ℝ :=
  max 0 (arrivalRate * period - capacity)

/-- On integer inputs, the continuous hinge is exactly the cast of the
existing natural-number evidence-loss accounting. -/
theorem realEvidenceLoss_natCast_eq_lostEvidence
    (capacity arrivalRate period : ℕ) :
    realEvidenceLoss capacity arrivalRate period =
      (lostEvidence capacity arrivalRate period : ℝ) := by
  by_cases hbefore : arrivalRate * period ≤ capacity
  · have hreal :
        (arrivalRate : ℝ) * (period : ℝ) - (capacity : ℝ) ≤ 0 := by
      have hcast :
          (arrivalRate : ℝ) * (period : ℝ) ≤ (capacity : ℝ) := by
        exact_mod_cast hbefore
      linarith
    rw [realEvidenceLoss, max_eq_left hreal]
    simp [lostEvidence, admittedEvidence, arrivedEvidence,
      min_eq_right hbefore]
  · have hafter : capacity ≤ arrivalRate * period := by omega
    have hreal :
        0 ≤ (arrivalRate : ℝ) * (period : ℝ) - (capacity : ℝ) := by
      have hcast :
          (capacity : ℝ) ≤ (arrivalRate : ℝ) * (period : ℝ) := by
        exact_mod_cast hafter
      linarith
    rw [realEvidenceLoss, max_eq_right hreal]
    simp [lostEvidence, admittedEvidence, arrivedEvidence,
      min_eq_left hafter, Nat.cast_sub hafter]

/-- Total consolidation cost for an explicitly counted number of updates. -/
noncomputable def countedUpdateCost (count : ℕ) (updateCost : ℝ) : ℝ :=
  count * updateCost

/-- Total loss cost over identical periodic cycles. -/
noncomputable def countedEvidenceLossCost
    (count : ℕ) (lossCost capacity arrivalRate period : ℝ) : ℝ :=
  count * lossCost * realEvidenceLoss capacity arrivalRate period

/-- Elapsed time for `count` cycles of the declared period. -/
noncomputable def countedCadenceHorizon (count : ℕ) (period : ℝ) : ℝ :=
  count * period

/-- Average cost obtained from the two counted totals, with no additional
functional-form term. -/
noncomputable def countedCadenceAverageCost
    (count : ℕ) (arrivalRate capacity updateCost lossCost period : ℝ) : ℝ :=
  (countedUpdateCost count updateCost +
      countedEvidenceLossCost count lossCost capacity arrivalRate period) /
    countedCadenceHorizon count period

/-- The per-time objective after cancellation of a positive repeated-cycle
count. -/
noncomputable def derivedCadenceObjective
    (arrivalRate capacity updateCost lossCost period : ℝ) : ℝ :=
  (updateCost + lossCost * realEvidenceLoss capacity arrivalRate period) /
    period

/-- B1 crown: counted update cost plus exact evidence loss, divided by the
counted horizon, is the derived hinge objective. -/
theorem countedCadenceAverageCost_eq_derived
    (count : ℕ) (arrivalRate capacity updateCost lossCost period : ℝ)
    (hcount : 0 < count) (hperiod : period ≠ 0) :
    countedCadenceAverageCost count arrivalRate capacity updateCost lossCost period =
      derivedCadenceObjective arrivalRate capacity updateCost lossCost period := by
  have hcountReal : (count : ℝ) ≠ 0 := by exact_mod_cast hcount.ne'
  unfold countedCadenceAverageCost countedUpdateCost countedEvidenceLossCost
    countedCadenceHorizon derivedCadenceObjective
  field_simp [hcountReal, hperiod]

/-! ## B2: exact solution of the derived objective -/

/-- At an exact saturation deadline `capacity = arrivalRate * deadline`, the
hinge vanishes and only the update cost remains. -/
theorem derivedCadenceObjective_at_exactDeadline
    (arrivalRate capacity updateCost lossCost deadline : ℝ)
    (hcapacity : capacity = arrivalRate * deadline) :
    derivedCadenceObjective arrivalRate capacity updateCost lossCost deadline =
      updateCost / deadline := by
  simp [derivedCadenceObjective, realEvidenceLoss, hcapacity]

/-- Before the deadline, more frequent updates are strictly more expensive. -/
theorem derivedCadenceObjective_strictly_larger_before_deadline
    (arrivalRate capacity updateCost lossCost deadline period : ℝ)
    (harrival : 0 < arrivalRate) (hupdate : 0 < updateCost)
    (hdeadline : 0 < deadline) (hperiod : 0 < period)
    (hcapacity : capacity = arrivalRate * deadline)
    (hbefore : period < deadline) :
    derivedCadenceObjective arrivalRate capacity updateCost lossCost deadline <
      derivedCadenceObjective arrivalRate capacity updateCost lossCost period := by
  have hperiodLoss : arrivalRate * period - capacity ≤ 0 := by
    rw [hcapacity]
    nlinarith
  rw [derivedCadenceObjective_at_exactDeadline _ _ _ _ _ hcapacity,
    derivedCadenceObjective, realEvidenceLoss, max_eq_left hperiodLoss]
  simp only [mul_zero, add_zero]
  rw [div_lt_div_iff₀ hdeadline hperiod]
  nlinarith

/-- If losing one full register costs more than one update, waiting beyond
the deadline is also strictly more expensive. -/
theorem derivedCadenceObjective_strictly_larger_after_deadline
    (arrivalRate capacity updateCost lossCost deadline period : ℝ)
    (harrival : 0 < arrivalRate) (hdeadline : 0 < deadline)
    (hperiod : deadline < period)
    (hcapacity : capacity = arrivalRate * deadline)
    (hpenalty : updateCost < lossCost * capacity) :
    derivedCadenceObjective arrivalRate capacity updateCost lossCost deadline <
      derivedCadenceObjective arrivalRate capacity updateCost lossCost period := by
  have hperiodPos : 0 < period := hdeadline.trans hperiod
  have hperiodLoss : 0 ≤ arrivalRate * period - capacity := by
    rw [hcapacity]
    nlinarith
  rw [derivedCadenceObjective_at_exactDeadline _ _ _ _ _ hcapacity,
    derivedCadenceObjective, realEvidenceLoss, max_eq_right hperiodLoss]
  rw [div_lt_div_iff₀ hdeadline hperiodPos]
  rw [hcapacity] at hpenalty ⊢
  nlinarith [mul_pos (sub_pos.mpr hperiod)
    (sub_pos.mpr hpenalty)]

/-- B2 crown: the exact saturation deadline is the unique global minimizer of
the derived objective on positive periods. -/
theorem derivedCadenceObjective_unique_minimum_at_deadline
    (arrivalRate capacity updateCost lossCost deadline : ℝ)
    (harrival : 0 < arrivalRate) (hupdate : 0 < updateCost)
    (hdeadline : 0 < deadline)
    (hcapacity : capacity = arrivalRate * deadline)
    (hpenalty : updateCost < lossCost * capacity) :
    (∀ period : ℝ, 0 < period →
      derivedCadenceObjective arrivalRate capacity updateCost lossCost deadline ≤
        derivedCadenceObjective arrivalRate capacity updateCost lossCost period) ∧
      (∀ period : ℝ, 0 < period → (
        derivedCadenceObjective arrivalRate capacity updateCost lossCost period =
            derivedCadenceObjective arrivalRate capacity updateCost lossCost deadline ↔
          period = deadline)) := by
  constructor
  · intro period hperiod
    rcases lt_trichotomy period deadline with hbefore | hequal | hafter
    · exact (derivedCadenceObjective_strictly_larger_before_deadline
        arrivalRate capacity updateCost lossCost deadline period harrival hupdate
        hdeadline hperiod hcapacity hbefore).le
    · subst period
      exact le_rfl
    · exact (derivedCadenceObjective_strictly_larger_after_deadline
        arrivalRate capacity updateCost lossCost deadline period harrival hdeadline
        hafter hcapacity hpenalty).le
  · intro period hperiod
    constructor
    · intro hequal
      rcases lt_trichotomy period deadline with hbefore | heq | hafter
      · have hstrict := derivedCadenceObjective_strictly_larger_before_deadline
          arrivalRate capacity updateCost lossCost deadline period harrival hupdate
          hdeadline hperiod hcapacity hbefore
        linarith
      · exact heq
      · have hstrict := derivedCadenceObjective_strictly_larger_after_deadline
          arrivalRate capacity updateCost lossCost deadline period harrival hdeadline
          hafter hcapacity hpenalty
        linarith
    · rintro rfl
      rfl

/-! ## B3: explicit divergence from the declared quadratic -/

/-- Status of a cadence model after tracing its terms to accounting. -/
inductive CadenceModelStatus where
  | derivedFromCountedUpdatesAndEvidenceLoss
  | declaredApproximation
  | refutedAsDerivedObjective
  deriving DecidableEq, Repr

/-- The symmetric quadratic remains valid algebra, but is not derived from
the module's evidence accounting. -/
def quadraticCadenceModelStatus : CadenceModelStatus :=
  .declaredApproximation

theorem quadraticCadenceModel_is_declaredApproximation :
    quadraticCadenceModelStatus = .declaredApproximation := rfl

/-- The existing rate-two/capacity-eight fixture has a unique derived optimum
at deadline four, while the declared quadratic chooses period two. -/
theorem derivedCadence_rateTwo_capacityEight_unique_deadline :
    (∀ period : ℝ, 0 < period →
      derivedCadenceObjective 2 8 (1 / 4) 1 4 ≤
        derivedCadenceObjective 2 8 (1 / 4) 1 period) ∧
      (∀ period : ℝ, 0 < period → (
        derivedCadenceObjective 2 8 (1 / 4) 1 period =
            derivedCadenceObjective 2 8 (1 / 4) 1 4 ↔
          period = 4)) := by
  exact derivedCadenceObjective_unique_minimum_at_deadline
    2 8 (1 / 4) 1 4 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)

/-- Exact error values expose rather than hide the mismatch: the old
quadratic objective selects two, although the accounted objective strictly
prefers four. -/
theorem quadraticCadence_refuted_as_derived_fixture :
    optimalConsolidationPeriod 2 8 (1 / 4) = 2 ∧
      cadenceObjective 2 8 (1 / 4) 2 -
          derivedCadenceObjective 2 8 (1 / 4) 1 2 = 15 / 8 ∧
      cadenceObjective 2 8 (1 / 4) 4 -
          derivedCadenceObjective 2 8 (1 / 4) 1 4 = 63 / 16 ∧
      derivedCadenceObjective 2 8 (1 / 4) 1 4 <
        derivedCadenceObjective 2 8 (1 / 4) 1 2 := by
  norm_num [optimalConsolidationPeriod, quadraticOptimalPeriod,
    cadenceObjective, quadraticCadenceObjective, realSaturationDeadline,
    derivedCadenceObjective, realEvidenceLoss]

#print axioms realEvidenceLoss_natCast_eq_lostEvidence
#print axioms countedCadenceAverageCost_eq_derived
#print axioms derivedCadenceObjective_unique_minimum_at_deadline
#print axioms quadraticCadence_refuted_as_derived_fixture

end Mettapedia.MachineLearning.NeuralNetworks.TwoTimescaleAdaptation
