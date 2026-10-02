import Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.TotalVariation
import Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.HistoryFiltration

/-!
# Value Continuity on Finite Prefix Spaces

This file provides small, reusable “bounded function” corollaries for the `l1DistanceReal` bound
from `TotalVariation.lean`, specialized to the interaction prefix types used in the Leike-style
Thompson sampling development.
-/

namespace Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.ValueContinuity

open scoped BigOperators
open Mettapedia.UniversalAI.BayesianAgents
open Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.HistoryFiltration
open Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.TotalVariation

/-! ## Reward sums on `Fin t → Step` -/

noncomputable def rewardSum (t : ℕ) (pfx : Fin t → Step) : ℝ :=
  ∑ i : Fin t, (pfx i).percept.reward

theorem abs_rewardSum_le (t : ℕ) (pfx : Fin t → Step) : |rewardSum t pfx| ≤ t := by
  have h_nonneg : 0 ≤ rewardSum t pfx := by
    dsimp [rewardSum]
    exact Finset.sum_nonneg fun i _ => Percept.reward_nonneg (pfx i).percept
  have h_le : rewardSum t pfx ≤ t := by
    dsimp [rewardSum]
    have h_term : ∀ i : Fin t, (pfx i).percept.reward ≤ (1 : ℝ) := fun i =>
      Percept.reward_le_one (pfx i).percept
    calc
      (∑ i : Fin t, (pfx i).percept.reward) ≤ ∑ i : Fin t, (1 : ℝ) := by
        refine Finset.sum_le_sum ?_
        intro i hi
        simpa using h_term i
      _ = t := by simp
  -- Since the sum is nonnegative, `|x| = x`.
  simpa [abs_of_nonneg h_nonneg] using h_le

theorem abs_integral_rewardSum_sub_integral_rewardSum_le (t : ℕ) (μ ν : MeasureTheory.Measure (Fin t → Step))
    (hμ : MeasureTheory.Integrable (rewardSum t) μ)
    (hν : MeasureTheory.Integrable (rewardSum t) ν) :
    |(∫ pfx, rewardSum t pfx ∂μ) - (∫ pfx, rewardSum t pfx ∂ν)| ≤ t * l1DistanceReal μ ν := by
  classical
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    (abs_integral_sub_integral_le_mul_l1DistanceReal (μ := μ) (ν := ν) (f := rewardSum t) (B := (t : ℝ))
      (hf := abs_rewardSum_le t) hμ hν)

end Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.ValueContinuity
