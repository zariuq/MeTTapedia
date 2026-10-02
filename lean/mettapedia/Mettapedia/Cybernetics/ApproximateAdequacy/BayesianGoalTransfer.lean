import Mettapedia.Cybernetics.ApproximateAdequacy.Weighting
import Mettapedia.Cybernetics.ApproximateAdequacy.AdaptiveTrace
import Mettapedia.Cybernetics.ApproximateAdequacy.ControllerCoupling
import Mettapedia.ProbabilityTheory.BayesianInference.ExpectationBounds

/-!
# Goal changes over finite adaptive executions

Execution traces and their posterior laws are independent of how a goal weights
the error reports. A new goal inherits the previous average-error certificate
only when its weighting is dominated. Charging a formerly invisible trace has
an explicit no-transfer control.
-/

namespace Mettapedia.Cybernetics.ApproximateAdequacy

open Mettapedia.InformationTheory

variable {S O A : Type*} [Fintype S] [Fintype O] [DecidableEq S] [DecidableEq O]

/-- Probability execution laws supply the existing finitely supported weighting interface. -/
def probabilityWeighting {X : Type*} [Fintype X] (law : Prob X) : FiniteWeighting ℝ X :=
  ⟨Finset.univ, law.1, fun x _ => law.2.1 x, law.2.2⟩

/-- Reweighting the same finite trace-error report changes its guarantee by
at most the checked domination factor. -/
theorem adaptive_goal_transfer {n : ℕ}
    (kernel : A → S → Prob (S × O)) (policy : ObservationPolicy O A n) (initial : S)
    (newGoal : FiniteWeighting ℝ (Fin n → S × O))
    (error : (Fin n → S × O) → ℝ) (nonneg : ∀ trace, 0 ≤ error trace)
    (factor bound : ℝ) (factor_nonneg : 0 ≤ factor)
    (dominated : ∀ trace ∈ newGoal.support,
      newGoal.weight trace ≤ factor * (traceLaw kernel policy initial).1 trace)
    (certified : (probabilityWeighting (traceLaw kernel policy initial)).expectation error ≤ bound) :
    newGoal.expectation error ≤ factor * bound := by
  have transfer := FiniteWeighting.expectation_le_mul_of_le
    (w := probabilityWeighting (traceLaw kernel policy initial))
    (w' := newGoal) (fun trace _ => nonneg trace) factor_nonneg
    (fun trace member => ⟨Finset.mem_univ _, dominated trace member⟩)
  exact transfer.trans (mul_le_mul_of_nonneg_left certified factor_nonneg)

/-- A goal that starts charging an invisible outcome can invalidate a zero-error report. -/
theorem changed_goal_can_expose_error :
    (twoPoint (0 : ℝ) (by norm_num) (by norm_num)).expectation
        (fun b => if b then (1 : ℝ) else 0) = 0 ∧
      (twoPoint (1 : ℝ) (by norm_num) (by norm_num)).expectation
        (fun b => if b then (1 : ℝ) else 0) = 1 := by
  simp [FiniteWeighting.expectation, twoPoint]

section LogarithmicGoals

variable {T U B : Type*} [Fintype T] [Fintype U]

omit [DecidableEq S] [DecidableEq O] in
/-- A common positive lower bound transports an actual execution certificate
to logarithmic terminal objectives, scaling its discrepancy by `1 / δ`. -/
theorem CoupledExecution.logarithmic
    {first : A → S → Prob (S × O)} {second : B → T → Prob (T × U)}
    {firstReward : S → ℝ} {secondReward : T → ℝ} {metric : S → T → ℝ}
    {n : ℕ} {p : ObservationPolicy O A n} {q : ObservationPolicy U B n} {s t}
    (certificate : CoupledExecution first second firstReward secondReward metric p q s t)
    (δ : ℝ) (positive : 0 < δ)
    (firstLower : ∀ s, δ ≤ firstReward s) (secondLower : ∀ t, δ ≤ secondReward t) :
    CoupledExecution first second (fun s => Real.log (firstReward s))
      (fun t => Real.log (secondReward t)) (fun s t => metric s t / δ) p q s t := by
  induction certificate with
  | terminal bounded =>
      apply CoupledExecution.terminal
      exact (Mettapedia.ProbabilityTheory.BayesianInference.abs_log_sub_le_of_lower
        positive (firstLower _) (secondLower _)).trans
          (div_le_div_of_nonneg_right bounded positive.le)
  | step coupling continues bounded ih =>
      refine CoupledExecution.step coupling (fun x y mass => ih x y mass) ?_
      have scaled := div_le_div_of_nonneg_right bounded positive.le
      simpa only [Coupling.cost, mul_div_assoc, Finset.sum_div] using scaled

omit [DecidableEq S] [DecidableEq O] in
/-- Independent initial beliefs retain the scaled logarithmic score guarantee. -/
theorem coupled_logarithmic_score_bound
    (first : A → S → Prob (S × O)) (second : B → T → Prob (T × U))
    (firstReward : S → ℝ) (secondReward : T → ℝ) (metric : S → T → ℝ)
    {n : ℕ} (p : ObservationPolicy O A n) (q : ObservationPolicy U B n)
    (firstPrior : Prob S) (secondPrior : Prob T) (initial : Coupling firstPrior.1 secondPrior.1)
    (certificates : ∀ s t, 0 < initial.weight s t →
      CoupledExecution first second firstReward secondReward metric p q s t)
    (δ : ℝ) (positive : 0 < δ)
    (firstLower : ∀ s, δ ≤ firstReward s) (secondLower : ∀ t, δ ≤ secondReward t) :
    |expect firstPrior.1 (adaptiveValue first (fun s => Real.log (firstReward s)) p) -
        expect secondPrior.1 (adaptiveValue second (fun t => Real.log (secondReward t)) q)| ≤
      initial.cost metric / δ := by
  have bound := CoupledExecution.expected_bound p q firstPrior secondPrior initial
    (fun s t mass => (certificates s t mass).logarithmic δ positive firstLower secondLower)
  simpa only [Coupling.cost, mul_div_assoc, Finset.sum_div] using bound

end LogarithmicGoals

end Mettapedia.Cybernetics.ApproximateAdequacy
