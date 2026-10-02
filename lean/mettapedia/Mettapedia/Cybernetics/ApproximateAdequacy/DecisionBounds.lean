import Mettapedia.Cybernetics.ApproximateAdequacy.AdaptivePolicy
import Mettapedia.Enactive.Razor
import Mathlib.Data.Finset.Max

/-!
# Predictive error and decision regret

Prediction error, posterior approximation and numerical evaluation are separate
error sources. Their score errors add. Approximate maximization transfers a
uniform score error into a regret bound; candidate-specific bounds instead
produce certified score intervals. Selection uses the existing constrained
criterion, so preference never expands the admissible candidates.
-/

namespace Mettapedia.Cybernetics.ApproximateAdequacy.DecisionBounds

open Finset
open Mettapedia.Enactive.Razor

variable {Candidate : Type*}

/-- Three independently bounded score errors compose additively. -/
theorem score_error_chain (actual predicted inferred computed : ℝ)
    (predictionError inferenceError numericalError : ℝ)
    (prediction : |actual - predicted| ≤ predictionError)
    (inference : |predicted - inferred| ≤ inferenceError)
    (numerics : |inferred - computed| ≤ numericalError) :
    |actual - computed| ≤ predictionError + inferenceError + numericalError := by
  calc
    |actual - computed| = |(actual - predicted) + (predicted - inferred) +
      (inferred - computed)| := by congr 1; ring
    _ ≤ |actual - predicted| + |predicted - inferred| + |inferred - computed| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ _ := add_le_add (add_le_add prediction inference) numerics

/-- Approximate maximization under a uniform score certificate loses at most `2δ + η`. -/
theorem regret_le_of_score_error (actual computed : Candidate → ℝ)
    (admissible : Candidate → Prop) (selected : Candidate) (δ η : ℝ)
    (error : ∀ c, admissible c → |actual c - computed c| ≤ δ)
    (selected_admissible : admissible selected)
    (approximately_best : ∀ c, admissible c → computed c ≤ computed selected + η)
    (alternative : Candidate) (alternative_admissible : admissible alternative) :
    actual alternative - actual selected ≤ 2 * δ + η := by
  have hsel := abs_le.mp (error selected selected_admissible)
  have halt := abs_le.mp (error alternative alternative_admissible)
  have hbest := approximately_best alternative alternative_admissible
  linarith

/-- A criterion-optimal model-scored choice is a `2δ`-optimal actual choice. -/
theorem criterion_optimal_regret (actual computed : Candidate → ℝ)
    (admissible : Candidate → Prop) (selected : Candidate) (δ : ℝ)
    (error : ∀ c, admissible c → |actual c - computed c| ≤ δ)
    (optimal : (Criterion.ofBenefit admissible computed).IsOptimal selected)
    (alternative : Candidate) (alternative_admissible : admissible alternative) :
    actual alternative - actual selected ≤ 2 * δ := by
  simpa using regret_le_of_score_error actual computed admissible selected δ 0 error optimal.1
    (fun c hc => by simpa [Criterion.ofBenefit] using optimal.2 c hc)
    alternative alternative_admissible

/-- Candidate-dependent bounds produce rigorous true-score intervals. -/
theorem true_score_interval (actual computed radius : Candidate → ℝ)
    (error : ∀ c, |actual c - computed c| ≤ radius c) (c : Candidate) :
    computed c - radius c ≤ actual c ∧ actual c ≤ computed c + radius c := by
  have h := abs_le.mp (error c)
  constructor <;> linarith

/-- A separated lower/upper comparison certifies optimality without a uniform error radius. -/
theorem optimal_of_separated_intervals (actual computed radius : Candidate → ℝ)
    (admissible : Candidate → Prop) (selected : Candidate)
    (error : ∀ c, admissible c → |actual c - computed c| ≤ radius c)
    (selected_admissible : admissible selected)
    (separated : ∀ c, admissible c → c ≠ selected →
      computed c + radius c ≤ computed selected - radius selected) :
    (Criterion.ofBenefit admissible actual).IsOptimal selected := by
  refine ⟨selected_admissible, ?_⟩
  intro c hc
  change actual c ≤ actual selected
  by_cases same : c = selected
  · simp [same]
  · have hsel := abs_le.mp (error selected selected_admissible)
    have halt := abs_le.mp (error c hc)
    have hgap := separated c hc same
    linarith

/-- A nonempty finite admissible set has a score-optimal candidate. -/
theorem finite_optimal_exists [Fintype Candidate] (admissible : Candidate → Prop)
    (score : Candidate → ℝ) (nonempty : ∃ c, admissible c) :
    ∃ c, (Criterion.ofBenefit admissible score).IsOptimal c := by
  classical
  let options := Finset.univ.filter admissible
  have hoptions : options.Nonempty := by
    obtain ⟨c, hc⟩ := nonempty
    exact ⟨c, by simp [options, hc]⟩
  obtain ⟨c, hc, maximal⟩ := Finset.exists_max_image options score hoptions
  refine ⟨c, ?_, ?_⟩
  · exact (Finset.mem_filter.mp hc).2
  · intro other hother
    exact maximal other (Finset.mem_filter.mpr ⟨Finset.mem_univ other, hother⟩)

end Mettapedia.Cybernetics.ApproximateAdequacy.DecisionBounds
