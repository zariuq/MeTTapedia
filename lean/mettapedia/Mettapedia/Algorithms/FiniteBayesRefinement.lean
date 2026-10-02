import Mettapedia.Algorithms.FiniteBayes
import Mettapedia.ProbabilityTheory.BayesianInference.Basic

/-! # Correctness of rational conditioning in the real Bayesian model -/

namespace Mettapedia.Algorithms.FiniteBayes

open Finset
open Mettapedia.InformationTheory
open Mettapedia.ProbabilityTheory.BayesianInference
open Mettapedia.Cybernetics.ApproximateAdequacy

variable {S : Type*} [Fintype S]

/-- A checked rational probability distribution, embedded in the shared simplex. -/
def realDistribution (mass : S → ℚ) (valid : IsDistribution mass) : Prob S :=
  ⟨fun s => (mass s : ℝ), (fun s => by
    change 0 ≤ (mass s : ℝ)
    exact_mod_cast valid.nonneg s), by
    change (∑ s, (mass s : ℝ)) = 1
    exact_mod_cast valid.sum_eq_one⟩

theorem normalizer_cast (prior likelihood : S → ℚ) (valid : IsDistribution prior) :
    (normalizer prior likelihood : ℝ) =
      evidence (realDistribution prior valid) (fun s => (likelihood s : ℝ)) := by
  simp [normalizer, evidence, realDistribution]

/-- Every returned rational posterior is the independently defined real posterior. -/
theorem update_refines (prior likelihood output : S → ℚ)
    (accepted : update prior likelihood = some output) :
    ∃ valid : IsDistribution prior,
      ∃ nonneg : ∀ s, 0 ≤ (likelihood s : ℝ),
      ∃ possible : 0 < evidence (realDistribution prior valid) (fun s => (likelihood s : ℝ)),
      realDistribution output (update_sound prior likelihood output accepted) =
        posterior (realDistribution prior valid) (fun s => (likelihood s : ℝ)) nonneg possible := by
  obtain ⟨valid, nonnegQ, positiveQ, formula⟩ := update_accepted prior likelihood output accepted
  have nonneg : ∀ s, 0 ≤ (likelihood s : ℝ) := fun s => by exact_mod_cast nonnegQ s
  have possible : 0 < evidence (realDistribution prior valid) (fun s => (likelihood s : ℝ)) := by
    rw [← normalizer_cast prior likelihood valid]
    exact_mod_cast positiveQ
  refine ⟨valid, nonneg, possible, ?_⟩
  apply Subtype.ext
  funext s
  simp only [realDistribution, posterior_apply, formula, Rat.cast_div, Rat.cast_mul]
  rw [normalizer_cast prior likelihood valid]
  rfl

end Mettapedia.Algorithms.FiniteBayes
