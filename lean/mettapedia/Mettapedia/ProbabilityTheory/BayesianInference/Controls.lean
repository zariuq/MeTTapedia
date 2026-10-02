import Mettapedia.ProbabilityTheory.BayesianInference.Variational
import Mettapedia.ProbabilityTheory.BayesianInference.PriorReduction
import Mettapedia.ProbabilityTheory.BayesianInference.Information

/-!
# Finite Bayesian positive and negative controls

The controls compute a two-state posterior, a prior reduction, and impossible
evidence. They also show why prior support and a fixed likelihood are necessary
for reusing an old posterior.
-/

namespace Mettapedia.ProbabilityTheory.BayesianInference.Controls

noncomputable section

open Finset
open Mettapedia.InformationTheory

def binaryPrior (p : ℝ) (nonneg : 0 ≤ p) (le_one : p ≤ 1) : Prob (Fin 2) :=
  ⟨![p, 1 - p], by
    constructor
    · intro i
      fin_cases i <;> simp <;> linarith
    · simp [Fin.sum_univ_two]⟩

def fair : Prob (Fin 2) := binaryPrior (1 / 2) (by norm_num) (by norm_num)

def asymmetricLikelihood : Fin 2 → ℝ := ![3 / 4, 1 / 4]

theorem asymmetric_nonneg (s : Fin 2) : 0 ≤ asymmetricLikelihood s := by
  fin_cases s <;> norm_num [asymmetricLikelihood]

theorem fair_evidence : evidence fair asymmetricLikelihood = 1 / 2 := by
  norm_num [evidence, fair, binaryPrior, asymmetricLikelihood, Fin.sum_univ_two]

theorem fair_possible : 0 < evidence fair asymmetricLikelihood := by
  rw [fair_evidence]
  norm_num

theorem posterior_three_quarters :
    (posterior fair asymmetricLikelihood asymmetric_nonneg fair_possible).1 0 = 3 / 4 := by
  rw [posterior_apply, fair_evidence]
  norm_num [fair, binaryPrior, asymmetricLikelihood]

theorem posterior_one_quarter :
    (posterior fair asymmetricLikelihood asymmetric_nonneg fair_possible).1 1 = 1 / 4 := by
  rw [posterior_apply, fair_evidence]
  norm_num [fair, binaryPrior, asymmetricLikelihood]

theorem impossible_evidence : evidence fair (fun _ => 0) = 0 := by
  simp [evidence]

theorem impossible_not_possible : ¬ 0 < evidence fair (fun _ => 0) := by
  rw [impossible_evidence]
  exact lt_irrefl _

def concentratedZero : Prob (Fin 2) := binaryPrior 1 (by norm_num) (by norm_num)
def concentratedOne : Prob (Fin 2) := binaryPrior 0 (by norm_num) (by norm_num)

/-- Extending prior support cannot be recovered by reweighting its old posterior. -/
theorem support_expansion_breaks_evidence_ratio :
    evidence concentratedZero (priorRatio concentratedZero concentratedOne) ≠
      evidence concentratedOne (fun _ => 1) / evidence concentratedZero (fun _ => 1) := by
  norm_num [evidence, concentratedZero, concentratedOne, binaryPrior, priorRatio, Fin.sum_univ_two]

def shiftedPrior : Prob (Fin 2) := binaryPrior (3 / 4) (by norm_num) (by norm_num)

theorem shifted_possible : 0 < evidence shiftedPrior asymmetricLikelihood := by
  norm_num [evidence, shiftedPrior, binaryPrior, asymmetricLikelihood, Fin.sum_univ_two]

/-- A changed prior, with unchanged likelihood, gives the expected nontrivial posterior. -/
theorem reduced_posterior_nine_tenths :
    (posterior shiftedPrior asymmetricLikelihood asymmetric_nonneg shifted_possible).1 0 = 9 / 10 := by
  norm_num [posterior_apply, evidence, shiftedPrior, binaryPrior, asymmetricLikelihood, Fin.sum_univ_two]

/-- Even with the same prior, changing the observation likelihood changes the posterior. -/
theorem changed_likelihood_not_reusable :
    posterior fair asymmetricLikelihood asymmetric_nonneg fair_possible ≠
      posterior fair (fun _ => 1) (fun _ => by norm_num) (by rw [evidence_one]; norm_num) := by
  intro same
  have h := congrArg (fun p : Prob (Fin 2) => p.1 0) same
  rw [posterior_three_quarters, posterior_one] at h
  norm_num [fair, binaryPrior] at h

end

end Mettapedia.ProbabilityTheory.BayesianInference.Controls
