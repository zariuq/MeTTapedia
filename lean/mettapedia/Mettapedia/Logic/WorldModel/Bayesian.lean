import Mettapedia.Logic.WorldModel.Basic
import Mettapedia.ProbabilityTheory.BayesianInference.Basic

/-!
# A Bayesian likelihood-revision world model

Nonnegative likelihood functions form a multiplicative revision monoid. The
reference prior is fixed for this instance. Queries return expectations under
the posterior, or no answer if the accumulated evidence is impossible.

This is a genuine nonadditive revision regime. A change of the reference prior
uses the separate Bayesian prior-reduction theorem.
-/

namespace Mettapedia.Logic.WorldModel.Bayesian

open Mettapedia.InformationTheory
open Mettapedia.ProbabilityTheory.BayesianInference
open scoped NNReal

variable {S : Type*} [Fintype S]

noncomputable def query (prior : Prob S) (likelihood : S → ℝ≥0) (consumer : S → ℝ) :
    Option ℝ :=
  if possible : 0 < evidence prior (fun s => (likelihood s : ℝ)) then
    some (∑ s, (posterior prior (fun s => (likelihood s : ℝ))
      (fun s => (likelihood s).coe_nonneg) possible).1 s * consumer s)
  else none

@[instance_reducible] noncomputable def model (prior : Prob S) :
    MonoidalWorldModel (S → ℝ≥0) (S → ℝ) (Option ℝ) where
  revise first second := fun s => first s * second s
  empty := fun _ => 1
  extract := query prior
  revise_assoc := by intros; funext s; exact mul_assoc _ _ _
  revise_empty_left := by intros; funext s; exact one_mul _
  revise_empty_right := by intros; funext s; exact mul_one _

theorem query_one (prior : Prob S) (consumer : S → ℝ) :
    query prior (fun _ => 1) consumer = some (∑ s, prior.1 s * consumer s) := by
  simp [query, evidence_one, posterior_one]

theorem query_zero (prior : Prob S) (consumer : S → ℝ) :
    query prior (fun _ => 0) consumer = none := by
  simp [query, evidence]

theorem query_revise (prior : Prob S) (first second : S → ℝ≥0)
    (consumer : S → ℝ) (first_possible : 0 < evidence prior (fun s => (first s : ℝ))) :
    query (posterior prior (fun s => (first s : ℝ))
      (fun s => (first s).coe_nonneg) first_possible) second consumer =
      query prior (fun s => first s * second s) consumer := by
  unfold query
  have evidence_eq := evidence_posterior prior (fun s => (first s : ℝ))
    (fun s => (second s : ℝ)) (fun s => (first s).coe_nonneg) first_possible
  by_cases possible : 0 < evidence prior (fun s => (first s : ℝ) * (second s : ℝ))
  · have conditional_possible : 0 < evidence
        (posterior prior (fun s => (first s : ℝ))
          (fun s => (first s).coe_nonneg) first_possible) (fun s => (second s : ℝ)) := by
      rw [evidence_eq]
      exact div_pos possible first_possible
    simp only [dif_pos conditional_possible, NNReal.coe_mul]
    rw [posterior_posterior]
    simp [possible]
  · have impossible : ¬ 0 < evidence
        (posterior prior (fun s => (first s : ℝ))
          (fun s => (first s).coe_nonneg) first_possible) (fun s => (second s : ℝ)) := by
      rw [evidence_eq]
      exact not_lt.mpr (div_nonpos_of_nonpos_of_nonneg (not_lt.mp possible) first_possible.le)
    simp only [dif_neg impossible, NNReal.coe_mul]
    simp [possible]

end Mettapedia.Logic.WorldModel.Bayesian
