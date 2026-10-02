import Mettapedia.ProbabilityTheory.BayesianInference.Basic
import Mettapedia.InformationTheory.FiniteProbability

/-!
# Sufficient finite observations

Probability aggregation is the existing finite pushforward, bundled with its
normalization proof. A likelihood that factors through an observation can be
updated entirely in that observation: aggregation and conditioning commute.
This is statistical sufficiency for the specified observation likelihood.
-/

namespace Mettapedia.ProbabilityTheory.BayesianInference

open Finset
open Mettapedia.InformationTheory
open Mettapedia.InformationTheory.FiniteRV
open Mettapedia.InformationTheory.Prob

variable {S C O : Type*} [Fintype S] [Fintype C] [Fintype O] [DecidableEq C]

theorem evidence_coarsen (prior : Prob S) (view : S → C) (likelihood : C → ℝ) :
    evidence (coarsen prior view) likelihood = evidence prior (likelihood ∘ view) :=
  coarsen_expectation prior view likelihood

/-- Aggregation commutes with a Bayesian update whose likelihood factors through the view. -/
theorem coarsen_posterior (prior : Prob S) (view : S → C) (likelihood : C → ℝ)
    (nonneg : ∀ c, 0 ≤ likelihood c)
    (possible : 0 < evidence prior (likelihood ∘ view)) :
    coarsen (posterior prior (likelihood ∘ view) (fun s => nonneg (view s)) possible) view =
      posterior (coarsen prior view) likelihood nonneg
        (by rw [evidence_coarsen]; exact possible) := by
  apply Subtype.ext
  funext c
  simp only [coarsen_apply, posterior_apply, evidence_coarsen]
  unfold pushforward
  simp only [posterior_apply]
  rw [Finset.sum_mul, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro s hs
  have hview := (Finset.mem_filter.mp hs).2
  simp only [Function.comp_apply, hview]

/-- Observation aggregation commutes with marginalization of a finite kernel. -/
theorem coarsen_observationLaw (prior : Prob S) (kernel : S → Prob O) (view : O → C) :
    coarsen (observationLaw prior kernel) view =
      observationLaw prior (fun s => coarsen (kernel s) view) :=
  coarsen_bind prior kernel view

/-- Aggregating latent states preserves the joint law when the observation
kernel depends only on the retained state. -/
theorem coarsen_joint [DecidableEq O] (prior : Prob S) (view : S → C)
    (kernel : C → Prob O) :
    coarsen (joint prior (kernel ∘ view)) (fun so => (view so.1, so.2)) =
      joint (coarsen prior view) kernel := by
  apply Subtype.ext
  funext co
  rcases co with ⟨c, o⟩
  simp only [coarsen_apply, pushforward_eq_sum_ite, joint_apply,
    Fintype.sum_prod_type, Function.comp_apply, Prod.mk.injEq]
  simp only [ite_and]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s _
  by_cases same : view s = c
  · simp [same]
  · simp [same]

end Mettapedia.ProbabilityTheory.BayesianInference
