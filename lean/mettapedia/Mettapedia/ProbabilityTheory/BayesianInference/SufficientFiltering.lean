import Mettapedia.ProbabilityTheory.FiniteLumpability
import Mettapedia.ProbabilityTheory.BayesianInference.Coarsening

/-!
# Filtering with sufficient state observations

State aggregation commutes with controlled prediction by strong lumpability.
It also commutes with Bayesian conditioning when the emission likelihood is
constant inside each state class. Together these independent conditions make
the aggregated distribution sufficient for the next prediction-and-observation
update. This supplies a finite update square for sufficient concepts.
-/

namespace Mettapedia.ProbabilityTheory.BayesianInference

open Mettapedia.InformationTheory
open Mettapedia.InformationTheory.Prob
open Mettapedia.ProbabilityTheory.FiniteLumpability

variable {S C A : Type*} [Fintype S] [Fintype C] [DecidableEq C]

/-- A genuine compressed filtering update, with both transition and emission obligations. -/
theorem coarsen_filter_step (view : S → C) (kernel : A → S → Prob S)
    (representative : C → S) (sectionLaw : Function.RightInverse representative view)
    (lumpable : StrongLumpability view kernel) (prior : Prob S) (action : A)
    (likelihood : C → ℝ) (nonneg : ∀ c, 0 ≤ likelihood c)
    (possible : 0 < evidence (Prob.bind prior (kernel action)) (likelihood ∘ view)) :
    coarsen (posterior (Prob.bind prior (kernel action)) (likelihood ∘ view)
      (fun s => nonneg (view s)) possible) view =
    posterior (Prob.bind (coarsen prior view) (lumpedKernel view kernel representative action))
      likelihood nonneg
      (by
        rw [← coarsen_predict view kernel representative sectionLaw lumpable, evidence_coarsen]
        exact possible) := by
  rw [coarsen_posterior]
  apply Subtype.ext
  funext c
  simp only [posterior_apply, coarsen_predict view kernel representative sectionLaw lumpable]

end Mettapedia.ProbabilityTheory.BayesianInference
