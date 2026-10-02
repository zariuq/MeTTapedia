import Mettapedia.Algorithms.FiniteBayesRefinement
import Mettapedia.GSLT.Dynamics.AdaptiveContinuationPlanning

/-!
# Retained posterior computations through world-model revision

The checked rational update is a finitely supported computation. Its two
dependencies are the prior and likelihood tables, not a global revision tag.
The existing snapshot checker establishes equality with a fresh update, from
which the Bayesian correctness theorem transfers to the retained result.
-/

namespace Mettapedia.GSLT.Scope.BayesianDependencyReuse

open Mettapedia.Algorithms.FiniteBayes
open Mettapedia.GSLT.Dynamics.AdaptiveContinuationPlanning
open Mettapedia.InformationTheory
open Mettapedia.ProbabilityTheory.BayesianInference
open Mettapedia.Cybernetics.ApproximateAdequacy

variable {S : Type*} [Fintype S]

/-- `true` names the prior table; `false` names the likelihood table. -/
def posteriorPlan : FinitelySupportedPlan Bool (S → ℚ) (Option (S → ℚ)) :=
  (FinitelySupportedPlan.read true).combine (FinitelySupportedPlan.read false) update

theorem posteriorPlan_support :
    (posteriorPlan (S := S)).support = {true, false} := by
  simp [posteriorPlan, FinitelySupportedPlan.read, FinitelySupportedPlan.combine]

/-- An accepted retained result is a sound update of the actual current tables. -/
theorem reuse_refines
    (saved : PreparedArtifact (posteriorPlan (S := S))) (current : Bool → S → ℚ)
    (output : S → ℚ) (accepted : reuse saved current = some (some output)) :
    ∃ valid : IsDistribution (current true),
      ∃ nonneg : ∀ s, 0 ≤ (current false s : ℝ),
      ∃ possible : 0 < evidence (realDistribution (current true) valid)
        (fun s => (current false s : ℝ)),
      ∃ outputValid : IsDistribution output,
        realDistribution output outputValid =
          posterior (realDistribution (current true) valid)
            (fun s => (current false s : ℝ)) nonneg possible := by
  have fresh := reuse_eq_fresh posteriorPlan saved current (some output) accepted
  have updateAccepted : update (current true) (current false) = some output := fresh.symm
  obtain ⟨valid, nonneg, possible, correct⟩ := update_refines _ _ _ updateAccepted
  exact ⟨valid, nonneg, possible, update_sound _ _ _ updateAccepted, correct⟩

/-- A changed sensor table is a changed named dependency, and reuse abstains. -/
theorem changed_likelihood_refuses
    (saved : PreparedArtifact (posteriorPlan (S := S))) (current : Bool → S → ℚ)
    (old : S → ℚ) (recorded : (false, old) ∈ saved.dependencies)
    (changed : old ≠ current false) : reuse saved current = none :=
  changed_dependency_refuses posteriorPlan saved current false old recorded changed

end Mettapedia.GSLT.Scope.BayesianDependencyReuse
