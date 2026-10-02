import Mettapedia.KR.ConceptOntology.StochasticSufficiencyControls
import Mettapedia.Cybernetics.DistinctionCalculus.Weighted
import Mettapedia.Cybernetics.ApproximateAdequacy.ObservationCoupling

/-!
# Measured concept-compression loss

The four-state sufficient compression retains its exact policy contract.
For a different consumer that values the hidden bit, its distortion is
measured under an independent, declared uniform distribution. Pairwise
observer distortion and task-value error are different quantities.
-/

namespace Mettapedia.KR.ConceptOntology.StochasticSufficiency.CompressionControl

open Mettapedia.Cybernetics.DistinctionCalculus
open Mettapedia.Cybernetics.ApproximateAdequacy
open Mettapedia.InformationTheory

/-- The declared measure for the representation-loss calculation. -/
def uniform : Distribution State where
  weight _ := 1/4
  nonnegative _ := by norm_num
  normalized := by norm_num [Fintype.sum_prod_type, Fintype.sum_bool]

/-- Forgetting the implementation bit merges one quarter of ordered state pairs. -/
theorem observer_distortion :
    uniform.distortion (Tolerance.ofReport (id : State → State))
      (Tolerance.ofReport (id : Bool → Bool)) Prod.fst = 1/4 := by
  norm_num [Distribution.distortion, Distribution.pairAverage, uniform, Tolerance.ofReport,
    Fintype.sum_prod_type, Fintype.sum_bool]

noncomputable def uniformPrior : Prob State :=
  ⟨fun _ => 1/4, (fun _ => by norm_num), by
    norm_num [Fintype.sum_prod_type, Fintype.sum_bool]⟩

def retainedUtility (bit : Bool) : ℝ := if bit then 1 else 0

noncomputable def richerUtility (state : State) : ℝ :=
  retainedUtility state.1 + if state.2 then 1/4 else 0

/-- The newly valued hidden distinction causes an actual, nonzero task-score loss. -/
theorem task_loss :
    |expect uniformPrior.1 richerUtility -
      expect (Prob.coarsen uniformPrior Prod.fst).1 retainedUtility| = 1/8 := by
  unfold expect
  rw [Prob.coarsen_expectation]
  norm_num [uniformPrior, richerUtility, retainedUtility,
    Fintype.sum_prod_type, Fintype.sum_bool]

/-- The canonical observation coupling supplies a quantitative guarantee for
this changed consumer, without licensing state substitution. -/
theorem task_loss_bound :
    |expect uniformPrior.1 richerUtility -
      expect (Prob.coarsen uniformPrior Prod.fst).1 retainedUtility| ≤ 1/4 := by
  have bound := observed_consumer_error uniformPrior Prod.fst richerUtility retainedUtility
    (fun _ => (1/4 : ℝ)) (fun state => by
      rcases state with ⟨first, second⟩
      cases first <;> cases second <;> norm_num [richerUtility, retainedUtility])
  simpa [expect, uniformPrior, Fintype.sum_prod_type, Fintype.sum_bool] using bound

end Mettapedia.KR.ConceptOntology.StochasticSufficiency.CompressionControl
