import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalPartnerCongruence
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalPartnerControls
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.ReductionObservationBoundary

/-!
# Framed name equations, whole futures, and the reduction boundary

A nonempty closed frame preserves the actual authored name equation and
retains a supplied synchronization target. The complete final successor
readout exercises the contextual action. The established bare-reduction
counterexample remains a separate negative, so that observation cannot
replace partner bisimilarity in the congruence theorem.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalPartnerCongruenceControls

open Mettapedia.CategoryTheory
open CanonicalBag CanonicalReaction CanonicalReactionOccurrences
open CanonicalPartnerCoalgebra CanonicalPartnerObservations CanonicalPartnerCongruence

def frame := toProcess CanonicalReactionControls.oneOutput

theorem framed_name_equation_observations :
    observe (fromProcess (ParallelContextAdequacy.par
      CanonicalReactionControls.alternateSource frame)) =
      observe (fromProcess (ParallelContextAdequacy.par
        (CanonicalReactionControls.rule.source empty) frame)) :=
  public_observation_parallel
    (congrArg observe CanonicalReactionControls.equation_retains_reaction_inventory) frame

theorem actual_framed_inventory :
    fromProcess (ParallelContextAdequacy.par CanonicalReactionControls.alternateSource frame) =
      CanonicalReactionControls.duplicates := by
  rw [fromProcess_par, CanonicalReactionControls.equation_retains_reaction_inventory,
    CanonicalReaction.GroundComm.source_inventory, append_empty]
  exact congrArg (append CanonicalReactionControls.rule.redex)
    (fromProcess_toProcess CanonicalReactionControls.oneOutput)

theorem actual_framed_target : CanonicalReactionControls.first.target ∈
    successors (fromProcess (ParallelContextAdequacy.par
      CanonicalReactionControls.alternateSource frame)) empty := by
  rw [actual_framed_inventory, mem_successors_iff_reaction, append_empty]
  exact CanonicalReactionControls.first.reaction

theorem actual_complete_framed_future : observe CanonicalReactionControls.first.target ∈
    FiniteActionTree.Tree.step (observe (fromProcess (ParallelContextAdequacy.par
      CanonicalReactionControls.alternateSource frame))) empty := by
  rw [observe_successors, FinitePowerset.mem_map]
  exact ⟨CanonicalReactionControls.first.target, actual_framed_target, rfl⟩

/-- The earlier independent core receipt supplies the reduction-congruence failure. -/
theorem bare_reduction_is_the_wrong_congruence_contract :
    ¬ ∀ first second, ReductionObservationBoundary.ReductionBisimilar first second →
      ReductionObservationBoundary.ReductionBisimilar
        (ReductionObservationBoundary.withOutput first)
        (ReductionObservationBoundary.withOutput second) :=
  ReductionObservationBoundary.reduction_bisimilarity_not_parallel_congruence

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalPartnerCongruenceControls
