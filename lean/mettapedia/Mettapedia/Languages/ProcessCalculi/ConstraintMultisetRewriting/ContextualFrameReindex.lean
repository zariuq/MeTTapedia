import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualResidual
import Mettapedia.OSLF.Syntax.ContextualFamilyReindex

/-!
# Reindexing a solver frame preserves every residual solution

An arity-preserving identity map with a left inverse changes the representation
of a contextual equation queue. The actual reindexing assignment and mapped
equations form a sound and complete residual transformation. No equation is
solved or discarded by this change of frame.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrameReindex

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

variable {S : Signature} {V W : Type} {source : V → MetaArity S} {target : W → MetaArity S}

theorem reduction (forward : V → W) (backward : W → V)
    (forwardPreserves : ∀ identity, target (forward identity) = source identity)
    (backwardPreserves : ∀ identity, source (backward identity) = target identity)
    (inverse : Function.LeftInverse backward forward) (problem : ContextualResidual.Problem source) :
    ContextualResidual.Reduction problem (reindex forward forwardPreserves)
      (ContextualResidual.mapProblem (reindex forward forwardPreserves) problem) := by
  constructor
  · intro Variables declaration residual solved
    exact (ContextualResidual.models_mapProblem _ _ _).mp solved
  · intro Variables declaration candidate solved
    let residual := Assignment.compose candidate (reindex backward backwardPreserves)
    have composed : Assignment.compose residual (reindex forward forwardPreserves) = candidate := by
      rw [← Assignment.compose_associative,
        reindex_left_inverse forward backward forwardPreserves backwardPreserves inverse,
        Assignment.compose_identity_right]
    have factors : ∀ identity, candidate identity = instantiate residual (reindex forward forwardPreserves identity) :=
      fun identity => (congrFun composed identity).symm
    exact ⟨residual, (ContextualResidual.models_of_components candidate _ residual factors problem).mp solved, factors⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrameReindex
