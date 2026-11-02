import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFlexPairProgress
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFlexPairControls

/-!
# A shared binder body is counted once after flexible-pair solving

The two source images each contain a lambda and a pair. Their common image
has four nodes, so merging the two declarations removes four model nodes.
An unrelated active contextual image contributes on both sides. Dropping the
factorization requirement is unsound: the retained interface cannot repair
a dependency on an unshared parameter.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFlexPairProgress.Controls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualFlexPair.Controls
open ScopePullback.Controls (base leftMap rightMap pullback)

theorem both_source_images_have_four_nodes :
    termSize (candidate (.inl false)) = 4 ∧ termSize (candidate (.inl true)) = 4 := ⟨rfl, rfl⟩

theorem the_shared_image_has_four_nodes : termSize (residual (.inl ())) = 4 := rfl

theorem retaining_an_unrelated_active_image_preserves_strict_progress :
    targetPotential [()] () others residual {9} < sourcePotential [(), ()] [(), ()] () others candidate {9} :=
  decreases_of_factors pullback () others candidate residual
    the_candidate_factors_through_the_shared_binder_body {9}

def problem : ContextualResidual.Problem source :=
  [(observe (rename (S := signature base source) leftMap (generator source (.inl false))),
    observe (rename (S := signature base source) rightMap (generator source (.inl true))))]

theorem the_actual_solution_yields_a_smaller_residual_model :
    ∃ remaining : Assignment target others,
      ContextualResidual.Models remaining
        (ContextualResidual.mapProblem (ContextualFlexPair.answer pullback () others) problem) ∧
      (∀ identity, candidate identity =
        instantiate remaining (ContextualFlexPair.answer pullback () others identity)) ∧
      targetPotential [()] () others remaining {9} < sourcePotential [(), ()] [(), ()] () others candidate {9} := by
  apply model_progress pullback () others problem (List.mem_singleton_self _) candidate
  exact (ContextualResidual.models_observed_iff _ _ _).mpr binder_containing_candidate_is_a_solution

theorem an_unshared_dependency_cannot_supply_the_factorization :
    ¬ ∃ remaining : Assignment target others,
      ∀ identity, incompatible identity =
        instantiate remaining (ContextualFlexPair.answer pullback () others identity) := by
  rintro ⟨remaining, components⟩
  have solved := congrArg (instantiate remaining) (ContextualFlexPair.sound pullback () others)
  have first := ContextualFrameUnifier.factor_terms incompatible
    (ContextualFlexPair.answer pullback () others) remaining components
    (rename (S := signature base source) leftMap (generator source (.inl false)))
  have second := ContextualFrameUnifier.factor_terms incompatible
    (ContextualFlexPair.answer pullback () others) remaining components
    (rename (S := signature base source) rightMap (generator source (.inl true)))
  exact unshared_dependencies_are_not_a_solution (first.trans (solved.trans second.symm))

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFlexPairProgress.Controls
