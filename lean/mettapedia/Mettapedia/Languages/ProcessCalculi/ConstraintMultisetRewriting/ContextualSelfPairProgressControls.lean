import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSelfPairProgress
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSelfPairControls

/-!
# Same-hole progress keeps local binders while pruning old parameters

A swapped two-parameter hole can retain its own lambda binder. Its image
size is unchanged, but the parameter interface shrinks from two to zero.
Equal maps give a contrasting case: pruning them makes no strict parameter
progress, so a reflexive solver branch must remove their equation instead.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSelfPairProgress.Controls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualSelfPair.Controls
open ScopePullback.Controls (base)

theorem the_swapped_maps_differ : identityMap ≠ swappedMap := by
  intro same
  have first := congrFun (congrFun same ()) Var.zero
  cases first

theorem pruning_the_swap_strictly_decreases_parameters :
    parameterPotential swapped.context others {9} < parameterPotential [(), ()] others {9} :=
  parameter_size_decreases the_swapped_maps_differ others {9}

def observedProblem : ContextualResidual.Problem old :=
  [(observe (rename (S := signature base old) identityMap (generator old (.inl ()))),
    observe (rename (S := signature base old) swappedMap (generator old (.inl ()))))]

theorem a_model_using_its_own_binder_makes_secondary_progress :
    ∃ remaining : Assignment (ContextualSelfPair.declarations swapped.context () others) others,
      ContextualResidual.Models remaining
        (ContextualResidual.mapProblem frameAnswer observedProblem) ∧
      (∀ identity, locallyBound identity = instantiate remaining (frameAnswer identity)) ∧
      imagePotential swapped.context () others remaining {9} = imagePotential [(), ()] () others locallyBound {9} ∧
      parameterPotential swapped.context others {9} < parameterPotential [(), ()] others {9} := by
  apply model_progress the_swapped_maps_differ () others observedProblem (List.mem_singleton_self _) locallyBound
  exact (ContextualResidual.models_observed_iff _ _ _).mpr
    (a_local_binder_remains_available _ (List.mem_singleton_self _))

theorem equal_maps_retain_both_parameters :
    (ScopeEqualizer.Finite.build identityMap identityMap).context.length = 2 := by
  exact ScopeEqualizer.Finite.context_length_same identityMap

theorem equal_maps_do_not_make_strict_parameter_progress :
    ¬ parameterPotential (ScopeEqualizer.Finite.build identityMap identityMap).context others {9} <
      parameterPotential [(), ()] others {9} := by
  unfold parameterPotential
  rw [equal_maps_retain_both_parameters]
  change ¬ (2 + _) < 2 + _
  omega

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSelfPairProgress.Controls
