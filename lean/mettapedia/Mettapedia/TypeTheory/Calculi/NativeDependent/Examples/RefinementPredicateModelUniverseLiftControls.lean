import Mettapedia.TypeTheory.ContextualPredicateModelScopeUniverseLift
import Mettapedia.TypeTheory.ContextualPredicateValueSubstitution
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementContextualModel
import Mettapedia.TypeTheory.Calculi.NativeDependent.Examples.RefinementContextualRefinementControls

/-!
# Retained values and rejected assumptions through predicate-model lifts

The generated local model has distinct ordinary proposition values which
satisfy the same refinement guard. Both supplied values remain distinct
after changing all five carrier sizes. A context projection tests actual
refinement substitution. A mixed scope retains its ordinary proposition
variable through an assumption, while a false assumption still rejects the
complete empty argument array.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.UniverseLiftControls

open Mettapedia.GSLT.Core.ContextualLadder
open ContextualPredicateModel ContextualPredicateModelUniverseLift
open ContextualPredicateModelScopes ContextualPredicateModelScopeUniverseLift
open ContextualModelTelescopes ContextualProductComparison

attribute [local instance] ContextualPredicateModelUniverseLift.liftedHeytingAlgebra

universe uc vs wt ms ps

noncomputable section

abbrev source := QuotientCwf.withTerminal Controls.signature
abbrev original := generatedModel Controls.signature
abbrev liftedBase := ContextualCwfUniverseLift.liftWithTerminal.{0, 0, 0, 0, uc, vs, wt, ms} source
abbrev model : LocalModel liftedBase := lift.{0, 0, 0, 0, 0, uc, vs, wt, ms, ps} original

theorem qualified : Qualification (model.{uc, vs, wt, ms, ps}) :=
  qualificationLift original (generatedModel_qualification Controls.signature)

def refinedTruth : liftedBase.toCwf.Tm (ULift.up RefinementControls.qcontext)
    ((model.{uc, vs, wt, ms, ps}).refinements.refined
      (ULift.up RefinementControls.domain) (ULift.up RefinementControls.selected)) :=
  ULift.up RefinementControls.refinedTruth

def refinedFalse : liftedBase.toCwf.Tm (ULift.up RefinementControls.qcontext)
    ((model.{uc, vs, wt, ms, ps}).refinements.refined
      (ULift.up RefinementControls.domain) (ULift.up RefinementControls.selected)) :=
  ULift.up RefinementControls.refinedFalse

theorem truth_forget_readout :
    ((model.{uc, vs, wt, ms, ps}).refinements.forget
      (ULift.up RefinementControls.domain) (ULift.up RefinementControls.selected) refinedTruth).down =
        RefinementControls.truthValue := RefinementControls.source_beta_retains_truth

theorem falsehood_forget_readout :
    ((model.{uc, vs, wt, ms, ps}).refinements.forget
      (ULift.up RefinementControls.domain) (ULift.up RefinementControls.selected) refinedFalse).down =
        RefinementControls.falseValue := RefinementControls.source_beta_retains_falsehood

theorem retained_values_are_distinct :
    refinedTruth.{uc, vs, wt, ms, ps} ≠ refinedFalse.{uc, vs, wt, ms, ps} := by
  intro same
  exact RefinementControls.selected_values_remain_distinct (congrArg ULift.down same)

/-- Keeping the guard alone loses a distinction retained by the complete
lifted refinement sections. -/
theorem identical_guards_do_not_identify_values :
    (model.{uc, vs, wt, ms, ps}).doctrine.reindex
        (selfExtend liftedBase.toCwf ((model.{uc, vs, wt, ms, ps}).refinements.forget
          (ULift.up RefinementControls.domain) (ULift.up RefinementControls.selected) refinedTruth))
        (ULift.up RefinementControls.selected) =
      (model.{uc, vs, wt, ms, ps}).doctrine.reindex
        (selfExtend liftedBase.toCwf ((model.{uc, vs, wt, ms, ps}).refinements.forget
          (ULift.up RefinementControls.domain) (ULift.up RefinementControls.selected) refinedFalse))
        (ULift.up RefinementControls.selected) ∧
      refinedTruth.{uc, vs, wt, ms, ps} ≠ refinedFalse.{uc, vs, wt, ms, ps} := by
  constructor
  · exact ((model.{uc, vs, wt, ms, ps}).refinements.forget_guard
      (ULift.up RefinementControls.domain) (ULift.up RefinementControls.selected)
        refinedTruth.{uc, vs, wt, ms, ps}).trans
      ((model.{uc, vs, wt, ms, ps}).refinements.forget_guard
        (ULift.up RefinementControls.domain) (ULift.up RefinementControls.selected)
          refinedFalse.{uc, vs, wt, ms, ps}).symm
  · exact retained_values_are_distinct

/-- The projection comes from an actual added data variable. -/
theorem supplied_substitution_changes_context :
    RefinementControls.extended.arity ≠ RefinementControls.context.arity :=
  RefinementControls.extension_changes_raw_scope

def transported : liftedBase.toCwf.Tm (ULift.up RefinementControls.qextended)
    ((model.{uc, vs, wt, ms, ps}).refinements.refined
      (liftedBase.toCwf.tySub (ULift.up RefinementControls.domain)
        (ULift.up RefinementControls.dropVariable))
      ((model.{uc, vs, wt, ms, ps}).doctrine.reindex
        (TypeOver.extensionSubstitution (ULift.up RefinementControls.dropVariable)
          (ULift.up RefinementControls.domain)) (ULift.up RefinementControls.selected))) :=
  ContextualPredicateValueSubstitution.RefinementOperations.substitute
    (C := liftedBase.{uc, vs, wt, ms}.toCwf)
    (model.{uc, vs, wt, ms, ps}).refinements (ULift.up RefinementControls.dropVariable)
    (ULift.up RefinementControls.domain) (ULift.up RefinementControls.selected)
      refinedTruth.{uc, vs, wt, ms, ps}

theorem complete_forgetting_substitution :
    HEq (liftedBase.toCwf.tmSub
      ((model.{uc, vs, wt, ms, ps}).refinements.forget
        (ULift.up RefinementControls.domain) (ULift.up RefinementControls.selected) refinedTruth)
      (ULift.up RefinementControls.dropVariable))
      ((model.{uc, vs, wt, ms, ps}).refinements.forget
        (liftedBase.toCwf.tySub (ULift.up RefinementControls.domain)
          (ULift.up RefinementControls.dropVariable))
        ((model.{uc, vs, wt, ms, ps}).doctrine.reindex
          (TypeOver.extensionSubstitution (ULift.up RefinementControls.dropVariable)
            (ULift.up RefinementControls.domain)) (ULift.up RefinementControls.selected))
          transported.{uc, vs, wt, ms, ps}) :=
  (model.{uc, vs, wt, ms, ps}).refinements.forget_substitution
    (ULift.up RefinementControls.dropVariable) (ULift.up RefinementControls.domain)
    (ULift.up RefinementControls.selected) refinedTruth.{uc, vs, wt, ms, ps}
      transported.{uc, vs, wt, ms, ps}
    (ContextualPredicateValueSubstitution.RefinementOperations.substitute_heq
      (C := liftedBase.{uc, vs, wt, ms}.toCwf)
      (model.{uc, vs, wt, ms, ps}).refinements (ULift.up RefinementControls.dropVariable)
      (ULift.up RefinementControls.domain) (ULift.up RefinementControls.selected)
        refinedTruth.{uc, vs, wt, ms, ps}).symm

def ordinaryScope : ContextualPredicateModelScopes.Scope source original.doctrine original.assumptions 1 :=
  (ContextualPredicateModelScopes.Scope.nil source original.doctrine original.assumptions).snoc
    RefinementControls.domain

def guardedScope : ContextualPredicateModelScopes.Scope source original.doctrine original.assumptions 1 :=
  ordinaryScope.assume ⊤

theorem variable_survives_assumption :
    ContextualCwfUniverseLift.lowerValue.{0, 0, 0, 0, uc, vs, wt, ms}
      ((liftScope.{0, 0, 0, 0, 0, uc, vs, wt, ms, ps} guardedScope).2.lookup 0) =
        (ordinaryScope.2.lookup 0).substitute
          (original.assumptions.inclusion (⊤ : original.doctrine.Predicate ordinaryScope.1)) := by
  exact lookup_readout guardedScope.2 (0 : Fin 1)

theorem supplied_guarded_arguments_assemble :
    (liftScope.{0, 0, 0, 0, 0, uc, vs, wt, ms, ps} guardedScope).2.assemble?
      (fun index => some (ContextualCwfUniverseLift.liftValue.{0, 0, 0, 0, uc, vs, wt, ms}
        (guardedScope.2.components (source.toCwf.idS guardedScope.1) index))) =
          some (ULift.up (source.toCwf.idS guardedScope.1)) :=
  (liftScopeData_assemble_eq_some_iff guardedScope.2 _ _).mpr
    (ContextualPredicateModelScopes.ScopeData.assemble?_components guardedScope.2 _)

theorem falsehood_is_not_truth : (⊥ : original.doctrine.Predicate source.empty) ≠ ⊤ := by
  intro same
  apply RefinementControls.predicates_remain_distinct
  exact same.symm

def impossibleScope : ContextualPredicateModelScopes.Scope source original.doctrine original.assumptions 0 :=
  (ContextualPredicateModelScopes.Scope.nil source original.doctrine original.assumptions).assume ⊥

theorem false_assumption_rejects : impossibleScope.2.assemble?
    (source := source.empty) (fun index => Fin.elim0 index) = none := by
  classical
  change select? original.assumptions (⊥ : original.doctrine.Predicate source.empty)
    (source.toEmpty source.empty) = none
  have rejected : original.doctrine.reindex (source.toEmpty source.empty)
      (⊥ : original.doctrine.Predicate source.empty) ≠ ⊤ := by
    rw [map_bot]
    exact falsehood_is_not_truth
  exact dif_neg rejected

/-- There are no missing data components here. Rejection comes from the
retained false assumption and is preserved by the complete model lift. -/
theorem lifted_false_assumption_rejects :
    (liftScope.{0, 0, 0, 0, 0, uc, vs, wt, ms, ps} impossibleScope).2.assemble?
      (source := ULift.up source.empty) (fun index => Fin.elim0 index) = none := by
  have same := liftScopeData_assemble.{0, 0, 0, 0, 0, uc, vs, wt, ms, ps}
    impossibleScope.2 (source := source.empty) (fun index => Fin.elim0 index)
  rw [false_assumption_rejects] at same
  exact same

end

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.UniverseLiftControls
