import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementContextualAssumptionMorphism
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementContextualRefinementMorphism
import Mettapedia.TypeTheory.ContextualPredicateMorphism
import Mettapedia.TypeTheory.ContextualPredicateModelUniverseLift

/-!
# Complete local predicate preservation of generated interpretation

The constructed contextual morphism preserves the generated Heyting
doctrine, ordinary proposition terms, guarded assumption inclusions and
retained refinement inhabitants. Its five local comparisons are earned
from independently evaluated constructors and complete substitution maps.
Predicate carrier levels remain independent of the four contextual levels.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.Interpretation

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualPredicateModel
open Mettapedia.TypeTheory.ContextualPredicateMorphism
open Mettapedia.TypeTheory.ContextualCwfUniverseLift (up_heq down_heq)
open Refinement.Abstract

universe u c s t m p z
variable {S : Symbols.{u}} {D : Signature S} {C : CwfWithTerminal.{c,s,t,m}}

noncomputable def sourceLocalModel (D : Signature S) :
    LocalModel.{max u z, max u z, max u z, max u z, u} (SourceModel.{u,z} D) :=
  Mettapedia.TypeTheory.ContextualPredicateModelUniverseLift.lift.{u,u,u,u,u,
    max u z, max u z, max u z, max u z, 0} (generatedModel D)

variable (model : QualifiedModel.{u,c,s,t,m,p} D C)

def targetLocalModel :
    LocalModel.{max u c s t m, max u c s t m, max u c s t m, max u c s t m, p}
      (TargetModel.{u,c,s,t,m} C) :=
  Mettapedia.TypeTheory.ContextualPredicateModelUniverseLift.lift.{c,s,t,m,p,
    max u c s t m, max u c s t m, max u c s t m, max u c s t m, 0} model.localModel

noncomputable def liftedPredicateHom (context : (SourceModel.{u,max c s t m} D).toCwf.Ctx) :
    HeytingHom ((sourceLocalModel.{u,max c s t m} D).doctrine.Predicate context)
      ((targetLocalModel model).doctrine.Predicate ((familyMorphism model).base.obj ⟨context⟩).val) where
  toFun predicate := ULift.up (predicateValue model predicate.down)
  map_inf' first second := congrArg ULift.up (predicateValue_inf model first.down second.down)
  map_sup' first second := congrArg ULift.up (predicateValue_sup model first.down second.down)
  map_bot' := congrArg ULift.up (predicateValue_bot model context.down.as)
  map_himp' first second := congrArg ULift.up (predicateValue_himp model first.down second.down)

set_option backward.isDefEq.respectTransparency false in
noncomputable def doctrine_preserved :
    DoctrinePreservation (strictMorphism model) (sourceLocalModel.{u,max c s t m} D).doctrine
      (targetLocalModel model).doctrine where
  hom := liftedPredicateHom model
  natural substitution predicate :=
    congrArg ULift.up (predicate_substitution model predicate.down substitution.down)
  all type predicate body bodies := by
    have original := down_heq
      (congrArg model.localModel.doctrine.Predicate
        (congrArg Sigma.fst (represented_extension model type.down))) bodies
    exact congrArg ULift.up (all_value model type.down predicate.down body.down original)
  some type predicate body bodies := by
    have original := down_heq
      (congrArg model.localModel.doctrine.Predicate
        (congrArg Sigma.fst (represented_extension model type.down))) bodies
    exact congrArg ULift.up (some_value model type.down predicate.down body.down original)

theorem propositions_preserved :
    PropositionPreservation (doctrine_preserved model)
      (sourceLocalModel.{u,max c s t m} D).propositions (targetLocalModel model).propositions where
  formation context := congrArg ULift.up (omega_value model context.down)
  quote predicate := up_heq (quote_value model predicate.down)

theorem lifted_assumed_context (context : (SourceModel.{u,max c s t m} D).toCwf.Ctx)
    (predicate : (sourceLocalModel.{u,max c s t m} D).doctrine.Predicate context) :
    (familyMorphism model).base.obj
      ⟨(sourceLocalModel.{u,max c s t m} D).assumptions.assumed context predicate⟩ =
        (⟨(targetLocalModel model).assumptions.assumed
          ((familyMorphism model).base.obj ⟨context⟩).val
          (liftedPredicateHom model context predicate)⟩ : (TargetModel.{u,c,s,t,m} C).toCwf.base.Context) := by
  apply ContextualBase.Context.ext
  exact congrArg ULift.up (assumption_context_value model context.down predicate.down)

theorem assumptions_preserved :
    AssumptionPreservation (doctrine_preserved model)
      (sourceLocalModel.{u,max c s t m} D).assumptions (targetLocalModel model).assumptions where
  assumed := lifted_assumed_context model
  inclusion predicate :=
    hom_eq_of_source_heq (lifted_assumed_context model _ predicate) _ _
      (up_heq (assumption_inclusion_value model predicate.down))

set_option backward.isDefEq.respectTransparency false in
theorem refinements_preserved :
    RefinementPreservation (doctrine_preserved model)
      (sourceLocalModel.{u,max c s t m} D).refinements (targetLocalModel model).refinements where
  formation type predicate body bodies := by
    have original := down_heq
      (congrArg model.localModel.doctrine.Predicate
        (congrArg Sigma.fst (represented_extension model type.down))) bodies
    exact congrArg ULift.up (refinement_type_value model type.down predicate.down body.down original)
  intro type predicate body bodies term guard transportedGuard := by
    have original := down_heq
      (congrArg model.localModel.doctrine.Predicate
        (congrArg Sigma.fst (represented_extension model type.down))) bodies
    have sourceGuard := Mettapedia.TypeTheory.ContextualPredicateModelUniverseLift.refinement_guard_readout
      (predicateDoctrine D) predicate term guard
    have computed := refinement_introduction_value model predicate.down term.down body.down original
      (termValue model term.down) HEq.rfl sourceGuard
    exact up_heq computed
  forget type predicate body bodies term value terms := by
    have original := down_heq
      (congrArg model.localModel.doctrine.Predicate
        (congrArg Sigma.fst (represented_extension model type.down))) bodies
    have formation := refinement_type_value model type.down predicate.down body.down original
    have originalTerms := down_heq
      (congrArg (C.toCwf.Tm (contextValue model _).1) formation) terms
    exact up_heq (refinement_forgetting_value model predicate.down term.down body.down original
      value.down originalTerms)

noncomputable def predicate_logical_preservation :
    PredicateLogicalPreservation (strictMorphism model) (sourceLocalModel.{u,max c s t m} D)
      (targetLocalModel model) :=
  ⟨doctrine_preserved model, propositions_preserved model,
    assumptions_preserved model, refinements_preserved model⟩

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.Interpretation
