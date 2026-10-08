import Mettapedia.Languages.ProcessCalculi.PolyadicPi.BindingClosedGeneratedOperationalEndpoints
import Mettapedia.OSLF.Syntax.BindingClosedGeneratedModelReadout

/-!
# Whole COMM generators on complete binding-function domains

An authored communication edge is transported from its declared domain to
the independent binding model's generic context and complete receiver-family
object. The actual constructor comparison gives both full endpoint readings.
Every arity is included; no receiver is required to represent a raw body.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.BindingClosedGeneratedCommunication

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open CartesianMonoidalCategory
open Mettapedia.CategoryTheory RelativeClosedSyntax GeneratedCategory
open Mettapedia.OSLF.Binding

universe k

abbrev binding := BindingClosedGeneratedOperationalModel.binding.{k}
abbrev constructors := BindingClosedGeneratedOperationalModel.constructors.{k}
abbrev category := BindingClosedGeneratedOperationalModel.category.{k}
abbrev vertex := BindingClosedGeneratedOperationalEndpoints.vertex.{k}
abbrev categoryMap := BindingClosedGeneratedOperationalEndpoints.categoryMap.{k}
abbrev declarations := BindingClosedGeneratedOperationalEndpoints.declarations.{k}

def origin (arity : Nat) : ULift.{k} BindingClosedGeneratedOperational.Origin := ⟨.communication arity⟩

def stage (arity : Nat) := binding.{k}.context (AllArity.comm arity).ctx ⊗
  binding.family (AllArity.communicationMetas arity)

abbrev declaredStage (arity : Nat) :=
  RelativeClosedInternalCategory.RulePresentation.ruleDomain vertex.{k} categoryMap declarations (origin arity)

theorem declaration_stage (arity : Nat) : declaredStage.{k} arity = constructors.obj
    (ClosedPresentation.SchemaExpressions.genericStage AllArity.sig
      (AllArity.communicationMetas arity) (AllArity.comm arity).ctx) :=
  SignatureMap.object_compose BindingClosedGeneratedOperationalEndpoints.arrowInclusion
    BindingClosedGeneratedOperationalEndpoints.equationInclusion (declarations (origin arity)).domain

def stageComparison (arity : Nat) : declaredStage.{k} arity ≅ stage arity :=
  eqToIso (declaration_stage arity) ≪≫
    ClosedPresentation.GeneratedModel.schemaComparison constructors
      (AllArity.communicationMetas arity) (AllArity.comm arity).ctx

theorem complete_before_declaration (arity : Nat) :
    eqToHom (declaration_stage.{k} arity) ≫
      constructors.map (classOf (ClosedPresentation.SchemaExpressions.expression AllArity.sig
        (AllArity.comm arity).lhs)) =
    classOf (RelativeClosedInternalCategory.RulePresentation.before vertex categoryMap declarations (origin arity)) := by
  simp only [eqToHom_refl, Category.id_comp]
  rfl

theorem complete_after_declaration (arity : Nat) :
    eqToHom (declaration_stage.{k} arity) ≫
      constructors.map (classOf (ClosedPresentation.SchemaExpressions.expression AllArity.sig
        (AllArity.comm arity).rhs)) =
    classOf (RelativeClosedInternalCategory.RulePresentation.after vertex categoryMap declarations (origin arity)) := by
  simp only [eqToHom_refl, Category.id_comp]
  rfl

def firing (arity : Nat) : stage.{k} arity ⟶ category.edge :=
  (stageComparison arity).inv ≫ BindingClosedGeneratedOperationalEndpoints.firing (origin arity)

theorem vertex_comparison : BindingClosedGeneratedOperationalEndpoints.vertexComparison.{k} =
    BindingClosedGeneratedOperationalModel.processComparison := rfl

theorem complete_source (arity : Nat) : firing.{k} arity ≫ category.source =
    binding.model.generic (AllArity.communicationMetas arity) (AllArity.comm arity).lhs ≫
      BindingClosedGeneratedOperationalModel.processComparison.hom := by
  rw [firing, Category.assoc, BindingClosedGeneratedOperationalEndpoints.firing_source,
    ← complete_before_declaration]
  simp only [stageComparison, Iso.trans_inv, eqToIso.inv, Category.assoc,
    eqToHom_refl, Category.id_comp]
  have complete := ClosedPresentation.GeneratedModel.complete_schema_arrow constructors (AllArity.comm arity).lhs
  rw [ClosedPresentation.GeneratedModel.sortComparison_hom] at complete
  erw [Category.comp_id] at complete
  simpa only [Category.assoc, binding, BindingClosedGeneratedOperationalModel.binding,
    stage, category, vertex_comparison] using congrArg
    (fun arrow => arrow ≫ BindingClosedGeneratedOperationalModel.processComparison.hom) complete

theorem complete_target (arity : Nat) : firing.{k} arity ≫ category.target =
    binding.model.generic (AllArity.communicationMetas arity) (AllArity.comm arity).rhs ≫
      BindingClosedGeneratedOperationalModel.processComparison.hom := by
  rw [firing, Category.assoc, BindingClosedGeneratedOperationalEndpoints.firing_target,
    ← complete_after_declaration]
  simp only [stageComparison, Iso.trans_inv, eqToIso.inv, Category.assoc,
    eqToHom_refl, Category.id_comp]
  have complete := ClosedPresentation.GeneratedModel.complete_schema_arrow constructors (AllArity.comm arity).rhs
  rw [ClosedPresentation.GeneratedModel.sortComparison_hom] at complete
  erw [Category.comp_id] at complete
  simpa only [Category.assoc, binding, BindingClosedGeneratedOperationalModel.binding,
    stage, category, vertex_comparison] using congrArg
    (fun arrow => arrow ≫ BindingClosedGeneratedOperationalModel.processComparison.hom) complete

def suppliedFiring (arity : Nat) {world : BindingClosedGeneratedOperationalModel.Target.{k}}
    (parameters : world ⟶ binding.family (AllArity.communicationMetas arity))
    (environment : binding.model.Env world (AllArity.comm arity).ctx) : world ⟶ category.edge :=
  lift (binding.model.tupleEnv environment) parameters ≫ firing arity

theorem supplied_source (arity : Nat) {world : BindingClosedGeneratedOperationalModel.Target.{k}}
    (parameters : world ⟶ binding.family (AllArity.communicationMetas arity))
    (environment : binding.model.Env world (AllArity.comm arity).ctx) :
    suppliedFiring arity parameters environment ≫ category.source =
      (binding.model.interp (AllArity.communicationMetas arity) (AllArity.comm arity).lhs).value
        world parameters environment ≫ BindingClosedGeneratedOperationalModel.processComparison.hom := by
  rw [suppliedFiring, Category.assoc, complete_source, ← Category.assoc]
  rw [← binding.schema_value_from_generic]

theorem supplied_target (arity : Nat) {world : BindingClosedGeneratedOperationalModel.Target.{k}}
    (parameters : world ⟶ binding.family (AllArity.communicationMetas arity))
    (environment : binding.model.Env world (AllArity.comm arity).ctx) :
    suppliedFiring arity parameters environment ≫ category.target =
      (binding.model.interp (AllArity.communicationMetas arity) (AllArity.comm arity).rhs).value
        world parameters environment ≫ BindingClosedGeneratedOperationalModel.processComparison.hom := by
  rw [suppliedFiring, Category.assoc, complete_target, ← Category.assoc]
  rw [← binding.schema_value_from_generic]

theorem supplied_substitution (arity : Nat)
    {world future : BindingClosedGeneratedOperationalModel.Target.{k}}
    (change : future ⟶ world) (parameters : world ⟶ binding.family (AllArity.communicationMetas arity))
    (environment : binding.model.Env world (AllArity.comm arity).ctx) :
    suppliedFiring arity (change ≫ parameters) (binding.model.restage change environment) =
      change ≫ suppliedFiring arity parameters environment := by
  rw [suppliedFiring, suppliedFiring, binding.model.tupleEnv_restage, comp_lift_assoc]

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.BindingClosedGeneratedCommunication
