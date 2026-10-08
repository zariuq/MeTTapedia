import Mettapedia.OSLF.Syntax.BindingClosedSchemaSemantics
import Mettapedia.OSLF.Syntax.CategoricalBindingFunctor

/-!
# Generic schema arrows classify complete natural-family equality

The independently encoded schema arrow is read at the product of its ordinary
context and actual metavariable function family. Naturality then reconstructs
every supplied-stage evaluation. Equality of those generic arrow images is
equivalent to equality of the complete independent natural-family readings.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Binding.ClosedPresentation.Operations

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open CartesianMonoidalCategory
open Mettapedia.CategoryTheory.RelativeClosedSyntax
open GeneratedCategory (RawHom)
open CategoricalBindingModel

universe u v

variable {binding : Mettapedia.OSLF.Binding.Signature}
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
variable [MonoidalClosed C] [HasFiniteLimits C]
variable (operations : Operations binding C)
variable {metavariables : List (MetaArity binding)} {context : Ctx binding} {sort : binding.Srt}

theorem schema_generic_read (term : Term (withMetas binding metavariables) context sort) :
    operations.assignment.evaluateArrow (SchemaExpressions.expression.{v} binding term).code =
      some ⟨operations.context context ⊗ operations.family metavariables, operations.sort sort,
        operations.model.generic metavariables term⟩ := by
  apply operations.schema_read term
    (operations.assignment.evaluate_product (operations.context_read context)
      (operations.family_read metavariables))
    (SchemaExpressions.genericMetas binding metavariables context) (snd _ _)
    (operations.assignment.evaluate_second (operations.context_read context)
      (operations.family_read metavariables))
    (SchemaExpressions.genericEnvironment binding metavariables context)
    (operations.model.genericEnv context (operations.family metavariables))
  intro result position
  exact operations.assignment.evaluate_compose _ _
    (operations.assignment.evaluate_first (operations.context_read context)
      (operations.family_read metavariables)) (operations.projection_read position)

theorem schema_complete_readout (term : Term (withMetas binding metavariables) context sort) :
    (⟨operations.interpretation.functor.obj (SchemaExpressions.genericStage.{v} binding metavariables context),
      operations.interpretation.functor.obj (sortObject binding sort),
      operations.interpretation.functor.map (GeneratedCategory.classOf
        (SchemaExpressions.expression binding term))⟩ : Interpretation.ArrowValue C) =
      ⟨operations.context context ⊗ operations.family metavariables, operations.sort sort,
        operations.model.generic metavariables term⟩ :=
  Option.some.inj ((Interpretation.functor_complete_readout operations.assignment operations.realization
    (SchemaExpressions.expression binding term)).symm.trans (operations.schema_generic_read term))

omit [HasFiniteLimits C] in
theorem schema_generic_eq_iff (first second : Term (withMetas binding metavariables) context sort) :
    operations.model.generic metavariables first = operations.model.generic metavariables second ↔
      operations.model.interp metavariables first = operations.model.interp metavariables second := by
  constructor
  · intro same
    apply Model.ElemOver.ext
    funext Z metas environment
    rw [operations.model.value_eq_generic (operations.model.interp metavariables first) Z metas environment,
      operations.model.value_eq_generic (operations.model.interp metavariables second) Z metas environment]
    exact congrArg (fun arrow => lift (operations.model.tupleEnv environment) metas ≫ arrow) same
  · intro same
    exact congrArg (fun value => value.value (operations.context context ⊗ operations.family metavariables)
      (snd _ _) (operations.model.genericEnv context (operations.family metavariables))) same

theorem schema_arrow_eq_iff (first second : Term (withMetas binding metavariables) context sort) :
    operations.interpretation.functor.map (GeneratedCategory.classOf
        (SchemaExpressions.expression.{v} binding first)) =
      operations.interpretation.functor.map (GeneratedCategory.classOf
        (SchemaExpressions.expression binding second)) ↔
      operations.model.interp metavariables first = operations.model.interp metavariables second := by
  constructor
  · intro same
    have complete := congrArg (fun arrow =>
      (⟨operations.interpretation.functor.obj (SchemaExpressions.genericStage binding metavariables context),
        operations.interpretation.functor.obj (sortObject binding sort), arrow⟩ : Interpretation.ArrowValue C)) same
    rw [operations.schema_complete_readout, operations.schema_complete_readout] at complete
    exact (operations.schema_generic_eq_iff first second).mp (Interpretation.ArrowValue.arrow_injective complete)
  · intro same
    have genericSame := (operations.schema_generic_eq_iff first second).mpr same
    apply Interpretation.ArrowValue.arrow_injective
    rw [operations.schema_complete_readout, operations.schema_complete_readout, genericSame]

omit [HasFiniteLimits C] in
theorem schema_value_from_generic (term : Term (withMetas binding metavariables) context sort)
    (Z : C) (metas : Z ⟶ operations.family metavariables) (environment : operations.model.Env Z context) :
    (operations.model.interp metavariables term).value Z metas environment =
      lift (operations.model.tupleEnv environment) metas ≫ operations.model.generic metavariables term :=
  operations.model.value_eq_generic _ Z metas environment

end Mettapedia.OSLF.Binding.ClosedPresentation.Operations
