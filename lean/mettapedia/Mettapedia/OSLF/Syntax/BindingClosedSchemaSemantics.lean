import Mettapedia.OSLF.Syntax.BindingClosedSchemaReadout

/-!
# Complete schema interpretation at every categorical stage

The equation-schema encoder is compared with the independent natural-family
fold. The comparison covers supplied function-valued metavariables, ambient
variables and arbitrary ordered binder lists. No whole-schema interpretation
is included among the primitive realization assumptions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Binding.ClosedPresentation.Operations

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open CartesianMonoidalCategory
open Mettapedia.CategoryTheory.RelativeClosedSyntax
open GeneratedCategory (RawHom Object product)
open CategoricalBindingModel

universe u v

variable {binding : Mettapedia.OSLF.Binding.Signature}
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
variable [MonoidalClosed C] [HasFiniteLimits C]
variable (operations : Operations binding C)
variable {metavariables : List (MetaArity binding)}

mutual

theorem schema_read : {context : Ctx binding} → {sort : binding.Srt} →
    (term : Term (withMetas binding metavariables) context sort) →
    {stage : Object (signature.{v} binding)} → {Z : C} →
    (stageRead : operations.assignment.evaluateObject stage.code = some Z) →
    (metas : RawHom stage (familyObject binding metavariables)) →
    (actualMetas : Z ⟶ operations.family metavariables) →
    (metasRead : operations.assignment.evaluateArrow metas.code =
      some ⟨Z, operations.family metavariables, actualMetas⟩) →
    (environment : SchemaExpressions.Environment binding stage context) →
    (actualEnvironment : operations.model.Env Z context) →
    operations.EnvironmentRead environment actualEnvironment →
    operations.assignment.evaluateArrow (SchemaExpressions.encode binding metas environment term).code =
      some ⟨Z, operations.sort sort,
        (operations.model.interp metavariables term).value Z actualMetas actualEnvironment⟩
  | _, _, .var position, _, _, _, _, _, _, _, _, environmentRead => by
      rw [SchemaExpressions.encode]
      exact environmentRead _ position
  | _, _, .op (Sum.inl operation) arguments, _, _, stageRead,
      metas, actualMetas, metasRead, environment, actualEnvironment, environmentRead => by
      rw [SchemaExpressions.encode]
      exact operations.assignment.evaluate_compose _ _
        (schemaArgs_read arguments stageRead metas actualMetas metasRead
          environment actualEnvironment environmentRead) rfl
  | _, _, .op (Sum.inr (.mk index)) arguments, _, _, stageRead,
      metas, actualMetas, metasRead, environment, actualEnvironment, environmentRead => by
      rw [SchemaExpressions.encode]
      exact operations.applyFunction_read (metavariables.get index).1 (metavariables.get index).2
        (RawHom.compose metas (SchemaExpressions.familyProjection binding metavariables index))
        (SchemaExpressions.encodeMetaArgs binding metas (metavariables.get index).1 environment arguments)
        (actualMetas ≫ operations.model.familyProj metavariables index) _
        (operations.assignment.evaluate_compose _ _ metasRead
          (operations.familyProjection_read metavariables index))
        (schemaMetaArgs_read (metavariables.get index).1 arguments stageRead
          metas actualMetas metasRead environment actualEnvironment environmentRead)
termination_by _ _ term => 2 * termSize term
decreasing_by all_goals simp only [termSize]; omega

theorem schemaArgs_read : {context : Ctx binding} → {arities : List (MetaArity binding)} →
    (arguments : Args (withMetas binding metavariables) arities context) →
    {stage : Object (signature.{v} binding)} → {Z : C} →
    (stageRead : operations.assignment.evaluateObject stage.code = some Z) →
    (metas : RawHom stage (familyObject binding metavariables)) →
    (actualMetas : Z ⟶ operations.family metavariables) →
    (metasRead : operations.assignment.evaluateArrow metas.code =
      some ⟨Z, operations.family metavariables, actualMetas⟩) →
    (environment : SchemaExpressions.Environment binding stage context) →
    (actualEnvironment : operations.model.Env Z context) →
    operations.EnvironmentRead environment actualEnvironment →
    operations.assignment.evaluateArrow (SchemaExpressions.encodeArgs binding metas environment arguments).code =
      some ⟨Z, operations.family arities,
        operations.model.tupleArgs
          (BindingCloneFoldSubstitution.interpretArgs (operations.model.kripke metavariables) arguments)
          Z actualMetas actualEnvironment⟩
  | _, _, .nil, _, _, stageRead, _, _, _, _, _, _ => by
      rw [SchemaExpressions.encodeArgs]
      exact operations.assignment.evaluate_terminal_arrow stageRead
  | _, _, .cons (bs := binders) body rest, stage, Z, stageRead,
      metas, actualMetas, metasRead, environment, actualEnvironment, environmentRead => by
      rw [SchemaExpressions.encodeArgs]
      have bodyRead := schema_read body
        (operations.assignment.evaluate_product (operations.context_read binders) stageRead)
        (RawHom.compose (RawHom.second (contextObject binding binders) stage) metas)
        (snd (operations.context binders) Z ≫ actualMetas)
        (operations.assignment.evaluate_compose _ _
          (operations.assignment.evaluate_second (operations.context_read binders) stageRead) metasRead)
        (SchemaExpressions.extendEnvironment binding binders environment)
        (operations.model.extendEnv binders actualEnvironment)
        (operations.extendEnvironment_read binders stageRead environment actualEnvironment environmentRead)
      exact operations.assignment.evaluate_pair _ _
        (operations.curry_read binders _ stageRead _ _ bodyRead)
        (schemaArgs_read rest stageRead metas actualMetas metasRead
          environment actualEnvironment environmentRead)
termination_by _ _ arguments => 2 * argsSize arguments + 1
decreasing_by all_goals simp only [argsSize]; have := termSize_pos body; omega

theorem schemaMetaArgs_read : (dependencies : Ctx binding) → {context : Ctx binding} →
    (arguments : Args (withMetas binding metavariables)
      (dependencies.map (fun sort => ([], sort))) context) →
    {stage : Object (signature.{v} binding)} → {Z : C} →
    (stageRead : operations.assignment.evaluateObject stage.code = some Z) →
    (metas : RawHom stage (familyObject binding metavariables)) →
    (actualMetas : Z ⟶ operations.family metavariables) →
    (metasRead : operations.assignment.evaluateArrow metas.code =
      some ⟨Z, operations.family metavariables, actualMetas⟩) →
    (environment : SchemaExpressions.Environment binding stage context) →
    (actualEnvironment : operations.model.Env Z context) →
    operations.EnvironmentRead environment actualEnvironment →
    operations.assignment.evaluateArrow
      (SchemaExpressions.encodeMetaArgs binding metas dependencies environment arguments).code =
      some ⟨Z, operations.context dependencies,
        operations.model.tupleCtx dependencies
          (BindingCloneFoldSubstitution.interpretArgs (operations.model.kripke metavariables) arguments)
          Z actualMetas actualEnvironment⟩
  | [], _, .nil, _, _, stageRead, _, _, _, _, _, _ => by
      rw [SchemaExpressions.encodeMetaArgs]
      exact operations.assignment.evaluate_terminal_arrow stageRead
  | _ :: dependencies, _, .cons head rest, _, _, stageRead,
      metas, actualMetas, metasRead, environment, actualEnvironment, environmentRead => by
      rw [SchemaExpressions.encodeMetaArgs]
      exact operations.assignment.evaluate_pair _ _
        (schema_read head stageRead metas actualMetas metasRead environment actualEnvironment environmentRead)
        (schemaMetaArgs_read dependencies rest stageRead metas actualMetas metasRead
          environment actualEnvironment environmentRead)
termination_by _ _ arguments => 2 * argsSize arguments + 1
decreasing_by all_goals simp only [argsSize]; have := termSize_pos head; omega

end

end Mettapedia.OSLF.Binding.ClosedPresentation.Operations
