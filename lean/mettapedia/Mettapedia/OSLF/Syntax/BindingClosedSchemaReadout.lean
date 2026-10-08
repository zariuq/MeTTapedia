import Mettapedia.OSLF.Syntax.BindingClosedSchemaExpressions
import Mettapedia.OSLF.Syntax.BindingClosedContextSemantics

/-!
# Readouts of schema environments and complete function arguments

The structural parser reads the independently constructed schema projections,
environment extensions, applications and abstractions as the actual categorical
binding operations. These comparisons hold at arbitrary supplied stages and
retain every ordered binder and the complete function-valued argument.
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

abbrev EnvironmentRead {stage : Object (signature.{v} binding)} {Z : C}
    {context : Ctx binding} (environment : SchemaExpressions.Environment binding stage context)
    (actual : operations.model.Env Z context) : Prop :=
  ∀ sort position, operations.assignment.evaluateArrow (environment sort position).code =
    some ⟨Z, operations.sort sort, actual sort position⟩

theorem extendEnvironment_read : (binders : Ctx binding) →
    {stage : Object (signature.{v} binding)} → {Z : C} → {context : Ctx binding} →
    (stageRead : operations.assignment.evaluateObject stage.code = some Z) →
    (environment : SchemaExpressions.Environment binding stage context) →
    (actual : operations.model.Env Z context) → operations.EnvironmentRead environment actual →
    operations.EnvironmentRead (SchemaExpressions.extendEnvironment binding binders environment)
      (operations.model.extendEnv binders actual)
  | [], _, _, _, stageRead, _, _, environmentRead => fun sort position =>
      operations.assignment.evaluate_compose _ _
        (operations.assignment.evaluate_second (operations.context_read []) stageRead)
        (environmentRead sort position)
  | head :: binders, _, _, _, stageRead, environment, actual, environmentRead =>
      fun sort position => match position with
      | .zero => operations.assignment.evaluate_compose _ _
          (operations.assignment.evaluate_first (operations.context_read (head :: binders)) stageRead)
          (operations.assignment.evaluate_first (operations.sort_read head) (operations.context_read binders))
      | .succ old => operations.assignment.evaluate_compose _ _
          (operations.assignment.evaluate_pair _ _
            (operations.assignment.evaluate_compose _ _
              (operations.assignment.evaluate_first (operations.context_read (head :: binders)) stageRead)
              (operations.assignment.evaluate_second (operations.sort_read head) (operations.context_read binders)))
            (operations.assignment.evaluate_second (operations.context_read (head :: binders)) stageRead))
          (extendEnvironment_read binders stageRead environment actual environmentRead sort old)

theorem familyProjection_read : (arities : List (MetaArity binding)) →
    (index : Fin arities.length) →
    operations.assignment.evaluateArrow (SchemaExpressions.familyProjection.{v} binding arities index).code =
      some ⟨operations.family arities, operations.power (arities.get index).1 (arities.get index).2,
        operations.model.familyProj arities index⟩
  | arity :: rest, ⟨0, _⟩ =>
      operations.assignment.evaluate_first (operations.power_read arity.1 arity.2) (operations.family_read rest)
  | arity :: rest, ⟨n + 1, bound⟩ => operations.assignment.evaluate_compose _ _
      (operations.assignment.evaluate_second (operations.power_read arity.1 arity.2) (operations.family_read rest))
      (familyProjection_read rest ⟨n, Nat.lt_of_succ_lt_succ bound⟩)

theorem applyFunction_read {stage : Object (signature.{v} binding)} {Z : C}
    (binders : Ctx binding) (sort : binding.Srt)
    (function : RawHom stage (powerObject binding binders sort))
    (value : RawHom stage (contextObject binding binders))
    (actualFunction : Z ⟶ operations.power binders sort)
    (actualValue : Z ⟶ operations.context binders)
    (functionRead : operations.assignment.evaluateArrow function.code =
      some ⟨Z, operations.power binders sort, actualFunction⟩)
    (valueRead : operations.assignment.evaluateArrow value.code =
      some ⟨Z, operations.context binders, actualValue⟩) :
    operations.assignment.evaluateArrow (SchemaExpressions.applyFunction binding
      (argument := contextObject binding binders) (result := sortObject binding sort) function value).code =
      some ⟨Z, operations.sort sort,
        lift actualValue actualFunction ≫ operations.model.eval binders sort⟩ := by
  have complete := operations.assignment.evaluate_compose _ _
    (operations.assignment.evaluate_pair _ _ functionRead valueRead)
    (operations.assignment.evaluate_evaluation (operations.context_read binders) (operations.sort_read sort))
  have exchanged : lift actualFunction actualValue ≫
      Interpretation.exchange (operations.power binders sort) (operations.context binders) =
      lift actualValue actualFunction := by
    apply hom_ext <;> simp [Interpretation.exchange]
  have same : lift actualFunction actualValue ≫
      Interpretation.evaluation (operations.context binders) (operations.sort sort) =
      lift actualValue actualFunction ≫ operations.model.eval binders sort := by
    change lift actualFunction actualValue ≫
      (Interpretation.exchange (operations.power binders sort) (operations.context binders) ≫
        operations.model.eval binders sort) = _
    rw [← Category.assoc, exchanged]
  exact complete.trans (congrArg (fun arrow => some
    (⟨Z, operations.sort sort, arrow⟩ : Interpretation.ArrowValue C)) same)

omit [MonoidalClosed C] [HasFiniteLimits C] in
private theorem exchange_twice (first second : C) :
    Interpretation.exchange first second ≫ Interpretation.exchange second first = 𝟙 (first ⊗ second) := by
  apply hom_ext <;> simp [Interpretation.exchange]

theorem curry_read {stage : Object (signature.{v} binding)} {Z : C}
    (binders : Ctx binding) (sort : binding.Srt)
    (stageRead : operations.assignment.evaluateObject stage.code = some Z)
    (body : RawHom (product (contextObject binding binders) stage) (sortObject binding sort))
    (actual : operations.context binders ⊗ Z ⟶ operations.sort sort)
    (bodyRead : operations.assignment.evaluateArrow body.code =
      some ⟨operations.context binders ⊗ Z, operations.sort sort, actual⟩) :
    operations.assignment.evaluateArrow (RawHom.curry body).code =
      some ⟨Z, operations.power binders sort, operations.model.curry actual⟩ := by
  have swapped := operations.assignment.evaluate_pair _ _
    (operations.assignment.evaluate_second stageRead (operations.context_read binders))
    (operations.assignment.evaluate_first stageRead (operations.context_read binders))
  have complete := operations.assignment.evaluate_abstraction _ stageRead
    (operations.context_read binders) (operations.sort_read sort)
    (operations.assignment.evaluate_compose _ _ swapped bodyRead)
  have same : Interpretation.abstraction
      (Interpretation.exchange Z (operations.context binders) ≫ actual) = operations.model.curry actual := by
    unfold Interpretation.abstraction
    rw [← Category.assoc, exchange_twice, Category.id_comp]
    rfl
  exact complete.trans (congrArg (fun arrow => some
    (⟨Z, operations.power binders sort, arrow⟩ : Interpretation.ArrowValue C)) same)

end Mettapedia.OSLF.Binding.ClosedPresentation.Operations
