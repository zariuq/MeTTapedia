import Mettapedia.OSLF.Syntax.BindingClosedTermSemantics
import Mettapedia.OSLF.Syntax.CategoricalBindingKripke
import Mettapedia.OSLF.Syntax.SignatureMorphism

/-!
# Comparison with the categorical binding model at all environments

Open terms are interpreted independently by the generated closed expression
evaluator and by the existing natural-family model. Their complete readings
agree at every stage and variable environment, including beneath arbitrary
ordered binder lists. The comparison is earned from product universality and
the naturality of currying.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Binding.ClosedPresentation

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open CartesianMonoidalCategory
open CategoricalBindingModel

universe u v

variable {binding : Mettapedia.OSLF.Binding.Signature}
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
variable [MonoidalClosed C]

namespace Operations

variable (operations : Operations binding C)

theorem restage_projections {Z : C} {context : Ctx binding}
    (environment : operations.model.Env Z context) :
    operations.model.restage (operations.model.tupleEnv environment)
      (operations.model.projections context) = environment := by
  funext sort position
  exact operations.model.tupleEnv_projectVar environment position

theorem appendContext_environment (before after : Ctx binding) :
    operations.appendContext before after = operations.model.tupleEnv
      (operations.model.extendEnv before (operations.model.projections after)) := by
  induction before with
  | nil =>
      change snd _ _ = operations.model.tupleEnv
        (operations.model.restage (snd _ _) (operations.model.projections after))
      rw [operations.model.tupleEnv_restage, operations.model.tupleEnv_projections, Category.comp_id]
  | cons sort before inductionHypothesis =>
      change lift _ (_ ≫ operations.appendContext before after) = lift _
        (operations.model.tupleEnv (operations.model.restage
          (lift (fst _ _ ≫ snd _ _) (snd _ _))
          (operations.model.extendEnv before (operations.model.projections after))))
      rw [operations.model.tupleEnv_restage, inductionHypothesis]
      rfl

theorem appendContext_natural {Z : C} (binders : Ctx binding) {context : Ctx binding}
    (environment : operations.model.Env Z context) :
    operations.model.tupleEnv (operations.model.extendEnv binders environment) =
      (operations.context binders ◁ operations.model.tupleEnv environment) ≫
        operations.appendContext binders context := by
  rw [operations.appendContext_environment]
  have extended := operations.model.extendEnv_restage
    (operations.model.tupleEnv environment) binders (operations.model.projections context)
  rw [operations.restage_projections environment] at extended
  rw [extended, operations.model.tupleEnv_restage]
  rfl

mutual

theorem meaning_model_value : {context : Ctx binding} → {sort : binding.Srt} →
    (term : Term binding context sort) → (Z : C) → (metas : Z ⟶ operations.model.family []) →
    (environment : operations.model.Env Z context) →
    (operations.model.interp [] (embed term)).value Z metas environment =
      operations.model.tupleEnv environment ≫ operations.meaning term
  | _, _, .var position, _, _, environment =>
      (operations.model.tupleEnv_projectVar environment position).symm
  | _, _, .op operator arguments, Z, metas, environment => by
      change operations.model.tupleArgs
        (BindingCloneFoldSubstitution.interpretArgs (operations.model.kripke []) (embedArgs arguments))
          Z metas environment ≫ operations.operation operator = _
      change _ = operations.model.tupleEnv environment ≫
        (operations.meaningArgs arguments ≫ operations.operation operator)
      rw [meaningArgs_model_value arguments Z metas environment, Category.assoc]

theorem meaningArgs_model_value : {context : Ctx binding} →
    {arities : List (Ctx binding × binding.Srt)} →
    (arguments : Args binding arities context) → (Z : C) → (metas : Z ⟶ operations.model.family []) →
    (environment : operations.model.Env Z context) →
    operations.model.tupleArgs
      (BindingCloneFoldSubstitution.interpretArgs (operations.model.kripke []) (embedArgs arguments))
        Z metas environment = operations.model.tupleEnv environment ≫ operations.meaningArgs arguments
  | _, _, .nil, _, _, _ => toUnit_unique _ _
  | _, _, .cons (bs := binders) body rest, Z, metas, environment => by
      change lift (operations.model.curry
        ((operations.model.interp [] (embed body)).value (operations.model.ctx binders ⊗ Z)
          (snd _ _ ≫ metas) (operations.model.extendEnv binders environment)))
        (operations.model.tupleArgs
          (BindingCloneFoldSubstitution.interpretArgs (operations.model.kripke []) (embedArgs rest))
          Z metas environment) = _
      change _ = operations.model.tupleEnv environment ≫
        lift (MonoidalClosed.curry (operations.appendContext binders _ ≫ operations.meaning body))
          (operations.meaningArgs rest)
      rw [meaning_model_value body, meaningArgs_model_value rest, operations.appendContext_natural,
        Category.assoc]
      change lift (MonoidalClosed.curry
        ((operations.context binders ◁ operations.model.tupleEnv environment) ≫
          (operations.appendContext binders _ ≫ operations.meaning body))) _ = _
      rw [MonoidalClosed.curry_natural_left]
      exact (comp_lift _ _ _).symm

end

theorem meaning_at_projections {context : Ctx binding} {sort : binding.Srt}
    (term : Term binding context sort) :
    (operations.model.interp [] (embed term)).value (operations.context context)
      (toUnit (operations.context context)) (operations.model.projections context) =
      operations.meaning term := by
  rw [operations.meaning_model_value, operations.model.tupleEnv_projections]
  exact Category.id_comp _

end Operations

end Mettapedia.OSLF.Binding.ClosedPresentation
