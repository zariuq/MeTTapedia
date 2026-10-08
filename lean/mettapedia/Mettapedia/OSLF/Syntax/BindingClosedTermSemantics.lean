import Mettapedia.OSLF.Syntax.BindingClosedInterpretation
import Mettapedia.OSLF.Syntax.BindingClosedTerms

/-!
# Complete open-term readouts in arbitrary closed targets

The target interpretation is computed independently from the scoped binding
term, using its actual products, projections and function objects. Evaluation
of the generated raw expression is then compared with that computation. The
comparison retains the ambient context, every bound variable and the whole
ordered operator argument vector.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Binding.ClosedPresentation

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open CartesianMonoidalCategory
open Mettapedia.CategoryTheory.RelativeClosedSyntax
open GeneratedCategory (RawHom)
open CategoricalBindingModel

universe u v

variable {binding : Mettapedia.OSLF.Binding.Signature}
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
variable [MonoidalClosed C] [HasFiniteLimits C]

namespace Operations

variable (operations : Operations binding C)

def appendContext : (before after : Ctx binding) →
    operations.context before ⊗ operations.context after ⟶ operations.context (before ++ after)
  | [], after => snd _ (operations.context after)
  | sort :: before, after =>
      lift (fst _ (operations.context after) ≫ fst (operations.sort sort) (operations.context before))
        (lift (fst _ (operations.context after) ≫ snd (operations.sort sort) (operations.context before))
          (snd _ (operations.context after)) ≫ appendContext before after)

mutual

def meaning : {context : Ctx binding} → {sort : binding.Srt} → Term binding context sort →
    (operations.context context ⟶ operations.sort sort)
  | _, _, .var position => projectVar operations.sort position
  | _, _, .op operator arguments => meaningArgs arguments ≫ operations.operation operator

def meaningArgs : {context : Ctx binding} → {arities : List (Ctx binding × binding.Srt)} →
    Args binding arities context → (operations.context context ⟶ operations.family arities)
  | context, _, .nil => toUnit (operations.context context)
  | _, _, .cons (bs := binders) body rest =>
      lift (MonoidalClosed.curry (operations.appendContext binders _ ≫ meaning body))
        (meaningArgs rest)

end

theorem projection_read : {context : Ctx binding} → {sort : binding.Srt} →
    (position : Var context sort) →
    operations.assignment.evaluateArrow (projection.{v} binding position).code =
      some ⟨operations.context context, operations.sort sort, projectVar operations.sort position⟩
  | sort :: context, _, .zero =>
      operations.assignment.evaluate_first (operations.sort_read sort) (operations.context_read context)
  | old :: context, _, .succ position =>
      operations.assignment.evaluate_compose _ _
        (operations.assignment.evaluate_second (operations.sort_read old) (operations.context_read context))
        (projection_read position)

theorem appendContext_read : (before after : Ctx binding) →
    operations.assignment.evaluateArrow (contextAppend.{v} binding before after).code =
      some ⟨operations.context before ⊗ operations.context after,
        operations.context (before ++ after), operations.appendContext before after⟩
  | [], after => operations.assignment.evaluate_second
      (operations.context_read []) (operations.context_read after)
  | sort :: before, after => by
      apply operations.assignment.evaluate_pair
      · exact operations.assignment.evaluate_compose _ _
          (operations.assignment.evaluate_first (operations.context_read (sort :: before))
            (operations.context_read after))
          (operations.assignment.evaluate_first (operations.sort_read sort) (operations.context_read before))
      · apply operations.assignment.evaluate_compose
        · apply operations.assignment.evaluate_pair
          · exact operations.assignment.evaluate_compose _ _
              (operations.assignment.evaluate_first (operations.context_read (sort :: before))
                (operations.context_read after))
              (operations.assignment.evaluate_second (operations.sort_read sort)
                (operations.context_read before))
          · exact operations.assignment.evaluate_second (operations.context_read (sort :: before))
              (operations.context_read after)
        · exact appendContext_read before after

omit [MonoidalClosed C] [HasFiniteLimits C] in
private theorem exchange_twice (first second : C) :
    Interpretation.exchange first second ≫ Interpretation.exchange second first = 𝟙 (first ⊗ second) := by
  apply hom_ext <;> simp [Interpretation.exchange]

theorem bindBody_read {context binders : Ctx binding} {sort : binding.Srt}
    (body : RawHom (contextObject.{v} binding (binders ++ context)) (sortObject binding sort))
    (actual : operations.context (binders ++ context) ⟶ operations.sort sort)
    (bodyRead : operations.assignment.evaluateArrow body.code =
      some ⟨operations.context (binders ++ context), operations.sort sort, actual⟩) :
    operations.assignment.evaluateArrow (bindBody binding body).code =
      some ⟨operations.context context, operations.power binders sort,
        MonoidalClosed.curry (operations.appendContext binders context ≫ actual)⟩ := by
  have exchanged := operations.assignment.evaluate_pair _ _
    (operations.assignment.evaluate_second (operations.context_read context) (operations.context_read binders))
    (operations.assignment.evaluate_first (operations.context_read context) (operations.context_read binders))
  have joined := operations.assignment.evaluate_compose _ _
    (operations.appendContext_read binders context) bodyRead
  have complete := operations.assignment.evaluate_abstraction _
    (operations.context_read context) (operations.context_read binders) (operations.sort_read sort)
    (operations.assignment.evaluate_compose _ _ exchanged joined)
  have arrowSame : Interpretation.abstraction
      (lift (snd (operations.context context) (operations.context binders))
        (fst (operations.context context) (operations.context binders)) ≫
          operations.appendContext binders context ≫ actual) =
      MonoidalClosed.curry (operations.appendContext binders context ≫ actual) := by
    unfold Interpretation.abstraction
    change MonoidalClosed.curry (Interpretation.exchange (operations.context binders) (operations.context context) ≫
      Interpretation.exchange (operations.context context) (operations.context binders) ≫
        operations.appendContext binders context ≫ actual) = _
    rw [← Category.assoc, exchange_twice, Category.id_comp]
  exact complete.trans (congrArg (fun arrow => some
    (⟨operations.context context, operations.power binders sort, arrow⟩ : Interpretation.ArrowValue C)) arrowSame)

mutual

theorem meaning_read : {context : Ctx binding} → {sort : binding.Srt} →
    (term : Term binding context sort) →
    operations.assignment.evaluateArrow (encode.{v} binding term).code =
      some ⟨operations.context context, operations.sort sort, operations.meaning term⟩
  | _, _, .var position => operations.projection_read position
  | _, _, .op _operator arguments => operations.assignment.evaluate_compose _ _
      (meaningArgs_read arguments) rfl

theorem meaningArgs_read : {context : Ctx binding} → {arities : List (Ctx binding × binding.Srt)} →
    (arguments : Args binding arities context) →
    operations.assignment.evaluateArrow (encodeArgs.{v} binding arguments).code =
      some ⟨operations.context context, operations.family arities, operations.meaningArgs arguments⟩
  | context, _, .nil => operations.assignment.evaluate_terminal_arrow (operations.context_read context)
  | _, _, .cons body rest => operations.assignment.evaluate_pair _ _
      (operations.bindBody_read (encode binding body) (operations.meaning body) (meaning_read body))
      (meaningArgs_read rest)

end

theorem term_complete_readout {context : Ctx binding} {sort : binding.Srt}
    (term : Term binding context sort) :
    (⟨operations.interpretation.functor.obj (contextObject.{v} binding context),
      operations.interpretation.functor.obj (sortObject binding sort),
      operations.interpretation.functor.map (termArrow binding term)⟩ : Interpretation.ArrowValue C) =
      ⟨operations.context context, operations.sort sort, operations.meaning term⟩ := by
  exact Option.some.inj
    ((Interpretation.functor_complete_readout operations.assignment operations.realization (encode binding term)).symm.trans
      (operations.meaning_read term))

end Operations

end Mettapedia.OSLF.Binding.ClosedPresentation
