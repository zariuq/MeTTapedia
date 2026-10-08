import Mettapedia.OSLF.Syntax.BindingClosedGeneratedModelReadout
import Mettapedia.CategoryTheory.RelativeClosedSyntaxSignatureMapNormalization

/-!
# Complete recovered binding operations through declaration maps

Postcomposition by an actual declaration map transports the complete ordered
operator function family and the mapped primitive arrow. This comparison is
derived from closed-shape normalization, including every binder position.
It applies to arbitrary finite-limit closed interpretations into the source
generated category. Arbitrary closed functors may have different native
choices; their strict chosen stability is not asserted here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Binding.ClosedPresentation.GeneratedFunctor

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open Mettapedia.CategoryTheory.RelativeClosedSyntax GeneratedCategory FunctorNormalization
open CategoricalBindingModel

universe k

variable {binding : Mettapedia.OSLF.Binding.Signature}
variable {D E : Type k} [Category.{k} D] [Category.{k} E]
variable {middleNames targetNames : Symbols.{k}}
variable {middle : Mettapedia.CategoryTheory.RelativeClosedSyntax.Signature (C := D) (symbols := middleNames)}
variable {target : Mettapedia.CategoryTheory.RelativeClosedSyntax.Signature (C := E) (symbols := targetNames)}
variable (mapping : SignatureMap middle target)

theorem context_map (sort : binding.Srt → Object middle) : (context : Ctx binding) →
    mapping.functor.obj (contextOf sort context) = contextOf (fun result => mapping.functor.obj (sort result)) context
  | [] => rfl
  | result :: rest => by
      change mapping.functor.obj (sort result) ⊗ mapping.functor.obj (contextOf sort rest) = _
      rw [context_map sort rest]

theorem power_map (sort : binding.Srt → Object middle) (context : Ctx binding) (result : binding.Srt) :
    mapping.functor.obj (contextOf sort context ⟶[Object middle] sort result) =
      (contextOf (fun result => mapping.functor.obj (sort result)) context ⟶[Object target]
        mapping.functor.obj (sort result)) := by
  change (mapping.functor.obj (contextOf sort context) ⟶[Object target] mapping.functor.obj (sort result)) = _
  rw [context_map]

theorem family_map (sort : binding.Srt → Object middle) : (arities : List (Ctx binding × binding.Srt)) →
    mapping.functor.obj (familyOf (fun context result => contextOf sort context ⟶[Object middle] sort result) arities) =
      familyOf (fun context result => contextOf (fun result => mapping.functor.obj (sort result)) context
        ⟶[Object target] mapping.functor.obj (sort result)) arities
  | [] => rfl
  | arity :: rest => by
      change mapping.functor.obj (contextOf sort arity.1 ⟶[Object middle] sort arity.2) ⊗
        mapping.functor.obj (familyOf (fun context result => contextOf sort context ⟶[Object middle] sort result) rest) = _
      rw [power_map, family_map sort rest]

/-- The full primitive family is transported before applying the mapped arrow. -/
def mapOperations (operations : Operations binding (Object middle)) : Operations binding (Object target) where
  sort result := mapping.functor.obj (operations.sort result)
  operation operator := eqToHom (family_map mapping operations.sort (binding.arity operator)).symm ≫
    mapping.functor.map (operations.operation operator)

private theorem transported_value {first nextFirst last : Object target}
    (arrow : first ⟶ last) (same : first = nextFirst) :
    (⟨nextFirst, last, eqToHom same.symm ≫ arrow⟩ : Interpretation.ArrowValue (Object target)) =
      ⟨first, last, arrow⟩ := by
  cases same
  simp only [eqToHom_refl, Category.id_comp]

theorem mapOperations_primitive (operations : Operations binding (Object middle))
    (origin : Sigma binding.Op) :
    (mapOperations mapping operations).primitiveValue origin =
      (⟨mapping.functor.obj (operations.family (binding.arity origin.2)),
        mapping.functor.obj (operations.sort origin.1),
        mapping.functor.map (operations.operation origin.2)⟩ : Interpretation.ArrowValue (Object target)) :=
  transported_value _ (family_map mapping operations.sort (binding.arity origin.2))

theorem mapOperations_operation_heq (operations : Operations binding (Object middle))
    {result : binding.Srt} (operator : binding.Op result) :
    HEq ((mapOperations mapping operations).operation operator)
      (mapping.functor.map (operations.operation operator)) :=
  Interpretation.ArrowValue.arrows_heq (mapOperations_primitive mapping operations ⟨result, operator⟩)

private theorem context_shape : (context : Ctx binding) →
    SignatureMap.ClosedShape (contextObject.{k} binding context)
  | [] => .unit
  | result :: rest => .product
      (SignatureMap.ClosedShape.named (source := signature.{k} binding) (ULift.up result)) (context_shape rest)

private theorem family_shape : (arities : List (Ctx binding × binding.Srt)) →
    SignatureMap.ClosedShape (familyObject.{k} binding arities)
  | [] => .unit
  | arity :: rest => .product (.function (context_shape arity.1)
      (SignatureMap.ClosedShape.named (source := signature.{k} binding) (ULift.up arity.2)))
      (family_shape rest)

variable (before : Object (signature.{k} binding) ⥤ Object middle)
variable [PreservesFiniteLimits before] [MonoidalClosedFunctor before]

private instance composite_finite : PreservesFiniteLimits (before ⋙ mapping.functor) :=
  comp_preservesFiniteLimits _ _

private instance composite_closed : MonoidalClosedFunctor (before ⋙ mapping.functor) :=
  Mettapedia.CategoryTheory.CartesianClosedFunctorCoherence.closed_composition _ _

private def mapValue (value : Interpretation.ArrowValue (Object middle)) :
    Interpretation.ArrowValue (Object target) :=
  ⟨mapping.functor.obj value.source, mapping.functor.obj value.target, mapping.functor.map value.arrow⟩

theorem primitive_postcomposition (origin : Sigma binding.Op) :
    (GeneratedModel.operations (before ⋙ mapping.functor)).primitiveValue origin =
      (mapOperations mapping (GeneratedModel.operations before)).primitiveValue origin := by
  have whole := mapping.normalized_arrow_postcomposition before
    (family_shape (binding.arity origin.2))
      (SignatureMap.ClosedShape.named (source := signature.{k} binding) (ULift.up origin.1))
      (classOf (operator binding origin.2))
  have old := congrArg (mapValue mapping) (GeneratedModel.primitive_value before origin)
  exact (GeneratedModel.primitive_value (before ⋙ mapping.functor) origin).trans
    (whole.trans (old.symm.trans (mapOperations_primitive mapping (GeneratedModel.operations before) origin).symm))

private theorem operations_ext (first second : Operations binding (Object target))
    (sortSame : first.sort = second.sort)
    (primitiveSame : ∀ origin, first.primitiveValue origin = second.primitiveValue origin) : first = second := by
  cases first with
  | mk firstSort firstOperation =>
    cases second with
    | mk secondSort secondOperation =>
      dsimp at sortSame
      cases sortSame
      have operationSame : @firstOperation = @secondOperation := by
        funext result operator
        exact Interpretation.ArrowValue.arrow_injective (primitiveSame ⟨result, operator⟩)
      cases operationSame
      rfl

/-- Equality is earned on both complete primitive domains and arrows. -/
theorem operations_postcomposition :
    GeneratedModel.operations (before ⋙ mapping.functor) =
      mapOperations mapping (GeneratedModel.operations before) :=
  operations_ext _ _ rfl (primitive_postcomposition mapping before)

end Mettapedia.OSLF.Binding.ClosedPresentation.GeneratedFunctor
