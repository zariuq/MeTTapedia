import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementSyntacticReadoutFold
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementChosenContextFixedPoint
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementContextualPresentationEquality

/-!
# Mixed source context and annotation readbacks

Successful evaluation reconstructs a generated context equation between the
actual chosen mixed scope and the authored context. Selection fixes the supplied
native mixed, so the resulting semantic context is exactly the chosen
presentation of the authored context. This uses the complete local constructor
readouts; no header realization or whole-source inverse is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.SyntacticReification

open _root_.CategoryTheory
open Mettapedia.TypeTheory.ContextualPredicateModelScopes
open SyntacticModel SyntacticScopes
open External (bindResult bindResult_eq_some_iff)

universe u
variable {S : Symbols.{u}} {D : Signature S}

set_option backward.isDefEq.respectTransparency false in
theorem raw_context_readout (headers : HeaderFormation D) : {n : Nat} →
    (raw : ContextExpr S n) → (scope : Scope D n) →
    (data headers).evaluateContext raw = some scope.semantic →
    Holds D (.contextEq scope.raw raw)
  | _, .nil, scope, evaluated => by
      have same : Scope.nil D = scope := Scope.semantic_injective (Option.some.inj evaluated)
      rw [← same]
      exact conclude (.contextReflexivity .nil) ⟨(Scope.nil D).formed.judgment, trivial⟩
  | _, .snoc previous type, scope, evaluated => by
      rw [Abstract.ModelData.evaluateContext] at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨earlier, earlierRead, rest⟩
      rcases (bindResult_eq_some_iff _ _ _).mp rest with ⟨A, typeRead, result⟩
      rcases (⟨Scope.ofSemantic earlier, Scope.ofSemantic_semantic earlier⟩ :
        ∃ preceding : Scope D _, preceding.semantic = earlier) with ⟨preceding, rfl⟩
      have same : preceding.snoc A = scope := by
        apply Scope.semantic_injective
        rw [Scope.snoc_semantic]
        exact Option.some.inj result
      rw [← same]
      have before := raw_context_readout headers previous preceding earlierRead
      rcases raw_type_readout headers type preceding A typeRead with
        ⟨annotation, codeRead, classRead⟩
      have types := domain_equality annotation classRead
      rw [codeRead] at types
      have typed : Holds D (.type previous type) := by
        have original := annotation.formed
        rw [codeRead] at original
        exact conclude (.transportType preceding.raw previous type) ⟨before, original, trivial⟩
      exact conclude (.contextExtendEquality preceding.raw previous
        (QuotientCwf.typeRepresentative A).code type) ⟨before, types, typed, trivial⟩


  | _, .assume previous predicate, scope, evaluated => by
      rw [Abstract.ModelData.evaluateContext] at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨earlier, earlierRead, rest⟩
      rcases (bindResult_eq_some_iff _ _ _).mp rest with ⟨body, predicateRead, result⟩
      rcases (⟨Scope.ofSemantic earlier, Scope.ofSemantic_semantic earlier⟩ :
        ∃ preceding : Scope D _, preceding.semantic = earlier) with ⟨preceding, rfl⟩
      have same : preceding.assume body = scope := by
        apply Scope.semantic_injective
        rw [Scope.assume_semantic]
        exact Option.some.inj result
      rw [← same]
      have before := raw_context_readout headers previous preceding earlierRead
      rcases raw_predicate_readout headers predicate preceding body predicateRead with
        ⟨annotation, codeRead, classRead⟩
      have predicates := (QPredicate.mk_eq_iff _ _).mp
        ((AssumptionModel.chosen_class body).trans classRead.symm)
      rw [codeRead] at predicates
      have formed : Holds D (.predicate previous predicate) := by
        have original := annotation.formed
        rw [codeRead] at original
        exact conclude (.transportPredicate preceding.raw previous predicate) ⟨before, original, trivial⟩
      exact conclude (.contextAssumeEquality preceding.raw previous
        (AssumptionModel.chosen body).code predicate) ⟨before, predicates, formed, trivial⟩

theorem parameterScope_mixed {n : Nat}
    (context : Abstract.ModelScope (C D) (generatedModel D) n) :
    HEq (parameterScope context.1.as) context := by
  rcases context with ⟨⟨⟨arity, raw, formed⟩⟩, mixed⟩
  have counts : arity = n := scope_arity mixed
  cases counts
  have fixed := Presentation.selectedContext_scope_fixed mixed
  apply heq_of_eq
  apply semantic_scope_ext
  exact congrArg (quotientProjection D).obj fixed

set_option backward.isDefEq.respectTransparency false in
theorem context_evaluation_normalized (headers : HeaderFormation D) {n : Nat}
    (raw : ContextExpr S n) (formed : Formed D raw)
    (context : Abstract.ModelScope (C D) (generatedModel D) n)
    (read : (data headers).evaluateContext raw = some context) :
    context = parameterScope ⟨n, raw, formed⟩ := by
  let scope := Scope.ofSemantic context
  have scopeRead : (data headers).evaluateContext raw = some scope.semantic := by
    rw [Scope.ofSemantic_semantic]
    exact read
  have same := raw_context_readout headers raw scope scopeRead
  have selected := PresentationEquality.selected_scope same scope.formed formed
  have fixed : parameterScope scope.source = scope.semantic :=
    eq_of_heq (parameterScope_mixed scope.semantic)
  change parameterScope scope.source = parameterScope ⟨n, raw, formed⟩ at selected
  exact (Scope.ofSemantic_semantic context).symm.trans (fixed.symm.trans selected)

set_option backward.isDefEq.respectTransparency false in
theorem type_evaluation_class (headers : HeaderFormation D) {n : Nat}
    (context : Abstract.ModelScope (C D) (generatedModel D) n)
    (raw : TypeExpr S n) (annotation : TypeOver context.1.as)
    (codeRead : HEq annotation.code raw)
    (value : QuotientCwf.Ty context.1)
    (read : (data headers).evaluateType context raw = some value) :
    value = QType.mk annotation := by
  rcases (⟨Scope.ofSemantic context, Scope.ofSemantic_semantic context⟩ :
    ∃ scope : Scope D n, scope.semantic = context) with ⟨scope, rfl⟩
  rcases raw_type_readout headers raw scope value read with ⟨supplied, suppliedCode, classRead⟩
  have annotations : supplied = annotation := TypeOver.ext
    (suppliedCode.trans (eq_of_heq codeRead).symm)
  exact classRead.symm.trans (congrArg QType.mk annotations)


set_option backward.isDefEq.respectTransparency false in
theorem predicate_evaluation_class (headers : HeaderFormation D) {n : Nat}
    (context : Abstract.ModelScope (C D) (generatedModel D) n)
    (raw : PropExpr S n) (annotation : PredicateOver context.1.as)
    (codeRead : HEq annotation.code raw) (value : QPredicate context.1.as)
    (read : (data headers).evaluatePredicate context raw = some value) :
    value = QPredicate.mk annotation := by
  rcases (⟨Scope.ofSemantic context, Scope.ofSemantic_semantic context⟩ :
    ∃ scope : Scope D n, scope.semantic = context) with ⟨scope, rfl⟩
  rcases raw_predicate_readout headers raw scope value read with ⟨supplied, suppliedCode, classRead⟩
  have annotations : supplied = annotation := PredicateOver.ext
    (suppliedCode.trans (eq_of_heq codeRead).symm)
  exact classRead.symm.trans (congrArg QPredicate.mk annotations)

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.SyntacticReification
