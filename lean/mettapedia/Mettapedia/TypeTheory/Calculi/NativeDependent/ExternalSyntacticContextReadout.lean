import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalSyntacticReadoutFold
import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalChosenContextFixedPoint
import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalContextualPresentationEquality

/-!
# Source context readbacks

Successful evaluation reconstructs a generated context equation between the
actual chosen telescope and the authored context. Selection fixes the supplied
native telescope, so the resulting semantic context is exactly the chosen
presentation of the authored context. This uses the complete local constructor
readouts; no header realization or whole-source inverse is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External.Contextual.SyntacticReification

open _root_.CategoryTheory
open Mettapedia.TypeTheory.ContextualModelTelescopes
open SyntacticModel SyntacticTelescopes

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
      rw [ModelData.evaluateContext] at evaluated
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

theorem parameterContext_telescope {n : Nat}
    (context : Mettapedia.TypeTheory.ContextualModelTelescopes.Context (C D) n) :
    HEq (parameterContext context.1.as) context := by
  rcases context with ⟨⟨⟨arity, raw, formed⟩⟩, telescope⟩
  have counts : arity = n := telescope_arity telescope
  cases counts
  have fixed := Presentation.selectedContext_telescope_fixed telescope
  apply heq_of_eq
  apply semantic_context_ext
  exact congrArg (quotientProjection D).obj fixed

set_option backward.isDefEq.respectTransparency false in
theorem context_evaluation_normalized (headers : HeaderFormation D) {n : Nat}
    (raw : ContextExpr S n) (formed : Formed D raw)
    (context : Mettapedia.TypeTheory.ContextualModelTelescopes.Context (C D) n)
    (read : (data headers).evaluateContext raw = some context) :
    context = parameterContext ⟨n, raw, formed⟩ := by
  let scope := Scope.ofSemantic context
  have scopeRead : (data headers).evaluateContext raw = some scope.semantic := by
    rw [Scope.ofSemantic_semantic]
    exact read
  have same := raw_context_readout headers raw scope scopeRead
  have selected := PresentationEquality.selected_parameter_context same scope.formed formed
  have fixed : parameterContext scope.source = scope.semantic :=
    eq_of_heq (parameterContext_telescope scope.semantic)
  change parameterContext scope.source = parameterContext ⟨n, raw, formed⟩ at selected
  exact (Scope.ofSemantic_semantic context).symm.trans (fixed.symm.trans selected)

set_option backward.isDefEq.respectTransparency false in
theorem type_evaluation_class (headers : HeaderFormation D) {n : Nat}
    (context : Mettapedia.TypeTheory.ContextualModelTelescopes.Context (C D) n)
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

end Mettapedia.TypeTheory.Calculi.NativeDependent.External.Contextual.SyntacticReification
