import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalSyntacticRealization
import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalContextualInterpretation

/-!
# The qualified generated source model

Formed ordered primitive declarations earn the local model qualifier. On the
chosen telescope image, actual source evaluation recovers each supplied family,
complete term class and admitted ordered substitution. Raw context objects are
still retained; contextual comparison and classifying uniqueness are separate
from these source readbacks.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External.Contextual.SyntacticModel

open _root_.CategoryTheory
open Mettapedia.TypeTheory.ContextualModelTelescopes
open SyntacticReification

universe u
variable {S : Symbols.{u}} {D : Signature S}

noncomputable def qualified (headers : HeaderFormation D) : Interpretation.QualifiedModel D (C D) where
  data := data headers
  realization := realization headers
  products_substitution := products_substitution headers
  products_beta := products_beta headers
  products_eta := products_eta headers

theorem context_recovery (headers : HeaderFormation D) (context : Context D) :
    Interpretation.contextValue (qualified headers) context = parameterContext context :=
  context_evaluation_normalized headers context.raw context.formed _
    (Interpretation.context_readout (qualified headers) context)

theorem scope_context_read (headers : HeaderFormation D) {n : Nat} (scope : Scope D n) :
    (data headers).evaluateContext scope.raw = some scope.semantic := by
  have read := Interpretation.context_readout (qualified headers) scope.source
  have fixed : parameterContext scope.source = scope.semantic :=
    eq_of_heq (parameterContext_telescope scope.semantic)
  exact read.trans (congrArg some ((context_recovery headers scope.source).trans fixed))

theorem scope_type_read (headers : HeaderFormation D) {n : Nat} (scope : Scope D n)
    (annotation : TypeOver scope.source) :
    (data headers).evaluateType scope.semantic annotation.code = some (QType.mk annotation) := by
  rcases ((Classical.choice annotation.formed).sound (data headers) (realization headers)
    (products_substitution headers) (products_beta headers) (products_eta headers)).typeAt
      scope.semantic (scope_context_read headers scope) with ⟨value, read⟩
  exact read.trans (congrArg some (type_evaluation_class headers scope.semantic
    annotation.code annotation HEq.rfl value read))

set_option backward.isDefEq.respectTransparency false in
theorem scope_term_read (headers : HeaderFormation D) {n : Nat} (scope : Scope D n)
    {annotation : TypeOver scope.source} (term : Term scope.source annotation) :
    (data headers).evaluateTerm scope.semantic term.code =
      some (⟨QType.mk annotation, ⟨QTerm.mk term, rfl⟩⟩ :
        Value (QuotientCwf.cwf D) ((quotientProjection D).obj scope.source)) := by
  rcases ((Classical.choice term.typed).sound (data headers) (realization headers)
    (products_substitution headers) (products_beta headers) (products_eta headers)).termAt
      scope.semantic (QType.mk annotation) (scope_context_read headers scope)
      (scope_type_read headers scope annotation) with ⟨value, read⟩
  have generated := raw_term_readout headers term.code scope ⟨QType.mk annotation, value⟩ read
  rcases retype generated annotation rfl with ⟨supplied, codeRead, classRead⟩
  have same : supplied = term := Term.ext codeRead
  rw [same] at classRead
  exact read.trans (congrArg some (value_ext classRead.symm))

set_option backward.isDefEq.respectTransparency false in
theorem scope_substitution_read (headers : HeaderFormation D) {n k : Nat}
    (source : Scope D n) (target : Scope D k) (morphism : source.source ⟶ target.source) :
    (data headers).evaluateSubstitution source.semantic target.semantic morphism.substitution =
      some ((quotientProjection D).map morphism) := by
  rcases ((Classical.choice morphism.admitted).sound (data headers) (realization headers)
    (products_substitution headers) (products_beta headers) (products_eta headers)).substitutionAt
      source.semantic target.semantic (scope_context_read headers source)
      (scope_context_read headers target) with ⟨arrow, read⟩
  rcases assemble_readout target.telescope source.source morphism.substitution
    (fun index => (data headers).evaluateTerm source.semantic (morphism.substitution index))
    (fun index value valueRead => raw_term_readout headers (morphism.substitution index) source value valueRead)
    arrow read with ⟨supplied, projected, components⟩
  have same : supplied = morphism := Hom.ext (funext components)
  rw [same] at projected
  exact read.trans (congrArg some projected.symm)

end Mettapedia.TypeTheory.Calculi.NativeDependent.External.Contextual.SyntacticModel
