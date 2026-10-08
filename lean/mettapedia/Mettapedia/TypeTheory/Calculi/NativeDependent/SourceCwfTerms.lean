import Mettapedia.TypeTheory.Calculi.NativeDependent.SourceCwfInterpretation

/-!
# Typed source terms and complete native conservativity

The generated primitive source term has an independently checked typing
tree. Its parser returns the entire source section. Comprehension recovers
every native section uniquely as a source term, and equality of parser
results reflects equality of source terms.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.SourceCwfDeclarations

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open ContextualModelTelescopes NativeLocalTypeFormers

universe u w w'
variable {K : Cwf.{u, u, w, w'}}

noncomputable section

def sourceTerm {context : K.Ctx} {type : K.Ty context} (term : K.Tm context type) :
    TermExpr (symbols K) 1 := .primitive (.source term) TermExpr.var

def sourceTermFormed {context : K.Ctx} {type : K.Ty context} (term : K.Tm context type) :
    Derivation (signature K) (.term (objectContext (⟨context⟩ : Base K))
      (sourceTerm term) (sourceType type (.var 0))) := by
  have tree := deriveList (.primitive (objectContext (⟨context⟩ : Base K)) (.source term) TermExpr.var)
    (.cons (objectContextFormed _) (.cons (objectContextFormed _)
      (.cons (sourceTypeFormed type)
        (.cons (deriveList (.substitutionIdentity (objectContext (⟨context⟩ : Base K)))
          (.cons (objectContextFormed _) .nil)) .nil))))
  change Derivation (signature K) (.term (objectContext (⟨context⟩ : Base K)) (sourceTerm term)
    ((sourceType type (.var 0)).substitute TermExpr.var)) at tree
  rw [TypeExpr.substitute_identity] at tree
  exact tree

set_option backward.isDefEq.respectTransparency false in
theorem source_term_read {context : K.Ctx} {type : K.Ty context} (term : K.Tm context type) :
    (model K).evaluateTerm (objectScope (⟨context⟩ : Base K)) (sourceTerm term) =
      some ⟨sourceMeaning type, sourceValue term⟩ := by
  have read := (model K).evaluate_primitive (objectScope (⟨context⟩ : Base K)) (.source term)
    TermExpr.var (𝟙 (objectScope (⟨context⟩ : Base K)).1) (by
      intro position
      cases position using Fin.cases with
      | zero => exact variable_identity _
      | succ impossible => exact Fin.elim0 impossible)
  change (model K).evaluateTerm (objectScope (⟨context⟩ : Base K)) (sourceTerm term) =
    some (Value.substitute (K := (NativeModel (Base K)).toCwf)
      (⟨sourceMeaning type, sourceValue term⟩ : NativeValue (objectScope (⟨context⟩ : Base K)).1)
      (𝟙 (objectScope (⟨context⟩ : Base K)).1)) at read
  exact read.trans (congrArg some (Value.substitute_identity
    (K := (NativeModel (Base K)).toCwf) ⟨sourceMeaning type, sourceValue term⟩))

theorem generated_sound {judgment : Judgment (symbols K)}
    (derivation : Derivation (signature K) judgment) : Interprets (model K) judgment :=
  derivation.sound (model K) (realization K)
    (NativeLocalTypeOperations.products_substitution (Base K))
    (NativeLocalTypeOperations.products_beta (Base K)) (NativeLocalPiEta.products_eta (Base K))

theorem generated_source_term_interpreted {context : K.Ctx} {type : K.Ty context}
    (term : K.Tm context type) : Interprets (model K)
      (.term (objectContext (⟨context⟩ : Base K)) (sourceTerm term) (sourceType type (.var 0))) :=
  generated_sound (sourceTermFormed term)

def recoverSourceTerm {context : K.Ctx} {type : K.Ty context}
    (sectionValue : (sourceMeaning type).decoded.sections) : K.Tm context type :=
  (sourceTermEquiv type).symm sectionValue

theorem recover_sourceValue {context : K.Ctx} {type : K.Ty context} (term : K.Tm context type) :
    recoverSourceTerm (sourceValue term) = term := (sourceTermEquiv type).symm_apply_apply term

theorem sourceValue_recover {context : K.Ctx} {type : K.Ty context}
    (sectionValue : (sourceMeaning type).decoded.sections) :
    sourceValue (recoverSourceTerm sectionValue) = sectionValue :=
  (sourceTermEquiv type).apply_symm_apply sectionValue

/-- Every complete native term of this original type has one source origin. -/
theorem complete_section_unique_origin {context : K.Ctx} {type : K.Ty context}
    (sectionValue : (sourceMeaning type).decoded.sections) :
    ∃! term : K.Tm context type, sourceValue term = sectionValue := by
  refine ⟨recoverSourceTerm sectionValue, sourceValue_recover sectionValue, ?_⟩
  intro term reading
  exact sourceValue_injective (reading.trans (sourceValue_recover sectionValue).symm)

theorem parser_conservative {context : K.Ctx} {type : K.Ty context}
    (first second : K.Tm context type) :
    (model K).evaluateTerm (objectScope (⟨context⟩ : Base K)) (sourceTerm first) =
      (model K).evaluateTerm (objectScope (⟨context⟩ : Base K)) (sourceTerm second) ↔ first = second := by
  constructor
  · intro equal
    rw [source_term_read, source_term_read] at equal
    have sections := congrArg
      (fun parsed : Option (NativeValue (objectScope (⟨context⟩ : Base K)).1) =>
        ModelData.check? parsed (sourceMeaning type)) equal
    rw [ModelData.check?_supplied, ModelData.check?_supplied] at sections
    exact sourceValue_injective (Option.some.inj sections)
  · intro equal
    cases equal
    rfl

end

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.SourceCwfDeclarations
