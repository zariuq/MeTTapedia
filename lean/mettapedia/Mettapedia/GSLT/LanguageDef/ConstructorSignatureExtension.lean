import Mettapedia.GSLT.LanguageDef.CalculusLanguageExtension

/-!
# Constructor-signature extensions

This is the compositional validation law for an append-only extension that
adds fresh carrier sorts and fresh constructor rows to an inert language.
Validation of the already admitted prefix is transported monotonically along
the enlarged sort namespace; only the new finite delta is checked afresh.

The theorem is deliberately generic.  Large generated signatures should not
be flattened and re-evaluated whenever a small semantic carrier is appended.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax

namespace ConstructorSignatureExtension

def ofLists (types : List TypeDecl) (terms : List GrammarRule)
    (rename : Option String := none) :
    CalculusLanguageExtension :=
  { newTypes := types, newTerms := terms, rename := rename }

private theorem validateTerm_mono
    (source target : LanguageDef) (term : GrammarRule)
    (clean : source.validateTerm term = [])
    (typesMonotone : ∀ name ∈ source.typeNames, name ∈ target.typeNames) :
    target.validateTerm term = [] := by
  simp only [LanguageDef.validateTerm, List.append_eq_nil_iff] at clean ⊢
  refine ⟨⟨?_, ?_⟩, clean.2⟩
  · have sourceCategory : term.category ∈ source.typeNames := by
      by_contra missing
      simp [missing] at clean
    simp [typesMonotone term.category sourceCategory]
  · rw [List.flatMap_eq_nil_iff]
    intro parameter parameterMembership
    apply LanguageDef.validateTypeExpr_eq_nil_of_baseNames
    intro name nameMembership
    apply typesMonotone name
    have sourceParameterClean :=
      (List.flatMap_eq_nil_iff.mp clean.1.2) parameter parameterMembership
    exact LanguageDef.baseName_mem_of_validateTypeExpr_eq_nil
      source.typeNames s!"term {term.label}"
      (TermParam.typeExpr parameter) sourceParameterClean nameMembership

/-- Fresh sorts and constructors preserve validation without re-evaluating
the full accepted prefix.  Equations and rewrites are excluded because their
stability under signature growth requires separate operational hypotheses. -/
theorem apply_language_validate
    (base : CalculusLanguageDef)
    (types : List TypeDecl) (terms : List GrammarRule)
    (rename : Option String)
    (baseValid : base.toLanguageDef.validate = [])
    (baseEquations : base.equations = [])
    (baseRewrites : base.rewrites = [])
    (typeNamesNodup : (types.map (·.name)).Nodup)
    (typeNamesDisjoint :
      List.Disjoint base.toLanguageDef.typeNames (types.map (·.name)))
    (termLabelsNodup : (terms.map (·.label)).Nodup)
    (termLabelsDisjoint :
      List.Disjoint (base.terms.map (·.label)) (terms.map (·.label)))
    (termsValid : ∀ term ∈ terms,
      ((ofLists types terms rename).apply base).toLanguageDef.validateTerm term = []) :
    ((ofLists types terms rename).apply base).toLanguageDef.validate = [] := by
  let target := (ofLists types terms rename).apply base
  have targetTypeNames :
      target.toLanguageDef.typeNames =
        base.toLanguageDef.typeNames ++ types.map (·.name) := by
    simp [target, ofLists, LanguageDef.typeNames]
  apply LanguageDef.validate_eq_nil_of_rows
  · rw [targetTypeNames]
    exact List.Nodup.append
      (LanguageDef.typeNames_nodup_of_validate_eq_nil
        base.toLanguageDef baseValid)
      typeNamesNodup typeNamesDisjoint
  · change ((base.terms ++ terms).map (·.label)).Nodup
    rw [List.map_append]
    exact List.Nodup.append
      (LanguageDef.constructorLabels_nodup_of_validate_eq_nil
        base.toLanguageDef baseValid)
      termLabelsNodup termLabelsDisjoint
  · simp [ofLists, baseEquations]
  · simp [ofLists, baseRewrites]
  · intro term membership
    change term ∈ base.terms ++ terms at membership
    rcases List.mem_append.mp membership with
        baseMembership | addedMembership
    · apply validateTerm_mono base.toLanguageDef target.toLanguageDef term
      · exact LanguageDef.validateTerm_eq_nil_of_validate_eq_nil
          base.toLanguageDef baseValid term baseMembership
      · intro name nameMembership
        rw [targetTypeNames]
        exact List.mem_append_left _ nameMembership
    · exact termsValid term addedMembership
  · intro equation membership
    simp [ofLists, baseEquations] at membership
  · intro rewrite membership
    simp [ofLists, baseRewrites] at membership

/-! ## Positive and negative controls -/

namespace Canary

private def oldType : TypeDecl := TypeDecl.plain "signature-extension:old"
private def newType : TypeDecl := TypeDecl.plain "signature-extension:new"

private def oldTerm : GrammarRule where
  label := "signature-extension:old-term"
  category := oldType.name
  params := []
  syntaxPattern := []

private def newTerm : GrammarRule where
  label := "signature-extension:new-term"
  category := newType.name
  params := []
  syntaxPattern := []

private def base : CalculusLanguageDef where
  name := "signature-extension"
  types := [oldType]
  terms := [oldTerm]
  equations := []
  rewrites := []

private theorem base_valid : base.toLanguageDef.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
    simp [base, oldType, oldTerm, TypeDecl.plain, LanguageDef.typeNames]

theorem fresh_signature_valid :
    ((ofLists [newType] [newTerm] none).apply base).toLanguageDef.validate = [] := by
  apply apply_language_validate base [newType] [newTerm] none base_valid <;>
    simp [base, oldType, newType, oldTerm, newTerm, ofLists,
      LanguageDef.validateTerm, LanguageDef.typeNames, TypeDecl.plain]

private def duplicateType : TypeDecl :=
  TypeDecl.plain "signature-extension:old"

theorem duplicate_sort_invalid :
    ((ofLists [duplicateType] [] none).apply base).toLanguageDef.validate ≠ [] := by
  intro valid
  have nodup := LanguageDef.typeNames_nodup_of_validate_eq_nil
    ((ofLists [duplicateType] [] none).apply base).toLanguageDef valid
  simp [ofLists, base, oldType, duplicateType, TypeDecl.plain,
    LanguageDef.typeNames] at nodup

end Canary

#print axioms apply_language_validate
#print axioms Canary.fresh_signature_valid
#print axioms Canary.duplicate_sort_invalid

end ConstructorSignatureExtension

end Mettapedia.GSLT.LanguageDef
