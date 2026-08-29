import Mathlib.Data.List.Nodup
import Mettapedia.OSLF.Framework.DisplayedRewriteSiteEnumeration
import Mettapedia.OSLF.Framework.SelectedModalNaming

/-!
# Selected-site unary modal-signature skeleton

This module is a calibration skeleton: it materializes one unary modal
type-former declaration for every selected rewrite occurrence.  It is exact
for root or otherwise dependency-free occurrences.  It is not the contextual
OSLF signature, because a nonempty displayed context requires one rely
argument per external dependency plus a dependent result family.

The ordinary validated `LanguageDef` output remains useful as a negative
control for the contextual generator and as a minimal compilation fixture.
No consumer should infer contextual completeness from this skeleton.

Generated names use stable occurrence slots.  Slot `i` belongs to selected
occurrence `i`.  Consequently extending a request by appending sites leaves
every prior declaration and name in place.  Per-carrier sort formers such as
`*^T` and `□^T` are a distinct generated family and are not conflated with
these contextual modalities.
-/

namespace Mettapedia.OSLF.Framework

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef

namespace SelectedUnaryModalSignature

open SelectedModalNaming

/-- The carrier of generated modal formulas. -/
def formulaSortName : String := "$oslf:formula"

/-- One deliberately unary modal type-former declaration. -/
def modalRule (slot : Nat) : GrammarRule where
  label := SelectedModalNaming.label slot
  category := formulaSortName
  params := [.simple "body" (.base formulaSortName)]
  syntaxPattern := []

theorem modalRule_injective : Function.Injective modalRule := by
  intro first second equality
  apply SelectedModalNaming.label_injective
  exact congrArg GrammarRule.label equality

/-- Generate consecutive stable modal slots. -/
def modalTermsFrom (first count : Nat) : List GrammarRule :=
  (List.range' first count).map modalRule

/-- A nonempty generated interval exposes its first stable modal slot and
continues from the successor slot. -/
@[simp] theorem modalTermsFrom_succ (first count : Nat) :
    modalTermsFrom first (count + 1) =
      modalRule first :: modalTermsFrom (first + 1) count := by
  simp [modalTermsFrom, List.range'_succ]

/-- Exactly one unary modal declaration per selected occurrence. -/
def modalTermsForSiteCount (siteCount : Nat) : List GrammarRule :=
  modalTermsFrom 0 siteCount

/-- Modal declarations requested by one occurrence-sensitive language. -/
def modalTerms (request : DisplayedOccurrenceLanguage) : List GrammarRule :=
  modalTermsForSiteCount request.selectedSites.length

@[simp]
theorem length_modalTermsFrom (first count : Nat) :
    (modalTermsFrom first count).length = count := by
  simp [modalTermsFrom]

@[simp]
theorem length_modalTermsForSiteCount (siteCount : Nat) :
    (modalTermsForSiteCount siteCount).length = siteCount := by
  simp [modalTermsForSiteCount]

@[simp]
theorem length_modalTerms (request : DisplayedOccurrenceLanguage) :
    (modalTerms request).length = request.selectedSites.length := by
  simp [modalTerms]

/-- Incremental generation is an exact append: extending a request never
renumbers or regenerates its existing declarations. -/
theorem modalTermsForSiteCount_add (base delta : Nat) :
    modalTermsForSiteCount (base + delta) =
      modalTermsForSiteCount base ++ modalTermsFrom base delta := by
  unfold modalTermsForSiteCount modalTermsFrom
  rw [← List.map_append]
  congr 1
  simpa using
    (List.range'_append (s := 0) (m := base) (n := delta)
      (step := 1)).symm

theorem modalTermLabels (siteCount : Nat) :
    (modalTermsForSiteCount siteCount).map (fun rule => rule.label) =
      (List.range' 0 siteCount).map SelectedModalNaming.label := by
  simp [modalTermsForSiteCount, modalTermsFrom, modalRule, List.map_map]

theorem modalTermLabelsFrom (first count : Nat) :
    (modalTermsFrom first count).map (fun rule => rule.label) =
      (List.range' first count).map SelectedModalNaming.label := by
  simp [modalTermsFrom, modalRule, List.map_map]

theorem modalTermLabelsFrom_nodup (first count : Nat) :
    ((modalTermsFrom first count).map (fun rule => rule.label)).Nodup := by
  rw [modalTermLabelsFrom]
  exact (List.nodup_range' 1).map SelectedModalNaming.label_injective

theorem modalTermLabels_nodup (siteCount : Nat) :
    ((modalTermsForSiteCount siteCount).map (fun rule => rule.label)).Nodup := by
  exact modalTermLabelsFrom_nodup 0 siteCount

/-- The selected unary skeleton as an ordinary five-field language
definition. -/
def language (request : DisplayedOccurrenceLanguage) : LanguageDef :=
  { name := "$oslf:selected-modal:" ++ request.definition.language.name
    types := [TypeDecl.plain formulaSortName]
    terms := modalTerms request
    equations := []
    rewrites := [] }

theorem language_validate (request : DisplayedOccurrenceLanguage) :
    (language request).validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly
  · rfl
  · rfl
  · simp [language, formulaSortName, LanguageDef.typeNames, TypeDecl.plain]
  · simpa [language, modalTerms] using
      modalTermLabels_nodup request.selectedSites.length
  · intro term termMembership
    simp only [language] at termMembership
    unfold modalTerms modalTermsForSiteCount modalTermsFrom at termMembership
    rw [List.mem_map] at termMembership
    obtain ⟨slot, _, rfl⟩ := termMembership
    change formulaSortName ∈ [formulaSortName]
    simp
  · intro term termMembership parameter parameterMembership typeName
      typeNameMembership
    simp only [language] at termMembership
    unfold modalTerms modalTermsForSiteCount modalTermsFrom at termMembership
    rw [List.mem_map] at termMembership
    obtain ⟨slot, _, rfl⟩ := termMembership
    have parameterEquality :
        parameter = TermParam.simple "body" (.base formulaSortName) := by
      simpa [modalRule] using parameterMembership
    subst parameter
    change typeName ∈ [formulaSortName]
    simpa [TermParam.typeExpr, TypeExpr.baseNames] using typeNameMembership
  · intro term termMembership
    simp only [language] at termMembership
    unfold modalTerms modalTermsForSiteCount modalTermsFrom at termMembership
    rw [List.mem_map] at termMembership
    obtain ⟨slot, _, rfl⟩ := termMembership
    exact Or.inl rfl

/-- Validated selected modal signature. -/
def validatedLanguage (request : DisplayedOccurrenceLanguage) :
    ValidatedLanguageDef :=
  ⟨language request, language_validate request⟩

/-- Full paper-style site selection, passed through the same sparse generator.
This is the reference specialization rather than a separate implementation. -/
def completeRequest (source : ValidatedLanguageDef) :
    DisplayedOccurrenceLanguage :=
  .atSelection source (DisplayedSiteSelection.complete source.language)

/-- Full selected-modal signature.  Later adequacy theorems may compare a
target-specific sparse request to this reference object. -/
def completeValidatedLanguage (source : ValidatedLanguageDef) :
    ValidatedLanguageDef :=
  validatedLanguage (completeRequest source)

/-! ## Positive and negative controls -/

namespace Canary

@[simp]
theorem empty_request_has_no_modal_terms (source : ValidatedLanguageDef) :
    (language (.atSelection source [])).terms = [] := by
  rfl

@[simp]
theorem singleton_request_has_one_modal_term
    (source : ValidatedLanguageDef)
    (site : DisplayedRewriteSite source.language) :
    (language (.atSelection source [site])).terms.length = 1 := by
  simp [language, modalTerms, DisplayedOccurrenceLanguage.atSelection]

/-- Sparse demand is observable in the generated artifact: one selected
occurrence cannot masquerade as two merely because their focused terms agree. -/
theorem one_site_signature_ne_two_site_signature
    (source : ValidatedLanguageDef)
    (first second : DisplayedRewriteSite source.language) :
    language (.atSelection source [first]) ≠
      language (.atSelection source [first, second]) := by
  intro equality
  have termLengths := congrArg (fun definition => definition.terms.length) equality
  simp [language, modalTerms, DisplayedOccurrenceLanguage.atSelection]
    at termLengths

end Canary

#print axioms modalTermsForSiteCount_add
#print axioms modalTermLabels_nodup
#print axioms language_validate
#print axioms Canary.one_site_signature_ne_two_site_signature

end SelectedUnaryModalSignature

end Mettapedia.OSLF.Framework
