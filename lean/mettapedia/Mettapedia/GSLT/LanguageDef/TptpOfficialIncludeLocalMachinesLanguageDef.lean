import Mettapedia.GSLT.LanguageDef.TptpOfficialIncludeDirectiveLanguageDef
import Mettapedia.GSLT.LanguageDef.TptpOfficialIncludeSelectionLanguageDef
import Mettapedia.GSLT.LanguageDef.TptpOfficialIncludeEnvironmentLookupLanguageDef
import Mettapedia.GSLT.LanguageDef.TptpOfficialIncludeInputClassificationLanguageDef
import Mettapedia.GSLT.LanguageDef.RewriteValidationCertificateExtension

/-!
# One LanguageDef for the local TPTP include machines

Recursive include resolution needs four independently qualified operations in
one contextual rewrite system:

* decode one official include directive;
* classify one official input from any TPTP formula family;
* look up documents and parent-relative include bindings;
* apply a formula selection after recursive expansion.

This module assembles exactly those declarations and rules over the shared
include-resolution result carrier.  It adds no recursive controller and no
file-system operation.  The component namespaces remain visible in rule names,
so generated runtimes can retain exact rule provenance.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpOfficialIncludeLocalMachinesLanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.RewriteValidationCertificate

namespace Directive

abbrev language :=
  TptpOfficialIncludeDirectiveLanguageDef.language
abbrev addedTypes :=
  TptpOfficialIncludeDirectiveLanguageDef.addedTypes
abbrev addedTerms :=
  TptpOfficialIncludeDirectiveLanguageDef.addedTerms
abbrev rewrites :=
  TptpOfficialIncludeDirectiveLanguageDef.rewrites

end Directive

namespace Selection

abbrev language :=
  TptpOfficialIncludeSelectionLanguageDef.language
abbrev supportTypes :=
  TptpOfficialIncludeSelectionLanguageDef.supportTypes
abbrev supportTerms :=
  TptpOfficialIncludeSelectionLanguageDef.supportTerms
abbrev rewrites :=
  TptpOfficialIncludeSelectionLanguageDef.rewrites

end Selection

namespace Lookup

abbrev language :=
  TptpOfficialIncludeEnvironmentLookupLanguageDef.language
abbrev supportTypes :=
  TptpOfficialIncludeEnvironmentLookupLanguageDef.supportTypes
abbrev supportTerms :=
  TptpOfficialIncludeEnvironmentLookupLanguageDef.supportTerms
abbrev rewrites :=
  TptpOfficialIncludeEnvironmentLookupLanguageDef.rewrites

end Lookup

namespace Classification

abbrev language :=
  TptpOfficialIncludeInputClassificationLanguageDef.language
abbrev supportTypes :=
  TptpOfficialIncludeInputClassificationLanguageDef.supportTypes
abbrev supportTerms :=
  TptpOfficialIncludeInputClassificationLanguageDef.supportTerms
abbrev rewrites :=
  TptpOfficialIncludeInputClassificationLanguageDef.rewrites

end Classification

namespace Equality

abbrev types := PatternEqualityDecision.language.types
abbrev terms := PatternEqualityDecision.language.terms
abbrev relationEnv := PatternEqualityDecision.relationEnv

end Equality

def addedTypes : List TypeDecl :=
  Directive.addedTypes ++ Equality.types ++ Selection.supportTypes ++
    Lookup.supportTypes ++ Classification.supportTypes

def addedTerms : List GrammarRule :=
  Directive.addedTerms ++ Equality.terms ++ Selection.supportTerms ++
    Lookup.supportTerms ++ Classification.supportTerms

def rewrites : List RewriteRule :=
  Directive.rewrites ++ Selection.rewrites ++ Lookup.rewrites ++
    Classification.rewrites

private def signatureBase : CalculusLanguageDef :=
  CalculusLanguageDef.extend
    TptpOfficialIncludeResolutionResultCarrier.language {}

private def signatureExtension : CalculusLanguageExtension :=
  ConstructorSignatureExtension.ofLists addedTypes addedTerms
    (some "TptpOfficialIncludeLocalMachinesV1")

private def signatureCalculusLanguage : CalculusLanguageDef :=
  signatureExtension.apply signatureBase

def signatureLanguage : LanguageDef :=
  signatureCalculusLanguage.toLanguageDef

def language : LanguageDef := {
  name := "TptpOfficialIncludeLocalMachinesV1"
  types := signatureLanguage.types
  terms := signatureLanguage.terms
  equations := []
  rewrites
}

@[simp] theorem language_rewrites : language.rewrites = rewrites := rfl

@[simp] theorem typeNames_exact :
    language.typeNames =
      TptpOfficialIncludeResolutionResultCarrier.language.typeNames ++
        addedTypes.map (·.name) := by
  simp [language, signatureLanguage, signatureCalculusLanguage,
    signatureExtension, signatureBase, ConstructorSignatureExtension.ofLists,
    LanguageDef.typeNames]

@[simp] theorem constructorSignatures_exact :
    RewriteValidationCertificate.constructorSignatures language =
      RewriteValidationCertificate.constructorSignatures
        TptpOfficialIncludeResolutionResultCarrier.language ++
      addedTerms.map fun declaration =>
        (declaration.label, declaration.params.length) := by
  simp [RewriteValidationCertificate.constructorSignatures, language,
    signatureLanguage, signatureCalculusLanguage, signatureExtension,
    signatureBase, ConstructorSignatureExtension.ofLists]

@[simp] theorem constructorLabels_exact :
    RewriteValidationCertificate.constructorLabels language =
      RewriteValidationCertificate.constructorLabels
        TptpOfficialIncludeResolutionResultCarrier.language ++
      addedTerms.map (·.label) := by
  simp [RewriteValidationCertificate.constructorLabels, language,
    signatureLanguage, signatureCalculusLanguage, signatureExtension,
    signatureBase, ConstructorSignatureExtension.ofLists]

private theorem added_type_names_nodup :
    (addedTypes.map (·.name)).Nodup := by
  decide +kernel

private def addedTypeNamespace (name : String) : Bool :=
  name.startsWith "TptpInclude:" ||
    name.startsWith "PatternEqualityDecision:" ||
    name.startsWith "TptpIncludeSelection:" ||
    name.startsWith "TptpIncludeLookup:" ||
    name.startsWith "TptpIncludeInput:"

private theorem added_type_names_disjoint :
    List.Disjoint signatureBase.toLanguageDef.typeNames
      (addedTypes.map (·.name)) := by
  have baseSeparate :
      signatureBase.toLanguageDef.typeNames.all
        (fun name => !addedTypeNamespace name) = true := by
    decide +kernel
  have addedNamespaced :
      (addedTypes.map (·.name)).all addedTypeNamespace = true := by
    decide +kernel
  rw [List.disjoint_left]
  intro name baseMembership addedMembership
  have baseNot :=
    (List.all_eq_true.mp baseSeparate) name baseMembership
  have addedYes :=
    (List.all_eq_true.mp addedNamespaced) name addedMembership
  simp [addedYes] at baseNot

private theorem added_term_labels_nodup :
    (addedTerms.map (·.label)).Nodup := by
  decide +kernel

private def addedTermNamespace (label : String) : Bool :=
  label.startsWith "tptp-include:" ||
    label.startsWith "pattern-equality-decision:" ||
    label.startsWith "tptp-include-selection:" ||
    label.startsWith "tptp-include-lookup:" ||
    label.startsWith "tptp-include-input:"

private theorem added_term_labels_disjoint :
    List.Disjoint (signatureBase.toLanguageDef.terms.map (·.label))
      (addedTerms.map (·.label)) := by
  have baseSeparate :
      (signatureBase.toLanguageDef.terms.map (·.label)).all
        (fun label => !addedTermNamespace label) = true := by
    decide +kernel
  have addedNamespaced :
      (addedTerms.map (·.label)).all addedTermNamespace = true := by
    decide +kernel
  rw [List.disjoint_left]
  intro label baseMembership addedMembership
  have baseNot :=
    (List.all_eq_true.mp baseSeparate) label baseMembership
  have addedYes :=
    (List.all_eq_true.mp addedNamespaced) label addedMembership
  simp [addedYes] at baseNot

private theorem added_terms_validate_all :
    addedTerms.all
      (fun term => signatureLanguage.validateTerm term == []) = true := by
  decide +kernel

private theorem added_terms_valid (term : GrammarRule)
    (membership : term ∈ addedTerms) :
    signatureLanguage.validateTerm term = [] := by
  have checked :=
    (List.all_eq_true.mp added_terms_validate_all) term membership
  simpa using checked

theorem signatureLanguage_validate : signatureLanguage.validate = [] := by
  apply ConstructorSignatureExtension.apply_language_validate
    signatureBase addedTypes addedTerms
      (some "TptpOfficialIncludeLocalMachinesV1")
  · simpa [signatureBase] using
      TptpOfficialIncludeResolutionResultCarrier.language_validate
  · rfl
  · rfl
  · exact added_type_names_nodup
  · exact added_type_names_disjoint
  · exact added_term_labels_nodup
  · exact added_term_labels_disjoint
  · exact added_terms_valid

private theorem language_constructor_labels_nodup :
    (language.terms.map (·.label)).Nodup := by
  simpa [language] using
    LanguageDef.constructorLabels_nodup_of_validate_eq_nil
      signatureLanguage signatureLanguage_validate

def constructorLabelReserved (label : String) : Bool :=
  label.startsWith "tptp" ||
    label.startsWith "pattern-equality-decision:"

private theorem constructor_labels_reserved :
    (RewriteValidationCertificate.constructorLabels language).all
      constructorLabelReserved = true := by
  decide +kernel

theorem rewrite_schema_names_unreserved {rewrite : RewriteRule}
    (membership : rewrite ∈ rewrites) :
    (RewriteValidationCertificateExtension.schemaNames rewrite).all
      (fun candidate => !constructorLabelReserved candidate) = true := by
  simp only [rewrites, List.mem_append] at membership
  rcases membership with ((directiveMember | selectionMember) | lookupMember) |
      classificationMember
  · simpa [constructorLabelReserved,
      TptpOfficialIncludeDirectiveLanguageDef.constructorLabelNamespaced]
      using TptpOfficialIncludeDirectiveLanguageDef.rewrite_schema_names_unreserved
        rewrite directiveMember
  · simpa [constructorLabelReserved,
      TptpOfficialIncludeSelectionLanguageDef.constructorLabelReserved]
      using TptpOfficialIncludeSelectionLanguageDef.rewrite_schema_names_unreserved
        rewrite selectionMember
  · simpa [constructorLabelReserved,
      TptpOfficialIncludeEnvironmentLookupLanguageDef.constructorLabelReserved]
      using TptpOfficialIncludeEnvironmentLookupLanguageDef.rewrite_schema_names_unreserved
        rewrite lookupMember
  · simpa [constructorLabelReserved,
      TptpOfficialIncludeInputClassificationLanguageDef.constructorLabelReserved]
      using TptpOfficialIncludeInputClassificationLanguageDef.rewrite_schema_names_unreserved
        rewrite classificationMember

private theorem schema_avoids_target {rewrite : RewriteRule}
    (membership : rewrite ∈ rewrites) :
    ∀ name ∈ RewriteValidationCertificateExtension.schemaNames rewrite,
      name ∉ RewriteValidationCertificate.constructorLabels language := by
  intro name schemaMembership constructorMembership
  have allPlain :
      (RewriteValidationCertificateExtension.schemaNames rewrite).all
        (fun candidate => !constructorLabelReserved candidate) = true := by
    exact rewrite_schema_names_unreserved membership
  have plainChecked :=
    (List.all_eq_true.mp allPlain) name schemaMembership
  have reservedChecked :=
    (List.all_eq_true.mp constructor_labels_reserved) name
      constructorMembership
  have notReserved : constructorLabelReserved name = false := by
    simpa using plainChecked
  simp [notReserved] at reservedChecked

private theorem directive_type_names_subset :
    ∀ name ∈ Directive.language.typeNames, name ∈ language.typeNames := by
  intro name membership
  simp only [TptpOfficialIncludeDirectiveLanguageDef.typeNames_exact,
    typeNames_exact,
    TptpOfficialIncludeResolutionResultCarrier.typeNames_exact,
    TptpOfficialIncludeResolutionCarrier.typeNames_exact,
    addedTypes, List.map_append, List.mem_append] at membership ⊢
  aesop

private theorem selection_type_names_subset :
    ∀ name ∈ Selection.language.typeNames, name ∈ language.typeNames := by
  intro name membership
  simp only [TptpOfficialIncludeSelectionLanguageDef.typeNames_exact,
    typeNames_exact, addedTypes, List.map_append, List.mem_append] at membership ⊢
  aesop

private theorem lookup_type_names_subset :
    ∀ name ∈ Lookup.language.typeNames, name ∈ language.typeNames := by
  intro name membership
  simp only [TptpOfficialIncludeEnvironmentLookupLanguageDef.typeNames_exact,
    typeNames_exact, addedTypes, List.map_append, List.mem_append] at membership ⊢
  aesop

private theorem classification_type_names_subset :
    ∀ name ∈ Classification.language.typeNames, name ∈ language.typeNames := by
  intro name membership
  simp only [TptpOfficialIncludeInputClassificationLanguageDef.typeNames_exact,
    typeNames_exact, addedTypes, List.map_append, List.mem_append] at membership ⊢
  aesop

private theorem directive_signatures_subset :
    ∀ signature ∈ RewriteValidationCertificate.constructorSignatures
        Directive.language,
      signature ∈ RewriteValidationCertificate.constructorSignatures
        language := by
  intro signature membership
  simp only [TptpOfficialIncludeDirectiveLanguageDef.constructorSignatures_exact,
    constructorSignatures_exact,
    TptpOfficialIncludeResolutionResultCarrier.constructorSignatures_exact,
    TptpOfficialIncludeResolutionCarrier.constructorSignatures_exact,
    addedTerms, List.map_append, List.mem_append] at membership ⊢
  aesop

private theorem selection_signatures_subset :
    ∀ signature ∈ RewriteValidationCertificate.constructorSignatures
        Selection.language,
      signature ∈ RewriteValidationCertificate.constructorSignatures
        language := by
  intro signature membership
  simp only [TptpOfficialIncludeSelectionLanguageDef.constructorSignatures_exact,
    constructorSignatures_exact, addedTerms, List.map_append,
    List.mem_append] at membership ⊢
  aesop

private theorem lookup_signatures_subset :
    ∀ signature ∈ RewriteValidationCertificate.constructorSignatures
        Lookup.language,
      signature ∈ RewriteValidationCertificate.constructorSignatures
        language := by
  intro signature membership
  simp only [TptpOfficialIncludeEnvironmentLookupLanguageDef.constructorSignatures_exact,
    constructorSignatures_exact, addedTerms, List.map_append,
    List.mem_append] at membership ⊢
  aesop

private theorem classification_signatures_subset :
    ∀ signature ∈ RewriteValidationCertificate.constructorSignatures
        Classification.language,
      signature ∈ RewriteValidationCertificate.constructorSignatures
        language := by
  intro signature membership
  simp only [TptpOfficialIncludeInputClassificationLanguageDef.constructorSignatures_exact,
    constructorSignatures_exact, addedTerms, List.map_append,
    List.mem_append] at membership ⊢
  aesop

private theorem source_certificate_embeds
    {source : LanguageDef} {rewrite : RewriteRule}
    (sourceCertificate :
      RewriteValidationCertificate.Certificate source rewrite)
    (typesSubset : ∀ name ∈ source.typeNames, name ∈ language.typeNames)
    (signaturesSubset : ∀ signature ∈
        RewriteValidationCertificate.constructorSignatures source,
      signature ∈ RewriteValidationCertificate.constructorSignatures language)
    (membership : rewrite ∈ rewrites) :
    RewriteValidationCertificate.Certificate language rewrite := by
  apply RewriteValidationCertificateExtension.Certificate.embed
    sourceCertificate
  exact {
    typeNames := typesSubset
    signatures := signaturesSubset
    avoidsSchema := schema_avoids_target membership
  }

theorem rewrite_certificate (rewrite : RewriteRule)
    (membership : rewrite ∈ rewrites) :
    RewriteValidationCertificate.Certificate language rewrite := by
  simp only [rewrites, List.mem_append] at membership
  rcases membership with ((directiveMember | selectionMember) | lookupMember) |
      classificationMember
  · apply source_certificate_embeds
      (TptpOfficialIncludeDirectiveLanguageDef.rewrite_certificate
        rewrite directiveMember)
      directive_type_names_subset directive_signatures_subset
    simp [rewrites, directiveMember]
  · apply source_certificate_embeds
      (TptpOfficialIncludeSelectionLanguageDef.rewrite_certificate
        rewrite selectionMember)
      selection_type_names_subset selection_signatures_subset
    simp [rewrites, selectionMember]
  · apply source_certificate_embeds
      (TptpOfficialIncludeEnvironmentLookupLanguageDef.rewrite_certificate
        rewrite lookupMember)
      lookup_type_names_subset lookup_signatures_subset
    simp [rewrites, lookupMember]
  · apply source_certificate_embeds
      (TptpOfficialIncludeInputClassificationLanguageDef.rewrite_certificate
        rewrite classificationMember)
      classification_type_names_subset classification_signatures_subset
    simp [rewrites, classificationMember]

private theorem rewrites_valid :
    ∀ rewrite ∈ rewrites, language.validateRewrite rewrite = [] := by
  intro rewrite membership
  apply RewriteValidationCertificate.validateRewrite_eq_nil
    language_constructor_labels_nodup
  exact rewrite_certificate rewrite membership

private theorem rewrite_names_nodup :
    (rewrites.map (·.name)).Nodup := by
  decide +kernel

theorem language_validate : language.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_rows
  · exact LanguageDef.typeNames_nodup_of_validate_eq_nil
      signatureLanguage signatureLanguage_validate
  · exact LanguageDef.constructorLabels_nodup_of_validate_eq_nil
      signatureLanguage signatureLanguage_validate
  · simp [language]
  · exact rewrite_names_nodup
  · intro term membership
    exact LanguageDef.validateTerm_eq_nil_of_validate_eq_nil
      signatureLanguage signatureLanguage_validate term membership
  · intro equation membership
    simp [language] at membership
  · exact rewrites_valid

def validated : ValidatedLanguageDef :=
  ⟨language, language_validate⟩

theorem language_supported : CanonicalWire.languageSupported language := by
  decide +kernel

theorem directive_rule_mem {rule : RewriteRule}
    (member : rule ∈ Directive.rewrites) : rule ∈ language.rewrites := by
  simp [language_rewrites, rewrites, member]

theorem selection_rule_mem {rule : RewriteRule}
    (member : rule ∈ Selection.rewrites) : rule ∈ language.rewrites := by
  simp [language_rewrites, rewrites, member]

theorem lookup_rule_mem {rule : RewriteRule}
    (member : rule ∈ Lookup.rewrites) : rule ∈ language.rewrites := by
  simp [language_rewrites, rewrites, member]

theorem classification_rule_mem {rule : RewriteRule}
    (member : rule ∈ Classification.rewrites) : rule ∈ language.rewrites := by
  simp [language_rewrites, rewrites, member]

theorem rewrite_count : rewrites.length = 76 := by
  decide +kernel

#print axioms language_validate
#print axioms language_supported
#print axioms directive_rule_mem
#print axioms selection_rule_mem
#print axioms lookup_rule_mem
#print axioms classification_rule_mem
#print axioms rewrite_certificate
#print axioms rewrite_count

end Mettapedia.GSLT.LanguageDef.TptpOfficialIncludeLocalMachinesLanguageDef
