import Mettapedia.GSLT.LanguageDef.TptpOfficialRoleSemantics
import Mettapedia.GSLT.LanguageDef.TptpFofClausificationBatchGenerationLanguageDef
import Mettapedia.GSLT.LanguageDef.RewriteValidationCertificate
import Mettapedia.GSLT.LanguageDef.RewriteValidationCertificateExtension
import Mettapedia.GSLT.LanguageDef.ConstructorSignatureExtension

/-!
# Official FOF metadata projection into clausification batches

This language combines the complete official semantic carrier with the
source-indexed batch-generation target along their exact builtin `String` and
`Integer` interface.  Its authored rules project only an official FOF
occurrence and formula role into a metadata-free batch request.  Formula
names, annotations, source spans, terms and generated clauses are bound as
opaque typed values and cannot influence the projection.

The projection is not clausification by itself.  Its Skolem and CNF inputs
must come from the independently proved seven-stage pipeline.  This language
only makes the document-level occurrence and polarity boundary operational.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpOfficialFofBatchProjectionLanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.CalculusLanguageExtension
open Mettapedia.GSLT.LanguageDef.RewriteValidationCertificateExtension

def a (label : String) (arguments : List Pattern := []) : Pattern :=
  .apply label arguments

def v (name : String) : Pattern := .fvar name

private def ctor (label category : String)
    (parameters : List (String × String))
    (policy : Option TermEvalPolicy := none) : GrammarRule := {
  label
  category
  params := parameters.map fun parameter =>
    .simple parameter.1 (.base parameter.2)
  syntaxPattern := []
  evalPolicy? := policy
}

def projectionRequest (source skolem cnf : Pattern) : Pattern :=
  a "tptp-fof-batch-project:request" [source, skolem, cnf]

def targetRequest (occurrence polarity skolem cnf : Pattern) : Pattern :=
  TptpFofClausificationBatchGenerationLanguageDef.request
    occurrence polarity skolem cnf

def sourceDigest (digest : Pattern) : Pattern :=
  a "tptp-semantic:source-digest" [digest]

def sourceOccurrence (digest index : Pattern) : Pattern :=
  a "tptp-semantic:occurrence-id" [sourceDigest digest, index]

def batchOccurrence (digest index : Pattern) : Pattern :=
  a "tptp-fof-batch:occurrence" [digest, index]

def tokenLowerWord (lexeme : Pattern) : Pattern :=
  a "tptp92-ast:token:lower-word" [lexeme]

def plainRole (code : String) : Pattern :=
  a "tptp92-ast:formula-role:alt-1" [tokenLowerWord (a code)]

def refinedRole (code : String) (refinement : Pattern) : Pattern :=
  a "tptp92-ast:formula-role:alt-2"
    [tokenLowerWord (a code), refinement]

def sourceFofInput (occurrence role : Pattern) : Pattern :=
  a "tptp-semantic:fof-input" [occurrence,
    a "tptp92-ast:fof-annotated:alt-1"
      [v "name", role, v "formula", v "annotations"],
    v "span"]

structure RolePolicyEntry where
  code : String
  polarity : Bool
  deriving DecidableEq, Repr

def rolePolicy : List RolePolicyEntry := [
  ⟨"axiom", true⟩,
  ⟨"hypothesis", true⟩,
  ⟨"definition", true⟩,
  ⟨"assumption", true⟩,
  ⟨"lemma", true⟩,
  ⟨"theorem", true⟩,
  ⟨"corollary", true⟩,
  ⟨"conjecture", false⟩,
  ⟨"negated_conjecture", true⟩,
  ⟨"plain", true⟩]

def encodePolarity (polarity : Bool) : Pattern :=
  TptpFofClausificationBatchLanguageDef.encodePolarity polarity

@[simp] theorem encodePolarity_true :
    encodePolarity true = a "tptp-fof-batch:positive" := by
  rfl

@[simp] theorem encodePolarity_false :
    encodePolarity false = a "tptp-fof-batch:negative" := by
  rfl

def mkProjectionRule (entry : RolePolicyEntry) (withRefinement : Bool) :
    RewriteRule := {
  name := "tptp-fof-batch-project:" ++ entry.code ++
    (if withRefinement then ":refined" else ":plain")
  typeContext := [
    ("digest", .base "String"),
    ("index", .base "Integer"),
    ("name", .base "Tptp92Ast:name"),
    ("formula", .base "Tptp92Ast:fof-formula"),
    ("annotations", .base "Tptp92Ast:annotations"),
    ("span", .base "Tptp92Ast:source-span"),
    ("refinement", .base "Tptp92Ast:general-term"),
    ("skolem", .base "TptpFofSkolem:Output"),
    ("cnf", .base "TptpFofCnf:Output")]
  premises := []
  left := projectionRequest
    (sourceFofInput (sourceOccurrence (v "digest") (v "index"))
      (if withRefinement then refinedRole entry.code (v "refinement")
       else plainRole entry.code))
    (v "skolem") (v "cnf")
  right := targetRequest
    (batchOccurrence (v "digest") (v "index"))
    (encodePolarity entry.polarity) (v "skolem") (v "cnf")
}

def projectionRules : List RewriteRule :=
  rolePolicy.flatMap fun entry =>
    [mkProjectionRule entry false, mkProjectionRule entry true]

def roleLexemeTerms : List GrammarRule :=
  rolePolicy.map fun entry => ctor entry.code "String" []

def projectionTerm : GrammarRule :=
  ctor "tptp-fof-batch-project:request" "TptpFofBatchGen:Request"
    [("source", "TptpSemantic:annotated-input"),
     ("skolem", "TptpFofSkolem:Output"),
     ("cnf", "TptpFofCnf:Output")]
    (some .rewrite)

private def sharedTypeNames : List String := ["String", "Integer"]

/-- The two source languages overlap exactly at the builtin scalar rows. -/
def batchAdditionalTypes : List TypeDecl :=
  TptpFofClausificationBatchGenerationLanguageDef.language.types.filter
    fun declaration => !(sharedTypeNames.contains declaration.name)

def addedTerms : List GrammarRule :=
    TptpFofClausificationBatchGenerationLanguageDef.language.terms ++
    roleLexemeTerms ++ [projectionTerm]

private def signatureBase : CalculusLanguageDef :=
  CalculusLanguageDef.extend TptpOfficialSemanticCarrier.language {}

private def signatureExtension : CalculusLanguageExtension :=
  ConstructorSignatureExtension.ofLists batchAdditionalTypes addedTerms
    (some "TptpOfficialFofBatchProjectionSignatureV1")

private def signatureCalculusLanguage : CalculusLanguageDef :=
  signatureExtension.apply signatureBase

def signatureLanguage : LanguageDef :=
  signatureCalculusLanguage.toLanguageDef

def rewrites : List RewriteRule :=
    TptpFofClausificationBatchGenerationLanguageDef.language.rewrites ++
      projectionRules

def language : LanguageDef := {
  signatureLanguage with
  name := "TptpOfficialFofBatchProjection"
  rewrites
}

@[simp] theorem language_rewrites : language.rewrites = rewrites := rfl

theorem source_shared_types_exact :
    TptpOfficialSemanticCarrier.language.typeNames.filter
        (fun name =>
          TptpFofClausificationBatchGenerationLanguageDef.language.typeNames
            |>.contains name) = ["Integer", "String"] := by
  decide +kernel

private theorem startsWith_tptp92_not_tptpFof (label : String)
    (official : label.startsWith "tptp92-ast:" = true) :
    label.startsWith "tptp-fof-" = false := by
  rw [String.startsWith_string_eq_false_iff]
  intro batchPrefix
  have officialPrefix : "tptp92-ast:".toList <+: label.toList := by
    simpa [String.startsWith_string_iff] using official
  rcases officialPrefix with ⟨suffix, equality⟩
  rw [← equality] at batchPrefix
  simp at batchPrefix

private theorem startsWith_semantic_not_tptpFof (label : String)
    (official : label.startsWith "tptp-semantic:" = true) :
    label.startsWith "tptp-fof-" = false := by
  rw [String.startsWith_string_eq_false_iff]
  intro batchPrefix
  have officialPrefix : "tptp-semantic:".toList <+: label.toList := by
    simpa [String.startsWith_string_iff] using official
  rcases officialPrefix with ⟨suffix, equality⟩
  rw [← equality] at batchPrefix
  simp at batchPrefix

private theorem official_namespace_excludes_batch (label : String)
    (official :
      TptpOfficialSemanticCarrier.constructorLabelNamespaced label = true)
    (batch :
      TptpFofClausificationBatchGenerationLanguageDef.constructorLabelNamespaced
        label = true) : False := by
  simp only [TptpOfficialSemanticCarrier.constructorLabelNamespaced,
    Bool.or_eq_true] at official
  simp only [
    TptpFofClausificationBatchGenerationLanguageDef.constructorLabelNamespaced]
    at batch
  rcases official with ast | semantic
  · have incompatible := startsWith_tptp92_not_tptpFof label ast
    simp [incompatible] at batch
  · have incompatible := startsWith_semantic_not_tptpFof label semantic
    simp [incompatible] at batch

theorem constructor_labels_disjoint :
    List.Disjoint
      (TptpOfficialSemanticCarrier.language.terms.map (fun term => term.label))
      (TptpFofClausificationBatchGenerationLanguageDef.language.terms.map
        (fun term => term.label)) := by
  rw [List.disjoint_left]
  intro label sourceMembership batchMembership
  have official := (List.all_eq_true.mp
    TptpOfficialSemanticCarrier.constructorLabels_namespaced)
      label sourceMembership
  have batch := (List.all_eq_true.mp
    TptpFofClausificationBatchGenerationLanguageDef.constructorLabels_namespaced)
      label batchMembership
  exact official_namespace_excludes_batch label official batch

private theorem added_type_names_nodup :
    (batchAdditionalTypes.map (fun declaration => declaration.name)).Nodup := by
  have sourceNodup := LanguageDef.typeNames_nodup_of_validate_eq_nil
    TptpFofClausificationBatchGenerationLanguageDef.language
    TptpFofClausificationBatchGenerationLanguageDef.language_validate
  change (TptpFofClausificationBatchGenerationLanguageDef.language.types.map
    (fun declaration : TypeDecl => declaration.name)).Nodup at sourceNodup
  unfold batchAdditionalTypes
  have filteredSublist : List.Sublist
      (TptpFofClausificationBatchGenerationLanguageDef.language.types.filter
        (fun declaration : TypeDecl =>
          !(sharedTypeNames.contains declaration.name)))
      TptpFofClausificationBatchGenerationLanguageDef.language.types :=
    List.filter_sublist
  exact List.Nodup.sublist
    (filteredSublist.map (fun declaration : TypeDecl => declaration.name))
    sourceNodup

private theorem added_type_names_disjoint :
    List.Disjoint signatureBase.typeNames
      (batchAdditionalTypes.map (fun declaration => declaration.name)) := by
  rw [List.disjoint_left]
  intro name baseMembership addedMembership
  rcases List.mem_map.mp addedMembership with
    ⟨addedDeclaration, addedDeclarationMembership, rfl⟩
  have filtered := List.mem_filter.mp addedDeclarationMembership
  have sourceNameMembership : addedDeclaration.name ∈
      TptpFofClausificationBatchGenerationLanguageDef.language.typeNames := by
    exact List.mem_map.mpr ⟨addedDeclaration, filtered.1, rfl⟩
  have intersectionMembership : addedDeclaration.name ∈
      TptpOfficialSemanticCarrier.language.typeNames.filter
        (fun candidate =>
          TptpFofClausificationBatchGenerationLanguageDef.language.typeNames
            |>.contains candidate) := by
    apply List.mem_filter.mpr
    exact ⟨by simpa [signatureBase] using baseMembership,
      List.elem_eq_true_of_mem sourceNameMembership⟩
  rw [source_shared_types_exact] at intersectionMembership
  have sharedMembership : addedDeclaration.name ∈ sharedTypeNames := by
    simpa [sharedTypeNames, or_comm] using intersectionMembership
  have excluded : addedDeclaration.name ∉ sharedTypeNames := by
    intro candidate
    have impossible := filtered.2
    simp at impossible
    exact impossible candidate
  exact excluded sharedMembership

private theorem added_term_labels_nodup :
    (addedTerms.map (fun term => term.label)).Nodup := by
  decide +kernel

private theorem added_term_labels_nonofficial :
    (addedTerms.map (fun term => term.label)).all
      (fun label =>
        !(TptpOfficialSemanticCarrier.constructorLabelNamespaced label)) =
      true := by
  decide +kernel

private theorem added_term_labels_disjoint :
    List.Disjoint (signatureBase.terms.map (fun term => term.label))
      (addedTerms.map (fun term => term.label)) := by
  rw [List.disjoint_left]
  intro label baseMembership addedMembership
  have official := (List.all_eq_true.mp
    TptpOfficialSemanticCarrier.constructorLabels_namespaced)
      label (by simpa [signatureBase] using baseMembership)
  have addedNotOfficial :=
    (List.all_eq_true.mp added_term_labels_nonofficial) label addedMembership
  simp [official] at addedNotOfficial

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
    signatureBase batchAdditionalTypes addedTerms
      (some "TptpOfficialFofBatchProjectionSignatureV1")
  · simpa [signatureBase] using
      TptpOfficialSemanticCarrier.language_validate
  · rfl
  · rfl
  · exact added_type_names_nodup
  · exact added_type_names_disjoint
  · exact added_term_labels_nodup
  · exact added_term_labels_disjoint
  · exact added_terms_valid

theorem role_policy_codes_nodup :
    (rolePolicy.map (fun entry => entry.code)).Nodup := by
  decide +kernel

theorem projection_rule_names_nodup :
    (projectionRules.map (fun rule => rule.name)).Nodup := by
  decide +kernel

theorem rewrite_names_nodup :
    (rewrites.map (fun rule => rule.name)).Nodup := by
  decide +kernel

theorem unsupported_roles_absent :
    ["type", "interpretation", "fi_domain", "fi_functors",
      "fi_predicates", "unknown"].all
      (fun code => !(rolePolicy.map (fun entry => entry.code)).contains code) =
        true := by
  decide +kernel

private def schemaNameReserve : List String := [
  "digest", "index", "name", "formula", "annotations", "span",
  "refinement", "skolem", "cnf", "occurrence", "polarity", "named",
  "clauses", "entries", "local-index", "clause"]

private theorem target_labels_avoid_schema_names :
    (RewriteValidationCertificate.constructorLabels language).all
      (fun label => !(schemaNameReserve.contains label)) = true := by
  decide +kernel

private theorem schema_name_not_constructor (name : String)
    (membership : name ∈ schemaNameReserve) :
    name ∉ RewriteValidationCertificate.constructorLabels language := by
  intro constructorMembership
  have avoided := (List.all_eq_true.mp target_labels_avoid_schema_names)
    name constructorMembership
  have excluded : name ∉ schemaNameReserve := by
    simpa using avoided
  exact excluded membership

private theorem source_type_names_embedded :
    TptpFofClausificationBatchGenerationLanguageDef.language.typeNames.all
      (fun name => decide (name ∈ signatureLanguage.typeNames)) = true := by
  decide +kernel

private theorem source_signatures_embedded :
    (RewriteValidationCertificate.constructorSignatures
      TptpFofClausificationBatchGenerationLanguageDef.language).all
      (fun signature => decide
        (signature ∈ RewriteValidationCertificate.constructorSignatures
          signatureLanguage)) = true := by
  decide +kernel

private theorem batch_schema_names_reserved (rewrite : RewriteRule)
    (membership : rewrite ∈
      TptpFofClausificationBatchGenerationLanguageDef.rewrites) :
    ∀ name ∈ RewriteValidationCertificateExtension.schemaNames rewrite,
      name ∈ schemaNameReserve := by
  simp only [TptpFofClausificationBatchGenerationLanguageDef.rewrites,
    List.mem_cons, List.mem_nil_iff, or_false] at membership
  rcases membership with rfl | rfl | rfl
  · rw [TptpFofClausificationBatchGenerationLanguageDef.start_schemaNames_exact]
    simp [schemaNameReserve]
  · rw [TptpFofClausificationBatchGenerationLanguageDef.nil_schemaNames_exact]
    simp [schemaNameReserve]
  · rw [TptpFofClausificationBatchGenerationLanguageDef.cons_schemaNames_exact]
    simp [schemaNameReserve]

private def batchSignatureEmbedding (rewrite : RewriteRule)
    (membership : rewrite ∈
      TptpFofClausificationBatchGenerationLanguageDef.rewrites) :
    SignatureEmbeddingFor
      TptpFofClausificationBatchGenerationLanguageDef.language signatureLanguage
      rewrite where
  typeNames name sourceMembership :=
    decide_eq_true_eq.mp
      ((List.all_eq_true.mp source_type_names_embedded) name sourceMembership)
  signatures signature sourceMembership :=
    decide_eq_true_eq.mp
      ((List.all_eq_true.mp source_signatures_embedded) signature
        sourceMembership)
  avoidsSchema name schemaMembership :=
    by
      simpa [signatureLanguage, language,
        RewriteValidationCertificate.constructorLabels] using
        schema_name_not_constructor name
          (batch_schema_names_reserved rewrite membership name schemaMembership)

private theorem batch_rewrites_valid (rewrite : RewriteRule)
    (membership : rewrite ∈
      TptpFofClausificationBatchGenerationLanguageDef.rewrites) :
    language.validateRewrite rewrite = [] := by
  change signatureLanguage.validateRewrite rewrite = []
  apply RewriteValidationCertificate.validateRewrite_eq_nil
    (LanguageDef.constructorLabels_nodup_of_validate_eq_nil
      signatureLanguage signatureLanguage_validate)
  exact RewriteValidationCertificateExtension.Certificate.embed
    (TptpFofClausificationBatchGenerationLanguageDef.rewrite_certificate
      rewrite membership)
    (batchSignatureEmbedding rewrite membership)

private def requiredProjectionTypes : List String := [
  "String", "Integer", "Tptp92Ast:name", "Tptp92Ast:fof-formula",
  "Tptp92Ast:annotations", "Tptp92Ast:source-span",
  "Tptp92Ast:general-term", "TptpFofSkolem:Output",
  "TptpFofCnf:Output"]

private theorem required_projection_types_declared :
    requiredProjectionTypes.all
      (fun name => decide (name ∈ language.typeNames)) = true := by
  decide +kernel

private theorem required_projection_type_declared (name : String)
    (membership : name ∈ requiredProjectionTypes) :
    name ∈ language.typeNames :=
  decide_eq_true_eq.mp
    ((List.all_eq_true.mp required_projection_types_declared) name membership)

private def requiredProjectionSignatures : List (String × Nat) := [
  ("tptp-fof-batch-project:request", 3),
  ("tptp-semantic:fof-input", 3),
  ("tptp-semantic:occurrence-id", 2),
  ("tptp-semantic:source-digest", 1),
  ("tptp92-ast:fof-annotated:alt-1", 4),
  ("tptp92-ast:formula-role:alt-1", 1),
  ("tptp92-ast:formula-role:alt-2", 2),
  ("tptp92-ast:token:lower-word", 1),
  ("tptp-fof-batch-gen:request", 4),
  ("tptp-fof-batch:occurrence", 2),
  ("tptp-fof-batch:positive", 0),
  ("tptp-fof-batch:negative", 0),
  ("axiom", 0), ("hypothesis", 0), ("definition", 0),
  ("assumption", 0), ("lemma", 0), ("theorem", 0),
  ("corollary", 0), ("conjecture", 0),
  ("negated_conjecture", 0), ("plain", 0)]

private theorem required_projection_signatures_declared :
    requiredProjectionSignatures.all
      (fun signature => decide
        (signature ∈ RewriteValidationCertificate.constructorSignatures
          language)) = true := by
  decide +kernel

private theorem required_projection_signature_declared
    (signature : String × Nat)
    (membership : signature ∈ requiredProjectionSignatures) :
    signature ∈ RewriteValidationCertificate.constructorSignatures language :=
  decide_eq_true_eq.mp
    ((List.all_eq_true.mp required_projection_signatures_declared)
      signature membership)

private theorem role_code_signature_declared (entry : RolePolicyEntry)
    (entryMembership : entry ∈ rolePolicy) :
    (entry.code, 0) ∈ RewriteValidationCertificate.constructorSignatures
      language := by
  simp only [rolePolicy, List.mem_cons, List.mem_nil_iff, or_false] at entryMembership
  rcases entryMembership with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact required_projection_signature_declared _ (by decide)

local macro "projection_row_simp" : tactic =>
  `(tactic|
    (simp_all [requiredProjectionTypes, requiredProjectionSignatures,
      required_projection_type_declared,
      required_projection_signature_declared,
      role_code_signature_declared,
      schemaNameReserve, schema_name_not_constructor,
      mkProjectionRule, projectionRequest, targetRequest, sourceFofInput,
      sourceOccurrence, sourceDigest, batchOccurrence, plainRole,
      refinedRole, tokenLowerWord, a, v,
      TptpFofClausificationBatchGenerationLanguageDef.request,
      TptpFofClausificationBatchGenerationLanguageDef.a,
      encodePolarity_true, encodePolarity_false,
      LanguageDef.premisePatterns, LanguageDef.patternFvarNames,
      LanguageDef.patternBinderNames, Pattern.constructorRefs,
      Pattern.constructorRefsList, Pattern.freeFvarNames,
      Pattern.isWellScoped, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt, LanguageDef.premiseFvarNames,
      LanguageDef.premiseForAllParams,
      LanguageDef.premiseProducedFvarNames, TypeExpr.baseNames,
      Pattern.zipHead, Pattern.mapHead, Pattern.evalHead] <;>
      first
      | exact required_projection_type_declared _ (by decide)
      | exact required_projection_signature_declared _ (by decide)
      | exact schema_name_not_constructor _ (by decide)
      | decide +kernel))

private theorem projection_contextTypes (entry : RolePolicyEntry)
    (_entryMembership : entry ∈ rolePolicy) (withRefinement : Bool) :
    ∀ contextEntry ∈ (mkProjectionRule entry withRefinement).typeContext,
      ∀ name ∈ contextEntry.2.baseNames, name ∈ language.typeNames := by
  cases withRefinement <;> projection_row_simp

private theorem projection_leftDeclared (entry : RolePolicyEntry)
    (entryMembership : entry ∈ rolePolicy) (withRefinement : Bool) :
    ∀ reference ∈ (mkProjectionRule entry withRefinement).left.constructorRefs,
      reference ∈ RewriteValidationCertificate.constructorSignatures language := by
  have roleDeclared := role_code_signature_declared entry entryMembership
  cases withRefinement <;> projection_row_simp

private theorem projection_rightDeclared (entry : RolePolicyEntry)
    (_entryMembership : entry ∈ rolePolicy) (withRefinement : Bool) :
    ∀ reference ∈ (mkProjectionRule entry withRefinement).right.constructorRefs,
      reference ∈ RewriteValidationCertificate.constructorSignatures language := by
  rcases entry with ⟨code, polarity⟩
  cases polarity <;> cases withRefinement <;> projection_row_simp

private theorem projection_premisesDeclared (entry : RolePolicyEntry)
    (_entryMembership : entry ∈ rolePolicy) (withRefinement : Bool) :
    ∀ pattern ∈ (mkProjectionRule entry withRefinement).premises.flatMap
        LanguageDef.premisePatterns,
      ∀ reference ∈ pattern.constructorRefs,
        reference ∈ RewriteValidationCertificate.constructorSignatures language := by
  simp [mkProjectionRule]

private theorem projection_allPatternsScoped (entry : RolePolicyEntry)
    (_entryMembership : entry ∈ rolePolicy) (withRefinement : Bool) :
    ([(mkProjectionRule entry withRefinement).left,
        (mkProjectionRule entry withRefinement).right] ++
      (mkProjectionRule entry withRefinement).premises.flatMap
        LanguageDef.premisePatterns).all Pattern.isWellScoped = true := by
  rcases entry with ⟨code, polarity⟩
  cases polarity <;> cases withRefinement <;> projection_row_simp

private theorem projection_fvarsAvoidConstructors (entry : RolePolicyEntry)
    (entryMembership : entry ∈ rolePolicy) (withRefinement : Bool) :
    ∀ name ∈ ((LanguageDef.patternFvarNames []
        (mkProjectionRule entry withRefinement).left ++
      LanguageDef.patternFvarNames []
        (mkProjectionRule entry withRefinement).right ++
      (mkProjectionRule entry withRefinement).premises.flatMap
        (LanguageDef.premiseFvarNames [])).eraseDups),
      name ∉ RewriteValidationCertificate.constructorLabels language := by
  rcases entry with ⟨code, polarity⟩
  cases polarity <;> cases withRefinement <;> projection_row_simp

private theorem projection_bindersAvoidConstructors (entry : RolePolicyEntry)
    (entryMembership : entry ∈ rolePolicy) (withRefinement : Bool) :
    ∀ name ∈ ((LanguageDef.patternBinderNames
        (mkProjectionRule entry withRefinement).left ++
      LanguageDef.patternBinderNames
        (mkProjectionRule entry withRefinement).right ++
      ((mkProjectionRule entry withRefinement).premises.flatMap
        LanguageDef.premisePatterns).flatMap
          LanguageDef.patternBinderNames ++
      (mkProjectionRule entry withRefinement).premises.flatMap
        LanguageDef.premiseForAllParams).eraseDups),
      name ∉ RewriteValidationCertificate.constructorLabels language := by
  rcases entry with ⟨code, polarity⟩
  cases polarity <;> cases withRefinement <;> projection_row_simp

private theorem projection_contextAvoidsConstructors (entry : RolePolicyEntry)
    (_entryMembership : entry ∈ rolePolicy) (withRefinement : Bool) :
    ∀ contextEntry ∈ (mkProjectionRule entry withRefinement).typeContext,
      contextEntry.1 ∉ RewriteValidationCertificate.constructorLabels language := by
  cases withRefinement <;> projection_row_simp

private theorem projection_rightBound (entry : RolePolicyEntry)
    (_entryMembership : entry ∈ rolePolicy) (withRefinement : Bool) :
    ∀ name ∈ (LanguageDef.patternFvarNames []
        (mkProjectionRule entry withRefinement).right).eraseDups,
      name ∈ LanguageDef.patternFvarNames []
          (mkProjectionRule entry withRefinement).left ++
        (mkProjectionRule entry withRefinement).premises.flatMap
          (LanguageDef.premiseProducedFvarNames []) := by
  rcases entry with ⟨code, polarity⟩
  cases polarity <;> cases withRefinement <;> projection_row_simp

private theorem projection_rule_certificate (entry : RolePolicyEntry)
    (entryMembership : entry ∈ rolePolicy) (withRefinement : Bool) :
    RewriteValidationCertificate.Certificate language
      (mkProjectionRule entry withRefinement) where
  contextTypes := projection_contextTypes entry entryMembership withRefinement
  leftDeclared := projection_leftDeclared entry entryMembership withRefinement
  rightDeclared := projection_rightDeclared entry entryMembership withRefinement
  premisesDeclared :=
    projection_premisesDeclared entry entryMembership withRefinement
  allPatternsScoped :=
    projection_allPatternsScoped entry entryMembership withRefinement
  fvarsAvoidConstructors :=
    projection_fvarsAvoidConstructors entry entryMembership withRefinement
  bindersAvoidConstructors :=
    projection_bindersAvoidConstructors entry entryMembership withRefinement
  contextAvoidsConstructors :=
    projection_contextAvoidsConstructors entry entryMembership withRefinement
  rightBound := projection_rightBound entry entryMembership withRefinement

private theorem projection_rewrites_valid (rewrite : RewriteRule)
    (membership : rewrite ∈ projectionRules) :
    language.validateRewrite rewrite = [] := by
  simp only [projectionRules, List.mem_flatMap] at membership
  obtain ⟨entry, entryMembership, ruleMembership⟩ := membership
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at ruleMembership
  rcases ruleMembership with rfl | rfl
  · exact RewriteValidationCertificate.validateRewrite_eq_nil
      (LanguageDef.constructorLabels_nodup_of_validate_eq_nil
        signatureLanguage signatureLanguage_validate)
      (projection_rule_certificate entry entryMembership false)
  · exact RewriteValidationCertificate.validateRewrite_eq_nil
      (LanguageDef.constructorLabels_nodup_of_validate_eq_nil
        signatureLanguage signatureLanguage_validate)
      (projection_rule_certificate entry entryMembership true)

private theorem rewrites_valid :
    ∀ rewrite ∈ rewrites, language.validateRewrite rewrite = [] := by
  intro rewrite membership
  simp only [rewrites, List.mem_append] at membership
  rcases membership with batchMembership | projectionMembership
  · exact batch_rewrites_valid rewrite batchMembership
  · exact projection_rewrites_valid rewrite projectionMembership

theorem language_validate : language.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_rows
  · exact LanguageDef.typeNames_nodup_of_validate_eq_nil
      signatureLanguage signatureLanguage_validate
  · exact LanguageDef.constructorLabels_nodup_of_validate_eq_nil
      signatureLanguage signatureLanguage_validate
  · exact LanguageDef.equationNames_nodup_of_validate_eq_nil
      signatureLanguage signatureLanguage_validate
  · exact rewrite_names_nodup
  · intro term membership
    exact LanguageDef.validateTerm_eq_nil_of_validate_eq_nil
      signatureLanguage signatureLanguage_validate term membership
  · intro equation membership
    exact LanguageDef.validateEquation_eq_nil_of_validate_eq_nil
      signatureLanguage signatureLanguage_validate equation membership
  · exact rewrites_valid

def validated : ValidatedLanguageDef := ⟨language, language_validate⟩

namespace Canary

theorem conjecture_rule_is_present :
    mkProjectionRule ⟨"conjecture", false⟩ false ∈ projectionRules := by
  simp [projectionRules, rolePolicy]

theorem unknown_role_is_unsupported :
    "unknown" ∉ rolePolicy.map (fun entry => entry.code) := by
  decide

theorem metadata_is_not_in_target (entry : RolePolicyEntry)
    (withRefinement : Bool) :
    (mkProjectionRule entry withRefinement).right =
      targetRequest (batchOccurrence (v "digest") (v "index"))
        (encodePolarity entry.polarity) (v "skolem") (v "cnf") := by
  rfl

end Canary

#print axioms source_shared_types_exact
#print axioms constructor_labels_disjoint
#print axioms projection_rule_names_nodup
#print axioms rewrite_names_nodup
#print axioms unsupported_roles_absent
#print axioms language_validate
#print axioms Canary.conjecture_rule_is_present
#print axioms Canary.unknown_role_is_unsupported
#print axioms Canary.metadata_is_not_in_target

end Mettapedia.GSLT.LanguageDef.TptpOfficialFofBatchProjectionLanguageDef
