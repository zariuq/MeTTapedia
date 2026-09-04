import Mettapedia.GSLT.LanguageDef.TptpFofClausificationBatchLanguageDef
import Mettapedia.GSLT.LanguageDef.RewriteValidationCertificate
import Mettapedia.GSLT.LanguageDef.RewriteValidationCertificateExtension
import Mettapedia.GSLT.LanguageDef.StructuralCategory
import Mettapedia.GSLT.LanguageDef.ConstructorSignatureExtension

/-!
# Authored construction of source-indexed clausification batches

This transformation adds stable local identities to an already generated
definitional-CNF clause list.  Three authored rewrites perform the work: one
opens the CNF output, and two traverse the clause list while incrementing its
local Peano index.  The transformation does not inspect predicates, terms, or
literals and does not assign concrete TPTP names or roles.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpFofClausificationBatchGenerationLanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.CalculusLanguageExtension

private def ctor (label category : String)
    (parameters : List (String × String)) : GrammarRule := {
  label
  category
  params := parameters.map fun parameter =>
    .simple parameter.1 (.base parameter.2)
  syntaxPattern := []
  evalPolicy? := none
}

def a (label : String) (arguments : List Pattern := []) : Pattern :=
  .apply label arguments

def v (name : String) : Pattern := .fvar name

def request (occurrence polarity skolem cnf : Pattern) : Pattern :=
  a "tptp-fof-batch-gen:request" [occurrence, polarity, skolem, cnf]

def indexEntries (occurrence localIndex clauses : Pattern) : Pattern :=
  a "tptp-fof-batch-gen:index-entries"
    [occurrence, localIndex, clauses]

def addedTypes : List TypeDecl := ["TptpFofBatchGen:Request"]

def addedTerms : List GrammarRule := [
  ctor "tptp-fof-batch-gen:request" "TptpFofBatchGen:Request"
    [("occurrence", "TptpFofBatch:Occurrence"),
     ("polarity", "TptpFofBatch:Polarity"),
     ("skolem", "TptpFofSkolem:Output"),
     ("cnf", "TptpFofCnf:Output")],
  ctor "tptp-fof-batch-gen:index-entries" "TptpFofBatch:ClauseEntries"
    [("occurrence", "TptpFofBatch:Occurrence"),
     ("local-index", "TptpResolvedFof:Index"),
     ("clauses", "TptpFofCnf:Clauses")]
]

def mkRule (name : String) (context : List (String × String))
    (premises : List Premise) (left right : Pattern) : RewriteRule := {
  name
  typeContext := context.map fun entry => (entry.1, .base entry.2)
  premises
  left
  right
}

def congruence (source target : Pattern) : Premise :=
  .congruence source target

def startRule : RewriteRule :=
  mkRule "tptp-fof-batch-gen:start" [
      ("occurrence", "TptpFofBatch:Occurrence"),
      ("polarity", "TptpFofBatch:Polarity"),
      ("skolem", "TptpFofSkolem:Output"),
      ("named", "TptpFofNamed:Output"),
      ("clauses", "TptpFofCnf:Clauses"),
      ("entries", "TptpFofBatch:ClauseEntries")]
    [congruence
      (indexEntries (v "occurrence")
        (a "tptp-fof-resolved:index-zero") (v "clauses"))
      (v "entries")]
    (request (v "occurrence") (v "polarity") (v "skolem")
      (TptpFofDefinitionalCnfLanguageDef.cnfOutput
        (v "named") (v "clauses")))
    (a "tptp-fof-batch:output" [
      v "occurrence", v "polarity", v "skolem",
      TptpFofDefinitionalCnfLanguageDef.cnfOutput
        (v "named") (v "clauses"),
      v "entries"])

def nilRule : RewriteRule :=
  mkRule "tptp-fof-batch-gen:entries-nil" [
      ("occurrence", "TptpFofBatch:Occurrence"),
      ("local-index", "TptpResolvedFof:Index")]
    []
    (indexEntries (v "occurrence") (v "local-index")
      TptpFofDefinitionalCnfLanguageDef.clausesNil)
    (a "tptp-fof-batch:entries-nil")

def consRule : RewriteRule :=
  mkRule "tptp-fof-batch-gen:entries-cons" [
      ("occurrence", "TptpFofBatch:Occurrence"),
      ("local-index", "TptpResolvedFof:Index"),
      ("clause", "TptpFofCnf:Clause"),
      ("clauses", "TptpFofCnf:Clauses"),
      ("entries", "TptpFofBatch:ClauseEntries")]
    [congruence
      (indexEntries (v "occurrence")
        (a "tptp-fof-resolved:index-succ" [v "local-index"])
        (v "clauses"))
      (v "entries")]
    (indexEntries (v "occurrence") (v "local-index")
      (TptpFofDefinitionalCnfLanguageDef.clausesCons
        (v "clause") (v "clauses")))
    (a "tptp-fof-batch:entries-cons" [
      a "tptp-fof-batch:clause-entry" [
        a "tptp-fof-batch:clause-id"
          [v "occurrence", v "local-index"],
        v "clause"],
      v "entries"])

def rewrites : List RewriteRule := [startRule, nilRule, consRule]

private def signatureBase : CalculusLanguageDef :=
  CalculusLanguageDef.extend
    TptpFofClausificationBatchLanguageDef.language {}

private def signatureExtension : CalculusLanguageExtension :=
  ConstructorSignatureExtension.ofLists addedTypes addedTerms
    (some "TptpFofClausificationBatchGenerationV1")

private def signatureCalculusLanguage : CalculusLanguageDef :=
  signatureExtension.apply signatureBase

def signatureLanguage : LanguageDef :=
  signatureCalculusLanguage.toLanguageDef

private theorem added_type_names_nodup :
    (addedTypes.map (·.name)).Nodup := by
  decide

private theorem added_type_names_absent :
    addedTypes.all (fun declaration =>
      !(signatureBase.types.any fun existing =>
        existing.name == declaration.name)) = true := by
  decide +kernel

private theorem added_type_names_disjoint :
    List.Disjoint signatureBase.toLanguageDef.typeNames
      (addedTypes.map (·.name)) := by
  have absent := added_type_names_absent
  simp only [List.all_eq_true, Bool.not_eq_true', List.any_eq_false] at absent
  rw [List.disjoint_left]
  intro name baseMembership addedMembership
  rcases List.mem_map.mp baseMembership with
    ⟨baseDeclaration, baseDeclarationMembership, baseName⟩
  rcases List.mem_map.mp addedMembership with
    ⟨addedDeclaration, addedDeclarationMembership, addedName⟩
  exact absent addedDeclaration addedDeclarationMembership
    baseDeclaration baseDeclarationMembership
    (by simpa using baseName.trans addedName.symm)

private theorem added_term_labels_nodup :
    (addedTerms.map (·.label)).Nodup := by
  decide

private theorem added_term_labels_absent :
    addedTerms.all (fun declaration =>
      !(signatureBase.terms.any fun existing =>
        existing.label == declaration.label)) = true := by
  decide +kernel

private theorem added_term_labels_disjoint :
    List.Disjoint (signatureBase.terms.map (·.label))
      (addedTerms.map (·.label)) := by
  have absent := added_term_labels_absent
  simp only [List.all_eq_true, Bool.not_eq_true', List.any_eq_false] at absent
  rw [List.disjoint_left]
  intro name baseMembership addedMembership
  rcases List.mem_map.mp baseMembership with
    ⟨baseDeclaration, baseDeclarationMembership, baseName⟩
  rcases List.mem_map.mp addedMembership with
    ⟨addedDeclaration, addedDeclarationMembership, addedName⟩
  exact absent addedDeclaration addedDeclarationMembership
    baseDeclaration baseDeclarationMembership
    (by simpa using baseName.trans addedName.symm)

private theorem added_terms_validate_all :
    addedTerms.all (fun term =>
      signatureLanguage.validateTerm term == []) = true := by
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
      (some "TptpFofClausificationBatchGenerationV1")
  · simpa [signatureBase] using
      TptpFofClausificationBatchLanguageDef.language_validate
  · rfl
  · rfl
  · exact added_type_names_nodup
  · exact added_type_names_disjoint
  · exact added_term_labels_nodup
  · exact added_term_labels_disjoint
  · exact added_terms_valid

def language : LanguageDef := {
  name := "TptpFofClausificationBatchGeneration"
  types := signatureLanguage.types
  terms := signatureLanguage.terms
  equations := []
  rewrites
}

@[simp] theorem language_rewrites : language.rewrites = rewrites := rfl

/-! Exact inventories keep validation of the three new rows proportional to
the extension rather than forcing reduction of the complete inherited FOF
carrier. -/

@[simp] theorem typeNames_exact : language.typeNames =
    TptpFofClausificationBatchLanguageDef.language.typeNames ++
      ["TptpFofBatchGen:Request"] := by
  simp [language, signatureLanguage, signatureCalculusLanguage,
    signatureExtension, signatureBase,
    ConstructorSignatureExtension.ofLists, LanguageDef.typeNames, addedTypes,
    TypeDecl.plain]

@[simp] theorem constructorSignatures_exact :
    RewriteValidationCertificate.constructorSignatures language =
      RewriteValidationCertificate.constructorSignatures
        TptpFofClausificationBatchLanguageDef.language ++ [
        ("tptp-fof-batch-gen:request", 4),
        ("tptp-fof-batch-gen:index-entries", 3)] := by
  simp [RewriteValidationCertificate.constructorSignatures, language,
    signatureLanguage, signatureCalculusLanguage, signatureExtension,
    signatureBase, ConstructorSignatureExtension.ofLists, addedTerms, ctor]

@[simp] theorem constructorLabels_exact :
    RewriteValidationCertificate.constructorLabels language =
      RewriteValidationCertificate.constructorLabels
        TptpFofClausificationBatchLanguageDef.language ++ [
        "tptp-fof-batch-gen:request",
        "tptp-fof-batch-gen:index-entries"] := by
  simp [RewriteValidationCertificate.constructorLabels, language,
    signatureLanguage, signatureCalculusLanguage, signatureExtension,
    signatureBase, ConstructorSignatureExtension.ofLists, addedTerms, ctor]

def constructorLabelNamespaced (label : String) : Bool :=
  label.startsWith "tptp-fof-"

theorem constructorLabels_namespaced :
    (RewriteValidationCertificate.constructorLabels language).all
      constructorLabelNamespaced = true := by
  simp [constructorLabelNamespaced,
    TptpFofClausificationBatchLanguageDef.constructorLabels_exact,
    TptpFofDefinitionalCnfLanguageDef.constructorLabels_exact,
    TptpFofSkolemLanguageDef.constructorLabels_exact]

private theorem plainName_not_constructor (name : String)
    (plain : constructorLabelNamespaced name = false) :
    name ∉ RewriteValidationCertificate.constructorLabels language := by
  intro membership
  have namespaced := (List.all_eq_true.mp constructorLabels_namespaced)
    name membership
  simp [plain] at namespaced

private def requiredTypes : List String := [
  "TptpResolvedFof:Index", "TptpFofNamed:Output",
  "TptpFofSkolem:Output", "TptpFofCnf:Clause",
  "TptpFofCnf:Clauses", "TptpFofCnf:Output",
  "TptpFofBatch:Occurrence", "TptpFofBatch:Polarity",
  "TptpFofBatch:ClauseId", "TptpFofBatch:ClauseEntry",
  "TptpFofBatch:ClauseEntries", "TptpFofBatch:Output",
  "TptpFofBatchGen:Request"]

private theorem requiredTypes_declared :
    requiredTypes.all (fun name => decide (name ∈ language.typeNames)) = true := by
  simp [requiredTypes,
    TptpFofClausificationBatchLanguageDef.typeNames_exact,
    TptpFofDefinitionalCnfLanguageDef.typeNames_exact,
    TptpFofSkolemLanguageDef.typeNames_exact]

@[simp] private theorem requiredType_declared (name : String)
    (membership : name ∈ requiredTypes) : name ∈ language.typeNames :=
  decide_eq_true_eq.mp
    (List.all_eq_true.mp requiredTypes_declared name membership)

private def requiredSignatures : List (String × Nat) := [
  ("tptp-fof-resolved:index-zero", 0),
  ("tptp-fof-resolved:index-succ", 1),
  ("tptp-fof-cnf:clauses-nil", 0),
  ("tptp-fof-cnf:clauses-cons", 2),
  ("tptp-fof-cnf:output", 2),
  ("tptp-fof-batch:positive", 0),
  ("tptp-fof-batch:negative", 0),
  ("tptp-fof-batch:clause-id", 2),
  ("tptp-fof-batch:clause-entry", 2),
  ("tptp-fof-batch:entries-nil", 0),
  ("tptp-fof-batch:entries-cons", 2),
  ("tptp-fof-batch:output", 5),
  ("tptp-fof-batch-gen:request", 4),
  ("tptp-fof-batch-gen:index-entries", 3)]

private theorem requiredSignatures_declared :
    requiredSignatures.all (fun signature => decide
      (signature ∈ RewriteValidationCertificate.constructorSignatures
        language)) = true := by
  simp [requiredSignatures,
    TptpFofClausificationBatchLanguageDef.constructorSignatures_exact,
    TptpFofDefinitionalCnfLanguageDef.constructorSignatures_exact,
    TptpFofSkolemLanguageDef.constructorSignatures_exact]

@[simp] private theorem requiredSignature_declared
    (signature : String × Nat) (membership : signature ∈ requiredSignatures) :
    signature ∈ RewriteValidationCertificate.constructorSignatures language :=
  decide_eq_true_eq.mp
    (List.all_eq_true.mp requiredSignatures_declared signature membership)

local macro "certify_batch_generation_row" : tactic =>
  `(tactic|
    (simp [RewriteValidationCertificate.check,
      RewriteValidationCertificate.contextTypesCheck,
      RewriteValidationCertificate.patternDeclaredCheck,
      RewriteValidationCertificate.premisesDeclaredCheck,
      RewriteValidationCertificate.allPatternsScopedCheck,
      RewriteValidationCertificate.fvarsAvoidConstructorsCheck,
      RewriteValidationCertificate.bindersAvoidConstructorsCheck,
      RewriteValidationCertificate.contextAvoidsConstructorsCheck,
      RewriteValidationCertificate.rightBoundCheck,
      requiredTypes, requiredSignatures, requiredType_declared,
      requiredSignature_declared, startRule, nilRule, consRule, request,
      indexEntries, mkRule, congruence, a, v,
      TptpFofClausificationBatchLanguageDef.typeNames_exact,
      TptpFofClausificationBatchLanguageDef.constructorSignatures_exact,
      TptpFofClausificationBatchLanguageDef.constructorLabels_exact,
      TptpFofDefinitionalCnfLanguageDef.typeNames_exact,
      TptpFofDefinitionalCnfLanguageDef.constructorSignatures_exact,
      TptpFofDefinitionalCnfLanguageDef.constructorLabels_exact,
      TptpFofSkolemLanguageDef.typeNames_exact,
      TptpFofSkolemLanguageDef.constructorSignatures_exact,
      TptpFofSkolemLanguageDef.constructorLabels_exact,
      TptpFofDefinitionalCnfLanguageDef.a,
      TptpFofDefinitionalCnfLanguageDef.cnfOutput,
      TptpFofDefinitionalCnfLanguageDef.clausesNil,
      TptpFofDefinitionalCnfLanguageDef.clausesCons,
      LanguageDef.premisePatterns, LanguageDef.patternFvarNames,
      LanguageDef.patternBinderNames, Pattern.constructorRefs,
      Pattern.constructorRefsList, Pattern.freeFvarNames,
      Pattern.isWellScoped, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt, LanguageDef.premiseFvarNames,
      LanguageDef.premiseForAllParams,
      LanguageDef.premiseProducedFvarNames, TypeExpr.baseNames,
      Pattern.zipHead, Pattern.mapHead, Pattern.evalHead,
      plainName_not_constructor, constructorLabelNamespaced] <;>
      decide +kernel))

theorem rewrite_names_exact : language.rewrites.map (·.name) = [
    "tptp-fof-batch-gen:start",
    "tptp-fof-batch-gen:entries-nil",
    "tptp-fof-batch-gen:entries-cons"] := by
  rfl

theorem rewrite_names_nodup : (language.rewrites.map (·.name)).Nodup := by
  rw [rewrite_names_exact]
  decide

private theorem check_of_component_checks (rewrite : RewriteRule)
    (contextTypes :
      RewriteValidationCertificate.contextTypesCheck language rewrite = true)
    (leftDeclared :
      RewriteValidationCertificate.patternDeclaredCheck language
        rewrite.left = true)
    (rightDeclared :
      RewriteValidationCertificate.patternDeclaredCheck language
        rewrite.right = true)
    (premisesDeclared :
      RewriteValidationCertificate.premisesDeclaredCheck language rewrite =
        true)
    (allPatternsScoped :
      RewriteValidationCertificate.allPatternsScopedCheck rewrite = true)
    (fvarsAvoidConstructors :
      RewriteValidationCertificate.fvarsAvoidConstructorsCheck language
        rewrite = true)
    (bindersAvoidConstructors :
      RewriteValidationCertificate.bindersAvoidConstructorsCheck language
        rewrite = true)
    (contextAvoidsConstructors :
      RewriteValidationCertificate.contextAvoidsConstructorsCheck language
        rewrite = true)
    (rightBound :
      RewriteValidationCertificate.rightBoundCheck rewrite = true) :
    RewriteValidationCertificate.check language rewrite = true := by
  simp [RewriteValidationCertificate.check, contextTypes, leftDeclared,
    rightDeclared, premisesDeclared, allPatternsScoped,
    fvarsAvoidConstructors, bindersAvoidConstructors,
    contextAvoidsConstructors, rightBound]

private theorem start_contextTypes :
    RewriteValidationCertificate.contextTypesCheck language startRule = true := by
  certify_batch_generation_row
private theorem start_leftDeclared :
    RewriteValidationCertificate.patternDeclaredCheck language
      startRule.left = true := by
  certify_batch_generation_row
private theorem start_rightDeclared :
    RewriteValidationCertificate.patternDeclaredCheck language
      startRule.right = true := by
  certify_batch_generation_row
private theorem start_premisesDeclared :
    RewriteValidationCertificate.premisesDeclaredCheck language startRule =
      true := by
  certify_batch_generation_row
private theorem start_allPatternsScoped :
    RewriteValidationCertificate.allPatternsScopedCheck startRule = true := by
  certify_batch_generation_row
private theorem start_fvarsAvoidConstructors :
    RewriteValidationCertificate.fvarsAvoidConstructorsCheck language
      startRule = true := by
  certify_batch_generation_row
private theorem start_bindersAvoidConstructors :
    RewriteValidationCertificate.bindersAvoidConstructorsCheck language
      startRule = true := by
  certify_batch_generation_row
private theorem start_contextAvoidsConstructors :
    RewriteValidationCertificate.contextAvoidsConstructorsCheck language
      startRule = true := by
  certify_batch_generation_row
private theorem start_rightBound :
    RewriteValidationCertificate.rightBoundCheck startRule = true := by
  certify_batch_generation_row

private theorem start_checked :
    RewriteValidationCertificate.check language startRule = true := by
  exact check_of_component_checks startRule start_contextTypes
    start_leftDeclared start_rightDeclared start_premisesDeclared
    start_allPatternsScoped start_fvarsAvoidConstructors
    start_bindersAvoidConstructors start_contextAvoidsConstructors
    start_rightBound

private theorem nil_checked :
    RewriteValidationCertificate.check language nilRule = true := by
  certify_batch_generation_row

private theorem cons_contextTypes :
    RewriteValidationCertificate.contextTypesCheck language consRule = true := by
  certify_batch_generation_row
private theorem cons_leftDeclared :
    RewriteValidationCertificate.patternDeclaredCheck language consRule.left =
      true := by
  certify_batch_generation_row
private theorem cons_rightDeclared :
    RewriteValidationCertificate.patternDeclaredCheck language consRule.right =
      true := by
  certify_batch_generation_row
private theorem cons_premisesDeclared :
    RewriteValidationCertificate.premisesDeclaredCheck language consRule =
      true := by
  certify_batch_generation_row
private theorem cons_allPatternsScoped :
    RewriteValidationCertificate.allPatternsScopedCheck consRule = true := by
  certify_batch_generation_row
private theorem cons_fvarsAvoidConstructors :
    RewriteValidationCertificate.fvarsAvoidConstructorsCheck language
      consRule = true := by
  certify_batch_generation_row
private theorem cons_bindersAvoidConstructors :
    RewriteValidationCertificate.bindersAvoidConstructorsCheck language
      consRule = true := by
  certify_batch_generation_row
private theorem cons_contextAvoidsConstructors :
    RewriteValidationCertificate.contextAvoidsConstructorsCheck language
      consRule = true := by
  certify_batch_generation_row
private theorem cons_rightBound :
    RewriteValidationCertificate.rightBoundCheck consRule = true := by
  certify_batch_generation_row

private theorem cons_checked :
    RewriteValidationCertificate.check language consRule = true := by
  exact check_of_component_checks consRule cons_contextTypes cons_leftDeclared
    cons_rightDeclared cons_premisesDeclared cons_allPatternsScoped
    cons_fvarsAvoidConstructors cons_bindersAvoidConstructors
    cons_contextAvoidsConstructors cons_rightBound

/-- Exact schema support of the start row.  Signature linkers can use this
finite interface without re-normalizing the authored row. -/
theorem start_schemaNames_exact :
    RewriteValidationCertificateExtension.schemaNames startRule =
      ["occurrence", "polarity", "skolem", "named", "clauses", "entries"] := by
  simp [RewriteValidationCertificateExtension.schemaNames, startRule, mkRule,
    request, indexEntries, congruence, a, v,
    TptpFofDefinitionalCnfLanguageDef.cnfOutput,
    TptpFofDefinitionalCnfLanguageDef.a,
    LanguageDef.patternFvarNames, LanguageDef.patternBinderNames,
    LanguageDef.premiseFvarNames, LanguageDef.premiseForAllParams,
    Pattern.freeFvarNames, LanguageDef.premisePatterns]
  decide +kernel

/-- Exact schema support of the empty-list row. -/
theorem nil_schemaNames_exact :
    RewriteValidationCertificateExtension.schemaNames nilRule =
      ["occurrence", "local-index"] := by
  simp [RewriteValidationCertificateExtension.schemaNames, nilRule, mkRule,
    indexEntries, a, v, TptpFofDefinitionalCnfLanguageDef.clausesNil,
    TptpFofDefinitionalCnfLanguageDef.a,
    LanguageDef.patternFvarNames, LanguageDef.patternBinderNames,
    Pattern.freeFvarNames]
  decide +kernel

/-- Exact schema support of the cons row. -/
theorem cons_schemaNames_exact :
    RewriteValidationCertificateExtension.schemaNames consRule =
      ["occurrence", "local-index", "clause", "clauses", "entries"] := by
  simp [RewriteValidationCertificateExtension.schemaNames, consRule, mkRule,
    indexEntries, congruence, a, v,
    TptpFofDefinitionalCnfLanguageDef.clausesCons,
    TptpFofDefinitionalCnfLanguageDef.a,
    LanguageDef.patternFvarNames, LanguageDef.patternBinderNames,
    LanguageDef.premiseFvarNames, LanguageDef.premiseForAllParams,
    Pattern.freeFvarNames, LanguageDef.premisePatterns]
  decide +kernel

/-- Every authored batch-generation row carries a reusable structural
certificate.  Signature gluing can transport this evidence without
re-evaluating the row against the complete combined presentation. -/
theorem rewrite_certificate (rewrite : RewriteRule)
    (membership : rewrite ∈ rewrites) :
    RewriteValidationCertificate.Certificate language rewrite := by
  simp only [rewrites, List.mem_cons, List.mem_nil_iff, or_false] at membership
  rcases membership with rfl | rfl | rfl
  · exact RewriteValidationCertificate.certificate_of_check start_checked
  · exact RewriteValidationCertificate.certificate_of_check nil_checked
  · exact RewriteValidationCertificate.certificate_of_check cons_checked

private theorem rewrites_valid :
    ∀ rewrite ∈ rewrites, language.validateRewrite rewrite = [] := by
  intro rewrite membership
  simp only [rewrites, List.mem_cons, List.mem_nil_iff, or_false] at membership
  rcases membership with rfl | rfl | rfl
  · exact RewriteValidationCertificate.validateRewrite_eq_nil_of_check
      (LanguageDef.constructorLabels_nodup_of_validate_eq_nil
        signatureLanguage signatureLanguage_validate) start_checked
  · exact RewriteValidationCertificate.validateRewrite_eq_nil_of_check
      (LanguageDef.constructorLabels_nodup_of_validate_eq_nil
        signatureLanguage signatureLanguage_validate) nil_checked
  · exact RewriteValidationCertificate.validateRewrite_eq_nil_of_check
      (LanguageDef.constructorLabels_nodup_of_validate_eq_nil
        signatureLanguage signatureLanguage_validate) cons_checked

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

def validated : ValidatedLanguageDef := ⟨language, language_validate⟩

def targetInclusion :
    StructuralMorphism TptpFofClausificationBatchLanguageDef.validated
      validated where
  symbols := LanguageDefSymbolMap.id
  mapsTypes declaration membership := by
    rw [mapTypeDecl_id]
    exact List.mem_append_left _ membership
  mapsTerms declaration membership := by
    rw [mapGrammarRule_id]
    exact List.mem_append_left _ membership
  mapsEquations declaration membership := by
    change declaration ∈
      TptpFofClausificationBatchLanguageDef.language.equations at membership
    simp [TptpFofClausificationBatchLanguageDef.no_equations] at membership
  mapsRewrites declaration membership := by
    change declaration ∈
      TptpFofClausificationBatchLanguageDef.language.rewrites at membership
    simp [TptpFofClausificationBatchLanguageDef.no_rewrites] at membership

namespace Canary

theorem cons_rule_is_present : consRule ∈ rewrites := by
  simp [rewrites]

theorem cons_rule_is_absent_after_deletion :
    consRule ∉ [startRule, nilRule] := by
  intro membership
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at membership
  rcases membership with equality | equality
  · have names := congrArg RewriteRule.name equality
    simp [consRule, startRule, mkRule] at names
  · have names := congrArg RewriteRule.name equality
    simp [consRule, nilRule, mkRule] at names

theorem no_role_or_name_constructor :
    "tptp-fof-batch-gen:role" ∉ addedTerms.map (·.label) ∧
    "tptp-fof-batch-gen:formula-name" ∉ addedTerms.map (·.label) := by
  simp [addedTerms, ctor]

end Canary

#print axioms language_validate
#print axioms targetInclusion
#print axioms rewrite_certificate
#print axioms start_schemaNames_exact
#print axioms nil_schemaNames_exact
#print axioms cons_schemaNames_exact
#print axioms rewrite_names_nodup
#print axioms constructorLabels_namespaced
#print axioms Canary.cons_rule_is_present
#print axioms Canary.cons_rule_is_absent_after_deletion
#print axioms Canary.no_role_or_name_constructor

end Mettapedia.GSLT.LanguageDef.TptpFofClausificationBatchGenerationLanguageDef
