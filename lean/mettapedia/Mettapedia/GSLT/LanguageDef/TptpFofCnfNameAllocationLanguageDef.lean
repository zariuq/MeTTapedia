import Mettapedia.GSLT.LanguageDef.TptpFofCnfAllocatedBatchLanguageDef
import Mettapedia.GSLT.LanguageDef.RewriteValidationCertificate
import Mettapedia.GSLT.LanguageDef.StructuralCategory
import Mettapedia.GSLT.LanguageDef.ConstructorSignatureExtension

/-!
# Authored fresh-name allocation for source-indexed CNF batches

Three rewrites thread a fresh natural-name frontier through one complete batch.
The source batch remains an exact subterm of the result.  Each source clause
identity is paired with the current frontier, the frontier advances once, and
the recursive result supplies the next unused name.

This is allocation, not TPTP rendering.  Mapping the abstract allocated names
to official name tokens and concrete text is a separate transformation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpFofCnfNameAllocationLanguageDef

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

def request (batch firstName : Pattern) : Pattern :=
  a "tptp-fof-cnf-name-allocation:request" [batch, firstName]

def allocateEntries (entries firstName : Pattern) : Pattern :=
  a "tptp-fof-cnf-name-allocation:entries" [entries, firstName]

def addedTypes : List TypeDecl := ["TptpFofCnfNameAllocation:Request"]

def addedTerms : List GrammarRule := [
  ctor "tptp-fof-cnf-name-allocation:request"
    "TptpFofCnfNameAllocation:Request"
    [("batch", "TptpFofBatch:Output"),
     ("first-name", "TptpResolvedFof:Index")],
  ctor "tptp-fof-cnf-name-allocation:entries"
    "TptpFofCnfAllocated:AllocationResult"
    [("entries", "TptpFofBatch:ClauseEntries"),
     ("first-name", "TptpResolvedFof:Index")]
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

def batchOutput (occurrence polarity skolem cnf entries : Pattern) : Pattern :=
  a "tptp-fof-batch:output"
    [occurrence, polarity, skolem, cnf, entries]

def batchEntriesNil : Pattern :=
  a "tptp-fof-batch:entries-nil"

def batchEntriesCons (head tail : Pattern) : Pattern :=
  a "tptp-fof-batch:entries-cons" [head, tail]

def batchClauseEntry (identity clause : Pattern) : Pattern :=
  a "tptp-fof-batch:clause-entry" [identity, clause]

def startRule : RewriteRule :=
  mkRule "tptp-fof-cnf-name-allocation:start" [
      ("occurrence", "TptpFofBatch:Occurrence"),
      ("polarity", "TptpFofBatch:Polarity"),
      ("skolem", "TptpFofSkolem:Output"),
      ("cnf", "TptpFofCnf:Output"),
      ("entries", "TptpFofBatch:ClauseEntries"),
      ("first-name", "TptpResolvedFof:Index"),
      ("next-name", "TptpResolvedFof:Index"),
      ("allocated", "TptpFofCnfAllocated:ClauseEntries")]
    [congruence
      (allocateEntries (v "entries") (v "first-name"))
      (TptpFofCnfAllocatedBatchLanguageDef.allocationResult
        (v "next-name") (v "allocated"))]
    (request
      (batchOutput (v "occurrence") (v "polarity") (v "skolem")
        (v "cnf") (v "entries"))
      (v "first-name"))
    (TptpFofCnfAllocatedBatchLanguageDef.allocatedOutput
      (batchOutput (v "occurrence") (v "polarity") (v "skolem")
        (v "cnf") (v "entries"))
      (v "first-name") (v "next-name") (v "allocated"))

def nilRule : RewriteRule :=
  mkRule "tptp-fof-cnf-name-allocation:entries-nil" [
      ("first-name", "TptpResolvedFof:Index")]
    []
    (allocateEntries batchEntriesNil (v "first-name"))
    (TptpFofCnfAllocatedBatchLanguageDef.allocationResult
      (v "first-name") TptpFofCnfAllocatedBatchLanguageDef.entriesNil)

def consRule : RewriteRule :=
  mkRule "tptp-fof-cnf-name-allocation:entries-cons" [
      ("identity", "TptpFofBatch:ClauseId"),
      ("clause", "TptpFofCnf:Clause"),
      ("rest", "TptpFofBatch:ClauseEntries"),
      ("first-name", "TptpResolvedFof:Index"),
      ("next-name", "TptpResolvedFof:Index"),
      ("allocated-rest", "TptpFofCnfAllocated:ClauseEntries")]
    [congruence
      (allocateEntries (v "rest")
        (a "tptp-fof-resolved:index-succ" [v "first-name"]))
      (TptpFofCnfAllocatedBatchLanguageDef.allocationResult
        (v "next-name") (v "allocated-rest"))]
    (allocateEntries
      (batchEntriesCons
        (batchClauseEntry (v "identity") (v "clause")) (v "rest"))
      (v "first-name"))
    (TptpFofCnfAllocatedBatchLanguageDef.allocationResult
      (v "next-name")
      (TptpFofCnfAllocatedBatchLanguageDef.entriesCons
        (a "tptp-fof-cnf-allocated:clause-entry" [
          v "identity",
          a "tptp-fof-cnf-allocated:name" [v "first-name"],
          v "clause"])
        (v "allocated-rest")))

def rewrites : List RewriteRule := [startRule, nilRule, consRule]

private def signatureBase : CalculusLanguageDef :=
  CalculusLanguageDef.extend
    TptpFofCnfAllocatedBatchLanguageDef.language {}

private def signatureExtension : CalculusLanguageExtension :=
  ConstructorSignatureExtension.ofLists addedTypes addedTerms
    (some "TptpFofCnfNameAllocationV1")

private def signatureCalculusLanguage : CalculusLanguageDef :=
  signatureExtension.apply signatureBase

def signatureLanguage : LanguageDef :=
  signatureCalculusLanguage.toLanguageDef

private theorem added_type_names_nodup :
    (addedTypes.map (·.name)).Nodup := by decide

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
    (addedTerms.map (·.label)).Nodup := by decide

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
      (some "TptpFofCnfNameAllocationV1")
  · simpa [signatureBase] using
      TptpFofCnfAllocatedBatchLanguageDef.language_validate
  · rfl
  · rfl
  · exact added_type_names_nodup
  · exact added_type_names_disjoint
  · exact added_term_labels_nodup
  · exact added_term_labels_disjoint
  · exact added_terms_valid

def language : LanguageDef := {
  name := "TptpFofCnfNameAllocation"
  types := signatureLanguage.types
  terms := signatureLanguage.terms
  equations := []
  rewrites
}

@[simp] theorem language_rewrites : language.rewrites = rewrites := rfl

theorem typeNames_exact : language.typeNames =
    TptpFofCnfAllocatedBatchLanguageDef.language.typeNames ++
      ["TptpFofCnfNameAllocation:Request"] := by
  simp [language, signatureLanguage, signatureCalculusLanguage,
    signatureExtension, signatureBase,
    ConstructorSignatureExtension.ofLists, LanguageDef.typeNames, addedTypes,
    TypeDecl.plain]

theorem constructorSignatures_exact :
    RewriteValidationCertificate.constructorSignatures language =
      RewriteValidationCertificate.constructorSignatures
        TptpFofCnfAllocatedBatchLanguageDef.language ++ [
        ("tptp-fof-cnf-name-allocation:request", 2),
        ("tptp-fof-cnf-name-allocation:entries", 2)] := by
  simp [RewriteValidationCertificate.constructorSignatures, language,
    signatureLanguage, signatureCalculusLanguage, signatureExtension,
    signatureBase, ConstructorSignatureExtension.ofLists, addedTerms, ctor]

theorem constructorLabels_exact :
    RewriteValidationCertificate.constructorLabels language =
      RewriteValidationCertificate.constructorLabels
        TptpFofCnfAllocatedBatchLanguageDef.language ++ [
        "tptp-fof-cnf-name-allocation:request",
        "tptp-fof-cnf-name-allocation:entries"] := by
  simp [RewriteValidationCertificate.constructorLabels, language,
    signatureLanguage, signatureCalculusLanguage, signatureExtension,
    signatureBase, ConstructorSignatureExtension.ofLists, addedTerms, ctor]

def constructorLabelNamespaced (label : String) : Bool :=
  label.startsWith "tptp-fof-"

theorem constructorLabels_namespaced :
    (RewriteValidationCertificate.constructorLabels language).all
      constructorLabelNamespaced = true := by
  rw [constructorLabels_exact]
  simp [constructorLabelNamespaced,
    TptpFofCnfAllocatedBatchLanguageDef.constructorLabels_exact,
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
  "TptpResolvedFof:Index", "TptpFofCnf:Clause",
  "TptpFofSkolem:Output", "TptpFofCnf:Output",
  "TptpFofBatch:Occurrence", "TptpFofBatch:Polarity",
  "TptpFofBatch:ClauseId", "TptpFofBatch:ClauseEntries",
  "TptpFofBatch:Output", "TptpFofCnfAllocated:Name",
  "TptpFofCnfAllocated:ClauseEntry",
  "TptpFofCnfAllocated:ClauseEntries",
  "TptpFofCnfAllocated:AllocationResult",
  "TptpFofCnfAllocated:Output", "TptpFofCnfNameAllocation:Request"]

private theorem requiredTypes_declared :
    requiredTypes.all (fun name => decide (name ∈ language.typeNames)) = true := by
  rw [typeNames_exact]
  simp [requiredTypes,
    TptpFofCnfAllocatedBatchLanguageDef.typeNames_exact,
    TptpFofClausificationBatchLanguageDef.typeNames_exact,
    TptpFofDefinitionalCnfLanguageDef.typeNames_exact,
    TptpFofSkolemLanguageDef.typeNames_exact]

@[simp] private theorem requiredType_declared (name : String)
    (membership : name ∈ requiredTypes) : name ∈ language.typeNames :=
  decide_eq_true_eq.mp
    (List.all_eq_true.mp requiredTypes_declared name membership)

private def requiredSignatures : List (String × Nat) := [
  ("tptp-fof-resolved:index-succ", 1),
  ("tptp-fof-batch:clause-entry", 2),
  ("tptp-fof-batch:entries-nil", 0),
  ("tptp-fof-batch:entries-cons", 2),
  ("tptp-fof-batch:output", 5),
  ("tptp-fof-cnf-allocated:name", 1),
  ("tptp-fof-cnf-allocated:clause-entry", 3),
  ("tptp-fof-cnf-allocated:entries-nil", 0),
  ("tptp-fof-cnf-allocated:entries-cons", 2),
  ("tptp-fof-cnf-allocated:allocation-result", 2),
  ("tptp-fof-cnf-allocated:output", 4),
  ("tptp-fof-cnf-name-allocation:request", 2),
  ("tptp-fof-cnf-name-allocation:entries", 2)]

private theorem requiredSignatures_declared :
    requiredSignatures.all (fun signature => decide
      (signature ∈ RewriteValidationCertificate.constructorSignatures
        language)) = true := by
  rw [constructorSignatures_exact]
  simp [requiredSignatures,
    TptpFofCnfAllocatedBatchLanguageDef.constructorSignatures_exact,
    TptpFofClausificationBatchLanguageDef.constructorSignatures_exact,
    TptpFofDefinitionalCnfLanguageDef.constructorSignatures_exact,
    TptpFofSkolemLanguageDef.constructorSignatures_exact]

@[simp] private theorem requiredSignature_declared
    (signature : String × Nat) (membership : signature ∈ requiredSignatures) :
    signature ∈ RewriteValidationCertificate.constructorSignatures language :=
  decide_eq_true_eq.mp
    (List.all_eq_true.mp requiredSignatures_declared signature membership)

local macro "certify_name_allocation_row" : tactic =>
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
      allocateEntries, batchOutput, batchEntriesNil, batchEntriesCons,
      batchClauseEntry, mkRule, congruence, a, v,
      TptpFofCnfAllocatedBatchLanguageDef.a,
      TptpFofCnfAllocatedBatchLanguageDef.allocationResult,
      TptpFofCnfAllocatedBatchLanguageDef.allocatedOutput,
      TptpFofCnfAllocatedBatchLanguageDef.entriesNil,
      TptpFofCnfAllocatedBatchLanguageDef.entriesCons,
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
    "tptp-fof-cnf-name-allocation:start",
    "tptp-fof-cnf-name-allocation:entries-nil",
    "tptp-fof-cnf-name-allocation:entries-cons"] := by
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
  certify_name_allocation_row
private theorem start_leftDeclared :
    RewriteValidationCertificate.patternDeclaredCheck language
      startRule.left = true := by
  certify_name_allocation_row
private theorem start_rightDeclared :
    RewriteValidationCertificate.patternDeclaredCheck language
      startRule.right = true := by
  certify_name_allocation_row
private theorem start_premisesDeclared :
    RewriteValidationCertificate.premisesDeclaredCheck language startRule =
      true := by
  certify_name_allocation_row
private theorem start_allPatternsScoped :
    RewriteValidationCertificate.allPatternsScopedCheck startRule = true := by
  certify_name_allocation_row
private theorem start_fvarsAvoidConstructors :
    RewriteValidationCertificate.fvarsAvoidConstructorsCheck language
      startRule = true := by
  certify_name_allocation_row
private theorem start_bindersAvoidConstructors :
    RewriteValidationCertificate.bindersAvoidConstructorsCheck language
      startRule = true := by
  certify_name_allocation_row
private theorem start_contextAvoidsConstructors :
    RewriteValidationCertificate.contextAvoidsConstructorsCheck language
      startRule = true := by
  certify_name_allocation_row
private theorem start_rightBound :
    RewriteValidationCertificate.rightBoundCheck startRule = true := by
  certify_name_allocation_row

private theorem start_checked :
    RewriteValidationCertificate.check language startRule = true := by
  exact check_of_component_checks startRule start_contextTypes
    start_leftDeclared start_rightDeclared start_premisesDeclared
    start_allPatternsScoped start_fvarsAvoidConstructors
    start_bindersAvoidConstructors start_contextAvoidsConstructors
    start_rightBound

private theorem nil_checked :
    RewriteValidationCertificate.check language nilRule = true := by
  certify_name_allocation_row

private theorem cons_contextTypes :
    RewriteValidationCertificate.contextTypesCheck language consRule = true := by
  certify_name_allocation_row
private theorem cons_leftDeclared :
    RewriteValidationCertificate.patternDeclaredCheck language consRule.left =
      true := by
  certify_name_allocation_row
private theorem cons_rightDeclared :
    RewriteValidationCertificate.patternDeclaredCheck language consRule.right =
      true := by
  certify_name_allocation_row
private theorem cons_premisesDeclared :
    RewriteValidationCertificate.premisesDeclaredCheck language consRule =
      true := by
  certify_name_allocation_row
private theorem cons_allPatternsScoped :
    RewriteValidationCertificate.allPatternsScopedCheck consRule = true := by
  certify_name_allocation_row
private theorem cons_fvarsAvoidConstructors :
    RewriteValidationCertificate.fvarsAvoidConstructorsCheck language
      consRule = true := by
  certify_name_allocation_row
private theorem cons_bindersAvoidConstructors :
    RewriteValidationCertificate.bindersAvoidConstructorsCheck language
      consRule = true := by
  certify_name_allocation_row
private theorem cons_contextAvoidsConstructors :
    RewriteValidationCertificate.contextAvoidsConstructorsCheck language
      consRule = true := by
  certify_name_allocation_row
private theorem cons_rightBound :
    RewriteValidationCertificate.rightBoundCheck consRule = true := by
  certify_name_allocation_row

private theorem cons_checked :
    RewriteValidationCertificate.check language consRule = true := by
  exact check_of_component_checks consRule cons_contextTypes cons_leftDeclared
    cons_rightDeclared cons_premisesDeclared cons_allPatternsScoped
    cons_fvarsAvoidConstructors cons_bindersAvoidConstructors
    cons_contextAvoidsConstructors cons_rightBound

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
    StructuralMorphism TptpFofCnfAllocatedBatchLanguageDef.validated
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
      TptpFofCnfAllocatedBatchLanguageDef.language.equations at membership
    simp [TptpFofCnfAllocatedBatchLanguageDef.no_equations] at membership
  mapsRewrites declaration membership := by
    change declaration ∈
      TptpFofCnfAllocatedBatchLanguageDef.language.rewrites at membership
    simp [TptpFofCnfAllocatedBatchLanguageDef.no_rewrites] at membership

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

end Canary

#print axioms language_validate
#print axioms targetInclusion
#print axioms Canary.cons_rule_is_present
#print axioms Canary.cons_rule_is_absent_after_deletion

end Mettapedia.GSLT.LanguageDef.TptpFofCnfNameAllocationLanguageDef
