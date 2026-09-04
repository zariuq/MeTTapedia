import Mettapedia.GSLT.LanguageDef.TptpFofDefinitionalCnfLanguageDef
import Mettapedia.GSLT.LanguageDef.ConstructorSignatureExtension
import Mettapedia.GSLT.LanguageDef.CarrierWellSorted
import Mettapedia.GSLT.LanguageDef.CanonicalWire
import Mettapedia.GSLT.LanguageDef.TotalGSLT
import Mettapedia.GSLT.LanguageDef.RewriteValidationCertificate

/-!
# Source-indexed FOF clausification batches

Clausification turns one source formula into an ordered family of clauses and
introduces both Skolem functions and definitional predicates.  This carrier
keeps that result as one source-indexed batch.  It extends the existing
evidence-bearing CNF carrier and does not copy the official TPTP document,
formula name, role, annotations, or source span.  Those remain authoritative
in the source document and are joined to a batch through its occurrence key.

The batch records:

* the source occurrence key and explicit positive/negative polarity;
* the complete Skolem output, including its fresh-function ledger;
* the complete definitional-CNF output, including its definition and
  fresh-predicate ledgers; and
* one stable local identity per generated clause, in exact clause order.

The carrier is inert.  Role policy, concrete fresh names, serialization, and
proof search are separate transformations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpFofClausificationBatchLanguageDef

open LO FirstOrder
open scoped LO.FirstOrder
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.CalculusLanguageExtension
open Mettapedia.GSLT.LanguageDef.CarrierWellSorted
open Mettapedia.GSLT.LanguageDef.TotalGSLT
open Mettapedia.OSLF.Framework.TypeSynthesis

private def ctor (label category : String)
    (parameters : List (String × String)) : GrammarRule := {
  label
  category
  params := parameters.map fun parameter =>
    .simple parameter.1 (.base parameter.2)
  syntaxPattern := []
  evalPolicy? := none
}

private def a (label : String) (arguments : List Pattern := []) : Pattern :=
  .apply label arguments

def addedTypes : List TypeDecl := [
  { name := "Integer", carrier := .builtinInt },
  "TptpFofBatch:Occurrence",
  "TptpFofBatch:Polarity",
  "TptpFofBatch:ClauseId",
  "TptpFofBatch:ClauseEntry",
  "TptpFofBatch:ClauseEntries",
  "TptpFofBatch:Output"]

def addedTerms : List GrammarRule := [
  ctor "tptp-fof-batch:occurrence" "TptpFofBatch:Occurrence"
    [("source-digest", "String"), ("index", "Integer")],
  ctor "tptp-fof-batch:positive" "TptpFofBatch:Polarity" [],
  ctor "tptp-fof-batch:negative" "TptpFofBatch:Polarity" [],
  ctor "tptp-fof-batch:clause-id" "TptpFofBatch:ClauseId"
    [("occurrence", "TptpFofBatch:Occurrence"),
     ("local-index", "TptpResolvedFof:Index")],
  ctor "tptp-fof-batch:clause-entry" "TptpFofBatch:ClauseEntry"
    [("identity", "TptpFofBatch:ClauseId"),
     ("clause", "TptpFofCnf:Clause")],
  ctor "tptp-fof-batch:entries-nil" "TptpFofBatch:ClauseEntries" [],
  ctor "tptp-fof-batch:entries-cons" "TptpFofBatch:ClauseEntries"
    [("head", "TptpFofBatch:ClauseEntry"),
     ("tail", "TptpFofBatch:ClauseEntries")],
  ctor "tptp-fof-batch:output" "TptpFofBatch:Output"
    [("occurrence", "TptpFofBatch:Occurrence"),
     ("polarity", "TptpFofBatch:Polarity"),
     ("skolem", "TptpFofSkolem:Output"),
     ("cnf", "TptpFofCnf:Output"),
     ("entries", "TptpFofBatch:ClauseEntries")]
]

private def base : CalculusLanguageDef :=
  CalculusLanguageDef.extend
    TptpFofDefinitionalCnfLanguageDef.language {}

def extension : CalculusLanguageExtension :=
  ConstructorSignatureExtension.ofLists addedTypes addedTerms
    (some "TptpFofClausificationBatchV1")

def calculusLanguage : CalculusLanguageDef := extension.apply base

def language : LanguageDef := calculusLanguage.toLanguageDef

@[simp] theorem typeNames_exact : language.typeNames =
    TptpFofDefinitionalCnfLanguageDef.language.typeNames ++ [
      "Integer", "TptpFofBatch:Occurrence", "TptpFofBatch:Polarity",
      "TptpFofBatch:ClauseId", "TptpFofBatch:ClauseEntry",
      "TptpFofBatch:ClauseEntries", "TptpFofBatch:Output"] := by
  simp [language, calculusLanguage, extension, base,
    ConstructorSignatureExtension.ofLists, LanguageDef.typeNames, addedTypes,
    TypeDecl.plain]

@[simp] theorem constructorSignatures_exact :
    RewriteValidationCertificate.constructorSignatures language =
      RewriteValidationCertificate.constructorSignatures
        TptpFofDefinitionalCnfLanguageDef.language ++ [
        ("tptp-fof-batch:occurrence", 2),
        ("tptp-fof-batch:positive", 0),
        ("tptp-fof-batch:negative", 0),
        ("tptp-fof-batch:clause-id", 2),
        ("tptp-fof-batch:clause-entry", 2),
        ("tptp-fof-batch:entries-nil", 0),
        ("tptp-fof-batch:entries-cons", 2),
        ("tptp-fof-batch:output", 5)] := by
  simp [RewriteValidationCertificate.constructorSignatures, language,
    calculusLanguage, extension, base, ConstructorSignatureExtension.ofLists,
    addedTerms, ctor]

@[simp] theorem constructorLabels_exact :
    RewriteValidationCertificate.constructorLabels language =
      RewriteValidationCertificate.constructorLabels
        TptpFofDefinitionalCnfLanguageDef.language ++ [
        "tptp-fof-batch:occurrence", "tptp-fof-batch:positive",
        "tptp-fof-batch:negative", "tptp-fof-batch:clause-id",
        "tptp-fof-batch:clause-entry", "tptp-fof-batch:entries-nil",
        "tptp-fof-batch:entries-cons", "tptp-fof-batch:output"] := by
  simp [RewriteValidationCertificate.constructorLabels, language,
    calculusLanguage, extension, base, ConstructorSignatureExtension.ofLists,
    addedTerms, ctor]

theorem extension_disjoint : extension.disjointFrom base = true := by
  decide +kernel

theorem appendOnly : AppendOnlyCalculusRefinement base calculusLanguage :=
  extension.apply_appendOnly base

private theorem added_type_names_nodup :
    (addedTypes.map (·.name)).Nodup := by
  decide +kernel

private theorem added_type_names_absent :
    addedTypes.all (fun declaration =>
      !(base.types.any fun existing => existing.name == declaration.name)) =
        true := by
  decide +kernel

private theorem added_type_names_disjoint :
    List.Disjoint base.toLanguageDef.typeNames (addedTypes.map (·.name)) := by
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
  decide +kernel

private theorem added_term_labels_absent :
    addedTerms.all (fun declaration =>
      !(base.terms.any fun existing => existing.label == declaration.label)) =
        true := by
  decide +kernel

private theorem added_term_labels_disjoint :
    List.Disjoint (base.terms.map (·.label)) (addedTerms.map (·.label)) := by
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
    addedTerms.all (fun term => language.validateTerm term == []) = true := by
  decide +kernel

private theorem added_terms_valid (term : GrammarRule)
    (membership : term ∈ addedTerms) : language.validateTerm term = [] := by
  have checked :=
    (List.all_eq_true.mp added_terms_validate_all) term membership
  simpa using checked

theorem language_validate : language.validate = [] := by
  apply ConstructorSignatureExtension.apply_language_validate
    base addedTypes addedTerms (some "TptpFofClausificationBatchV1")
  · simpa [base] using
      TptpFofDefinitionalCnfLanguageDef.language_validate
  · rfl
  · rfl
  · exact added_type_names_nodup
  · exact added_type_names_disjoint
  · exact added_term_labels_nodup
  · exact added_term_labels_disjoint
  · exact added_terms_valid

def validated : ValidatedLanguageDef := ⟨language, language_validate⟩

def cnfInclusion :
    StructuralMorphism TptpFofDefinitionalCnfLanguageDef.validated validated where
  symbols := LanguageDefSymbolMap.id
  mapsTypes declaration membership := by
    rw [mapTypeDecl_id]
    exact List.mem_append_left _ membership
  mapsTerms declaration membership := by
    rw [mapGrammarRule_id]
    exact List.mem_append_left _ membership
  mapsEquations declaration membership := by
    change declaration ∈
      TptpFofDefinitionalCnfLanguageDef.language.equations at membership
    simp [TptpFofDefinitionalCnfLanguageDef.no_equations] at membership
  mapsRewrites declaration membership := by
    change declaration ∈
      TptpFofDefinitionalCnfLanguageDef.language.rewrites at membership
    simp [TptpFofDefinitionalCnfLanguageDef.no_rewrites] at membership

theorem every_constructor_is_inert :
    language.terms.all (fun term => term.evalPolicy? = none) = true := by
  decide +kernel

theorem no_equations : language.equations = [] := rfl
theorem no_rewrites : language.rewrites = [] := rfl

def theory : Mettapedia.GSLT.GSLT :=
  languageGSLT language (ReductionRespectsEquations.of_equation_free rfl)

theorem theory_no_step (source target : Pattern) :
    Not (theory.Step source target) := by
  intro reduction
  unfold theory at reduction
  rw [languageGSLT_step] at reduction
  unfold langReducesUsing at reduction
  rcases reduction with ⟨_, step⟩
  cases step with
  | rule ruleMember => simp [language, calculusLanguage, extension, base,
      ConstructorSignatureExtension.ofLists,
      TptpFofDefinitionalCnfLanguageDef.no_rewrites] at ruleMember

/-! ## Source keys and exact clause identities -/

structure SourceOccurrence where
  sourceDigest : String
  indexLexeme : String
  deriving DecidableEq, Repr

def encodeString (value : String) : Pattern := a value

def encodeOccurrence (occurrence : SourceOccurrence) : Pattern :=
  a "tptp-fof-batch:occurrence"
    [encodeString occurrence.sourceDigest, encodeString occurrence.indexLexeme]

def encodePolarity (polarity : Bool) : Pattern :=
  if polarity then a "tptp-fof-batch:positive"
  else a "tptp-fof-batch:negative"

def encodeClauseId (occurrence : SourceOccurrence) (localIndex : Nat) : Pattern :=
  a "tptp-fof-batch:clause-id"
    [encodeOccurrence occurrence,
     TptpResolvedFofLanguageDef.encodeNatIndex localIndex]

noncomputable def encodeClauseEntry {depth : Nat}
    (occurrence : SourceOccurrence) (localIndex : Nat)
    (clause : TptpFofDefinitionalCnfSemantics.Clause depth) : Pattern :=
  a "tptp-fof-batch:clause-entry"
    [encodeClauseId occurrence localIndex,
     TptpFofDefinitionalCnfLanguageDef.encodeClause clause]

noncomputable def encodeClauseEntriesFrom {depth : Nat}
    (occurrence : SourceOccurrence) :
    Nat → List (TptpFofDefinitionalCnfSemantics.Clause depth) → Pattern
  | _, [] => a "tptp-fof-batch:entries-nil"
  | localIndex, clause :: clauses =>
      a "tptp-fof-batch:entries-cons"
        [encodeClauseEntry occurrence localIndex clause,
         encodeClauseEntriesFrom occurrence (localIndex + 1) clauses]

noncomputable def encodeClauseEntries {depth : Nat}
    (occurrence : SourceOccurrence)
    (clauses : List (TptpFofDefinitionalCnfSemantics.Clause depth)) : Pattern :=
  encodeClauseEntriesFrom occurrence 0 clauses

structure EncodedClauseEntry where
  identity : Pattern
  clause : Pattern
  deriving DecidableEq, Repr

noncomputable def encodedClauseEntriesFrom {depth : Nat}
    (occurrence : SourceOccurrence) :
    Nat → List (TptpFofDefinitionalCnfSemantics.Clause depth) →
      List EncodedClauseEntry
  | _, [] => []
  | localIndex, clause :: clauses =>
      ⟨encodeClauseId occurrence localIndex,
        TptpFofDefinitionalCnfLanguageDef.encodeClause clause⟩ ::
      encodedClauseEntriesFrom occurrence (localIndex + 1) clauses

def decodeClauseEntries? : Pattern → Option (List EncodedClauseEntry)
  | .apply "tptp-fof-batch:entries-nil" [] => some []
  | .apply "tptp-fof-batch:entries-cons"
      [.apply "tptp-fof-batch:clause-entry" [identity, clause], rest] => do
      let decodedRest ← decodeClauseEntries? rest
      some (⟨identity, clause⟩ :: decodedRest)
  | _ => none

theorem decode_encodeClauseEntriesFrom (occurrence : SourceOccurrence)
    (localIndex : Nat) {depth : Nat}
    (clauses : List (TptpFofDefinitionalCnfSemantics.Clause depth)) :
    decodeClauseEntries?
        (encodeClauseEntriesFrom occurrence localIndex clauses) =
      some (encodedClauseEntriesFrom occurrence localIndex clauses) := by
  induction clauses generalizing localIndex with
  | nil => rfl
  | cons clause clauses inductionHypothesis =>
      simp only [encodeClauseEntriesFrom, encodeClauseEntry, a,
        decodeClauseEntries?, encodedClauseEntriesFrom]
      rw [inductionHypothesis]
      rfl

theorem encodedClauseEntriesFrom_length (occurrence : SourceOccurrence)
    (localIndex : Nat) {depth : Nat}
    (clauses : List (TptpFofDefinitionalCnfSemantics.Clause depth)) :
    (encodedClauseEntriesFrom occurrence localIndex clauses).length =
      clauses.length := by
  induction clauses generalizing localIndex with
  | nil => rfl
  | cons clause clauses inductionHypothesis =>
      simp [encodedClauseEntriesFrom, inductionHypothesis]

def decodeNatIndex? : Pattern → Option Nat
  | .apply "tptp-fof-resolved:index-zero" [] => some 0
  | .apply "tptp-fof-resolved:index-succ" [predecessor] => do
      let index ← decodeNatIndex? predecessor
      some (index + 1)
  | _ => none

theorem decode_encodeNatIndex (index : Nat) :
    decodeNatIndex? (TptpResolvedFofLanguageDef.encodeNatIndex index) =
      some index := by
  induction index with
  | zero => rfl
  | succ index inductionHypothesis =>
      change decodeNatIndex?
        (.apply "tptp-fof-resolved:index-succ"
          [TptpResolvedFofLanguageDef.encodeNatIndex index]) =
        some (index + 1)
      simp [decodeNatIndex?, inductionHypothesis]

theorem encodeNatIndex_injective :
    Function.Injective TptpResolvedFofLanguageDef.encodeNatIndex := by
  intro left right equality
  have decoded := congrArg decodeNatIndex? equality
  simpa only [decode_encodeNatIndex, Option.some.injEq] using decoded

theorem clause_id_local_indices_nodup (occurrence : SourceOccurrence)
    (frontier : Nat) (count : Nat) :
    (List.range' frontier count |>.map (encodeClauseId occurrence)).Nodup := by
  apply List.Nodup.map
  · intro left right equality
    apply encodeNatIndex_injective
    simpa [encodeClauseId, encodeOccurrence, encodeString, a] using equality
  · exact List.nodup_range' (s := frontier) (n := count)

noncomputable def encodeOutput {depth : Nat} (occurrence : SourceOccurrence)
    (polarity : Bool)
    (skolem : TptpFofSkolemizationSemantics.Output 0)
    (skolemFree :
      TptpFofSkolemizationSemantics.ExistentialFree skolem.formula)
    (named : TptpFofDefinitionalNamingSemantics.Output depth)
    (quantifierFree : ∀ definition ∈ named.definitions,
      TptpFofDefinitionalNamingSemantics.QuantifierFree definition.source) :
    Pattern :=
  let clauses := TptpFofDefinitionalCnfSemantics.clausesForOutput named
  a "tptp-fof-batch:output"
    [encodeOccurrence occurrence,
     encodePolarity polarity,
     TptpFofSkolemLanguageDef.encodeOutput skolem skolemFree,
     TptpFofDefinitionalCnfLanguageDef.encodeCnfOutput named quantifierFree,
     encodeClauseEntries occurrence clauses]

/-! ## Positive and negative controls -/

namespace Canary

def occurrence : SourceOccurrence := ⟨"sha256-demo", "7"⟩

theorem polarity_is_load_bearing :
    encodePolarity true ≠ encodePolarity false := by
  decide

theorem two_clause_identities_are_distinct :
    encodeClauseId occurrence 0 ≠ encodeClauseId occurrence 1 := by
  decide

theorem malformed_entry_list_fails_closed :
    decodeClauseEntries?
      (a "tptp-fof-batch:entries-cons" [a "not-an-entry", a "tail"]) =
        none := by
  rfl

theorem empty_clause_entry_is_not_empty_entry_list :
    encodeClauseEntries occurrence
        (show List (TptpFofDefinitionalCnfSemantics.Clause 0) from [[]]) ≠
      encodeClauseEntries occurrence
        (show List (TptpFofDefinitionalCnfSemantics.Clause 0) from []) := by
  decide

end Canary

theorem language_supported : CanonicalWire.languageSupported language := by
  decide +kernel

theorem wire_isSome : (CanonicalWire.renderLanguage? language).isSome := by
  rw [CanonicalWire.renderLanguage?_isSome_eq_supported]
  exact language_supported

def wire : String := (CanonicalWire.renderLanguage? language).getD ""

def writeWire (path : System.FilePath) : IO Unit := IO.FS.writeFile path wire

#print axioms language_validate
#print axioms cnfInclusion
#print axioms theory_no_step
#print axioms decode_encodeClauseEntriesFrom
#print axioms encodedClauseEntriesFrom_length
#print axioms clause_id_local_indices_nodup
#print axioms Canary.polarity_is_load_bearing
#print axioms Canary.two_clause_identities_are_distinct
#print axioms Canary.malformed_entry_list_fails_closed
#print axioms Canary.empty_clause_entry_is_not_empty_entry_list

end Mettapedia.GSLT.LanguageDef.TptpFofClausificationBatchLanguageDef
