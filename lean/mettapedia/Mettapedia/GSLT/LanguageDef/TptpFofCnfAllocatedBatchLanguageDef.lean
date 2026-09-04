import Mettapedia.GSLT.LanguageDef.TptpFofClausificationBatchLanguageDef
import Mettapedia.GSLT.LanguageDef.ConstructorSignatureExtension
import Mettapedia.GSLT.LanguageDef.CarrierWellSorted
import Mettapedia.GSLT.LanguageDef.CanonicalWire
import Mettapedia.GSLT.LanguageDef.TotalGSLT
import Mettapedia.GSLT.LanguageDef.RewriteValidationCertificate

/-!
# Fresh-name allocation carrier for source-indexed CNF batches

This inert language is the boundary between clausification and concrete TPTP
serialization.  It preserves the complete source-indexed clausification batch
and adds a compact, document-local name allocation for every generated clause.

Allocated names are abstract natural indices at this boundary.  A later
serialization transformation maps them to canonical official TPTP names and
retains the identity-to-name rows for reconstruction of external TSTP parent
references.  Keeping allocation separate avoids encoding source digests into
external identifiers and makes freshness across several batches an explicit
state-threading property.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpFofCnfAllocatedBatchLanguageDef

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

def a (label : String) (arguments : List Pattern := []) : Pattern :=
  .apply label arguments

def addedTypes : List TypeDecl := [
  "TptpFofCnfAllocated:Name",
  "TptpFofCnfAllocated:ClauseEntry",
  "TptpFofCnfAllocated:ClauseEntries",
  "TptpFofCnfAllocated:AllocationResult",
  "TptpFofCnfAllocated:Output"]

def addedTerms : List GrammarRule := [
  ctor "tptp-fof-cnf-allocated:name" "TptpFofCnfAllocated:Name"
    [("index", "TptpResolvedFof:Index")],
  ctor "tptp-fof-cnf-allocated:clause-entry"
    "TptpFofCnfAllocated:ClauseEntry"
    [("identity", "TptpFofBatch:ClauseId"),
     ("name", "TptpFofCnfAllocated:Name"),
     ("clause", "TptpFofCnf:Clause")],
  ctor "tptp-fof-cnf-allocated:entries-nil"
    "TptpFofCnfAllocated:ClauseEntries" [],
  ctor "tptp-fof-cnf-allocated:entries-cons"
    "TptpFofCnfAllocated:ClauseEntries"
    [("head", "TptpFofCnfAllocated:ClauseEntry"),
     ("tail", "TptpFofCnfAllocated:ClauseEntries")],
  ctor "tptp-fof-cnf-allocated:allocation-result"
    "TptpFofCnfAllocated:AllocationResult"
    [("next", "TptpResolvedFof:Index"),
     ("entries", "TptpFofCnfAllocated:ClauseEntries")],
  ctor "tptp-fof-cnf-allocated:output" "TptpFofCnfAllocated:Output"
    [("batch", "TptpFofBatch:Output"),
     ("first-name", "TptpResolvedFof:Index"),
     ("next-name", "TptpResolvedFof:Index"),
     ("entries", "TptpFofCnfAllocated:ClauseEntries")]
]

private def base : CalculusLanguageDef :=
  CalculusLanguageDef.extend
    TptpFofClausificationBatchLanguageDef.language {}

def extension : CalculusLanguageExtension :=
  ConstructorSignatureExtension.ofLists addedTypes addedTerms
    (some "TptpFofCnfAllocatedBatchV1")

def calculusLanguage : CalculusLanguageDef := extension.apply base

def language : LanguageDef := calculusLanguage.toLanguageDef

@[simp] theorem typeNames_exact : language.typeNames =
    TptpFofClausificationBatchLanguageDef.language.typeNames ++ [
      "TptpFofCnfAllocated:Name",
      "TptpFofCnfAllocated:ClauseEntry",
      "TptpFofCnfAllocated:ClauseEntries",
      "TptpFofCnfAllocated:AllocationResult",
      "TptpFofCnfAllocated:Output"] := by
  simp [language, calculusLanguage, extension, base,
    ConstructorSignatureExtension.ofLists, LanguageDef.typeNames, addedTypes,
    TypeDecl.plain]

@[simp] theorem constructorSignatures_exact :
    RewriteValidationCertificate.constructorSignatures language =
      RewriteValidationCertificate.constructorSignatures
        TptpFofClausificationBatchLanguageDef.language ++ [
        ("tptp-fof-cnf-allocated:name", 1),
        ("tptp-fof-cnf-allocated:clause-entry", 3),
        ("tptp-fof-cnf-allocated:entries-nil", 0),
        ("tptp-fof-cnf-allocated:entries-cons", 2),
        ("tptp-fof-cnf-allocated:allocation-result", 2),
        ("tptp-fof-cnf-allocated:output", 4)] := by
  simp [RewriteValidationCertificate.constructorSignatures, language,
    calculusLanguage, extension, base, ConstructorSignatureExtension.ofLists,
    addedTerms, ctor]

@[simp] theorem constructorLabels_exact :
    RewriteValidationCertificate.constructorLabels language =
      RewriteValidationCertificate.constructorLabels
        TptpFofClausificationBatchLanguageDef.language ++ [
        "tptp-fof-cnf-allocated:name",
        "tptp-fof-cnf-allocated:clause-entry",
        "tptp-fof-cnf-allocated:entries-nil",
        "tptp-fof-cnf-allocated:entries-cons",
        "tptp-fof-cnf-allocated:allocation-result",
        "tptp-fof-cnf-allocated:output"] := by
  simp [RewriteValidationCertificate.constructorLabels, language,
    calculusLanguage, extension, base, ConstructorSignatureExtension.ofLists,
    addedTerms, ctor]

theorem extension_disjoint : extension.disjointFrom base = true := by
  decide +kernel

theorem appendOnly : AppendOnlyCalculusRefinement base calculusLanguage :=
  extension.apply_appendOnly base

private theorem added_type_names_nodup :
    (addedTypes.map (·.name)).Nodup := by
  decide

private theorem added_type_names_absent :
    addedTypes.all (fun declaration =>
      !(base.types.any fun existing =>
        existing.name == declaration.name)) = true := by
  decide +kernel

private theorem added_type_names_disjoint :
    List.Disjoint base.toLanguageDef.typeNames
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
      !(base.terms.any fun existing =>
        existing.label == declaration.label)) = true := by
  decide +kernel

private theorem added_term_labels_disjoint :
    List.Disjoint (base.terms.map (·.label))
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
    addedTerms.all (fun term => language.validateTerm term == []) = true := by
  decide +kernel

private theorem added_terms_valid (term : GrammarRule)
    (membership : term ∈ addedTerms) : language.validateTerm term = [] := by
  have checked :=
    (List.all_eq_true.mp added_terms_validate_all) term membership
  simpa using checked

theorem language_validate : language.validate = [] := by
  apply ConstructorSignatureExtension.apply_language_validate
    base addedTypes addedTerms (some "TptpFofCnfAllocatedBatchV1")
  · simpa [base] using
      TptpFofClausificationBatchLanguageDef.language_validate
  · rfl
  · rfl
  · exact added_type_names_nodup
  · exact added_type_names_disjoint
  · exact added_term_labels_nodup
  · exact added_term_labels_disjoint
  · exact added_terms_valid

def validated : ValidatedLanguageDef := ⟨language, language_validate⟩

def batchInclusion :
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
  | rule ruleMember =>
      simp [language, calculusLanguage, extension, base,
        ConstructorSignatureExtension.ofLists,
        TptpFofClausificationBatchLanguageDef.no_rewrites] at ruleMember

/-! ## Exact allocation data -/

def allocatedName (index : Nat) : Pattern :=
  a "tptp-fof-cnf-allocated:name"
    [TptpResolvedFofLanguageDef.encodeNatIndex index]

def allocatedClauseEntry (identity : Pattern) (index : Nat)
    (clause : Pattern) : Pattern :=
  a "tptp-fof-cnf-allocated:clause-entry"
    [identity, allocatedName index, clause]

def entriesNil : Pattern :=
  a "tptp-fof-cnf-allocated:entries-nil"

def entriesCons (head tail : Pattern) : Pattern :=
  a "tptp-fof-cnf-allocated:entries-cons" [head, tail]

def allocationResult (next entries : Pattern) : Pattern :=
  a "tptp-fof-cnf-allocated:allocation-result" [next, entries]

def allocatedOutput (batch firstName nextName entries : Pattern) : Pattern :=
  a "tptp-fof-cnf-allocated:output"
    [batch, firstName, nextName, entries]

/-- Recover the exact source batch retained by an allocated output. -/
def sourceBatch? : Pattern → Option Pattern
  | .apply "tptp-fof-cnf-allocated:output" [batch, _, _, _] => some batch
  | _ => none

theorem sourceBatch_allocatedOutput_exact
    (batch firstName nextName entries : Pattern) :
    sourceBatch? (allocatedOutput batch firstName nextName entries) =
      some batch := by
  rfl

structure AllocatedClauseEntry where
  identity : Pattern
  nameIndex : Nat
  clause : Pattern
  deriving DecidableEq, Repr

def allocateEncodedEntriesFrom : Nat →
    List TptpFofClausificationBatchLanguageDef.EncodedClauseEntry →
      List AllocatedClauseEntry
  | _, [] => []
  | nameIndex, entry :: rest =>
      ⟨entry.identity, nameIndex, entry.clause⟩ ::
        allocateEncodedEntriesFrom (nameIndex + 1) rest

def encodeAllocatedEntries : List AllocatedClauseEntry → Pattern
  | [] => entriesNil
  | entry :: rest => entriesCons
      (allocatedClauseEntry entry.identity entry.nameIndex entry.clause)
      (encodeAllocatedEntries rest)

def decodeAllocatedEntries? : Pattern → Option (List AllocatedClauseEntry)
  | .apply "tptp-fof-cnf-allocated:entries-nil" [] => some []
  | .apply "tptp-fof-cnf-allocated:entries-cons" [
      .apply "tptp-fof-cnf-allocated:clause-entry" [
        identity,
        .apply "tptp-fof-cnf-allocated:name" [index],
        clause], rest] => do
      let nameIndex ←
        TptpFofClausificationBatchLanguageDef.decodeNatIndex? index
      let tail ← decodeAllocatedEntries? rest
      some (⟨identity, nameIndex, clause⟩ :: tail)
  | _ => none

theorem decode_encodeAllocatedEntries (entries : List AllocatedClauseEntry) :
    decodeAllocatedEntries? (encodeAllocatedEntries entries) = some entries := by
  induction entries with
  | nil => rfl
  | cons entry rest inductionHypothesis =>
      simp [encodeAllocatedEntries, decodeAllocatedEntries?,
        allocatedClauseEntry, allocatedName, entriesCons, a,
        TptpFofClausificationBatchLanguageDef.decode_encodeNatIndex,
        inductionHypothesis]

theorem allocateEncodedEntriesFrom_length (firstName : Nat)
    (entries : List
      TptpFofClausificationBatchLanguageDef.EncodedClauseEntry) :
    (allocateEncodedEntriesFrom firstName entries).length = entries.length := by
  induction entries generalizing firstName with
  | nil => rfl
  | cons entry rest inductionHypothesis =>
      simp [allocateEncodedEntriesFrom, inductionHypothesis]

theorem allocateEncodedEntriesFrom_nameIndices (firstName : Nat)
    (entries : List
      TptpFofClausificationBatchLanguageDef.EncodedClauseEntry) :
    (allocateEncodedEntriesFrom firstName entries).map (·.nameIndex) =
      List.range' firstName entries.length := by
  induction entries generalizing firstName with
  | nil => rfl
  | cons entry rest inductionHypothesis =>
      simp [allocateEncodedEntriesFrom, List.range'_succ,
        inductionHypothesis]

theorem allocated_name_indices_nodup (firstName : Nat)
    (entries : List
      TptpFofClausificationBatchLanguageDef.EncodedClauseEntry) :
    ((allocateEncodedEntriesFrom firstName entries).map
      (·.nameIndex)).Nodup := by
  rw [allocateEncodedEntriesFrom_nameIndices]
  exact List.nodup_range' (s := firstName) (n := entries.length)

theorem allocatedName_injective : Function.Injective allocatedName := by
  intro left right equality
  apply TptpFofClausificationBatchLanguageDef.encodeNatIndex_injective
  simpa [allocatedName, a] using equality

private theorem map_allocatedName_eq (entries : List AllocatedClauseEntry) :
    entries.map (fun entry => allocatedName entry.nameIndex) =
      (entries.map (·.nameIndex)).map allocatedName := by
  induction entries with
  | nil => rfl
  | cons entry rest inductionHypothesis =>
      simp [inductionHypothesis]

theorem allocated_names_nodup (firstName : Nat)
    (entries : List
      TptpFofClausificationBatchLanguageDef.EncodedClauseEntry) :
    ((allocateEncodedEntriesFrom firstName entries).map
      (fun entry => allocatedName entry.nameIndex)).Nodup := by
  rw [map_allocatedName_eq]
  exact (allocated_name_indices_nodup firstName entries).map
    allocatedName_injective

theorem allocateEncodedEntriesFrom_identity_order (firstName : Nat)
    (entries : List
      TptpFofClausificationBatchLanguageDef.EncodedClauseEntry) :
    (allocateEncodedEntriesFrom firstName entries).map (·.identity) =
      entries.map (·.identity) := by
  induction entries generalizing firstName with
  | nil => rfl
  | cons entry rest inductionHypothesis =>
      simp [allocateEncodedEntriesFrom, inductionHypothesis]

theorem allocateEncodedEntriesFrom_clause_order (firstName : Nat)
    (entries : List
      TptpFofClausificationBatchLanguageDef.EncodedClauseEntry) :
    (allocateEncodedEntriesFrom firstName entries).map (·.clause) =
      entries.map (·.clause) := by
  induction entries generalizing firstName with
  | nil => rfl
  | cons entry rest inductionHypothesis =>
      simp [allocateEncodedEntriesFrom, inductionHypothesis]

theorem allocateEncodedEntriesFrom_append (firstName : Nat)
    (left right : List
      TptpFofClausificationBatchLanguageDef.EncodedClauseEntry) :
    allocateEncodedEntriesFrom firstName (left ++ right) =
      allocateEncodedEntriesFrom firstName left ++
        allocateEncodedEntriesFrom (firstName + left.length) right := by
  induction left generalizing firstName with
  | nil => simp [allocateEncodedEntriesFrom]
  | cons entry rest inductionHypothesis =>
      simp only [List.cons_append, allocateEncodedEntriesFrom,
        List.length_cons]
      rw [inductionHypothesis]
      have nextExact : firstName + 1 + rest.length =
          firstName + (rest.length + 1) := by
        omega
      rw [nextExact]

/-! ## Positive and negative controls -/

namespace Canary

def first : TptpFofClausificationBatchLanguageDef.EncodedClauseEntry :=
  ⟨a "source-id-0", a "clause-0"⟩

def second : TptpFofClausificationBatchLanguageDef.EncodedClauseEntry :=
  ⟨a "source-id-1", a "clause-1"⟩

theorem two_allocated_names_are_distinct :
    allocatedName 7 ≠ allocatedName 8 := by
  decide

theorem allocation_preserves_two_source_rows :
    allocateEncodedEntriesFrom 12 [first, second] = [
      ⟨first.identity, 12, first.clause⟩,
      ⟨second.identity, 13, second.clause⟩] := by
  rfl

theorem malformed_name_fails_closed :
    decodeAllocatedEntries?
      (entriesCons
        (a "tptp-fof-cnf-allocated:clause-entry" [
          first.identity, a "not-an-allocated-name", first.clause])
        entriesNil) = none := by
  rfl

theorem malformed_output_has_no_source_batch :
    sourceBatch? (a "tptp-fof-cnf-allocated:output" [a "batch-only"]) =
      none := by
  rfl

end Canary

theorem language_supported : CanonicalWire.languageSupported language := by
  decide +kernel

theorem wire_isSome : (CanonicalWire.renderLanguage? language).isSome := by
  rw [CanonicalWire.renderLanguage?_isSome_eq_supported]
  exact language_supported

def wire : String := (CanonicalWire.renderLanguage? language).getD ""

def writeWire (path : System.FilePath) : IO Unit := IO.FS.writeFile path wire

#print axioms language_validate
#print axioms batchInclusion
#print axioms theory_no_step
#print axioms decode_encodeAllocatedEntries
#print axioms sourceBatch_allocatedOutput_exact
#print axioms allocated_names_nodup
#print axioms allocateEncodedEntriesFrom_identity_order
#print axioms allocateEncodedEntriesFrom_clause_order
#print axioms allocateEncodedEntriesFrom_append
#print axioms Canary.two_allocated_names_are_distinct
#print axioms Canary.malformed_name_fails_closed
#print axioms Canary.malformed_output_has_no_source_batch

end Mettapedia.GSLT.LanguageDef.TptpFofCnfAllocatedBatchLanguageDef
