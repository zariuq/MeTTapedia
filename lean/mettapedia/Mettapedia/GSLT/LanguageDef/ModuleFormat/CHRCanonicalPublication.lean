import Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRCanonicalResult
import Mettapedia.OSLF.MeTTaIL.Complete.Normalized

/-! The prepared CHR plan declares no equation or flattening/extrusion law.
Its canonical commit is exactly bag canonicalization. The shared publication
receipt therefore has the same source selection and compact result, with
only its unordered remainder represented in canonical order. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRCompilation.CanonicalPublication

open Mettapedia.Languages.CHR
open Mettapedia.OSLF.MeTTaIL Syntax GeneralExecutionAdmission CanonicalBags

private theorem base_no_algebra : baseLanguage.terms.all (fun row => row.algebra?.isNone) = true := by
  decide +kernel

private theorem base_no_equations : baseLanguage.equations = [] := by
  decide +kernel

private theorem declared_nil (language : LanguageDef)
    (absent : ∀ row ∈ language.terms, row.algebra? = none) : CollectionLaws.declared language = [] := by
  unfold CollectionLaws.declared
  apply List.filterMap_eq_nil_iff.mpr
  intro kind _
  cases filtered : language.terms.filter (fun row => CollectionLaws.bareKind row == some kind) with
  | nil => rfl
  | cons row rest =>
    cases rest with
    | cons next tail => rfl
    | nil =>
      have member : row ∈ language.terms := (List.mem_filter.mp
        (show row ∈ language.terms.filter (fun row => CollectionLaws.bareKind row == some kind) by
          rw [filtered]; exact List.mem_singleton_self _)).1
      simp only [absent row member]

theorem laws_empty (program : Program) (seeds : List Constraint) (prepared : Prepared)
    (accepted : prepare program seeds = .ok prepared) : Complete.Normalized.laws (plan prepared) = [] := by
  change CollectionLaws.declared prepared.compiled = []
  apply declared_nil
  intro row member
  rw [(ProgramOrigins.prepare_source program seeds prepared accepted).terms] at member
  rcases List.mem_append.mp member with base | query
  · have absent := List.all_eq_true.mp base_no_algebra row base
    cases found : row.algebra? with
    | none => rfl
    | some algebra => rw [found] at absent; cases absent
  · obtain ⟨index, _, rfl⟩ := List.mem_map.mp query
    rfl

theorem equations_empty (program : Program) (seeds : List Constraint) (prepared : Prepared)
    (accepted : prepare program seeds = .ok prepared) : (plan prepared).equations = [] := by
  have empty : prepared.compiled.equations = [] :=
    (ProgramOrigins.prepare_source program seeds prepared accepted).equations.trans base_no_equations
  simp [plan, GeneralExecutionAdmission.compile, GeneralExecutionAdmission.equations,
    GeneralExecutionAdmission.selectedEquations, snapshot, permissions, empty]

theorem extrusions_empty (program : Program) (seeds : List Constraint) (prepared : Prepared)
    (accepted : prepare program seeds = .ok prepared) : Complete.Normalized.extrusions (plan prepared) = [] := by
  change CollectionLaws.extrusions prepared.compiled = []
  rw [CollectionLaws.extrusions, (ProgramOrigins.prepare_source program seeds prepared accepted).equations,
    base_no_equations]
  rfl

theorem commit_canonical (program : Program) (seeds : List Constraint) (prepared : Prepared)
    (accepted : prepare program seeds = .ok prepared) (pattern : Pattern) :
    Complete.Normalized.commit (plan prepared) .canonical pattern = canon pattern := by
  rw [Complete.Normalized.commit,
    Complete.Normalized.standard_lawFree (plan prepared)
      ⟨laws_empty program seeds prepared accepted, extrusions_empty program seeds prepared accepted⟩]

theorem conversion_trivial (program : Program) (seeds : List Constraint) (prepared : Prepared)
    (accepted : prepare program seeds = .ok prepared)
    {before after : Pattern} {history : List GeneralOccurrenceSemantics.Conversion}
    (converted : GeneralOccurrenceSemantics.ConversionPath (plan prepared) [] (.base "ChrMatchState")
      before after history) : before = after ∧ history = [] := by
  cases converted with
  | nil => exact ⟨rfl, rfl⟩
  | cons complete _ _ =>
    have member := List.fst_mem_of_mem_zipIdx complete.job.1
    rw [equations_empty program seeds prepared accepted] at member
    cases member
  | back complete _ _ =>
    have member := List.fst_mem_of_mem_zipIdx complete.job.1
    rw [equations_empty program seeds prepared accepted] at member
    cases member

theorem receipt_committed_source (program : Program) (seeds : List Constraint) (prepared : Prepared)
    (accepted : prepare program seeds = .ok prepared) (query activeId : Nat)
    (store : List Occurrence) (known : List Pattern)
    (encoded : store.mapM (OccurrenceEncoding.encode? prepared.vocabulary) = some known)
    (distinct : (store.map Occurrence.id).Nodup) (receipt : GeneralOccurrenceSemantics.Receipt)
    (valid : receipt.Valid (plan prepared) [] (.base "ChrMatchState")
      (request prepared.vocabulary query activeId known)) :
    ∃ (entry : Entry) (source : Rule) (environment : Environment) (selection : Selection),
      query = receipt.firing.job.declaration.declarationIndex ∧
      prepared.entries[query]? = some entry ∧ program.rules[entry.occurrence.rule]? = some source ∧
      entry.boundVariables = source.variables.eraseDups ∧
      selection.Matches source environment store ∧ selection.ActiveAt activeId entry.occurrence.head ∧
      MatchedEncoding.result? prepared.vocabulary environment entry.boundVariables selection =
        some (Complete.Normalized.commit (plan prepared) .canonical receipt.target) := by
  have representative := (conversion_trivial program seeds prepared accepted valid.1).1
  have firing := valid.2
  rw [← representative] at firing
  rw [commit_canonical program seeds prepared accepted]
  exact CanonicalResult.receipt_canonical_source program seeds prepared accepted query activeId store known
    encoded distinct receipt.firing firing

theorem canonical_request_committed_source (program : Program) (seeds : List Constraint) (prepared : Prepared)
    (accepted : prepare program seeds = .ok prepared) (query activeId : Nat)
    (store : List Occurrence) (known : List Pattern)
    (encoded : store.mapM (OccurrenceEncoding.encode? prepared.vocabulary) = some known)
    (distinct : (store.map Occurrence.id).Nodup) (receipt : GeneralOccurrenceSemantics.Receipt)
    (valid : receipt.Valid (plan prepared) [] (.base "ChrMatchState")
      (canon (request prepared.vocabulary query activeId known))) :
    ∃ (entry : Entry) (source : Rule) (environment : Environment) (selection : Selection),
      query = receipt.firing.job.declaration.declarationIndex ∧
      prepared.entries[query]? = some entry ∧ program.rules[entry.occurrence.rule]? = some source ∧
      entry.boundVariables = source.variables.eraseDups ∧
      selection.Matches source environment store ∧ selection.ActiveAt activeId entry.occurrence.head ∧
      MatchedEncoding.result? prepared.vocabulary environment entry.boundVariables selection =
        some (Complete.Normalized.commit (plan prepared) .canonical receipt.target) := by
  obtain ⟨reordered, permutation, reorderedRead⟩ := CanonicalData.canonical_sources prepared.vocabulary store known encoded
  have unique : (reordered.map Occurrence.id).Nodup := (permutation.map Occurrence.id).nodup_iff.mpr distinct
  rw [CanonicalData.request_canon prepared.vocabulary query activeId store known encoded] at valid
  obtain ⟨entry, source, environment, selection, querySame, atEntry, atSource, bound, matched, active, result⟩ :=
    receipt_committed_source program seeds prepared accepted query activeId reordered _ reorderedRead unique receipt valid
  exact ⟨entry, source, environment, selection, querySame, atEntry, atSource, bound,
    ⟨permutation.symm.trans matched.1, matched.2⟩, active, result⟩

theorem published_source (program : Program) (seeds : List Constraint) (prepared : Prepared)
    (accepted : prepare program seeds = .ok prepared) (query activeId : Nat)
    (store : List Occurrence) (known : List Pattern)
    (encoded : store.mapM (OccurrenceEncoding.encode? prepared.vocabulary) = some known)
    (distinct : (store.map Occurrence.id).Nodup) (work : Nat) (receipt : GeneralOccurrenceSemantics.Receipt)
    (published : receipt ∈ (Complete.Normalized.search (plan prepared) [] (.base "ChrMatchState") .canonical).publication
      ((Complete.Normalized.search (plan prepared) [] (.base "ChrMatchState") .canonical).run
        (canon (request prepared.vocabulary query activeId known)) work)) :
    ∃ (entry : Entry) (source : Rule) (environment : Environment) (selection : Selection),
      query = receipt.firing.job.declaration.declarationIndex ∧
      prepared.entries[query]? = some entry ∧ program.rules[entry.occurrence.rule]? = some source ∧
      entry.boundVariables = source.variables.eraseDups ∧
      selection.Matches source environment store ∧ selection.ActiveAt activeId entry.occurrence.head ∧
      MatchedEncoding.result? prepared.vocabulary environment entry.boundVariables selection =
        some ((Complete.Normalized.search (plan prepared) [] (.base "ChrMatchState") .canonical).target receipt) := by
  have valid := (Complete.Normalized.search_lawful (plan prepared) [] (.base "ChrMatchState") .canonical).sound
    (canon (request prepared.vocabulary query activeId known)) work receipt published
  exact canonical_request_committed_source program seeds prepared accepted query activeId store known
    encoded distinct receipt valid

#print axioms laws_empty
#print axioms commit_canonical
#print axioms receipt_committed_source
#print axioms canonical_request_committed_source
#print axioms published_source

end Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRCompilation.CanonicalPublication
