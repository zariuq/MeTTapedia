import Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRCanonicalData
import Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRPlanReading

/-! Canonical publication leaves the ordered environment and selected heads
unchanged and reorders only the bag remainder. Source matching, the active
occurrence and propagation key survive that change of representation. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRCompilation.CanonicalResult

open Mettapedia.Languages.CHR
open Mettapedia.OSLF.MeTTaIL Syntax CanonicalBags PatternLexOrder
open ScopedRuleMatching GeneralFirstOrderProjection

private theorem heads_canon (vocabulary : Vocabulary) (sources : List Occurrence) (codes : List Pattern)
    (encoded : sources.mapM (OccurrenceEncoding.encode? vocabulary) = some codes) :
    canon (heads codes) = heads codes := by
  simp only [heads, canon_apply, List.map_cons, List.map_nil, CanonicalData.vector_canon,
    CanonicalData.codes_canon vocabulary sources codes encoded]

theorem result_canon (vocabulary : Vocabulary) (environment : Environment) (indices : List Nat)
    (selection : Selection) (target : Pattern)
    (encoded : MatchedEncoding.result? vocabulary environment indices selection = some target) :
    ∃ (residual : List Occurrence), residual.Perm selection.rest ∧
      MatchedEncoding.result? vocabulary environment indices {selection with rest := residual} = some (canon target) := by
  simp only [MatchedEncoding.result?, Option.bind_eq_bind, Option.bind_eq_some_iff] at encoded
  obtain ⟨values, valuesRead, kept, keptRead, removed, removedRead, rest, restRead, same⟩ := encoded
  change some (Pattern.apply "ChrMatched" [vector values, heads kept, heads removed, store rest]) = some target at same
  cases Option.some.inj same
  obtain ⟨residual, permutation, residualRead⟩ :=
    CanonicalData.canonical_sources vocabulary selection.rest rest restRead
  have canonical : canon (.apply "ChrMatched" [vector values, heads kept, heads removed, store rest]) =
      .apply "ChrMatched" [vector values, heads kept, heads removed, store (sortLex rest)] := by
    simp only [canon_apply, List.map_cons, List.map_nil, CanonicalData.vector_canon,
      CanonicalData.environment_canon vocabulary environment indices values valuesRead,
      heads_canon vocabulary selection.kept kept keptRead,
      heads_canon vocabulary selection.removed removed removedRead,
      CanonicalData.store_canon vocabulary selection.rest rest restRead]
  refine ⟨residual, permutation, ?_⟩
  rw [canonical]
  simp only [MatchedEncoding.result?, valuesRead, keptRead, removedRead, residualRead]
  rfl

theorem matches_reordered_rest (selection : Selection) (residual : List Occurrence)
    (source : Rule) (environment : Environment) (store : List Occurrence)
    (matched : selection.Matches source environment store) (permutation : residual.Perm selection.rest) :
    ({selection with rest := residual} : Selection).Matches source environment store := by
  refine ⟨?_, matched.2⟩
  apply matched.1.trans
  simpa only [List.append_assoc] using
    (List.Perm.refl selection.kept).append ((List.Perm.refl selection.removed).append permutation.symm)

theorem active_reordered_rest (selection : Selection) (residual : List Occurrence) (active slot : Nat) :
    ({selection with rest := residual} : Selection).ActiveAt active slot ↔ selection.ActiveAt active slot := Iff.rfl

theorem key_reordered_rest (selection : Selection) (residual : List Occurrence) (ruleIndex : Nat) :
    ({selection with rest := residual} : Selection).key ruleIndex = selection.key ruleIndex := rfl

theorem receipt_canonical_source (program : Program) (seeds : List Constraint) (prepared : Prepared)
    (accepted : prepare program seeds = .ok prepared) (query activeId : Nat)
    (store : List Occurrence) (known : List Pattern)
    (encoded : store.mapM (OccurrenceEncoding.encode? prepared.vocabulary) = some known)
    (distinct : (store.map Occurrence.id).Nodup) (receipt : GeneralRuleJobs.Receipt)
    (valid : receipt.Valid (plan prepared) [] (.base "ChrMatchState")
      (request prepared.vocabulary query activeId known)) :
    ∃ (entry : Entry) (source : Rule) (environment : Environment) (selection : Selection),
      query = receipt.job.declaration.declarationIndex ∧
      prepared.entries[query]? = some entry ∧ program.rules[entry.occurrence.rule]? = some source ∧
      entry.boundVariables = source.variables.eraseDups ∧
      selection.Matches source environment store ∧ selection.ActiveAt activeId entry.occurrence.head ∧
      MatchedEncoding.result? prepared.vocabulary environment entry.boundVariables selection = some (canon receipt.target) := by
  obtain ⟨entry, source, environment, selected, querySame, atEntry, atSource, bound, read, target⟩ :=
    PlanReading.receipt_source_result program seeds prepared accepted query activeId store known encoded distinct receipt valid
  obtain ⟨residual, permutation, result⟩ := result_canon prepared.vocabulary environment entry.boundVariables
    selected receipt.target target
  exact ⟨entry, source, environment, {selected with rest := residual}, querySame, atEntry, atSource, bound,
    matches_reordered_rest selected residual source environment store read.sourceMatch permutation, read.active, result⟩

#print axioms result_canon
#print axioms matches_reordered_rest
#print axioms receipt_canonical_source

end Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRCompilation.CanonicalResult
