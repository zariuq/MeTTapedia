import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.CensusSourceCompilation
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.SourceAbsenceControls

/-! # The actual complete query compiler feeding one atomic batch -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.CensusSourceControls

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Sources Sources.Commutative Sources.AbsenceControls
open Mettapedia.Machines

def contents : List Occurrence := [(message .a, 0), (message .a, 1), (message .b, 2)]
def template : List Pattern := [.node .acknowledgement (.var 0) (.leaf .nil)]
def oneRead : SourceList Nat Value Pattern := .cons (.read messagePattern) .done
def source : SourceList Nat Value Pattern := .every oneRead
def footprint : Footprint Occurrence Value :=
  everyFootprint layer matcher label contents.toFinset template oneRead empty
def row : Subst Nat Value × List (Pick Occurrence Value) := (empty, [.amalgam footprint])
def census : PredicateQuery Occurrence Value :=
  ⟨Matcher.region matcher empty messagePattern, contents.toFinset⟩
def made : Finset Occurrence :=
  {(acknowledgement .a, 3), (acknowledgement .a, 4), (acknowledgement .b, 5)}
def batch : Commit Occurrence Value := ⟨∅, contents.toFinset, made, [census]⟩

theorem scanner_is_complete : Query.Complete label contents.toFinset (Query.scanList label contents) :=
  Query.scanList_complete label contents (by decide +kernel)

theorem actual_query_returns_the_aggregate :
    row ∈ (ReadOnlyQuery.run (Query.scanList label contents)
      (Query.compile layer matcher label template source empty)).answer := by
  apply Multiset.mem_coe.mp
  rw [Query.run_compile layer matcher label contents.toFinset _ scanner_is_complete template source empty]
  change row ∈ ({row} : Multiset _)
  exact Multiset.mem_singleton_self _

theorem the_aggregate_is_a_source_derivation :
    DRow layer label contents.toFinset template source empty row := by
  exact CensusSourceCompilation.query_row_is_declarative layer matcher
    (cmatch_sound (comm := noComm)) (cmatch_complete (comm := noComm)) (cmatch_minimal (comm := noComm))
    label contents (by decide +kernel) template source (by simp [source, oneRead, SourceList.lets])
    row actual_query_returns_the_aggregate

theorem complete_production_preserves_duplicates :
    footprint.makes = {acknowledgement .a, acknowledgement .a, acknowledgement .b} := by
  decide +kernel

theorem aggregate_has_the_census : footprint.queries = {census} := by
  rfl

theorem aggregate_is_linear : footprint.Linear := by decide +kernel

theorem batch_has_exactly_the_aggregate : IsCommitOf label contents.toFinset footprint batch := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · intro query
    rw [aggregate_has_the_census]
    rfl
  · decide +kernel
  · rw [complete_production_preserves_duplicates]
    decide +kernel

/-- This is a source firing from the actual compiler, not a free-standing
claim that a hand-written output list was complete. -/
theorem actual_source_firing : Fires layer matcher label contents.toFinset ⟨source, template⟩ batch := by
  refine ⟨row, ?_, ?_, ?_⟩
  · change row ∈ ({row} : Multiset _)
    exact Multiset.mem_singleton_self _
  · change (footprint + 0).Linear
    simpa only [add_zero] using aggregate_is_linear
  · change IsCommitOf label contents.toFinset (footprint + 0) batch
    simpa only [add_zero] using batch_has_exactly_the_aggregate

/-- The same concrete complete batch composes with any admitted retained
information store over these values. No empty-store hypothesis is built into
the bridge. Nontrivial logical-variable cuts are exercised in CensusControls. -/
theorem actual_query_batch_is_admitted {S : Type*} (action : SubstitutionAction Value S)
    (equations tells : EquationStore Value) (consistent : action.Consistent (equations ++ tells)) :
    PredicateQueryAdmission.Valid action label (CensusSourceCompilation.rule label batch tells)
      (batch.queries.map PredicateQueryAdmission.Query.fixed) ⟨equations, contents.toFinset⟩
      (CensusSourceCompilation.selection batch) :=
  CensusSourceCompilation.realize_commit action label batch tells _ actual_source_firing.enabled consistent

/-- The generated outputs are not re-read by the complete scan that
produced them. All three messages remain, and exactly three acknowledgements
appear together. -/
theorem one_physical_commit_has_all_three_answers :
    fire contents.toFinset batch = contents.toFinset ∪ made ∧
      labels label batch.made = {acknowledgement .a, acknowledgement .a, acknowledgement .b} := by
  exact ⟨by decide +kernel, by decide +kernel⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.CensusSourceControls
