import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.CensusSourceCompilation

/-!
# Ordered query transcripts at the candidate firing cut

A complete provider answers each region with all physical occurrences. Its
order is additional information. Admission retains the actual adaptive read
program and validates every observed list against the provider at the same
pre-update cut. Erasing those lists to finite sets recovers ordinary census
observations, but the converse does not justify replaying an ordered result.

The source bridge uses the existing finite source compiler, not an arbitrary
evaluator. It carries validated cached source answers into actual candidate
firings with their original produced bags. Matching and computation retain
that compiler's declared profile.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.OrderedPredicateQueryAdmission

open Mettapedia.Machines
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

universe uT uS uO uA uV uP
variable {T : Type uT} {S : Type uS} {O : Type uO} {Answer : Type uA} [DecidableEq O]

def readCensuses (reads : ReadOnlyQuery.Reads (T → Bool) (List O)) : List (PredicateQueryAdmission.Query T S O) :=
  reads.map fun observed => PredicateQueryAdmission.Query.fixed ⟨observed.1, observed.2.toFinset⟩

structure Valid (action : SubstitutionAction T S) (label : O → T) (rule : RuleInstance T)
    (queries : List (PredicateQueryAdmission.Query T S O)) (before : Configuration T O) (selection : Selection O)
    (program : ReadOnlyQuery.Program (T → Bool) (List O) Answer)
    (saved current : (T → Bool) → List O) : Prop where
  firing : PredicateQueryAdmission.Valid action label rule queries before selection
  complete : Sources.Query.Complete label before.present current
  agrees : ReadOnlyQuery.Agrees current (ReadOnlyQuery.run saved program).reads

namespace Valid

variable {action : SubstitutionAction T S} {label : O → T} {rule : RuleInstance T}
    {queries : List (PredicateQueryAdmission.Query T S O)} {before : Configuration T O} {selection : Selection O}
    {program : ReadOnlyQuery.Program (T → Bool) (List O) Answer}
    {saved current : (T → Bool) → List O}

theorem replay (valid : Valid action label rule queries before selection program saved current) :
    ReadOnlyQuery.run current program = ReadOnlyQuery.run saved program :=
  ReadOnlyQuery.run_eq_of_agrees saved current program valid.agrees

theorem checked (valid : Valid action label rule queries before selection program saved current) :
    ReadOnlyQuery.checkReads current (ReadOnlyQuery.run saved program).reads = true :=
  (ReadOnlyQuery.checkReads_iff _ _).mpr valid.agrees

/-- Ordered reads contribute complete predicate censuses at the actual
joint admission, even when the original rule had no explicit census. -/
theorem with_read_censuses (valid : Valid action label rule queries before selection program saved current) :
    PredicateQueryAdmission.Valid action label rule
      (queries ++ readCensuses (ReadOnlyQuery.run saved program).reads) before selection := by
  refine ⟨valid.firing.firing, ?_⟩
  intro query member
  rcases List.mem_append.mp member with original | observed
  · exact valid.firing.observations query original
  · obtain ⟨read, recorded, rfl⟩ := List.mem_map.mp observed
    intro _ _
    exact (valid.complete.seen read.1).symm.trans
      (congrArg List.toFinset (valid.agrees read recorded))

theorem answer (valid : Valid action label rule queries before selection program saved current) :
    (ReadOnlyQuery.run current program).answer = (ReadOnlyQuery.run saved program).answer :=
  congrArg ReadOnlyQuery.Observation.answer valid.replay

end Valid

/-- A validated ordered source observation supplies both the firing and
the unchanged ordered answer stream at its current cut. -/
theorem realize_source_row {V : Type uV} {P : Type uP}
    (action : SubstitutionAction T S) (layer : Sources.TermLayer V T P) (matcher : Sources.Matcher V T P)
    (label : O → T) (contents : List O) (unique : contents.Nodup)
    (before : Configuration T O) (present : contents.toFinset = before.present)
    (template : List P) (sources : Sources.SourceList V T P)
    (saved : (T → Bool) → List O)
    (validated : ReadOnlyQuery.checkReads (Sources.Query.scanList label contents)
      (ReadOnlyQuery.run saved (Sources.Query.compile layer matcher label template sources (fun _ => none))).reads = true)
    (row : Sources.Subst V T × List (Sources.Pick O T))
    (returned : row ∈ (ReadOnlyQuery.run saved
      (Sources.Query.compile layer matcher label template sources (fun _ => none))).answer)
    (linear : (Sources.footprintOf row.2).Linear) (tells : EquationStore T)
    (consistent : action.Consistent (before.equations ++ tells))
    (supply : ∀ (avoid : Finset O) (value : T), ∃ occurrence, occurrence ∉ avoid ∧ label occurrence = value) :
    ∃ commit : Commit O T,
      Sources.IsCommitOf label before.present (Sources.footprintOf row.2) commit ∧
      Valid action label (CensusSourceCompilation.rule label commit tells)
        (commit.queries.map PredicateQueryAdmission.Query.fixed) before (CensusSourceCompilation.selection commit)
        (Sources.Query.compile layer matcher label template sources (fun _ => none)) saved
        (Sources.Query.scanList label contents) ∧
      ((CensusSourceCompilation.rule label commit tells).produce : Multiset T) = (Sources.footprintOf row.2).makes := by
  have agrees := (ReadOnlyQuery.checkReads_iff _ _).mp validated
  have replay := ReadOnlyQuery.run_eq_of_agrees saved (Sources.Query.scanList label contents)
    (Sources.Query.compile layer matcher label template sources (fun _ => none)) agrees
  have currentReturned : row ∈ (ReadOnlyQuery.run (Sources.Query.scanList label contents)
      (Sources.Query.compile layer matcher label template sources (fun _ => none))).answer := by
    rw [replay]
    exact returned
  obtain ⟨commit, realized, admitted, _, produced⟩ := CensusSourceCompilation.realize_query_row action layer matcher
    label contents unique before present template sources row currentReturned linear tells consistent supply
  refine ⟨commit, realized, ⟨admitted, ?_, agrees⟩, produced⟩
  rw [← present]
  exact Sources.Query.scanList_complete label contents unique

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.OrderedPredicateQueryAdmission
