import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.OccurrenceStep

/-!
# Complete region observations at the same atomic admission

A census records every physical occurrence selected by a predicate. Its
query-local matching can range over several substitutions; it need not be
equality to one instance of a port pattern. Predicates may also depend on the
caller's solution. Such an observation must hold for every solution at the
firing's actual joint constraint cut, just like the existing asks.

This extends admission of the existing occurrence operation. It changes
neither its equations nor its occurrence update. An empty observation list
recovers exactly the original relation. Fixed predicates recover the existing
occurrence-commit predicate queries, including their bag multiplicities.

A source compiler must still connect its produced values to these complete
observations. A predicate, an arbitrary output and a certificate alone do not
establish that connection. Ordered answer streams additionally retain the
ordered scanner's certificate; an occurrence census by itself fixes a bag.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PredicateQueryAdmission

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

universe uT uS uO

structure Query (T : Type uT) (S : Type uS) (O : Type uO) where
  region : S → T → Bool
  seen : Finset O

namespace Query

variable {T : Type uT} {S : Type uS} {O : Type uO}

def atSolution (query : Query T S O) (candidate : S) : PredicateQuery O T :=
  ⟨query.region candidate, query.seen⟩

def fixed (query : PredicateQuery O T) : Query T S O :=
  ⟨fun _ => query.region, query.seen⟩

def Ask (A : SubstitutionAction T S) (problem : EquationStore T)
    (label : O → T) (world : Finset O) (query : Query T S O) : Prop :=
  A.Entails problem fun candidate => (query.atSolution candidate).Holds label world

def IgnoresWrites (A : SubstitutionAction T S) (problem : EquationStore T)
    (label : O → T) (writer : Selection O) (query : Query T S O) : Prop :=
  A.Entails problem fun candidate =>
    ∀ occurrence ∈ writer.taken ++ writer.made, query.region candidate (label occurrence) = false

theorem Ask.of_refines {A : SubstitutionAction T S} {stronger weaker : EquationStore T}
    {label : O → T} {world : Finset O} {query : Query T S O}
    (refines : A.Refines stronger weaker) (asked : query.Ask A weaker label world) :
    query.Ask A stronger label world := A.entails_of_refines refines asked

/-- Consistency rules out a vacuous completeness assertion. -/
theorem fixed_ask_iff {A : SubstitutionAction T S} {problem : EquationStore T}
    {label : O → T} {world : Finset O} {query : PredicateQuery O T}
    (consistent : A.Consistent problem) :
    (fixed query : Query T S O).Ask A problem label world ↔ query.Holds label world := by
  constructor
  · intro asked
    obtain ⟨candidate, solved⟩ := consistent
    exact asked candidate solved
  · intro holds _ _
    exact holds

theorem Ask.matchBag {A : SubstitutionAction T S} {problem : EquationStore T}
    {label : O → T} {world : Finset O} {query : Query T S O}
    (asked : query.Ask A problem label world) {candidate : S}
    (solved : A.Models candidate problem) :
    matchBag label world (query.region candidate) = labels label query.seen :=
  PredicateQuery.matchBag_eq_of_holds (asked candidate solved)

theorem Ask.card {A : SubstitutionAction T S} {problem : EquationStore T}
    {label : O → T} {world : Finset O} {query : Query T S O}
    (asked : query.Ask A problem label world) {candidate : S}
    (solved : A.Models candidate problem) :
    (regionOf label world (query.region candidate)).card = query.seen.card :=
  congrArg Finset.card (asked candidate solved)

end Query

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]

def commit (selection : Selection O) (queries : List (Query T S O)) (candidate : S) : Commit O T :=
  { (selection.commit (T := T)) with queries := queries.map fun query => query.atSolution candidate }

structure Valid (A : SubstitutionAction T S) (label : O → T) (rule : RuleInstance T)
    (queries : List (Query T S O)) (before : Configuration T O) (selection : Selection O) : Prop where
  firing : selection.Valid A label rule before
  observations : ∀ query ∈ queries, query.Ask A (selection.problem label rule before) label before.present

theorem valid_empty_iff (A : SubstitutionAction T S) (label : O → T) (rule : RuleInstance T)
    (before : Configuration T O) (selection : Selection O) :
    Valid A label rule [] before selection ↔ selection.Valid A label rule before := by
  constructor
  · exact Valid.firing
  · intro firing
    exact ⟨firing, by simp⟩

theorem Valid.enabled {A : SubstitutionAction T S} {label : O → T} {rule : RuleInstance T}
    {queries : List (Query T S O)} {before : Configuration T O} {selection : Selection O}
    (valid : Valid A label rule queries before selection) {candidate : S}
    (solved : A.Models candidate (selection.problem label rule before)) :
    Enabled label before.present (commit selection queries candidate) := by
  refine ⟨valid.firing.occurrences.taken_subset, valid.firing.occurrences.kept_subset,
    valid.firing.occurrences.apart, valid.firing.occurrences.fresh, ?_⟩
  intro read member
  obtain ⟨query, present, rfl⟩ := List.mem_map.mp member
  exact valid.observations query present candidate solved

theorem valid_iff_enabled (A : SubstitutionAction T S) (label : O → T) (rule : RuleInstance T)
    (queries : List (Query T S O)) (before : Configuration T O) (selection : Selection O) :
    Valid A label rule queries before selection ↔
      selection.Valid A label rule before ∧
        A.Entails (selection.problem label rule before)
          (fun candidate => Enabled label before.present (commit selection queries candidate)) := by
  constructor
  · intro valid
    exact ⟨valid.firing, fun _ solved => valid.enabled solved⟩
  · rintro ⟨firing, enabled⟩
    refine ⟨firing, ?_⟩
    intro query present candidate solved
    exact (enabled candidate solved).queries_hold _ (List.mem_map.mpr ⟨query, present, rfl⟩)

theorem valid_fixed_iff (A : SubstitutionAction T S) (label : O → T) (rule : RuleInstance T)
    (queries : List (PredicateQuery O T)) (before : Configuration T O) (selection : Selection O) :
    Valid A label rule (queries.map Query.fixed) before selection ↔
      selection.Valid A label rule before ∧ ∀ query ∈ queries, query.Holds label before.present := by
  constructor
  · intro valid
    refine ⟨valid.firing, ?_⟩
    intro query member
    exact (Query.fixed_ask_iff valid.firing.consistent).mp
      (valid.observations _ (List.mem_map.mpr ⟨query, member, rfl⟩))
  · rintro ⟨firing, holds⟩
    refine ⟨firing, ?_⟩
    intro query member
    obtain ⟨read, present, rfl⟩ := List.mem_map.mp member
    exact (Query.fixed_ask_iff firing.consistent).mpr (holds read present)

/-- Resource and information admission are retained from the existing step;
the complete observations survive writes outside their queried regions.
The noninterference obligation is evaluated at the new joint solution cut. -/
theorem Valid.after {A : SubstitutionAction T S} {label : O → T} {rule : RuleInstance T}
    {queries : List (Query T S O)} {before after : Configuration T O} {selection writer : Selection O}
    (valid : Valid A label rule queries before selection)
    (readmitted : selection.Valid A label rule after)
    (world : after.present = fire before.present (writer.commit (T := T)))
    (refines : A.Refines (selection.problem label rule after) (selection.problem label rule before))
    (ignored : ∀ query ∈ queries, query.IgnoresWrites A (selection.problem label rule after) label writer) :
    Valid A label rule queries after selection := by
  refine ⟨readmitted, ?_⟩
  intro query member candidate solved
  have noWrite : ∀ occurrence ∈ (writer.commit (T := T)).taken ∪ (writer.commit (T := T)).made,
      query.region candidate (label occurrence) = false := by
    intro occurrence written
    apply ignored query member candidate solved occurrence
    simpa only [Selection.commit, Finset.mem_union, List.mem_toFinset, List.mem_append] using written
  change regionOf label after.present (query.region candidate) = query.seen
  rw [world, regionOf_fire_of_no_write noWrite]
  exact valid.observations query member candidate (refines candidate solved)

/-- Observation checks and effects use one before-state. No public
intermediate state is introduced by the census. -/
theorem result_present (selection : Selection O) (queries : List (Query T S O)) (candidate : S)
    (label : O → T) (rule : RuleInstance T) (before : Configuration T O) :
    (selection.result label rule before).present = fire before.present (commit selection queries candidate) := rfl

def Step (A : SubstitutionAction T S) (label : O → T) (rule : RuleInstance T)
    (queries : List (Query T S O)) (before after : Configuration T O) : Prop :=
  ∃ selection, Valid A label rule queries before selection ∧ after = selection.result label rule before

theorem step_empty_iff (A : SubstitutionAction T S) (label : O → T) (rule : RuleInstance T)
    (before after : Configuration T O) :
    Step A label rule [] before after ↔
      ConstraintMultisetRewriting.Step A label rule before after := by
  simp only [Step, ConstraintMultisetRewriting.Step, valid_empty_iff]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PredicateQueryAdmission
