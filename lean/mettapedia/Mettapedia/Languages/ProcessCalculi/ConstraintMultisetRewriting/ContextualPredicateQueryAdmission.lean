import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PredicateQueryAdmission
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardEntryViews

/-!
# Existing predicate queries at a contextual firing's information cut

A typed candidate packages one future declaration family and its assignment.
Queries are the existing PredicateQueryAdmission.Query. Native labels retain both
occurrence identities and the actual conditional row data. Contextual admission
quantifies over all future models of the actual firing information. Query observations refine an existing firing;
they do not change its solver return, resource update or published rows.

An entry guard formula is witnessed by a complete query at a present control
occurrence. Its region tests that formula pointwise, not source admission or
a whole evaluator. Such a marker query alone does not validate the captured
data dependencies under interference. Data-region queries must retain those
dependencies; the marker is not a dynamic absence or count observation.
This semantic construction supplies no total decision
procedure for arbitrary contextual matching. The compiler must still supply
the control context and embed its full binding problem in the actual firing.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPredicateQueryAdmission

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

variable {S : Signature} {V O : Type} {declaration : V → MetaArity S}

structure Candidate (declaration : V → MetaArity S) : Type 1 where
  Variables : Type
  declarations : Variables → MetaArity S
  assignment : Assignment declaration declarations

abbrev Query (declaration : V → MetaArity S) (O : Type) := PredicateQueryAdmission.Query O (Candidate declaration) O
abbrev DataQuery (declaration : V → MetaArity S) (Label O : Type) := PredicateQueryAdmission.Query Label (Candidate declaration) O

def Holds (query : Query declaration O) (world : Finset O) (candidate : Candidate declaration) : Prop :=
  (query.atSolution candidate).Holds id world

def Ask (problem : ContextualResidual.Problem declaration) (query : Query declaration O) (world : Finset O) : Prop :=
  ∀ (Future : Type) (future : Future → MetaArity S) (candidate : Assignment declaration future),
    ContextualResidual.Models candidate problem → Holds query world ⟨Future, future, candidate⟩

def AskData {Label : Type} (problem : ContextualResidual.Problem declaration)
    (query : DataQuery declaration Label O) (label : O → Label) (world : Finset O) : Prop :=
  ∀ (Future : Type) (future : Future → MetaArity S) (candidate : Assignment declaration future),
    ContextualResidual.Models candidate problem → (query.atSolution ⟨Future, future, candidate⟩).Holds label world

def liftPoint {Label : Type} (query : Query declaration O) : DataQuery declaration (O × Label) O :=
  ⟨(fun candidate label => query.region candidate label.1), query.seen⟩

theorem lift_point_ask_iff {Label : Type} (problem : ContextualResidual.Problem declaration)
    (query : Query declaration O) (label : O → Label) (world : Finset O) :
    AskData problem (liftPoint query) (fun occurrence => (occurrence, label occurrence)) world ↔ Ask problem query world := by
  rfl

noncomputable def matchingQuery {Local : Type} (locals : Local → MetaArity S)
    {Γ : Ctx S} {sort : S.Srt} (pattern : Term (signature S declaration) Γ sort) (seen : Finset O) :
    DataQuery declaration (O × ContextualConditionalRows.Row locals declaration Γ sort) O := by
  classical
  exact ⟨(fun candidate label => decide (ContextualConditionalRows.Matches locals declaration candidate.assignment
    (instantiate candidate.assignment pattern) label.2)), seen⟩

theorem matching_holds_iff {Local : Type} (locals : Local → MetaArity S) {Γ : Ctx S} {sort : S.Srt}
    (pattern : Term (signature S declaration) Γ sort) (seen : Finset O)
    (rows : O → ContextualConditionalRows.Row locals declaration Γ sort) (world : Finset O)
    (candidate : Candidate declaration) :
    ((matchingQuery locals pattern seen).atSolution candidate).Holds
        (fun occurrence => (occurrence, rows occurrence)) world ↔
      ContextualConditionalGuards.region locals candidate.assignment rows world pattern = seen := by
  classical
  have same : regionOf (fun occurrence => (occurrence, rows occurrence)) world
      ((matchingQuery locals pattern seen).region candidate) =
      ContextualConditionalGuards.region locals candidate.assignment rows world pattern := by
    ext occurrence
    simp [mem_regionOf, ContextualConditionalGuards.mem_region, matchingQuery]
  change regionOf _ world ((matchingQuery locals pattern seen).region candidate) = seen ↔ _
  rw [same]

theorem matching_empty_iff {Local : Type} (locals : Local → MetaArity S) {Γ : Ctx S} {sort : S.Srt}
    (pattern : Term (signature S declaration) Γ sort) (rows : O → ContextualConditionalRows.Row locals declaration Γ sort)
    (world : Finset O) (candidate : Candidate declaration) :
    ((matchingQuery locals pattern (∅ : Finset O)).atSolution candidate).Holds
        (fun occurrence => (occurrence, rows occurrence)) world ↔
      ContextualConditionalGuards.Holds locals candidate.assignment rows world (.absent pattern) := by
  classical
  constructor
  · intro observed occurrence present matched
    have member : occurrence ∈ regionOf (fun occurrence => (occurrence, rows occurrence)) world
        ((matchingQuery locals pattern (∅ : Finset O)).region candidate) :=
      mem_regionOf.mpr ⟨present, by simpa only [matchingQuery, decide_eq_true_eq] using matched⟩
    change regionOf (fun occurrence => (occurrence, rows occurrence)) world
      ((matchingQuery locals pattern (∅ : Finset O)).region candidate) = ∅ at observed
    rw [observed] at member
    exact Finset.notMem_empty occurrence member
  · intro absent
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro occurrence member
    obtain ⟨present, matched⟩ := mem_regionOf.mp member
    exact absent occurrence present (of_decide_eq_true matched)

theorem matching_ask_empty_iff {Local : Type} (locals : Local → MetaArity S) {Γ : Ctx S} {sort : S.Srt}
    (problem : ContextualResidual.Problem declaration) (pattern : Term (signature S declaration) Γ sort)
    (rows : O → ContextualConditionalRows.Row locals declaration Γ sort) (world : Finset O) :
    AskData problem (matchingQuery locals pattern (∅ : Finset O)) (fun occurrence => (occurrence, rows occurrence)) world ↔
      ContextualConditionalGuards.Ask locals problem rows world (.absent pattern) := by
  constructor <;> intro observed Future future candidate model
  · exact (matching_empty_iff locals pattern rows world ⟨Future, future, candidate⟩).mp
      (observed Future future candidate model)
  · exact (matching_empty_iff locals pattern rows world ⟨Future, future, candidate⟩).mpr
      (observed Future future candidate model)

/-- Under fixed row labels, writes outside the actual queried region preserve admission. -/
theorem ask_data_after_writes {Label : Type} [DecidableEq O]
    (problem : ContextualResidual.Problem declaration) (query : DataQuery declaration Label O)
    (label : O → Label) (world : Finset O) (writer : Selection O)
    (asked : AskData problem query label world)
    (outside : ∀ (Future : Type) (future : Future → MetaArity S) (candidate : Assignment declaration future),
      ContextualResidual.Models candidate problem → ∀ occurrence ∈ writer.taken ++ writer.made,
        query.region ⟨Future, future, candidate⟩ (label occurrence) = false) :
    AskData problem query label (fire world (writer.commit (T := Label))) := by
  intro Future future candidate model
  have ignored : ∀ occurrence ∈ (writer.commit (T := Label)).taken ∪ (writer.commit (T := Label)).made,
      query.region ⟨Future, future, candidate⟩ (label occurrence) = false := by
    intro occurrence member
    apply outside Future future candidate model occurrence
    simpa only [Selection.commit, Finset.mem_union, List.mem_toFinset, List.mem_append] using member
  change regionOf label (fire world (writer.commit (T := Label))) (query.region ⟨Future, future, candidate⟩) = query.seen
  rw [regionOf_fire_of_no_write ignored]
  exact asked Future future candidate model

noncomputable def ofCondition [DecidableEq O] (condition : Candidate declaration → Prop) (marker : O) : Query declaration O := by
  classical
  exact ⟨(fun candidate occurrence => decide (occurrence = marker ∧ condition candidate)), {marker}⟩

theorem condition_holds_iff [DecidableEq O] (condition : Candidate declaration → Prop) (marker : O)
    (world : Finset O) (present : marker ∈ world) (candidate : Candidate declaration) :
    Holds (ofCondition condition marker) world candidate ↔ condition candidate := by
  classical
  constructor
  · intro observed
    change regionOf id world ((ofCondition condition marker).region candidate) = {marker} at observed
    have member : marker ∈ regionOf id world ((ofCondition condition marker).region candidate) := by
      rw [observed]
      exact Finset.mem_singleton_self _
    have picked := (mem_regionOf.mp member).2
    exact (of_decide_eq_true picked).2
  · intro accepted
    ext occurrence
    simp only [mem_regionOf, ofCondition, PredicateQueryAdmission.Query.atSolution, Finset.mem_singleton, id_eq,
      decide_eq_true_eq]
    constructor
    · exact fun member => member.2.1
    · intro same
      subst occurrence
      exact ⟨present, rfl, accepted⟩

theorem ask_condition_iff [DecidableEq O] (condition : Candidate declaration → Prop) (marker : O)
    (world : Finset O) (present : marker ∈ world) (problem : ContextualResidual.Problem declaration) :
    Ask problem (ofCondition condition marker) world ↔
      ∀ (Future : Type) (future : Future → MetaArity S) (candidate : Assignment declaration future),
        ContextualResidual.Models candidate problem → condition ⟨Future, future, candidate⟩ := by
  constructor <;> intro observed Future future candidate model
  · exact (condition_holds_iff condition marker world present _).mp (observed Future future candidate model)
  · exact (condition_holds_iff condition marker world present _).mpr (observed Future future candidate model)

section Firings

variable {Local : Type} (locals : Local → MetaArity S) [DecidableEq Local] [DecidableEq O]
    [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
    {Γ : Ctx S} {sort : S.Srt} {before : ContextualConditionalExecution.State locals O Γ sort}

def nativeLabels (before : ContextualConditionalExecution.State locals O Γ sort) (occurrence : O) :=
  (occurrence, ContextualConditionalExecution.guardRows locals before.declarations before.rows occurrence)

structure WithQueries (before : ContextualConditionalExecution.State locals O Γ sort) : Type 1 where
  firing : ContextualConditionalExecution.Firing locals before
  queries : List (DataQuery (ContextualActivatedStep.target locals before.declarations)
    (O × ContextualConditionalRows.Row locals (ContextualActivatedStep.target locals before.declarations) Γ sort) O)
  observations : ∀ query ∈ queries,
    AskData (ContextualConditionalExecution.information locals before.declarations before.occupied firing.selection firing.rule
      before.rows before.equations) query (nativeLabels locals before) before.present

def WithQueries.ofPlain (firing : ContextualConditionalExecution.Firing locals before) : WithQueries locals before :=
  ⟨firing, [], by intro query member; cases member⟩

theorem admit_data_query_iff (firing : ContextualConditionalExecution.Firing locals before)
    (query : DataQuery (ContextualActivatedStep.target locals before.declarations)
      (O × ContextualConditionalRows.Row locals (ContextualActivatedStep.target locals before.declarations) Γ sort) O) :
    (∃ observed : WithQueries locals before, observed.firing = firing ∧ observed.queries = [query]) ↔
      AskData (ContextualConditionalExecution.information locals before.declarations before.occupied firing.selection firing.rule
        before.rows before.equations) query (nativeLabels locals before) before.present := by
  constructor
  · rintro ⟨observed, same, queries⟩
    have checked := observed.observations query (by rw [queries]; exact List.mem_singleton_self _)
    rw [same] at checked
    exact checked
  · intro checked
    exact ⟨⟨firing, [query], fun selected member => (List.mem_singleton.mp member) ▸ checked⟩, rfl, rfl⟩

/-- The query is validated against exactly the existing firing's input information and world. -/
theorem admit_condition_iff (firing : ContextualConditionalExecution.Firing locals before)
    (condition : Candidate (ContextualActivatedStep.target locals before.declarations) → Prop)
    (marker : O) (present : marker ∈ before.present) :
    (∃ observed : WithQueries locals before,
      observed.firing = firing ∧ observed.queries = [liftPoint (ofCondition condition marker)]) ↔
      ∀ (Future : Type) (future : Future → MetaArity S)
        (candidate : Assignment (ContextualActivatedStep.target locals before.declarations) future),
        ContextualResidual.Models candidate
          (ContextualConditionalExecution.information locals before.declarations before.occupied firing.selection firing.rule
            before.rows before.equations) → condition ⟨Future, future, candidate⟩ := by
  constructor
  · rintro ⟨observed, sameFiring, sameQueries⟩
    have checked := observed.observations (liftPoint (ofCondition condition marker))
      (by rw [sameQueries]; exact List.mem_singleton_self _)
    rw [sameFiring] at checked
    exact (ask_condition_iff condition marker before.present present _).mp
      ((lift_point_ask_iff _ _ (ContextualConditionalExecution.guardRows locals before.declarations before.rows) before.present).mp checked)
  · intro accepted
    refine ⟨⟨firing, [liftPoint (ofCondition condition marker)], ?_⟩, rfl, rfl⟩
    intro query member
    have only := List.mem_singleton.mp member
    subst query
    apply (lift_point_ask_iff _ _ (ContextualConditionalExecution.guardRows locals before.declarations before.rows) before.present).mpr
    exact (ask_condition_iff condition marker before.present present _).mpr accepted

/-- A solvable native attempt cannot validate a false predicate through an empty model set. -/
theorem false_condition_is_refused (firing : ContextualConditionalExecution.Firing locals before)
    (marker : O) (present : marker ∈ before.present) :
    ¬ ∃ observed : WithQueries locals before,
      observed.firing = firing ∧ observed.queries = [liftPoint (ofCondition (fun _ => False) marker)] := by
  intro observed
  have impossible := (admit_condition_iff locals firing (fun _ => False) marker present).mp observed
  obtain ⟨Future, future, candidate, model⟩ := firing.admitted.solvable
  exact impossible Future future candidate model

end Firings

section SourceGuards

open ContextualSourceSchedules ContextualConjunctiveQueries

variable {SourceO First Last Marker : Type} [DecidableEq SourceO] [DecidableEq Marker]
    {first : First → MetaArity S} {last : Last → MetaArity S} {Γ : Ctx S} {sort : S.Srt}
    {before : ContextualClauseSourceState.World first SourceO Γ sort}
    {after : ContextualClauseSourceState.World last SourceO Γ sort}

noncomputable def ofOriginalGuardPoint {Variables : Type}
    (schedule : Schedule S SourceO Γ sort before after) (queries : Variables → MetaArity S)
    (check : Check (Term (signature S (queryFamily queries after.declarations)) Γ sort)) (marker : Marker) :
    Query (family queries last after.declarations) Marker :=
  ofCondition (fun candidate => schedule.ownEntryCondition queries check candidate.declarations candidate.assignment) marker

/-- Each regressed original guard is an existing complete predicate query at the same information cut. -/
theorem original_guards_as_point_queries {Variables : Type}
    (schedule : Schedule S SourceO Γ sort before after) (shapes : schedule.ShapesHold)
    (resources : Executable ContextualSourceSchedules.Schedule.unitLabel before.present schedule.commits)
    (queries : Variables → MetaArity S)
    (plan : ContextualPublication.Plan (Term (signature S (queryFamily queries after.declarations)) Γ sort))
    (picked : Selection SourceO) (marker : Marker) (observedWorld : Finset Marker) (present : marker ∈ observedWorld) :
    (originalCut after queries plan picked).Holds ↔
      ∀ check ∈ plan.rule.checks,
        Ask (ContextualClauseSourceState.information queries last after plan picked)
          (ofOriginalGuardPoint schedule queries check marker) observedWorld := by
  rw [schedule.original_cut_entry_iff shapes resources queries plan picked]
  apply forall_congr'
  intro check
  apply forall_congr'
  intro _member
  exact (ask_condition_iff
    (fun candidate => schedule.ownEntryCondition queries check candidate.declarations candidate.assignment)
    marker observedWorld present (ContextualClauseSourceState.information queries last after plan picked)).symm

end SourceGuards

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPredicateQueryAdmission
