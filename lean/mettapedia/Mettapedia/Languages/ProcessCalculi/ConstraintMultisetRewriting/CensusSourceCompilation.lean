import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PredicateQueryAdmission
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.SourceQueries

/-!
# Complete source observations compose with occurrence admission

The existing source compiler supplies the complete queries, resource picks
and produced label bag. This bridge retains a nonempty equation store and
explicit tells while realizing that footprint through the same atomic
occurrence update. It does not replace a source matcher by an evaluator.

The final theorem starts with the actual ordered read program over a concrete
duplicate-free occurrence list. Its scanner completeness is proved by
construction, rather than supplied as a certificate from an unspecified
provider. Every returned linear row has an admitted commit, with exactly its
produced bag, assuming a fresh occurrence supply and joint consistency.

The source's finite matching and pure computed-value contracts are retained.
Its multiset `every` rejects repeated consumption. The set-based MM2 profile
has a different removal rule and is compared separately. This bridge does
not assert that either source's raw labels are already a decoded higher-order
caller observation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.CensusSourceCompilation

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.Machines

universe uT uS uO uV uP
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]

noncomputable def selection (commit : Commit O T) : Selection O :=
  ⟨commit.taken.toList, commit.kept.toList, commit.made.toList⟩

noncomputable def rule (label : O → T) (commit : Commit O T) (tells : EquationStore T) : RuleInstance T :=
  ⟨commit.taken.toList.map label, commit.kept.toList.map label, tells, [], commit.made.toList.map label⟩

omit [DecidableEq O] in
theorem models_self (A : SubstitutionAction T S) (candidate : S) (label : O → T) :
    ∀ chosen : List O, A.Models candidate (Selection.equations label (chosen.map label) chosen)
  | [] => A.models_nil candidate
  | first :: rest => by
      change A.Models candidate ((label first, label first) :: Selection.equations label (rest.map label) rest)
      exact (A.models_cons _ _ _).mpr ⟨A.equivalence.refl _, models_self A candidate label rest⟩

omit [DecidableEq O] in
theorem models_problem_iff (A : SubstitutionAction T S) (candidate : S) (label : O → T)
    (commit : Commit O T) (tells : EquationStore T) (before : Configuration T O) :
    A.Models candidate ((selection commit).problem label (rule label commit tells) before) ↔
      A.Models candidate (before.equations ++ tells) := by
  change A.Models candidate
    (before.equations ++ Selection.equations label (commit.taken.toList.map label) commit.taken.toList ++
      Selection.equations label (commit.kept.toList.map label) commit.kept.toList ++ tells) ↔ _
  simp only [SubstitutionAction.models_append]
  have taken := models_self A candidate label commit.taken.toList
  have kept := models_self A candidate label commit.kept.toList
  tauto

theorem realize_commit (A : SubstitutionAction T S) (label : O → T) (commit : Commit O T)
    (tells : EquationStore T) (before : Configuration T O)
    (enabled : Enabled label before.present commit)
    (consistent : A.Consistent (before.equations ++ tells)) :
    PredicateQueryAdmission.Valid A label (rule label commit tells)
        (commit.queries.map PredicateQueryAdmission.Query.fixed) before (selection commit) := by
  apply (PredicateQueryAdmission.valid_fixed_iff A label _ _ _ _).mpr
  refine ⟨?_, enabled.queries_hold⟩
  refine ⟨Finset.nodup_toList _, Finset.nodup_toList _, by simp [rule, selection],
    by simp [rule, selection], rfl, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa only [Selection.commit, selection, Finset.toList_toFinset] using enabled.taken_subset
    · simpa only [Selection.commit, selection, Finset.toList_toFinset] using enabled.kept_subset
    · simpa only [Selection.commit, selection, Finset.toList_toFinset] using enabled.apart
    · simpa only [Selection.commit, selection, Finset.toList_toFinset] using enabled.fresh
    · intro query member
      simp only [Selection.commit, List.not_mem_nil] at member
  · obtain ⟨candidate, solved⟩ := consistent
    exact ⟨candidate, (models_problem_iff A candidate label commit tells before).mpr solved⟩
  · intro check member
    simp only [rule, List.not_mem_nil] at member

theorem physical_result (label : O → T) (commit : Commit O T) (tells : EquationStore T)
    (before : Configuration T O) :
    ((selection commit).result label (rule label commit tells) before).present = fire before.present commit := by
  simp only [Selection.result, Selection.commit, selection, fire, Finset.toList_toFinset]

omit [DecidableEq O] in
theorem produced_bag (label : O → T) (commit : Commit O T) (tells : EquationStore T) :
    ((rule label commit tells).produce : Multiset T) = labels label commit.made := by
  change ((commit.made.toList.map label : List T) : Multiset T) = _
  rw [← Multiset.map_coe, Finset.coe_toList]
  rfl

/-- An actual completed query supplies the row, its complete footprint and
the produced bag. Only the source's own resource admission remains to check. -/
theorem realize_query_row {V : Type uV} {P : Type uP}
    (A : SubstitutionAction T S) (layer : Sources.TermLayer V T P) (matcher : Sources.Matcher V T P)
    (label : O → T) (contents : List O) (unique : contents.Nodup)
    (before : Configuration T O) (present : contents.toFinset = before.present)
    (template : List P) (sources : Sources.SourceList V T P)
    (row : Sources.Subst V T × List (Sources.Pick O T))
    (returned : row ∈ (ReadOnlyQuery.run (Sources.Query.scanList label contents)
      (Sources.Query.compile layer matcher label template sources (fun _ => none))).answer)
    (linear : (Sources.footprintOf row.2).Linear) (tells : EquationStore T)
    (consistent : A.Consistent (before.equations ++ tells))
    (supply : ∀ (avoid : Finset O) (term : T), ∃ occurrence, occurrence ∉ avoid ∧ label occurrence = term) :
    ∃ commit : Commit O T,
      Sources.IsCommitOf label before.present (Sources.footprintOf row.2) commit ∧
      PredicateQueryAdmission.Valid A label (rule label commit tells)
        (commit.queries.map PredicateQueryAdmission.Query.fixed) before (selection commit) ∧
      ((selection commit).result label (rule label commit tells) before).present = fire before.present commit ∧
      ((rule label commit tells).produce : Multiset T) = (Sources.footprintOf row.2).makes := by
  have scanned : Sources.Query.Complete label before.present (Sources.Query.scanList label contents) := by
    rw [← present]
    exact Sources.Query.scanList_complete label contents unique
  have member : row ∈ Sources.rows layer matcher label before.present template sources (fun _ => none) := by
    rw [← Sources.Query.run_compile layer matcher label before.present _ scanned template sources]
    exact Multiset.mem_coe.mpr returned
  obtain ⟨commit, realized⟩ := Sources.exists_isCommitOf (label := label) (S := before.present)
    supply (Sources.footprintOf row.2)
  have fires : Sources.Fires layer matcher label before.present ⟨sources, template⟩ commit :=
    ⟨row, member, linear, realized⟩
  exact ⟨commit, realized, realize_commit A label commit tells before fires.enabled consistent,
    physical_result label commit tells before, (produced_bag label commit tells).trans realized.made⟩

/-- With the existing matcher laws, the completed query row satisfies the
independent source judgment, including its all-answer constructors. -/
theorem query_row_is_declarative {V : Type uV} [DecidableEq V] {P : Type uP}
    (layer : Sources.TermLayer V T P) (matcher : Sources.Matcher V T P)
    (sound : Sources.Matcher.Sound layer matcher) (complete : Sources.Matcher.Complete layer matcher)
    (minimal : Sources.Matcher.Minimal layer matcher)
    (label : O → T) (contents : List O) (unique : contents.Nodup)
    (template : List P) (sources : Sources.SourceList V T P)
    (respects : ∀ eval ∈ sources.lets, Sources.Respects layer eval)
    (row : Sources.Subst V T × List (Sources.Pick O T))
    (returned : row ∈ (ReadOnlyQuery.run (Sources.Query.scanList label contents)
      (Sources.Query.compile layer matcher label template sources (fun _ => none))).answer) :
    Sources.DRow layer label contents.toFinset template sources (fun _ => none) row := by
  apply (Sources.agreement sound complete minimal sources respects (fun _ => none)).1 row
  rw [← Sources.Query.run_compile layer matcher label contents.toFinset _
    (Sources.Query.scanList_complete label contents unique) template sources]
  exact Multiset.mem_coe.mpr returned

/-- Conversely, every independent linear source derivation has a censused
atomic realization. Produced values are compared through the source's own
declared equality, not silently identified as syntactically equal. -/
theorem realize_declarative_row {V : Type uV} [DecidableEq V] {P : Type uP}
    (A : SubstitutionAction T S) (layer : Sources.TermLayer V T P) (matcher : Sources.Matcher V T P)
    (sound : Sources.Matcher.Sound layer matcher) (complete : Sources.Matcher.Complete layer matcher)
    (minimal : Sources.Matcher.Minimal layer matcher) (label : O → T)
    (before : Configuration T O) (transform : Sources.Transform V T P)
    (respects : ∀ eval ∈ transform.sources.lets, Sources.Respects layer eval)
    (row : Sources.Subst V T × List (Sources.Pick O T))
    (declared : Sources.DRow layer label before.present transform.template transform.sources (fun _ => none) row)
    (linear : (Sources.footprintOf row.2).Linear) (tells : EquationStore T)
    (consistent : A.Consistent (before.equations ++ tells))
    (supply : ∀ (avoid : Finset O) (term : T), ∃ occurrence, occurrence ∉ avoid ∧ label occurrence = term) :
    ∃ commit : Commit O T,
      Sources.Fires layer matcher label before.present transform commit ∧
      PredicateQueryAdmission.Valid A label (rule label commit tells)
        (commit.queries.map PredicateQueryAdmission.Query.fixed) before (selection commit) ∧
      commit.taken = (Sources.footprintOf row.2).takes.toFinset ∧
      commit.kept = (Sources.footprintOf row.2).keeps.toFinset ∧
      (∀ query, query ∈ commit.queries ↔ query ∈ (Sources.footprintOf row.2).queries) ∧
      Multiset.Rel layer.E ((rule label commit tells).produce : Multiset T) (Sources.footprintOf row.2).makes := by
  obtain ⟨commit, fires, taken, kept, queries, made⟩ :=
    Sources.fires_of_declarative sound complete minimal supply respects declared linear
  refine ⟨commit, fires, realize_commit A label commit tells before fires.enabled consistent,
    taken, kept, queries, ?_⟩
  rw [produced_bag]
  exact made

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.CensusSourceCompilation
