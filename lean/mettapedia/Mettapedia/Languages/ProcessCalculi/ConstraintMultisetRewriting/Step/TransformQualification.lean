import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

/-!
# Joined qualification: the occurrence core is the one-frame step, and absence is one concept

The occurrence core (`ConstraintMultisetRewriting.Step`, the relation of `OccurrenceStep`) carries many
results: resource controls, the Need machine, snapshot copying, the census and the
absence controls. The candidate step's one-frame instance is `AnnotatedRuns.firstOrder`. This module
places the first inside the second, so those results are statements about one instance of the
common interface `Interface.Step`.

## Placement

* `core_step_iff_admitted`: a core step is exactly an admitted firing of `firstOrder` with no
  predicate queries, and its result.
* `query_step_iff_admitted`: a core step with predicate queries
  (`PredicateQueryAdmission.Step`) is exactly an admitted firing of `firstOrder` with those queries.
* `run_coreReaches`: every run of `firstOrder` projects to a core reachability; queries only
  restrict admission.
* `coreReaches_iff_run`: core reachability is exactly a run of `firstOrder` whose firings have no
  queries.

## What one firing commits

* `added_card_le`: an admitted firing adds at most as many occurrences as its rule produces.
* `no_bounded_family_commits`: a rule family with bounded produce lists cannot commit, in one
  firing, a block that adds more rows than the bound. Atomic blocks of unbounded size therefore need
  rules computed per block.

## Absence: a guard and a predicate query are the same observation

The tree states absence two ways: as the guard `Check.absent p` of a rule, and as a predicate query
whose census is empty. For a decidable equivalence they coincide.

* `absenceQuery_holds_iff`: at every solution, the empty-census query of the region of `p` holds
  exactly when the guard `absent p` holds.
* `admits_absent_check_iff_query`: moving an absence guard into the firing's predicate queries keeps
  admission of the one-frame instance, so the guard part and the query part of the interface's
  `Holds` read absence identically.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.TransformQualification

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
  (PredicateQuery regionOf)
open AnnotatedRuns (Firing firstOrder)

universe uT uS uO

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]
variable (A : SubstitutionAction T S) (label : O → T)

/-! ## The occurrence core inside the one-frame instance -/

/-- **A core step is an admitted firing of the one-frame instance without queries.** -/
theorem core_step_iff_admitted (rule : RuleInstance T) (C D : Configuration T O) :
    ConstraintMultisetRewriting.Step A label rule C D ↔
      ∃ (selection : Selection O)
        (admitted : (firstOrder (S := S) A label).Admits (s := C)
          (⟨rule, [], selection⟩ : Firing T S O)),
        (firstOrder A label).result _ admitted = D := by
  constructor
  · rintro ⟨selection, valid, rfl⟩
    exact ⟨selection, (PredicateQueryAdmission.valid_empty_iff A label rule C selection).mpr valid,
      rfl⟩
  · rintro ⟨selection, admitted, rfl⟩
    exact ⟨selection, (PredicateQueryAdmission.valid_empty_iff A label rule C selection).mp admitted,
      rfl⟩

/-- **A core step with predicate queries is an admitted firing of the one-frame instance with
those queries.** -/
theorem query_step_iff_admitted (rule : RuleInstance T)
    (queries : List (PredicateQueryAdmission.Query T S O)) (C D : Configuration T O) :
    PredicateQueryAdmission.Step A label rule queries C D ↔
      ∃ (selection : Selection O)
        (admitted : (firstOrder A label).Admits (s := C) (⟨rule, queries, selection⟩ : Firing T S O)),
        (firstOrder A label).result _ admitted = D := by
  constructor
  · rintro ⟨selection, valid, rfl⟩
    exact ⟨selection, valid, rfl⟩
  · rintro ⟨selection, admitted, rfl⟩
    exact ⟨selection, admitted, rfl⟩

/-- Reachability by steps of the occurrence core. -/
def CoreReaches (C D : Configuration T O) : Prop :=
  Relation.ReflTransGen (fun X Y => ∃ rule, ConstraintMultisetRewriting.Step A label rule X Y) C D

/-- **Every run of the one-frame instance projects to core reachability.** Queries only restrict
admission; the update is the core's. -/
theorem run_coreReaches : ∀ {C : Configuration T O} (r : (firstOrder (S := S) A label).Run C),
    CoreReaches A label C r.last
  | _, .nil _ => Relation.ReflTransGen.refl
  | _, .cons f admitted rest =>
      Relation.ReflTransGen.head ⟨f.rule, f.selection, admitted.firing, rfl⟩
        (run_coreReaches rest)

/-- **Core reachability is exactly a run of the one-frame instance without queries.** -/
theorem coreReaches_iff_run (C D : Configuration T O) :
    CoreReaches A label C D ↔
      ∃ r : (firstOrder (S := S) A label).Run C, r.last = D ∧ ∀ x ∈ r.word, x.2.queries = [] := by
  constructor
  · intro reach
    induction reach using Relation.ReflTransGen.head_induction_on with
    | refl => exact ⟨.nil D, rfl, by simp [Interface.Step.Run.word]⟩
    | head step _ ih =>
        obtain ⟨rule, selection, valid, rfl⟩ := step
        obtain ⟨r, last, free⟩ := ih
        refine ⟨.cons (⟨rule, [], selection⟩ : Firing T S O)
          ((PredicateQueryAdmission.valid_empty_iff A label rule _ selection).mpr valid) r, last, ?_⟩
        intro x member
        simp only [Interface.Step.Run.word, List.mem_cons] at member
        rcases member with rfl | member
        · rfl
        · exact free x member
  · rintro ⟨r, rfl, -⟩
    exact run_coreReaches A label r

/-! ## What one firing can commit

An admitted firing makes exactly its rule's produced terms, so the occurrences it adds number at
most the length of its rule's produce list. A family of rules whose produce lists are bounded
therefore bounds what one firing commits: an atomic block that must add more rows is not one firing
of any rule of the family. -/

/-- **One firing adds at most its rule's produced rows.** -/
theorem added_card_le {C : Configuration T O} (f : Firing T S O)
    (admitted : (firstOrder A label).Admits (s := C) f) :
    (((firstOrder A label).result f admitted).present \ C.present).card ≤ f.rule.produce.length := by
  have lengths : f.selection.made.length = f.rule.produce.length := by
    rw [← admitted.firing.outputs, List.length_map]
  calc (((firstOrder A label).result f admitted).present \ C.present).card
      ≤ f.selection.made.toFinset.card := by
        apply Finset.card_le_card
        intro o member
        change o ∈ MeTTaCalculus.OccurrenceCommits.fire C.present (f.selection.commit (T := T)) \
          C.present at member
        rw [Finset.mem_sdiff, MeTTaCalculus.OccurrenceCommits.mem_fire] at member
        rcases member.1 with old | made
        · exact absurd old.1 member.2
        · simpa [Selection.commit] using made
    _ ≤ f.selection.made.length := List.toFinset_card_le _
    _ = f.rule.produce.length := lengths

/-- **A bounded rule family bounds atomic commits.** If every rule a step may fire produces at most
`bound` terms, no admitted firing adds more than `bound` rows; a block that adds more is not one
firing. -/
theorem no_bounded_family_commits {C D : Configuration T O} (rules : Set (RuleInstance T))
    (bound : ℕ) (bounded : ∀ rule ∈ rules, rule.produce.length ≤ bound)
    (large : bound < (D.present \ C.present).card) :
    ¬ ∃ (f : Firing T S O) (admitted : (firstOrder A label).Admits (s := C) f),
      f.rule ∈ rules ∧ (firstOrder A label).result f admitted = D := by
  rintro ⟨f, admitted, member, rfl⟩
  exact absurd (le_trans (added_card_le A label f admitted) (bounded _ member)) (not_le.mpr large)

/-! ## Absence as a guard and as a predicate query -/

section Absence

variable [∀ a b : T, Decidable (A.E a b)]

/-- The predicate query whose region, at a solution, is the occurrences matching `pattern`, and
whose census is empty. -/
def absenceQuery (pattern : T) : PredicateQueryAdmission.Query T S O :=
  ⟨fun σ t => decide (A.E (A.apply σ pattern) (A.apply σ t)), ∅⟩

omit [DecidableEq O] in
/-- **The empty-census query is the absence guard**, at every solution and every store. -/
theorem absenceQuery_holds_iff (pattern : T) (σ : S) (store : Finset O) :
    ((absenceQuery (O := O) A pattern).atSolution σ).Holds label store ↔
      (Check.absent pattern).Holds A σ label store := by
  simp only [absenceQuery, PredicateQueryAdmission.Query.atSolution, PredicateQuery.Holds,
    regionOf, Check.Holds, Finset.filter_eq_empty_iff, decide_eq_true_eq]

/-- **Moving an absence guard into the predicate queries keeps admission.** The guard part and the
query part of the one-frame instance's `Holds` read absence identically. -/
theorem admits_absent_check_iff_query (rule : RuleInstance T) (pattern : T)
    (queries : List (PredicateQueryAdmission.Query T S O)) (selection : Selection O)
    (C : Configuration T O) :
    (firstOrder A label).Admits (s := C)
        (⟨{ rule with checks := rule.checks ++ [.absent pattern] }, queries, selection⟩ :
          Firing T S O) ↔
      (firstOrder A label).Admits (s := C)
        (⟨rule, queries ++ [absenceQuery A pattern], selection⟩ : Firing T S O) := by
  constructor
  · rintro ⟨firing, observations⟩
    refine ⟨⟨firing.take_distinct, firing.output_distinct, firing.take_length, firing.read_length,
      firing.outputs, firing.occurrences, firing.consistent,
      fun check member => firing.checks check (List.mem_append_left _ member)⟩, ?_⟩
    intro query member
    rcases List.mem_append.mp member with member | member
    · exact observations query member
    · obtain rfl := List.mem_singleton.mp member
      intro σ solved
      exact (absenceQuery_holds_iff A label pattern σ C.present).mpr
        (firing.checks _ (List.mem_append_right _ (List.mem_singleton_self _)) σ solved)
  · rintro ⟨firing, observations⟩
    refine ⟨⟨firing.take_distinct, firing.output_distinct, firing.take_length, firing.read_length,
      firing.outputs, firing.occurrences, firing.consistent, ?_⟩,
      fun query member => observations query (List.mem_append_left _ member)⟩
    intro check member
    rcases List.mem_append.mp member with member | member
    · exact firing.checks check member
    · obtain rfl := List.mem_singleton.mp member
      intro σ solved
      exact (absenceQuery_holds_iff A label pattern σ C.present).mp
        (observations _ (List.mem_append_right _ (List.mem_singleton_self _)) σ solved)

end Absence

#print axioms core_step_iff_admitted
#print axioms query_step_iff_admitted
#print axioms run_coreReaches
#print axioms coreReaches_iff_run
#print axioms added_card_le
#print axioms no_bounded_family_commits
#print axioms absenceQuery_holds_iff
#print axioms admits_absent_check_iff_query

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.TransformQualification
