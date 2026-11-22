import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.PatternFootprints.Kinds
import Mettapedia.GSLT.Causality.ResourceSelection
import Mathlib.Logic.Function.DependsOn
import Mathlib.Algebra.Group.Indicator

/-!
# Two readings of a match

A `match` reads a space through a pattern.  It can be read in two ways, and they
have different footprints.

**One answer of a match is a positive read of one kind** (`oneAnswer`): the
alternative sees that the kind is present and answers.

* Its footprint is that one kind (`oneAnswer_footprint`).
* Its outcome is still there on a state exactly when the kind is present there
  (`oneAnswer_stillHas_iff`).  So no addition invalidates it
  (`oneAnswer_stillHas_add`), no change of another kind invalidates it
  (`oneAnswer_stillHas_of_eq`), and the removal of the last occurrence of its
  own kind does (`ReadingControls.removal_of_its_kind_invalidates`).
* Validation by kept reads asks for more than that: the multiplicity must be the
  same (`oneAnswer_readsKept_iff`).  An addition of the kind itself changes what
  was read and leaves the answer valid (`oneAnswer_add_same_kind`).
* A match over finitely many candidate kinds is the region of these alternatives
  (`Region.matchKinds`), and its answers from a state are those of the candidates
  that are present (`Region.matchKinds_answers`).

**The whole bag of answers is a complete read of the pattern**: the
multiplicities of the state on the kinds the pattern matches, `Set.indicator`
of that set.

* It depends on the state at those kinds only (`dependsOn_indicator`), and every
  set of kinds it depends on contains all of them (`dependsOn_indicator_iff`).
  Two states have the same complete read exactly when they agree on those kinds
  (`indicator_eq_iff_eqOn`).
  So the footprint of the complete read is the pattern, exactly; over a pattern
  that matches infinitely many kinds it has no finite footprint
  (`not_dependsOn_indicator_finite`).
* An addition changes it exactly when it adds a kind that the pattern matches
  (`indicator_add_eq_iff`, `indicator_add_single_eq_iff`): the phantom.  So does
  a removal (`indicator_eq_of_add_single_iff` read from the result).
* It is the complete match of `GSLT.Causality.ResourceSelection`, read by kinds
  (`marking_allMatches`); there a new match invalidates a captured complete
  read (`ResourceSelection.commitAll_rejects_new_matches`) and a frame without a
  match does not (`ResourceSelection.commitAll_add_irrelevant_frame`).
* Over finitely many kinds it is a readout (`Readout.complete`); the proposal that
  answers with it reads those kinds and writes nothing (`allAnswers_footprint`),
  and for it the two validations coincide
  (`allAnswers_stillHas_iff_readsKept`): the complete read is exactly as
  sensitive as its footprint, and the positive read is less.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.FootprintedSpaceTransactions
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Causality

universe u w

variable {Location : Type u} {Answer : Type w}

/-! ## One answer of a match -/

section OneAnswer

variable [DecidableEq Location]

/-- Publishing the one step that sees a kind: the state, where the kind is
present. -/
theorem publish_seeKind (kind : Location) (state : Location → ℕ) :
    publish [seeKind kind] state = if 0 < state kind then some state else none := by
  rw [publish_cons]
  by_cases present : 0 < state kind
  · rw [if_pos present, (fire_seeKind_eq_some_iff kind state state).mpr ⟨present, rfl⟩]
    rfl
  · rw [if_neg present]
    cases fired : (seeKind kind).fire state with
    | none => rfl
    | some target =>
        exact absurd ((fire_seeKind_eq_some_iff kind state target).mp fired).1 present

/-- **One answer of a match**: see that one kind is present, and answer. -/
def oneAnswer (kind : Location) (answer : Answer) : Proposal Location ℕ Answer :=
  ⟨[seeKind kind], Readout.const answer⟩

/-- **Its footprint is the one kind**, read and not written. -/
theorem oneAnswer_footprint (kind : Location) (answer : Answer) :
    (oneAnswer kind answer).reads = {kind} ∧ (oneAnswer kind answer).writes = ∅ := by
  constructor
  · show (seeKind kind).rule.reads ∪ ∅ ∪ ∅ = {kind}
    rw [(seeKind_footprint kind).1, Finset.union_empty, Finset.union_empty]
  · show (seeKind kind).rule.writes ∪ ∅ = ∅
    rw [(seeKind_footprint kind).2, Finset.union_empty]

/-- **The outcome is still there exactly where the kind is present.** -/
theorem oneAnswer_stillHas_iff (kind : Location) (answer : Answer) (live : Location → ℕ) :
    (oneAnswer kind answer).region.StillHas live (answer, oneAnswer kind answer) ↔
      0 < live kind := by
  rw [Region.stillHas_iff, Proposal.region_proposals]
  show _ ∧ (∃ view, publish [seeKind kind] live = some view ∧ answer = answer) ↔ _
  rw [publish_seeKind]
  constructor
  · rintro ⟨-, view, published, -⟩
    by_contra absent
    rw [if_neg absent] at published
    cases published
  · intro present
    exact ⟨List.mem_singleton_self _, live, if_pos present, rfl⟩

/-- **No addition invalidates one answer of a match**, of its own kind or of
another. -/
theorem oneAnswer_stillHas_add {kind : Location} {answer : Answer} {state : Location → ℕ}
    (has : (oneAnswer kind answer).region.StillHas state (answer, oneAnswer kind answer))
    (added : Location → ℕ) :
    (oneAnswer kind answer).region.StillHas (state + added) (answer, oneAnswer kind answer) :=
  (oneAnswer_stillHas_iff kind answer _).mpr
    (Nat.lt_of_lt_of_le ((oneAnswer_stillHas_iff kind answer state).mp has) (Nat.le_add_right _ _))

/-- **No change of another kind invalidates it**: the removal of another kind
among them. -/
theorem oneAnswer_stillHas_of_eq {kind : Location} {answer : Answer} {state live : Location → ℕ}
    (has : (oneAnswer kind answer).region.StillHas state (answer, oneAnswer kind answer))
    (same : live kind = state kind) :
    (oneAnswer kind answer).region.StillHas live (answer, oneAnswer kind answer) :=
  (oneAnswer_stillHas_iff kind answer live).mpr
    (same ▸ (oneAnswer_stillHas_iff kind answer state).mp has)

/-- The removal of another kind, in particular. -/
theorem oneAnswer_stillHas_after_removeKind {kind other : Location} (different : other ≠ kind)
    {answer : Answer} {state next : Location → ℕ}
    (has : (oneAnswer kind answer).region.StillHas state (answer, oneAnswer kind answer))
    (removed : (removeKind other).fire state = some next) :
    (oneAnswer kind answer).region.StillHas next (answer, oneAnswer kind answer) := by
  refine oneAnswer_stillHas_of_eq has ?_
  have same := congrFun ((fire_removeKind_eq_some_iff other state next).mp removed) kind
  rw [same]
  show next kind = next kind + (Pi.single other 1 : Location → ℕ) kind
  rw [Pi.single_eq_of_ne (Ne.symm different), add_zero]

/-- **Validation by kept reads asks that the multiplicity is the same.** -/
theorem oneAnswer_readsKept_iff (kind : Location) (answer : Answer)
    (snapshot live : Location → ℕ) :
    (oneAnswer kind answer).ReadsKept snapshot live ↔ snapshot kind = live kind := by
  unfold Proposal.ReadsKept
  rw [(oneAnswer_footprint kind answer).1, (oneAnswer_footprint kind answer).2,
    Finset.union_empty]
  constructor
  · intro agrees
    exact agrees kind (Finset.mem_singleton_self kind)
  · intro same location inside
    rw [Finset.mem_singleton.mp inside]
    exact same

/-- **An addition of the kind itself changes what was read and leaves the answer
valid**: the reads are not kept, and the outcome is still there. -/
theorem oneAnswer_add_same_kind {kind : Location} {answer : Answer} {state : Location → ℕ}
    (has : (oneAnswer kind answer).region.StillHas state (answer, oneAnswer kind answer)) :
    (oneAnswer kind answer).region.StillHas (state + Pi.single kind 1)
        (answer, oneAnswer kind answer) ∧
      ¬ (oneAnswer kind answer).ReadsKept state (state + Pi.single kind 1) := by
  refine ⟨oneAnswer_stillHas_add has _, ?_⟩
  rw [oneAnswer_readsKept_iff]
  show ¬ state kind = state kind + (Pi.single kind 1 : Location → ℕ) kind
  rw [Pi.single_eq_same]
  omega

/-- **A match over finitely many candidate kinds, as a region**: one alternative
for each candidate, which sees the kind and answers with what the candidate
carries. -/
def Region.matchKinds (candidates : List (Location × Answer)) : Region Location ℕ Answer :=
  Region.alternatives (candidates.map fun candidate => (oneAnswer candidate.1 candidate.2).region)

/-- **Its answers from a state are those of the candidates that are present**, in
the order of the candidates. -/
theorem Region.matchKinds_answers (candidates : List (Location × Answer))
    (state : Location → ℕ) :
    ((Region.matchKinds candidates).branchLocal state).map Prod.fst =
      (candidates.filter fun candidate => 0 < state candidate.1).map Prod.snd := by
  unfold Region.matchKinds
  rw [Region.branchLocal_alternatives]
  induction candidates with
  | nil => rfl
  | cons candidate rest ih =>
      rw [List.map_cons, List.flatMap_cons, List.map_append, ih, Proposal.region_branchLocal]
      show (((publish [seeKind candidate.1] state).map fun view =>
        (candidate.2, oneAnswer candidate.1 candidate.2)).toList).map Prod.fst ++ _ = _
      rw [publish_seeKind]
      by_cases present : 0 < state candidate.1
      · rw [if_pos present, List.filter_cons_of_pos (by simpa using present)]
        rfl
      · rw [if_neg present, List.filter_cons_of_neg (by simpa using present)]
        rfl

end OneAnswer

/-! ## The bag of answers of a match -/

section Complete

/-- **The complete read depends on the state at the kinds of the pattern only.** -/
theorem dependsOn_indicator (footprint : Set Location) :
    DependsOn (fun state : Location → ℕ => footprint.indicator state) footprint := by
  classical
  intro state other agrees
  funext kind
  show footprint.indicator state kind = footprint.indicator other kind
  by_cases inside : kind ∈ footprint
  · rw [Set.indicator_of_mem inside, Set.indicator_of_mem inside]
    exact agrees kind inside
  · rw [Set.indicator_of_notMem inside, Set.indicator_of_notMem inside]

/-- **The footprint of the complete read is the pattern, exactly**: it depends on
a set of kinds exactly when that set contains every kind the pattern matches. -/
theorem dependsOn_indicator_iff {footprint reads : Set Location} :
    DependsOn (fun state : Location → ℕ => footprint.indicator state) reads ↔
      footprint ⊆ reads := by
  classical
  constructor
  · intro depends kind inside
    by_contra outside
    have same : footprint.indicator (0 : Location → ℕ) kind =
        footprint.indicator (Pi.single kind 1) kind :=
      congrFun
        (depends (x := 0) (y := Pi.single kind 1) fun other otherInside => by
          have different : other ≠ kind := fun equal => outside (equal ▸ otherInside)
          simp [different]) kind
    rw [Set.indicator_of_mem inside, Set.indicator_of_mem inside] at same
    simp at same
  · exact fun subset => (dependsOn_indicator footprint).mono subset

/-- **Two states have the same complete read exactly when they agree on the kinds
of the pattern.** -/
theorem indicator_eq_iff_eqOn (footprint : Set Location) (state other : Location → ℕ) :
    footprint.indicator state = footprint.indicator other ↔ Set.EqOn state other footprint := by
  constructor
  · intro same kind inside
    have atKind := congrFun same kind
    rwa [Set.indicator_of_mem inside, Set.indicator_of_mem inside] at atKind
  · exact fun agrees => dependsOn_indicator footprint fun kind inside => agrees inside

/-- **A complete read of a pattern that matches infinitely many kinds has no
finite footprint.** -/
theorem not_dependsOn_indicator_finite {footprint : Set Location} (infinite : footprint.Infinite)
    (reads : Finset Location) :
    ¬ DependsOn (fun state : Location → ℕ => footprint.indicator state) ↑reads := fun depends =>
  infinite (reads.finite_toSet.subset (dependsOn_indicator_iff.mp depends))

/-- **An addition changes the complete read exactly when it adds a kind the
pattern matches.** -/
theorem indicator_add_eq_iff (footprint : Set Location) (state added : Location → ℕ) :
    footprint.indicator (state + added) = footprint.indicator state ↔
      ∀ kind ∈ footprint, added kind = 0 := by
  classical
  constructor
  · intro same kind inside
    have atKind := congrFun same kind
    rw [Set.indicator_of_mem inside, Set.indicator_of_mem inside] at atKind
    have : state kind + added kind = state kind := atKind
    omega
  · intro nothing
    funext kind
    by_cases inside : kind ∈ footprint
    · rw [Set.indicator_of_mem inside, Set.indicator_of_mem inside]
      show state kind + added kind = state kind
      rw [nothing kind inside, add_zero]
    · rw [Set.indicator_of_notMem inside, Set.indicator_of_notMem inside]

/-- **The phantom.**  The addition of one occurrence changes the complete read
exactly when the pattern matches its kind. -/
theorem indicator_add_single_eq_iff [DecidableEq Location] (footprint : Set Location)
    (state : Location → ℕ) (kind : Location) :
    footprint.indicator (state + Pi.single kind 1) = footprint.indicator state ↔
      kind ∉ footprint := by
  rw [indicator_add_eq_iff]
  constructor
  · intro nothing inside
    have := nothing kind inside
    simp at this
  · intro outside other inside
    have different : other ≠ kind := fun equal => outside (equal ▸ inside)
    simp [different]

/-- And so does a removal: where the state is the result with one occurrence put
back, the complete reads of the two agree exactly when the pattern does not match
the kind. -/
theorem indicator_eq_of_add_single_iff [DecidableEq Location] (footprint : Set Location)
    {state next : Location → ℕ} {kind : Location} (removed : state = next + Pi.single kind 1) :
    footprint.indicator next = footprint.indicator state ↔ kind ∉ footprint := by
  rw [removed, eq_comm]
  exact indicator_add_single_eq_iff footprint next kind

/-- **The complete match of a bag, read by kinds, is the complete read of the
kinds the predicate accepts.** -/
theorem marking_allMatches [DecidableEq Location] (predicate : Location → Bool)
    (bag : Multiset Location) :
    marking (ResourceSelection.allMatches predicate bag) =
      Set.indicator {kind | predicate kind = true} (marking bag) := by
  funext kind
  show Multiset.count kind (bag.filter fun resource => predicate resource = true) = _
  rw [Multiset.count_filter]
  by_cases accepted : predicate kind = true
  · rw [if_pos accepted, Set.indicator_of_mem (by exact accepted)]
    rfl
  · rw [if_neg accepted, Set.indicator_of_notMem (by exact accepted)]

variable [DecidableEq Location]

/-- **The complete read of finitely many kinds, as a readout**: an answer that is
the whole bag of matches reads all of them. -/
def Readout.complete (footprint : Finset Location) : Readout Location ℕ (Location → ℕ) where
  reads := footprint
  value state kind := if kind ∈ footprint then state kind else 0
  value_local agrees := funext fun kind => by
    by_cases inside : kind ∈ footprint
    · rw [if_pos inside, if_pos inside]
      exact agrees kind inside
    · rw [if_neg inside, if_neg inside]

theorem Readout.complete_value (footprint : Finset Location) (state : Location → ℕ) :
    (Readout.complete footprint).value state = (↑footprint : Set Location).indicator state := by
  funext kind
  by_cases inside : kind ∈ footprint
  · rw [Set.indicator_of_mem (Finset.mem_coe.mpr inside)]
    exact if_pos inside
  · rw [Set.indicator_of_notMem (fun member => inside (Finset.mem_coe.mp member))]
    exact if_neg inside

/-- **The proposal that answers with the whole bag of matches**: no step, and the
complete read of the kinds. -/
def allAnswers (footprint : Finset Location) : Proposal Location ℕ (Location → ℕ) :=
  ⟨[], Readout.complete footprint⟩

/-- **Its footprint is the kinds of the pattern**, read and not written. -/
theorem allAnswers_footprint (footprint : Finset Location) :
    (allAnswers footprint).reads = footprint ∧ (allAnswers footprint).writes = ∅ := by
  constructor
  · show ∅ ∪ footprint = footprint
    exact Finset.empty_union footprint
  · rfl

/-- **For the complete read the two validations coincide.**  The answer read
from a snapshot is still the answer on a live state exactly when the reads are
kept. -/
theorem allAnswers_stillHas_iff_readsKept (footprint : Finset Location)
    (snapshot live : Location → ℕ) :
    (allAnswers footprint).region.StillHas live
        ((Readout.complete footprint).value snapshot, allAnswers footprint) ↔
      (allAnswers footprint).ReadsKept snapshot live := by
  rw [Region.stillHas_iff, Proposal.region_proposals]
  have footprintEq : (allAnswers footprint).reads ∪ (allAnswers footprint).writes = footprint := by
    show ∅ ∪ footprint ∪ ∅ = footprint
    rw [Finset.empty_union, Finset.union_empty]
  unfold Proposal.ReadsKept
  rw [footprintEq]
  constructor
  · rintro ⟨-, view, published, same⟩ kind inside
    cases published
    have atKind := congrFun same kind
    change (if kind ∈ footprint then live kind else 0) =
      (if kind ∈ footprint then snapshot kind else 0) at atKind
    rw [if_pos inside, if_pos inside] at atKind
    exact atKind.symm
  · intro kept
    refine ⟨List.mem_singleton_self _, live, rfl, ?_⟩
    exact (Readout.complete footprint).value_local fun kind inside => (kept kind inside).symm

end Complete

/-! ## Controls -/

namespace ReadingControls

open AddOnly (Kind noKinds)
open KindControls (oneA)

/-- **Positive, one answer**: with an `a` there, the answer for `a` is there. -/
theorem answer_where_present :
    (oneAnswer Kind.a ()).region.StillHas oneA ((), oneAnswer Kind.a ()) :=
  (oneAnswer_stillHas_iff _ _ _).mpr (by decide)

/-- **Negative, one answer**: without an `a` it is not. -/
theorem no_answer_where_absent :
    ¬ (oneAnswer Kind.a ()).region.StillHas noKinds ((), oneAnswer Kind.a ()) := fun has =>
  absurd ((oneAnswer_stillHas_iff _ _ _).mp has) (by decide)

/-- **The removal of the last occurrence of its own kind invalidates one answer**:
the removal fires, and on its result the answer is no longer there. -/
theorem removal_of_its_kind_invalidates :
    ((removeKind Kind.a).fire oneA).map (fun world => world .a) = some 0 ∧
      ∀ next, (removeKind Kind.a).fire oneA = some next →
        ¬ (oneAnswer Kind.a ()).region.StillHas next ((), oneAnswer Kind.a ()) := by
  refine ⟨by decide, fun next removed has => ?_⟩
  have present := (oneAnswer_stillHas_iff _ _ _).mp has
  have same := congrFun ((fire_removeKind_eq_some_iff Kind.a oneA next).mp removed) Kind.a
  have one : oneA Kind.a = 1 := rfl
  have single : (next + (Pi.single Kind.a 1 : Kind → ℕ)) Kind.a = next Kind.a + 1 := rfl
  rw [one, single] at same
  omega

/-- **Positive, a match as a region**: over the candidates `a` and `b`, with only
an `a` there, the match answers for `a`.  **Negative**: from the empty state it has
no answer. -/
theorem matchKinds_instances :
    ((Region.matchKinds [(Kind.a, 1), (Kind.b, 2)]).branchLocal oneA).map Prod.fst = [1] ∧
      ((Region.matchKinds [(Kind.a, 1), (Kind.b, 2)]).branchLocal noKinds).map Prod.fst = [] := by
  rw [Region.matchKinds_answers, Region.matchKinds_answers]
  decide

/-- **Positive, the complete read**: on the kind `a`, an addition of a `b` changes
nothing.  **Negative**: an addition of an `a` changes it. -/
theorem complete_read_instances :
    (Readout.complete {Kind.a}).value (oneA + Pi.single Kind.b 1) =
        (Readout.complete {Kind.a}).value oneA ∧
      (Readout.complete {Kind.a}).value (oneA + Pi.single Kind.a 1) ≠
        (Readout.complete {Kind.a}).value oneA := by
  rw [Readout.complete_value, Readout.complete_value, Readout.complete_value]
  constructor
  · exact (indicator_add_single_eq_iff _ _ _).mpr (by simp)
  · exact fun same => (indicator_add_single_eq_iff _ _ _).mp same (by simp)

/-- **Positive, the answer with the whole bag**: a change of another kind keeps
it.  **Negative**: the phantom does not. -/
theorem allAnswers_instances :
    (allAnswers {Kind.a}).region.StillHas (oneA + Pi.single Kind.b 1)
        ((Readout.complete {Kind.a}).value oneA, allAnswers {Kind.a}) ∧
      ¬ (allAnswers {Kind.a}).region.StillHas (oneA + Pi.single Kind.a 1)
        ((Readout.complete {Kind.a}).value oneA, allAnswers {Kind.a}) := by
  rw [allAnswers_stillHas_iff_readsKept, allAnswers_stillHas_iff_readsKept]
  constructor <;> decide

end ReadingControls

#print axioms publish_seeKind
#print axioms oneAnswer_footprint
#print axioms oneAnswer_stillHas_iff
#print axioms oneAnswer_stillHas_add
#print axioms oneAnswer_stillHas_of_eq
#print axioms oneAnswer_stillHas_after_removeKind
#print axioms oneAnswer_readsKept_iff
#print axioms oneAnswer_add_same_kind
#print axioms Region.matchKinds_answers
#print axioms dependsOn_indicator
#print axioms dependsOn_indicator_iff
#print axioms indicator_eq_iff_eqOn
#print axioms not_dependsOn_indicator_finite
#print axioms indicator_add_eq_iff
#print axioms indicator_add_single_eq_iff
#print axioms indicator_eq_of_add_single_iff
#print axioms marking_allMatches
#print axioms Readout.complete_value
#print axioms allAnswers_footprint
#print axioms allAnswers_stillHas_iff_readsKept
#print axioms ReadingControls.answer_where_present
#print axioms ReadingControls.no_answer_where_absent
#print axioms ReadingControls.removal_of_its_kind_invalidates
#print axioms ReadingControls.matchKinds_instances
#print axioms ReadingControls.complete_read_instances
#print axioms ReadingControls.allAnswers_instances

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions
