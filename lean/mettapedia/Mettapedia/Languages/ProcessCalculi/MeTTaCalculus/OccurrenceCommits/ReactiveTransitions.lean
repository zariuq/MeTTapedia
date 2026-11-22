import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Waves

/-!
# Reactive firing, waking contexts, and absence

A snapshot `transform` fires against the store it finds or fails. A reactive `for` (an `await`
statement, a conditional critical region, Linda's blocking `in`, STM's `retry`) **parks** until
its guard holds and then fires. This module asks what can wake a parked guard. It does not build
the borrowed-context transition system of Leifer–Milner and Ehrig–König (that is separate work);
it gives the facts about waking that such a system rests on.

## What wakes a parked guard

A guard is a predicate on stores. Arrivals only add occurrences.

* **Arrival adequacy is upward closure, restated** (`arrivalAdequate_iff`). "From every parked
  store, the arrival of a waking store's occurrences wakes the guard" is the same property as
  upward closure; the equivalence is a reformulation, not a result. It does not say that a guard
  which is not upward closed is never woken by an arrival: a uniqueness guard is woken from the
  empty store by one arrival (`Controls.uniqueness_woken_by_arrival`).
* **The content: a positive commit has a unique minimal waking context** (`enabled_union_iff`,
  `minimal_wake`). Parked at a store, a commit without predicate queries is woken by an arrival
  exactly when the arrival supplies `(taken ∪ kept) \ store`, what it needs and the store lacks;
  extra arrivals are framed (`fire_union_frame`). This is the minimal label a borrowed-context step
  of such a commit would carry.
* **Absence is downward closed** (`absence_downward_closed`). A parked absence guard is never
  woken by an arrival (`absence_not_woken_by_arrival`); it is woken by a removal
  (`absence_woken_by_removal`). `Controls.wait_for_unlock` waits for the lock to be taken: no
  additive context wakes it.
* **A predicate query of a non-empty region is neither** (`Controls.predicate_query_two_sided`):
  an arrival and a removal can each falsify it. It waits on any change of its region: an epoch.

So a runtime parks positive guards on **arrivals into the regions they use**, absence guards on
**removals from the regions they forbid**, and predicate queries on **any change of the regions
they query**: the per-region epoch (`CommitProtocol` proves that such an index misses no wakeup).

## Absence: stable only inside an owned scope, and the reason for strata

* **Stability** (`holds_fireList_of_no_write`): a predicate query stays valid across any run of
  commits none of which writes into its region. A region that only its owner writes is such a
  scope, and there an absence read is stable for as long as the owner does not write into it.
  One maker inside the region falsifies it (`Controls.absence_falsified_by_maker`).
* **Strata** (`exists_executable_perm_of_stratified`): a commit with an absence read must run
  before every commit that makes inside its region. A *stratification*, a rank that every
  such edge increases, is exactly a ranking of the precedence relation of a wave whose only spoils
  are absence spoils, so the strata order executes the wave. A cycle through absence has no
  stratification and no executable order (`Waves.Controls.absence_race_no_order`). Positive
  commits need no strata: they are stable under every arrival (`Enabled.frame_of_positive`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

universe u v

variable {O : Type u} [DecidableEq O] {R : Type v}

/-! ## Guards and arrivals -/

/-- A guard holds on every larger store once it holds. -/
def UpwardClosed (guard : Finset O → Prop) : Prop :=
  ∀ ⦃small large : Finset O⦄, small ⊆ large → guard small → guard large

/-- A guard holds on every smaller store once it holds. -/
def DownwardClosed (guard : Finset O → Prop) : Prop :=
  ∀ ⦃small large : Finset O⦄, small ⊆ large → guard large → guard small

/-- **Arrival adequacy**: whenever the guard holds at some store, every parked store that receives
that store's occurrences satisfies it. -/
def ArrivalAdequate (guard : Finset O → Prop) : Prop :=
  ∀ ⦃parked waking : Finset O⦄, guard waking → guard (parked ∪ waking)

/-- Arrival adequacy is upward closure, restated: a reformulation, not a result. -/
theorem arrivalAdequate_iff (guard : Finset O → Prop) : ArrivalAdequate guard ↔ UpwardClosed guard := by
  constructor
  · intro adequate small large sub holds
    have := adequate (parked := large) holds
    rwa [Finset.union_eq_left.mpr sub] at this
  · intro upward parked waking holds
    exact upward Finset.subset_union_right holds

omit [DecidableEq O] in
/-- A guard that is not upward closed has a wake that no arrival realizes: a store where it holds
and a larger store, reached by arrivals, where it fails. -/
theorem exists_unwake_of_not_upwardClosed {guard : Finset O → Prop} (notUp : ¬ UpwardClosed guard) :
    ∃ small large, small ⊆ large ∧ guard small ∧ ¬ guard large := by
  unfold UpwardClosed at notUp
  push Not at notUp
  obtain ⟨small, large, sub, holds, fails⟩ := notUp
  exact ⟨small, large, sub, holds, fails⟩

/-- A downward-closed guard that fails is never woken by an arrival. -/
theorem not_woken_by_arrival_of_downwardClosed {guard : Finset O → Prop}
    (downward : DownwardClosed guard) {parked : Finset O} (fails : ¬ guard parked)
    (arrival : Finset O) : ¬ guard (parked ∪ arrival) :=
  fun holds => fails (downward Finset.subset_union_left holds)

/-! ## Positive commits: a unique minimal waking context -/

section Positive

variable {label : O → R} {store : Finset O} {c : Commit O R}

/-- **Waking a positive commit.** For an arrival that avoids the commit's fresh identities, the
commit is enabled at the store plus the arrival exactly when the arrival supplies what the store
lacks of what the commit takes and keeps. -/
theorem enabled_union_iff (positive : c.Positive) (apart : Disjoint c.taken c.kept)
    (fresh : Disjoint c.made store) {arrival : Finset O} (avoids : Disjoint c.made arrival) :
    Enabled label (store ∪ arrival) c ↔ (c.taken ∪ c.kept) \ store ⊆ arrival := by
  constructor
  · intro enabled o member
    obtain ⟨used, notStore⟩ := Finset.mem_sdiff.mp member
    rcases Finset.mem_union.mp used with taken | kept
    · rcases Finset.mem_union.mp (enabled.taken_subset taken) with inStore | inArrival
      · exact absurd inStore notStore
      · exact inArrival
    · rcases Finset.mem_union.mp (enabled.kept_subset kept) with inStore | inArrival
      · exact absurd inStore notStore
      · exact inArrival
  · intro supplies
    have covered : ∀ o ∈ c.taken ∪ c.kept, o ∈ store ∪ arrival := by
      intro o used
      by_cases inStore : o ∈ store
      · exact Finset.mem_union_left _ inStore
      · exact Finset.mem_union_right _ (supplies (Finset.mem_sdiff.mpr ⟨used, inStore⟩))
    exact
      { taken_subset := fun o taken => covered o (Finset.mem_union_left _ taken)
        kept_subset := fun o kept => covered o (Finset.mem_union_right _ kept)
        apart := apart
        fresh := Finset.disjoint_union_right.mpr ⟨fresh, avoids⟩
        queries_hold := by simp [show c.queries = [] from positive] }

/-- **The minimal waking context** of a positive commit is what it needs and the store lacks: it
wakes the commit, and every waking arrival contains it. -/
theorem minimal_wake (positive : c.Positive) (apart : Disjoint c.taken c.kept)
    (fresh : Disjoint c.made store) (avoidsNeed : Disjoint c.made ((c.taken ∪ c.kept) \ store)) :
    Enabled label (store ∪ ((c.taken ∪ c.kept) \ store)) c ∧
      ∀ arrival, Disjoint c.made arrival → Enabled label (store ∪ arrival) c →
        (c.taken ∪ c.kept) \ store ⊆ arrival :=
  ⟨(enabled_union_iff positive apart fresh avoidsNeed).mpr le_rfl,
    fun _ avoids enabled => (enabled_union_iff positive apart fresh avoids).mp enabled⟩

/-- A positive commit's enabling is upward closed under arrivals that avoid its fresh
identities. -/
theorem enabled_upward_of_positive (positive : c.Positive) {small large : Finset O}
    (sub : small ⊆ large) (avoids : Disjoint c.made large) (enabled : Enabled label small c) :
    Enabled label large c := by
  have framed := enabled.frame_of_positive positive (frame := large \ small)
    (Finset.disjoint_of_subset_right Finset.sdiff_subset avoids)
  rwa [Finset.union_sdiff_of_subset sub] at framed

end Positive

/-! ## Absence -/

section Absence

variable {label : O → R}

/-- An absence read: the region holds nothing. -/
def AbsenceHolds (label : O → R) (region : R → Bool) (store : Finset O) : Prop :=
  (⟨region, ∅⟩ : PredicateQuery O R).Holds label store

omit [DecidableEq O] in
theorem absenceHolds_iff {region : R → Bool} {store : Finset O} :
    AbsenceHolds label region store ↔ ∀ o ∈ store, region (label o) = false := by
  unfold AbsenceHolds PredicateQuery.Holds
  constructor
  · intro empty o member
    by_contra inRegion
    have : o ∈ regionOf label store region :=
      mem_regionOf.mpr ⟨member, by simpa using inRegion⟩
    rw [empty] at this
    simp at this
  · intro outside
    ext o
    simp only [mem_regionOf, Finset.notMem_empty, iff_false, not_and]
    intro member inRegion
    rw [outside o member] at inRegion
    exact absurd inRegion (by decide)

omit [DecidableEq O] in
/-- **Absence is downward closed.** -/
theorem absence_downward_closed (region : R → Bool) :
    DownwardClosed (AbsenceHolds label region) := by
  intro small large sub holds
  rw [absenceHolds_iff] at holds ⊢
  exact fun o member => holds o (sub member)

/-- **A parked absence guard is never woken by an arrival.** -/
theorem absence_not_woken_by_arrival {region : R → Bool} {parked : Finset O}
    (fails : ¬ AbsenceHolds label region parked) (arrival : Finset O) :
    ¬ AbsenceHolds label region (parked ∪ arrival) :=
  not_woken_by_arrival_of_downwardClosed (absence_downward_closed region) fails arrival

/-- **A parked absence guard is woken by removing its region.** -/
theorem absence_woken_by_removal (region : R → Bool) (parked : Finset O) :
    AbsenceHolds label region (parked \ regionOf label parked region) := by
  rw [absenceHolds_iff]
  intro o member
  obtain ⟨inParked, notRegion⟩ := Finset.mem_sdiff.mp member
  by_contra inRegion
  exact notRegion (mem_regionOf.mpr ⟨inParked, by simpa using inRegion⟩)

/-- Along a run that makes nothing in a region, the region only shrinks
(`regionOf_fire_subset_of_no_make`, commit by commit). -/
theorem regionOf_fireList_subset_of_no_make {region : R → Bool} :
    ∀ {run : List (Commit O R)}, (∀ e ∈ run, ∀ o ∈ e.made, region (label o) = false) →
      ∀ store : Finset O, regionOf label (fireList store run) region ⊆ regionOf label store region
  | [], _, _ => fun _ member => member
  | e :: _, noMake, store =>
      (regionOf_fireList_subset_of_no_make
          (fun d member => noMake d (List.mem_cons_of_mem _ member)) (fire store e)).trans
        (regionOf_fire_subset_of_no_make (noMake e List.mem_cons_self))

/-- Along a run that takes nothing from a region, the region only grows
(`regionOf_subset_fire_of_no_take`, commit by commit). -/
theorem regionOf_subset_fireList_of_no_take {region : R → Bool} :
    ∀ {run : List (Commit O R)}, (∀ e ∈ run, ∀ o ∈ e.taken, region (label o) = false) →
      ∀ store : Finset O, regionOf label store region ⊆ regionOf label (fireList store run) region
  | [], _, _ => fun _ member => member
  | e :: _, noTake, store =>
      (regionOf_subset_fire_of_no_take (noTake e List.mem_cons_self)).trans
        (regionOf_subset_fireList_of_no_take
          (fun d member => noTake d (List.mem_cons_of_mem _ member)) (fire store e))

/-- A predicate query survives one commit that writes nothing inside its region. -/
theorem PredicateQuery.holds_fire_of_no_write {read : PredicateQuery O R} {store : Finset O}
    {c : Commit O R} (noWrite : ∀ o ∈ c.taken ∪ c.made, read.region (label o) = false)
    (holds : read.Holds label store) : read.Holds label (fire store c) := by
  unfold PredicateQuery.Holds at holds ⊢
  rw [regionOf_fire_of_no_write noWrite, holds]

/-- **Stability in a scope that nobody else writes.** A predicate query stays valid across any run
of commits that write nothing inside its region. -/
theorem holds_fireList_of_no_write {read : PredicateQuery O R} {store : Finset O}
    {run : List (Commit O R)}
    (noWrite : ∀ e ∈ run, ∀ o ∈ e.taken ∪ e.made, read.region (label o) = false)
    (holds : read.Holds label store) : read.Holds label (fireList store run) := by
  induction run generalizing store with
  | nil => exact holds
  | cons e rest ih =>
      exact ih (fun d member => noWrite d (List.mem_cons_of_mem _ member))
        (PredicateQuery.holds_fire_of_no_write (noWrite e List.mem_cons_self) holds)

end Absence

/-! ## Strata -/

/-- A commit's only spoils within a wave come from writes into the regions of its predicate
queries: no commit of the wave takes what another keeps. -/
def AbsenceOnlyConflicts (W : List (Commit O R)) : Prop :=
  ∀ e ∈ W, ∀ d ∈ W, Disjoint e.taken d.kept

/-- **Strata execute a wave.** If no commit of a clash-free wave takes what another keeps, a rank
that increases from every commit to every commit writing into the regions of its predicate
queries is a stratification; running the wave in strata order is executable. -/
theorem exists_executable_perm_of_stratified {label : O → R} {store : Finset O}
    {W : List (Commit O R)} (enabled : ∀ c ∈ W, Enabled label store c)
    (noClash : W.Pairwise (fun e d => ¬ Clash e d)) (absenceOnly : AbsenceOnlyConflicts W)
    {stratum : Commit O R → ℕ}
    (stratified : ∀ c ∈ W, ∀ p ∈ W, c ≠ p → WritesInto label p c → stratum c < stratum p) :
    ∃ l, l.Perm W ∧ Executable label store l := by
  refine exists_executable_perm_of_ranked enabled noClash (rank := stratum) ?_
  rintro e d ⟨inE, inD, different, spoils⟩
  rcases spoils with kept | writes
  · exact absurd (absenceOnly d inD e inE) kept
  · exact stratified e inE d inD different writes

/-! ## Controls -/

namespace Controls

open Atom

/-- **Waiting for an unlock.** "Add an output unless locked", parked at a store with the lock, is
not woken by any arrival; it is woken once the lock is taken. -/
theorem wait_for_unlock :
    (∀ arrival : Finset ℕ, ¬ AbsenceHolds label isLock ({1} ∪ arrival)) ∧
      AbsenceHolds label isLock (fire {1} lockTaker) := by
  refine ⟨fun arrival => absence_not_woken_by_arrival (by unfold AbsenceHolds; decide) arrival, ?_⟩
  unfold AbsenceHolds
  decide

/-- **A predicate query of a non-empty region is two-sided.** With occurrences `20` and `21` both
labelled `tok`, the query "the `tok` region is exactly occurrence `20`" holds at `{20}`; the
arrival of `21` falsifies it, and so does the removal of `20`. -/
theorem predicate_query_two_sided :
    (⟨isTok, {20}⟩ : PredicateQuery ℕ Atom).Holds cellLabel {20} ∧
      ¬ (⟨isTok, {20}⟩ : PredicateQuery ℕ Atom).Holds cellLabel ({20} ∪ {21}) ∧
      ¬ (⟨isTok, {20}⟩ : PredicateQuery ℕ Atom).Holds cellLabel ({20} \ {20}) := by
  refine ⟨by decide, by decide, by decide⟩

/-- Positive control: the token reader, parked at the empty store, is woken exactly by the
arrival of the token, its minimal waking context. -/
theorem reader_minimal_wake :
    Enabled label (∅ ∪ ((reader.taken ∪ reader.kept) \ ∅)) reader ∧
      (reader.taken ∪ reader.kept) \ (∅ : Finset ℕ) = {0} :=
  ⟨(minimal_wake (show reader.Positive from rfl) (by decide) (by decide) (by decide)).1, by decide⟩

/-- **An absence read is falsified by one maker inside its region**, and kept by a run that writes
only outside it. -/
theorem absence_falsified_by_maker :
    ¬ AbsenceHolds label isLock (fireList {0} [lockMaker]) ∧
      AbsenceHolds label isLock (fireList {0} [reader, taker]) := by
  refine ⟨by unfold AbsenceHolds; decide, ?_⟩
  exact holds_fireList_of_no_write
    (by
      intro e member o written
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · simp [reader] at written
        subst written
        rfl
      · simp [taker] at written
        rcases written with rfl | rfl <;> rfl)
    (by decide)

/-- Exactly one `tok` in the store (occurrences `20`, `21` are `tok` under `cellLabel`). -/
def exactlyOneTok (store : Finset ℕ) : Prop := (regionOf cellLabel store isTok).card = 1

instance (store : Finset ℕ) : Decidable (exactlyOneTok store) := inferInstanceAs (Decidable (_ = _))

/-- **A guard that is not upward closed can still be woken by an arrival.** "Exactly one token"
fails at the empty store and holds after `20` arrives, though it is not upward closed (a second
token falsifies it) and so not arrival adequate. -/
theorem uniqueness_woken_by_arrival :
    ¬ exactlyOneTok ∅ ∧ exactlyOneTok (∅ ∪ {20}) ∧ ¬ UpwardClosed exactlyOneTok ∧
      ¬ ArrivalAdequate exactlyOneTok := by
  have notUp : ¬ UpwardClosed exactlyOneTok := fun up => by
    have := up (show ({20} : Finset ℕ) ⊆ {20, 21} by decide) (by decide)
    revert this
    decide
  exact ⟨by decide, by decide, notUp, fun adequate => notUp ((arrivalAdequate_iff _).mp adequate)⟩

/-! ### Downward closure, absence-only conflicts -/

/-- **Negative control**: the presence guard "occurrence `0` is present" holds at `{0}` and fails
at the smaller `∅`: it is upward closed, not downward closed. -/
theorem presence_not_downwardClosed : ¬ DownwardClosed fun S : Finset ℕ => 0 ∈ S := by
  intro down
  have := down (Finset.empty_subset {0}) (by simp)
  simp at this

/-- **Positive control**: a taker of the token and a keeper of the lock: there is a take and a keep,
on different occurrences, so no commit of the wave takes what another keeps. -/
theorem takeKeepApart_absenceOnly :
    AbsenceOnlyConflicts [taker, (Commit.keepOne 1 : Commit ℕ Atom)] := by
  unfold AbsenceOnlyConflicts; decide

/-- **Negative control**: the taker takes the token the reader keeps. -/
theorem taker_reader_not_absenceOnly : ¬ AbsenceOnlyConflicts [taker, reader] := by
  unfold AbsenceOnlyConflicts; decide

end Controls

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
