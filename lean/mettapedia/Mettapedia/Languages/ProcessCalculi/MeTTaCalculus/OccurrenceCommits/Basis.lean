import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.ReactiveTransitions
import Mettapedia.Languages.MeTTa.TransformQuantifiers

/-!
# A basis for interaction over spaces and channels

## The basis

Every interaction is one atomic commit. A commit has four components:

1. **keep** (`kept`): read an occurrence and leave it; the interface of a double-pushout span.
   It may be copied and discarded: the `!` of linear logic.
2. **take** (`taken`): consume an occurrence; a linear resource, a Petri-net token.
3. **make** (`made`): produce occurrences with fresh identities; the right leg of the span.
4. **predicate query** (`queries`): observe every occurrence of a region that satisfies its
   predicate; an application condition of the span. Absence, uniqueness, counts, folds and the
   completeness of `every` are predicate queries.

Two further sources of behaviour are not commit components:

5. **fresh names** (`ν`): a make whose occurrences carry a name that occurs nowhere yet, with
   rights scoped to its holders (`ChannelAddressing`). It refines make: every commit that brings
   in a new name makes something and grows the store (`newName_grows_store`).
6. **choice**: a rule denotes a set of commits, one per binding, and a step fires one of them; the
   sum of worlds (`each`). A commit fires one way at a store; a rule with two rows fires two ways
   (`Controls.each_two_outcomes`).

The term layer (matching modulo the declared equations, `let`, functions, folds) is the language
the components are written in; it is not an interaction primitive.

## Definability

A commit `e` **encodes** a commit `c` (`Encodes`) when, at every store, `e` is enabled exactly
when `c` is, fires to a store with the same labels counted (so it may choose other identities for
what it makes), and is independent of exactly the commits enabled alongside that `c` is
independent of. The last clause is there because the meaning of a concurrent program includes
which of its steps commute, and independence of commits enabled together is exactly commuting
(`Exactness.independent_iff_both_orders`). Encodings compose (`Encodes.trans`).

| member | not encoded by | the law it breaks | hypothesis | Lean |
|---|---|---|---|---|
| take | any commit without take | no label leaves the store | none | `not_encodes_of_takeFree`, `Controls.taker_not_encoded` |
| make | any commit without make | no label arrives in the store | none | `not_encodes_of_makeFree`, `Controls.reader_not_encoded` |
| predicate query | any positive commit | the frame law, `Enabled.frame_of_positive` | the region can receive an occurrence outside any finite set | `not_encodes_predicateQuery`, `Controls.noOutput_not_encoded` |
| keep | any commit without keep, of a positive commit | an encoding takes the occurrence (and stops commuting with a second keeper) or queries its label (and a second occurrence with that label disables it) | labels repeat: an occurrence with the kept label can arrive | `not_encodes_keep`, `Controls.keeper_not_encoded` |
| fresh names | any name-closed commit | no name arrives in the store | none | `not_encodes_of_nameClosed`, `Controls.fresh_name_not_encoded` |

So take, make, predicate query and keep are four components none of which the others encode;
fresh names are separated from every name-closed commit, take, keep, make and predicate query
included; and
since a fresh name arrives only on a made occurrence, ν is a refinement of make, not a fifth
component beside it.

The two hypotheses are needed, and the necessity is shown:
* **keep needs labels that repeat.** With an injective label a predicate query of an
  occurrence's own label sees that occurrence alone, and it encodes a keep of it
  (`encodes_keepAsQuery`; `Controls.reader_encoded_when_injective`). A runtime whose atoms each
  occur at most once could drop keep.
* **predicate query needs an unbounded region.** When only finitely many identities can carry a
  region's labels, a commit that makes all of them is fresh exactly when the region is empty, so
  freshness stands in for the absence (`Controls.freshness_encodes_bounded_absence`).

Encodings are one commit for one commit. For take, make and fresh names the law holds along runs
too (`subset_fireList_of_noTake`, `fireList_subset_of_noMake`, `storeNames_fireList_subset`), so
no run of the smaller fragment has the effect either.
Tombstones (make "spent x" and read the absence of "spent x") simulate a take only up to the
tombstone labels, which the criterion counts, so they are not an encoding.

## What is derived, with the theorem that makes the derivation honest

* **Parking.** A parked once-`for` is a linear occurrence that its firing takes; an always-`for`
  is an occurrence its firings keep. So two messages for one once-`for` clash: one fires
  (`Controls.once_for_one_wake`); two for an always-`for` are independent: both fire, in either
  order (`Controls.always_for_two_wakes`). Waking is the step relation plus a fairness policy;
  `ReactiveTransitions` gives the open-system reading.
* **Cancellation and steering** (`Controls.cancel_or_wake`): cancelling a parked continuation
  takes its occurrence; cancel and wake clash, so exactly one of them happens.
* **Choice among waiting alternatives** (rho `select`, CML `choose`): the alternatives take one
  shared token; any two clash, so at most one commits (`Controls.select_at_most_one`).
* **`every` with completeness** (`every_complete_spoiled_by_arrival`): the amalgamation of all
  rows of a region together with the predicate query of that region. An arrival into the region
  spoils it, which is why `every` is not monotone; without the predicate query the amalgamation
  could commit with a row missing.
* **Absence, uniqueness, counts, folds**: a predicate query with the seen set empty, a singleton, or
  bound to a value that a term-level fold consumes.
* **Cell replace**: take the old value, make the new one; two replacers of one cell clash, so no
  update is lost (`Exactness.Controls.takers_clash` is the shape).
* The rest of the list maps onto these as shown in the report: the seven-operation table, the
  removal contract, MM2's `exec` and its sinks, rho's COMM, peek and persistent receipt, one
  evaluation step, Linda, CHR, join patterns, STM `retry`/`orElse`, Datalog with strata.

## Where the rest belongs

Time (timeouts, deadlines, cancellation by a clock) is a source of occurrences, a clock region,
plus cancellation (a take). Priority and weights are observers on choice (decision §11).
Durability and epochs are properties of a region's store. Failure observation is an occurrence
that a supervisor's `for` takes. Authority is the rights of fresh names and the capabilities
built on them. Fairness is a policy of the scheduler. None needs a new commit component.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

universe u v w

variable {O : Type u} [DecidableEq O] {R : Type v}

/-! ## Separations -/

/-- **Without take, stores never shrink.** -/
theorem subset_fire_of_noTake {store : Finset O} {c : Commit O R} (noTake : c.taken = ∅) :
    store ⊆ fire store c := by
  intro o member
  exact mem_fire.mpr (Or.inl ⟨member, by simp [noTake]⟩)

/-- **Without make, stores never grow.** -/
theorem fire_subset_of_noMake {store : Finset O} {c : Commit O R} (noMake : c.made = ∅) :
    fire store c ⊆ store := by
  intro o member
  rcases mem_fire.mp member with ⟨inStore, _⟩ | made
  · exact inStore
  · simp [noMake] at made

/-- Along a run without take, stores never shrink. -/
theorem subset_fireList_of_noTake {store : Finset O} {run : List (Commit O R)}
    (noTake : ∀ c ∈ run, c.taken = ∅) : store ⊆ fireList store run := by
  induction run generalizing store with
  | nil => exact le_rfl
  | cons c rest ih =>
      exact (subset_fire_of_noTake (noTake c List.mem_cons_self)).trans
        (ih fun d member => noTake d (List.mem_cons_of_mem _ member))

/-- Along a run without make, stores never grow. -/
theorem fireList_subset_of_noMake {store : Finset O} {run : List (Commit O R)}
    (noMake : ∀ c ∈ run, c.made = ∅) : fireList store run ⊆ store := by
  induction run generalizing store with
  | nil => exact le_rfl
  | cons c rest ih =>
      exact (ih fun d member => noMake d (List.mem_cons_of_mem _ member)).trans
        (fire_subset_of_noMake (noMake c List.mem_cons_self))

/-- **No make spoils a keep.** A commit without predicate queries is spoiled only by takes. -/
theorem keep_never_spoiled_by_make {label : O → R} {c d : Commit O R} (positive : c.Positive)
    (noTake : d.taken = ∅) : ¬ Spoils label d c := by
  rintro (kept | ⟨read, member, -⟩)
  · simp [noTake] at kept
  · simp [show c.queries = [] from positive] at member

/-- **Every predicate query is spoiled by an arrival into its region.** Whatever a predicate query
saw, a commit that makes one occurrence with a label of its region spoils it. -/
theorem predicateQuery_spoiled_by_maker {label : O → R} {c : Commit O R} {read : PredicateQuery O R}
    (member : read ∈ c.queries) {o : O} (inRegion : read.region (label o) = true) :
    Spoils label ⟨∅, ∅, {o}, []⟩ c :=
  Or.inr ⟨read, member, o, by simp, inRegion⟩

/-! ### Fresh names -/

section Names

variable {N : Type w} [DecidableEq N] (label : O → R) (names : R → Finset N)

/-- The names occurring in a set of occurrences. -/
def storeNames (X : Finset O) : Finset N := X.biUnion fun o => names (label o)

variable {label names}

/-- A commit builds names only from the names it uses and from constants. -/
def NameClosed (constants : Finset N) (c : Commit O R) : Prop :=
  ∀ o ∈ c.made, names (label o) ⊆ storeNames label names (c.taken ∪ c.kept) ∪ constants

theorem storeNames_fire_subset {constants : Finset N} {store : Finset O} {c : Commit O R}
    (enabled : Enabled label store c) (closed : NameClosed (label := label) (names := names) constants c) :
    storeNames label names (fire store c) ⊆ storeNames label names store ∪ constants := by
  intro n member
  obtain ⟨o, inFire, inNames⟩ := Finset.mem_biUnion.mp member
  rcases mem_fire.mp inFire with ⟨inStore, _⟩ | made
  · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨o, inStore, inNames⟩)
  · rcases Finset.mem_union.mp (closed o made inNames) with used | constant
    · obtain ⟨x, inUses, inX⟩ := Finset.mem_biUnion.mp used
      have inStore : x ∈ store := by
        rcases Finset.mem_union.mp inUses with taken | kept
        · exact enabled.taken_subset taken
        · exact enabled.kept_subset kept
      exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨x, inStore, inX⟩)
    · exact Finset.mem_union_right _ constant

/-- **Without fresh names, every name of a reachable store is an initial name or a constant.** -/
theorem storeNames_fireList_subset {constants : Finset N} {store : Finset O}
    {run : List (Commit O R)} (executable : Executable label store run)
    (closed : ∀ c ∈ run, NameClosed (label := label) (names := names) constants c) :
    storeNames label names (fireList store run) ⊆ storeNames label names store ∪ constants := by
  induction executable with
  | nil => exact Finset.subset_union_left
  | @cons store c rest enabled _ ih =>
      have step := storeNames_fire_subset enabled (closed c List.mem_cons_self)
      refine (ih fun d member => closed d (List.mem_cons_of_mem _ member)).trans ?_
      intro n member
      rcases Finset.mem_union.mp member with inFire | constant
      · exact step inFire
      · exact Finset.mem_union_right _ constant

end Names

/-! ## Definability -/

/-- `e` **encodes** `c`: at every store it is enabled exactly when `c` is, it then fires to a store
with the same labels counted, and it is independent of exactly the commits enabled alongside that
`c` is independent of. -/
structure Encodes (label : O → R) (c e : Commit O R) : Prop where
  enabled_iff : ∀ store, Enabled label store c ↔ Enabled label store e
  labels_eq : ∀ store, Enabled label store c → labels label (fire store c) = labels label (fire store e)
  independent_iff : ∀ store d, Enabled label store c → Enabled label store d →
    (Independent label c d ↔ Independent label e d)

theorem Encodes.refl (label : O → R) (c : Commit O R) : Encodes label c c :=
  ⟨fun _ => Iff.rfl, fun _ _ => rfl, fun _ _ _ _ => Iff.rfl⟩

theorem Encodes.trans {label : O → R} {c e f : Commit O R} (first : Encodes label c e)
    (second : Encodes label e f) : Encodes label c f where
  enabled_iff store := (first.enabled_iff store).trans (second.enabled_iff store)
  labels_eq store enabled :=
    (first.labels_eq store enabled).trans
      (second.labels_eq store ((first.enabled_iff store).mp enabled))
  independent_iff store d enabledC enabledD :=
    (first.independent_iff store d enabledC enabledD).trans
      (second.independent_iff store d ((first.enabled_iff store).mp enabledC) enabledD)

/-- **Take is not encoded without take.** A commit that removes a label from a store it fires at
is encoded by no commit that takes nothing. -/
theorem not_encodes_of_takeFree {label : O → R} {store : Finset O} {c e : Commit O R}
    (enabled : Enabled label store c) (removes : ¬ labels label store ≤ labels label (fire store c))
    (takeFree : e.taken = ∅) : ¬ Encodes label c e := fun encodes => by
  rw [encodes.labels_eq store enabled] at removes
  exact removes (labels_mono (subset_fire_of_noTake takeFree))

/-- **Make is not encoded without make.** A commit that adds a label to a store it fires at is
encoded by no commit that makes nothing. -/
theorem not_encodes_of_makeFree {label : O → R} {store : Finset O} {c e : Commit O R}
    (enabled : Enabled label store c) (adds : ¬ labels label (fire store c) ≤ labels label store)
    (makeFree : e.made = ∅) : ¬ Encodes label c e := fun encodes => by
  rw [encodes.labels_eq store enabled] at adds
  exact adds (labels_mono (fire_subset_of_noMake makeFree))

/-- **A predicate query is not encoded by a positive commit**, when its region can receive an
occurrence outside any finite set: such an arrival disables the predicate query, and by the frame
law it disables no positive commit that does not make it. -/
theorem not_encodes_predicateQuery {label : O → R} {store : Finset O} {c e : Commit O R}
    {read : PredicateQuery O R} (enabled : Enabled label store c) (member : read ∈ c.queries)
    (unbounded : ∀ F : Finset O, ∃ o ∉ F, read.region (label o) = true) (positive : e.Positive) :
    ¬ Encodes label c e := fun encodes => by
  obtain ⟨o, outside, inRegion⟩ := unbounded (store ∪ e.made)
  have absent : o ∉ store := fun inStore => outside (Finset.mem_union_left _ inStore)
  have notMade : o ∉ e.made := fun made => outside (Finset.mem_union_right _ made)
  have eLater : Enabled label (store ∪ {o}) e :=
    ((encodes.enabled_iff store).mp enabled).frame_of_positive positive
      (Finset.disjoint_singleton_right.mpr notMade)
  have holds := ((encodes.enabled_iff _).mpr eLater).queries_hold read member
  have before := enabled.queries_hold read member
  unfold PredicateQuery.Holds at holds before
  have seen : o ∈ read.seen := by
    rw [← holds]
    exact mem_regionOf.mpr ⟨Finset.mem_union_right _ (Finset.mem_singleton_self o), inRegion⟩
  rw [← before] at seen
  exact absent (mem_regionOf.mp seen).1

/-- **Keep is not encoded without keep**, when labels repeat. Let a positive commit keep `o`,
and let an occurrence `o'` with the label of `o` be able to arrive. A commit without keep that
took `o` would stop commuting with a second keeper of `o`; one that did not take `o` must query the
label of `o` to be disabled where `o` is missing, and then the arrival of `o'` disables it while
the keeper stays enabled. -/
theorem not_encodes_keep {label : O → R} {store : Finset O} {c e : Commit O R} {o o' : O}
    (positive : c.Positive) (enabled : Enabled label store c) (kept : o ∈ c.kept)
    (absent : o' ∉ store) (notMade : o' ∉ c.made) (sameLabel : label o' = label o)
    (keepFree : e.kept = ∅) : ¬ Encodes label c e := fun encodes => by
  have eEnabled := (encodes.enabled_iff store).mp enabled
  have present : o ∈ store := enabled.kept_subset kept
  have cQueries : c.queries = [] := positive
  by_cases taken : o ∈ e.taken
  · -- A second keeper of `o` commutes with `c`, not with `e`.
    let second : Commit O R := ⟨∅, {o}, ∅, []⟩
    have secondEnabled : Enabled label store second :=
      ⟨Finset.empty_subset _, Finset.singleton_subset_iff.mpr present, Finset.disjoint_empty_left _,
        Finset.disjoint_empty_left _, by simp [second]⟩
    have independentC : Independent label c second := by
      refine ⟨?_, ?_, ?_⟩
      · rintro (common | common) <;> simp [second] at common
      · rintro (common | ⟨read, member, -⟩)
        · refine common (Finset.disjoint_singleton_right.mpr fun inTaken => ?_)
          exact Finset.disjoint_left.mp enabled.apart inTaken kept
        · simp [second] at member
      · rintro (common | ⟨read, member, -⟩)
        · simp [second] at common
        · simp [cQueries] at member
    have independentE := (encodes.independent_iff store second enabled secondEnabled).mp independentC
    exact independentE.2.1 (Or.inl (Finset.not_disjoint_iff.mpr ⟨o, taken, by simp [second]⟩))
  · -- `e` must query the label of `o`.
    have readsLabel : ∃ read ∈ e.queries, read.region (label o) = true := by
      by_contra none
      simp only [not_exists, not_and, Bool.not_eq_true] at none
      have eEarlier : Enabled label (store.erase o) e := by
        refine ⟨fun x inTaken => Finset.mem_erase.mpr ⟨fun same => taken (same ▸ inTaken),
            eEnabled.taken_subset inTaken⟩, by simp [keepFree], eEnabled.apart,
          Finset.disjoint_of_subset_right (Finset.erase_subset _ _) eEnabled.fresh, ?_⟩
        intro read member
        have holds := eEnabled.queries_hold read member
        unfold PredicateQuery.Holds at holds ⊢
        rw [← holds]
        ext x
        simp only [mem_regionOf, Finset.mem_erase]
        constructor
        · rintro ⟨⟨_, inStore⟩, inRegion⟩
          exact ⟨inStore, inRegion⟩
        · rintro ⟨inStore, inRegion⟩
          refine ⟨⟨fun same => ?_, inStore⟩, inRegion⟩
          subst same
          rw [none read member] at inRegion
          exact absurd inRegion (by decide)
      have cEarlier := (encodes.enabled_iff _).mpr eEarlier
      exact (Finset.notMem_erase o store) (cEarlier.kept_subset kept)
    obtain ⟨read, member, inRegion⟩ := readsLabel
    have cLater : Enabled label (store ∪ {o'}) c :=
      enabled.frame_of_positive positive (Finset.disjoint_singleton_right.mpr notMade)
    have holds := ((encodes.enabled_iff _).mp cLater).queries_hold read member
    have before := eEnabled.queries_hold read member
    unfold PredicateQuery.Holds at holds before
    have seen : o' ∈ read.seen := by
      rw [← holds]
      exact mem_regionOf.mpr ⟨Finset.mem_union_right _ (Finset.mem_singleton_self o'),
        sameLabel ▸ inRegion⟩
    rw [← before] at seen
    exact absent (mem_regionOf.mp seen).1

section Injective

variable [DecidableEq R]

/-- A predicate query of the region of one label, having seen one occurrence. -/
def singletonQuery (label : O → R) (o : O) : PredicateQuery O R :=
  ⟨fun r => decide (r = label o), {o}⟩

/-- Replace the keep of `o` by a predicate query of the label of `o`. -/
def keepAsQuery (label : O → R) (o : O) (c : Commit O R) : Commit O R :=
  ⟨c.taken, c.kept.erase o, c.made, singletonQuery label o :: c.queries⟩

theorem singletonQuery_holds_iff {label : O → R} (injective : Function.Injective label)
    {store : Finset O} {o : O} : (singletonQuery label o).Holds label store ↔ o ∈ store := by
  unfold PredicateQuery.Holds singletonQuery
  dsimp only
  constructor
  · intro holds
    have member : o ∈ ({o} : Finset O) := Finset.mem_singleton_self o
    rw [← holds] at member
    exact (mem_regionOf.mp member).1
  · intro present
    ext x
    simp only [mem_regionOf, Finset.mem_singleton, decide_eq_true_eq, injective.eq_iff]
    constructor
    · exact fun both => both.2
    · rintro rfl
      exact ⟨present, rfl⟩

/-- **With an injective label, a keep is encoded by a predicate query of its own label.** So the
separation of keep from predicate query needs labels that repeat. -/
theorem encodes_keepAsQuery {label : O → R} (injective : Function.Injective label)
    {c : Commit O R} {o : O} (kept : o ∈ c.kept) (notTaken : o ∉ c.taken) :
    Encodes label c (keepAsQuery label o c) where
  enabled_iff store := by
    constructor
    · intro enabled
      refine ⟨enabled.taken_subset, (Finset.erase_subset _ _).trans enabled.kept_subset,
        Finset.disjoint_of_subset_right (Finset.erase_subset _ _) enabled.apart, enabled.fresh, ?_⟩
      intro read member
      rcases List.mem_cons.mp member with same | member
      · subst same
        exact (singletonQuery_holds_iff injective).mpr (enabled.kept_subset kept)
      · exact enabled.queries_hold read member
    · intro enabled
      have present : o ∈ store :=
        (singletonQuery_holds_iff injective).mp (enabled.queries_hold _ List.mem_cons_self)
      refine ⟨enabled.taken_subset, ?_, ?_, enabled.fresh,
        fun read member => enabled.queries_hold read (List.mem_cons_of_mem _ member)⟩
      · intro x keptX
        by_cases same : x = o
        · exact same ▸ present
        · exact enabled.kept_subset (Finset.mem_erase.mpr ⟨same, keptX⟩)
      · refine Finset.disjoint_left.mpr fun x inTaken keptX => ?_
        by_cases same : x = o
        · exact notTaken (same ▸ inTaken)
        · exact Finset.disjoint_left.mp enabled.apart inTaken (Finset.mem_erase.mpr ⟨same, keptX⟩)
  labels_eq _ _ := rfl
  independent_iff store d enabledC enabledD := by
    have present : o ∈ store := enabledC.kept_subset kept
    have notMade : o ∉ d.made := fun made => Finset.disjoint_left.mp enabledD.fresh made present
    have spoils : Spoils label d c ↔ Spoils label d (keepAsQuery label o c) := by
      unfold Spoils WritesInto keepAsQuery singletonQuery
      simp only [Finset.not_disjoint_iff, Finset.mem_erase, List.mem_cons, exists_eq_or_imp,
        decide_eq_true_eq, injective.eq_iff, exists_eq_right, Finset.mem_union, notMade, or_false]
      constructor
      · rintro (⟨x, inTaken, keptX⟩ | writes)
        · by_cases same : x = o
          · exact Or.inr (Or.inl (same ▸ inTaken))
          · exact Or.inl ⟨x, inTaken, same, keptX⟩
        · exact Or.inr (Or.inr writes)
      · rintro (⟨x, inTaken, -, keptX⟩ | inTaken | writes)
        · exact Or.inl ⟨x, inTaken, keptX⟩
        · exact Or.inl ⟨o, inTaken, kept⟩
        · exact Or.inr writes
    exact and_congr Iff.rfl (and_congr Iff.rfl (not_congr spoils))

end Injective

/-! ### Fresh names are separated from name-closed commits, and refine make -/

section NewNames

variable {N : Type w} [DecidableEq N] {label : O → R} {names : R → Finset N}

omit [DecidableEq O] in
/-- The names of a set of occurrences depend only on its labels. -/
theorem storeNames_eq_of_labels_eq {X Y : Finset O} (same : labels label X = labels label Y) :
    storeNames label names X = storeNames label names Y := by
  have mem : ∀ r, r ∈ labels label X ↔ r ∈ labels label Y := fun r => by rw [same]
  simp only [labels, Multiset.mem_map, Finset.mem_val] at mem
  ext n
  simp only [storeNames, Finset.mem_biUnion]
  constructor
  · rintro ⟨x, inX, inNames⟩
    obtain ⟨y, inY, eq⟩ := (mem (label x)).mp ⟨x, inX, rfl⟩
    exact ⟨y, inY, by rw [eq]; exact inNames⟩
  · rintro ⟨y, inY, inNames⟩
    obtain ⟨x, inX, eq⟩ := (mem (label y)).mpr ⟨y, inY, rfl⟩
    exact ⟨x, inX, by rw [eq]; exact inNames⟩

/-- **Fresh names are not encoded by name-closed commits.** A commit that brings a name into a
store, outside its names and the constants, is encoded by no name-closed commit. -/
theorem not_encodes_of_nameClosed {constants : Finset N} {store : Finset O} {c e : Commit O R}
    (enabled : Enabled label store c)
    (newName : ¬ storeNames label names (fire store c) ⊆ storeNames label names store ∪ constants)
    (closed : NameClosed (label := label) (names := names) constants e) : ¬ Encodes label c e :=
  fun encodes => by
    rw [storeNames_eq_of_labels_eq (encodes.labels_eq store enabled)] at newName
    exact newName (storeNames_fire_subset ((encodes.enabled_iff store).mp enabled) closed)

omit [DecidableEq N] in
theorem storeNames_fire_subset_of_noMake [DecidableEq N] {store : Finset O} {c : Commit O R}
    (noMake : c.made = ∅) :
    storeNames label names (fire store c) ⊆ storeNames label names store :=
  Finset.biUnion_subset_biUnion_of_subset_left _ (fire_subset_of_noMake noMake)

/-- **A fresh name refines make.** A commit that brings in a name outside the store's names and
the constants makes something, and grows the store: in this model a fresh name exists only on a
made occurrence, so ν breaks the law that separates make and is not a component beside it. -/
theorem newName_grows_store {constants : Finset N} {store : Finset O} {c : Commit O R}
    (enabled : Enabled label store c)
    (newName : ¬ storeNames label names (fire store c) ⊆ storeNames label names store ∪ constants) :
    c.made.Nonempty ∧ ¬ fire store c ⊆ store := by
  have made : c.made.Nonempty := by
    by_contra empty
    rw [Finset.not_nonempty_iff_eq_empty] at empty
    exact newName ((storeNames_fire_subset_of_noMake empty).trans Finset.subset_union_left)
  refine ⟨made, fun sub => ?_⟩
  obtain ⟨x, madeX⟩ := made
  exact Finset.disjoint_left.mp enabled.fresh madeX (sub (made_subset_fire madeX))

end NewNames

/-! ## `every` with completeness -/

/-- **`every` with completeness is spoiled by any arrival into its region.** The amalgamated rows
of a region together with the predicate query of that region: one more matching occurrence spoils
the commit, so the firing cannot silently miss a row. -/
theorem every_complete_spoiled_by_arrival {label : O → R} (rows : List (Commit O R))
    {region : R → Bool} {seen : Finset O} {o : O} (inRegion : region (label o) = true) :
    Spoils label ⟨∅, ∅, {o}, []⟩
      ⟨takenOf rows, keptOf rows, madeOf rows, ⟨region, seen⟩ :: queriesOf rows⟩ :=
  predicateQuery_spoiled_by_maker List.mem_cons_self inRegion

/-! ## Controls -/

namespace Controls

open Atom

/-- A take shrinks the store. -/
theorem taker_shrinks : ¬ ({0} : Finset ℕ) ⊆ fire {0} taker := by decide

/-- A make grows the store. -/
theorem maker_grows : ¬ fire ({0} : Finset ℕ) reader ⊆ {0} := by decide

/-- Take the token and make a fresh token. -/
def takeRemake : Commit ℕ Atom := ⟨{0}, ∅, {70}, []⟩

/-- A second take-and-remake of the token. -/
def takeRemake₂ : Commit ℕ Atom := ⟨{0}, ∅, {71}, []⟩

/-- **Keep is not take-and-remake.** Two readers of the token are independent; two commits that
take the token and make it again clash. -/
theorem keep_not_take_remake :
    Independent label reader reader₂ ∧ Clash takeRemake takeRemake₂ :=
  ⟨readers_independent, Or.inl (by simp [takeRemake, takeRemake₂])⟩

/-- Labels with names: occurrence `80` carries name `7`; every other occurrence carries name `1`. -/
def namedLabel : ℕ → ℕ
  | 80 => 7
  | _ => 1

/-- The names of a label. -/
def labelNames : ℕ → Finset ℕ := fun n => {n}

/-- **A fresh name escapes the closure.** Making occurrence `80` brings in name `7`, which is
neither in the store's names nor among the constants. -/
theorem fresh_name_escapes :
    ¬ storeNames namedLabel labelNames (fire {0} (⟨∅, ∅, {80}, []⟩ : Commit ℕ ℕ)) ⊆
      storeNames namedLabel labelNames {0} ∪ ∅ := by decide

/-- Make occurrence `80`, which carries the new name `7`. -/
def namer : Commit ℕ ℕ := ⟨∅, ∅, {80}, []⟩

theorem namer_enabled : Enabled namedLabel {0} namer where
  taken_subset := by decide
  kept_subset := by decide
  apart := by decide
  fresh := by decide
  queries_hold := by simp [namer]

/-- **The namer is encoded by no name-closed commit.** -/
theorem fresh_name_not_encoded (e : Commit ℕ ℕ)
    (closed : NameClosed (label := namedLabel) (names := labelNames) ∅ e) :
    ¬ Encodes namedLabel namer e :=
  not_encodes_of_nameClosed namer_enabled fresh_name_escapes closed

/-- **The namer is a make**: it grows the store. -/
theorem fresh_name_grows : namer.made.Nonempty ∧ ¬ fire ({0} : Finset ℕ) namer ⊆ {0} :=
  newName_grows_store namer_enabled fresh_name_escapes

/-! ### Definability -/

/-- **The taker is not encoded without take**: at `{0}` it removes the token's label. -/
theorem taker_not_encoded (e : Commit ℕ Atom) (takeFree : e.taken = ∅) :
    ¬ Encodes label taker e :=
  not_encodes_of_takeFree taker_enabled (by decide) takeFree

/-- **The reader is not encoded without make**: at `{0}` it adds an output. -/
theorem reader_not_encoded (e : Commit ℕ Atom) (makeFree : e.made = ∅) :
    ¬ Encodes label reader e :=
  not_encodes_of_makeFree reader_enabled (by decide) makeFree

/-- Fire when no output is present. -/
def noOutput : Commit ℕ Atom := ⟨∅, ∅, ∅, [⟨isOut, ∅⟩]⟩

theorem noOutput_enabled : Enabled label {0} noOutput where
  taken_subset := by decide
  kept_subset := by decide
  apart := by decide
  fresh := by decide
  queries_hold := by
    intro read member
    simp only [noOutput, List.mem_singleton] at member
    subst member
    decide

/-- Outputs can always arrive: every occurrence from `2` on is an output. -/
theorem outputs_unbounded (F : Finset ℕ) : ∃ o ∉ F, isOut (label o) = true :=
  ⟨F.sup id + 2, fun member => by
    have := Finset.le_sup (f := id) member
    simp only [id] at this
    omega, rfl⟩

/-- **The absence of outputs is not encoded by a positive commit.** -/
theorem noOutput_not_encoded (e : Commit ℕ Atom) (positive : e.Positive) :
    ¬ Encodes label noOutput e :=
  not_encodes_predicateQuery (read := ⟨isOut, ∅⟩) noOutput_enabled (by simp [noOutput])
    outputs_unbounded positive

theorem cell_isTok_iff (n : ℕ) : isTok (cellLabel n) = true ↔ n = 20 ∨ n = 21 := by
  unfold cellLabel
  split <;> simp_all [isTok]

/-- Under the cell label only `20` and `21` are tokens. -/
theorem regionOf_cell_isTok (store : Finset ℕ) :
    regionOf cellLabel store isTok = store ∩ {20, 21} := by
  ext n
  simp only [mem_regionOf, cell_isTok_iff, Finset.mem_inter, Finset.mem_insert,
    Finset.mem_singleton]

/-- Make both tokens of the cell when no token is present. -/
def makeBothTokens : Commit ℕ Atom := ⟨∅, ∅, {20, 21}, [⟨isTok, ∅⟩]⟩

/-- Make both tokens, with no predicate query. -/
def makeBothTokensPositive : Commit ℕ Atom := ⟨∅, ∅, {20, 21}, []⟩

/-- **A bounded region: freshness stands in for absence.** Only `20` and `21` can be tokens, so
making both is possible exactly where no token is present, and the positive commit encodes the
one with the absence read. The separation of predicate queries needs a region that can receive an
occurrence outside any finite set. -/
theorem freshness_encodes_bounded_absence :
    Encodes cellLabel makeBothTokens makeBothTokensPositive where
  enabled_iff store := by
    constructor
    · intro enabled
      exact ⟨enabled.taken_subset, enabled.kept_subset, enabled.apart, enabled.fresh, by
        simp [makeBothTokensPositive]⟩
    · intro enabled
      refine ⟨enabled.taken_subset, enabled.kept_subset, enabled.apart, enabled.fresh, ?_⟩
      intro read member
      simp only [makeBothTokens, List.mem_singleton] at member
      subst member
      unfold PredicateQuery.Holds
      rw [regionOf_cell_isTok, Finset.inter_comm]
      exact Finset.disjoint_iff_inter_eq_empty.mp enabled.fresh
  labels_eq _ _ := rfl
  independent_iff store d enabledC enabledD := by
    constructor
    · rintro ⟨noClash, notSpoiled, -⟩
      refine ⟨noClash, notSpoiled, ?_⟩
      rintro (common | ⟨read, member, -⟩)
      · simp [makeBothTokensPositive] at common
      · simp [makeBothTokensPositive] at member
    · rintro ⟨noClash, notSpoiled, -⟩
      refine ⟨noClash, notSpoiled, ?_⟩
      rintro (common | ⟨read, member, x, written, inRegion⟩)
      · simp [makeBothTokens] at common
      · simp only [makeBothTokens, List.mem_singleton] at member
        subst member
        have token : x ∈ ({20, 21} : Finset ℕ) := by
          simpa [Finset.mem_insert, Finset.mem_singleton] using (cell_isTok_iff x).mp inRegion
        rcases Finset.mem_union.mp written with inTaken | made
        · exact Finset.disjoint_left.mp enabledC.fresh token (enabledD.taken_subset inTaken)
        · exact noClash (Or.inr (Finset.not_disjoint_iff.mpr ⟨x, token, made⟩))

/-- Keep the token `20` and make `22`. -/
def keeper : Commit ℕ Atom := ⟨∅, {20}, {22}, []⟩

theorem keeper_enabled : Enabled cellLabel {20} keeper where
  taken_subset := by decide
  kept_subset := by decide
  apart := by decide
  fresh := by decide
  queries_hold := by simp [keeper]

/-- **The keeper is not encoded without keep**: the token `21` repeats the label of `20`. -/
theorem keeper_not_encoded (e : Commit ℕ Atom) (keepFree : e.kept = ∅) :
    ¬ Encodes cellLabel keeper e :=
  not_encodes_keep (o := 20) (o' := 21) rfl keeper_enabled (by simp [keeper]) (by decide)
    (by simp [keeper]) rfl keepFree

/-- The natural attempt: query the token region, having seen `20`, and make `22`. -/
def keeperAsQuery : Commit ℕ Atom := ⟨∅, ∅, {22}, [⟨isTok, {20}⟩]⟩

/-- **The natural attempt, concretely**: at `{20}` both are enabled; after a maker of the token
`21`, the keeper is still enabled and the predicate query is not. -/
theorem keeper_vs_keeperAsQuery :
    Enabled cellLabel {20} keeperAsQuery ∧
      Enabled cellLabel (fire {20} (⟨∅, ∅, {21}, []⟩ : Commit ℕ Atom)) keeper ∧
      ¬ Enabled cellLabel (fire {20} (⟨∅, ∅, {21}, []⟩ : Commit ℕ Atom)) keeperAsQuery := by
  refine ⟨⟨by decide, by decide, by decide, by decide, ?_⟩,
    ⟨by decide, by decide, by decide, by decide, by simp [keeper]⟩, fun enabled => ?_⟩
  · intro read member
    simp only [keeperAsQuery, List.mem_singleton] at member
    subst member
    decide
  · have := enabled.queries_hold ⟨isTok, {20}⟩ (by simp [keeperAsQuery])
    revert this
    decide

/-- A reader of occurrence `0` under the identity label, where no label repeats. -/
def idReader : Commit ℕ ℕ := ⟨∅, {0}, {5}, []⟩

/-- **With an injective label, the reader is encoded by a keep-free commit.** -/
theorem reader_encoded_when_injective :
    Encodes id idReader (keepAsQuery id 0 idReader) ∧ (keepAsQuery id 0 idReader).kept = ∅ :=
  ⟨encodes_keepAsQuery Function.injective_id (by simp [idReader]) (by simp [idReader]),
    by decide⟩

section Choice

open Mettapedia.Languages.MeTTa.TransformQuantifiers

/-- **Choice lives at the rule level**: a rule with two rows has two different outcomes at one
store, while a commit's firing is a function of the store. -/
theorem each_two_outcomes :
    Controls.writers.EachStep Controls.bothRows 0 {Controls.Atom.a} ∧
      Controls.writers.EachStep Controls.bothRows 0 {Controls.Atom.b} ∧
      ({Controls.Atom.a} : Multiset _) ≠ {Controls.Atom.b} := by
  refine ⟨⟨true, by simp [Controls.bothRows], by simp [Controls.writers],
      by simp [Footprints.fire, Controls.writers]⟩,
    ⟨false, by simp [Controls.bothRows], by simp [Controls.writers],
      by simp [Footprints.fire, Controls.writers]⟩, by decide⟩

end Choice

/-! ### Parking as data -/

/-- Wait labels: `90` is the parked continuation, `91` and `92` are messages. -/
def waitLabel : ℕ → Atom
  | 90 => lock
  | 91 => tok
  | 92 => tok
  | _ => out

/-- A once-`for` wakes on message `91`: it takes itself and the message. -/
def onceWake₁ : Commit ℕ Atom := ⟨{90, 91}, ∅, {93}, []⟩

/-- A once-`for` wakes on message `92`. -/
def onceWake₂ : Commit ℕ Atom := ⟨{90, 92}, ∅, {94}, []⟩

/-- An always-`for` wakes on message `91`: it keeps itself and takes the message. -/
def alwaysWake₁ : Commit ℕ Atom := ⟨{91}, {90}, {93}, []⟩

/-- An always-`for` wakes on message `92`. -/
def alwaysWake₂ : Commit ℕ Atom := ⟨{92}, {90}, {94}, []⟩

/-- **A once-`for` wakes once.** The two wakes clash: neither order runs both. -/
theorem once_for_one_wake : Clash onceWake₁ onceWake₂ :=
  Or.inl (by simp [onceWake₁, onceWake₂])

/-- **An always-`for` wakes for every message**: the two wakes are independent. -/
theorem always_for_two_wakes : Independent waitLabel alwaysWake₁ alwaysWake₂ := by
  refine ⟨?_, ?_, ?_⟩
  · unfold Clash; simp [alwaysWake₁, alwaysWake₂]
  · unfold Spoils WritesInto; simp [alwaysWake₁, alwaysWake₂]
  · unfold Spoils WritesInto; simp [alwaysWake₁, alwaysWake₂]

/-- Cancel the parked continuation: take it. -/
def cancel : Commit ℕ Atom := ⟨{90}, ∅, {95}, []⟩

/-- **Cancel or wake, never both**: they clash on the continuation. -/
theorem cancel_or_wake : Clash cancel onceWake₁ := Or.inl (by simp [cancel, onceWake₁])

/-- Two alternatives of a `select`, sharing the selection token `90`. -/
def selectLeft : Commit ℕ Atom := ⟨{90, 91}, ∅, {96}, []⟩

/-- The other alternative. -/
def selectRight : Commit ℕ Atom := ⟨{90, 92}, ∅, {97}, []⟩

/-- **A `select` commits at most one alternative.** -/
theorem select_at_most_one : Clash selectLeft selectRight := Or.inl (by simp [selectLeft, selectRight])

/-! ### Name-closed commits -/

/-- Keep occurrence `0` (name `1`) and make occurrence `81` (also name `1`). -/
def nameCopier : Commit ℕ ℕ := ⟨∅, {0}, {81}, []⟩

/-- **Positive control**: the copier makes only name `1`, which the occurrence it keeps carries. -/
theorem nameCopier_nameClosed :
    NameClosed (label := namedLabel) (names := labelNames) ∅ nameCopier := by
  unfold NameClosed storeNames; decide

/-- **Negative control**: the namer makes name `7` from nothing it uses and no constant. -/
theorem namer_not_nameClosed :
    ¬ NameClosed (label := namedLabel) (names := labelNames) ∅ namer := by
  unfold NameClosed storeNames; decide

end Controls

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
