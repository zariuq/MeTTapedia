import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Multiset.AddSub
import Mathlib.Tactic

/-!
# Commits over a located occurrence store

One semantic object carries both spaces and channels. A **store** is a finite set of
*occurrences*. Every occurrence has an identity and a label, given once for all occurrences by
`label : O → R`; a label records where the occurrence lives (a space region or a channel) and
which atom it carries. Two occurrences may carry one label: a bag of atoms is a set of
occurrences, and the identity is what a claim, a consumption or a validation refers to.

A **commit** is one ground firing of a transform: a double-pushout span over occurrences together
with application conditions.

* `taken` is what the commit consumes (the left side outside the interface);
* `kept` is what it reads and leaves in place (the interface);
* `made` is what it produces, with fresh identities (the right side outside the interface);
* `queries` are its **predicate queries**: each names a region, a predicate on labels, and the
  set of occurrences the query saw there. A predicate query holds at a store when the region's
  occurrences are exactly the ones seen, so its answer depends on every occurrence that satisfies
  the predicate, including one made there after the query looked. Absence is the predicate query
  that saw nothing; uniqueness, counts, folds and the rows of `every` are predicate queries of a
  region that bind what they saw.

A commit is **enabled** at a store when what it takes and keeps is present, nothing is both taken
and kept (the identification condition of double-pushout rewriting), what it makes is fresh, and
every predicate query holds. Firing removes what is taken and adds what is made (`fire`).

## Laws of one commit

* What is kept survives the firing, what is taken does not, what is made is present
  (`kept_subset_fire`, `disjoint_taken_fire`, `made_subset_fire`).
* **The frame law for positive commits** (`Enabled.frame`, `fire_union_frame`): a commit without
  predicate queries stays enabled when the store grows by occurrences it does not make, and fires
  to the same result plus that growth. A predicate query fails the law: an occurrence added inside
  its region disables it (`Controls.absence_not_framed`). This is the separation that makes
  predicate queries a primitive of their own.
* **Counted, a firing is the resource-system firing** (`labels_fire`): the labels of the result
  are the labels of the store, minus those taken, plus those made.
* **The frame law of a region** (`regionOf_fire_subset_of_no_make`,
  `regionOf_subset_fire_of_no_take`, `regionOf_fire_of_no_write`): a commit that makes nothing in a
  region only shrinks it, one that takes nothing from it only grows it, and one that writes nothing
  there leaves it as it was. The region laws of rights (`ChannelAddressing`, the missing-`send` and
  missing-`receive` laws of `InteractionTypes.Facets`), of read polarity
  (`RegionPermissions.ReadPolarity`) and of the wait index (`CommitProtocol`) are instances.

The commits `Commit.takeOne`, `Commit.keepOne` and `Commit.makeOne` touch one occurrence each.

## Positive and negative controls

`Controls` uses natural-number identities and three atoms. A reader and a taker of one
occurrence are both enabled at a one-occurrence store (`reader_enabled`, `taker_enabled`); a
commit that reads and takes one occurrence is not (`read_take_same_not_enabled`); the absence
read of a region holds at a store without it and fails once one occurrence is added
(`absence_holds_empty`, `absence_not_framed`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

universe u v

/-- A **predicate query** of a region: the region is a predicate on labels, and `seen` is the set
of occurrences that the query observed there at its snapshot. It holds only while the region holds
exactly those occurrences, so its answer depends on every occurrence that satisfies the predicate,
including one made later, and any take or make inside the region spoils it
(`Exactness.writesInto_iff`). It is the predicate read of database concurrency control
(Eswaran, Gray, Lorie and Traiger, 1976). -/
structure PredicateQuery (O : Type u) (R : Type v) where
  region : R → Bool
  seen : Finset O

/-- One ground firing: what it takes, keeps and makes, and its predicate queries. -/
structure Commit (O : Type u) (R : Type v) where
  taken : Finset O
  kept : Finset O
  made : Finset O
  queries : List (PredicateQuery O R)

namespace Commit

variable {O : Type u} {R : Type v} (o : O)

/-- The commit that takes one occurrence and does nothing else. -/
def takeOne : Commit O R := ⟨{o}, ∅, ∅, []⟩

/-- The commit that keeps one occurrence and does nothing else. -/
def keepOne : Commit O R := ⟨∅, {o}, ∅, []⟩

/-- The commit that makes one occurrence and does nothing else. -/
def makeOne : Commit O R := ⟨∅, ∅, {o}, []⟩

@[simp] theorem takeOne_taken : (takeOne o : Commit O R).taken = {o} := rfl
@[simp] theorem takeOne_kept : (takeOne o : Commit O R).kept = ∅ := rfl
@[simp] theorem takeOne_made : (takeOne o : Commit O R).made = ∅ := rfl
@[simp] theorem takeOne_queries : (takeOne o : Commit O R).queries = [] := rfl
@[simp] theorem keepOne_taken : (keepOne o : Commit O R).taken = ∅ := rfl
@[simp] theorem keepOne_kept : (keepOne o : Commit O R).kept = {o} := rfl
@[simp] theorem keepOne_made : (keepOne o : Commit O R).made = ∅ := rfl
@[simp] theorem keepOne_queries : (keepOne o : Commit O R).queries = [] := rfl
@[simp] theorem makeOne_taken : (makeOne o : Commit O R).taken = ∅ := rfl
@[simp] theorem makeOne_kept : (makeOne o : Commit O R).kept = ∅ := rfl
@[simp] theorem makeOne_made : (makeOne o : Commit O R).made = {o} := rfl
@[simp] theorem makeOne_queries : (makeOne o : Commit O R).queries = [] := rfl

end Commit

variable {O : Type u} [DecidableEq O] {R : Type v}

/-- The occurrences of a store inside a region. -/
def regionOf (label : O → R) (store : Finset O) (region : R → Bool) : Finset O :=
  store.filter fun o => region (label o) = true

/-- A predicate query holds at a store when the region's occurrences are exactly those seen. -/
def PredicateQuery.Holds (label : O → R) (store : Finset O) (read : PredicateQuery O R) : Prop :=
  regionOf label store read.region = read.seen

instance (label : O → R) (store : Finset O) (read : PredicateQuery O R) :
    Decidable (read.Holds label store) :=
  inferInstanceAs (Decidable (_ = _))

/-- The occurrences seen by a list of predicate queries. -/
def seenOf : List (PredicateQuery O R) → Finset O
  | [] => ∅
  | read :: rest => read.seen ∪ seenOf rest

@[simp] theorem seenOf_nil : seenOf ([] : List (PredicateQuery O R)) = ∅ := rfl

@[simp] theorem seenOf_cons (read : PredicateQuery O R) (rest : List (PredicateQuery O R)) :
    seenOf (read :: rest) = read.seen ∪ seenOf rest := rfl

theorem mem_seenOf {reads : List (PredicateQuery O R)} {o : O} :
    o ∈ seenOf reads ↔ ∃ read ∈ reads, o ∈ read.seen := by
  induction reads with
  | nil => simp
  | cons read rest ih => simp [ih]

namespace Commit

/-- What a commit uses: what it takes and what it keeps. -/
def uses (c : Commit O R) : Finset O := c.taken ∪ c.kept

/-- What a commit writes: what it takes and what it makes. -/
def writes (c : Commit O R) : Finset O := c.taken ∪ c.made

/-- A commit is positive when it has no predicate queries. -/
def Positive (c : Commit O R) : Prop := c.queries = []

/-- A commit is monotone when it is positive and takes nothing: it reads and adds. -/
def Monotone (c : Commit O R) : Prop := c.taken = ∅ ∧ c.queries = []

@[simp] theorem mem_uses {c : Commit O R} {o : O} : o ∈ c.uses ↔ o ∈ c.taken ∨ o ∈ c.kept :=
  Finset.mem_union

@[simp] theorem mem_writes {c : Commit O R} {o : O} : o ∈ c.writes ↔ o ∈ c.taken ∨ o ∈ c.made :=
  Finset.mem_union

/-- What a commit learns from: what it takes, what it keeps, and what its predicate queries saw.
Names (`ScopeExtrusion.learned`, `Reflection.learnedAtoms`) and facets (`InteractionTypes.learned`)
are learned from exactly these occurrences. -/
def learnedFrom (c : Commit O R) : Finset O := c.taken ∪ c.kept ∪ seenOf c.queries

@[simp] theorem mem_learnedFrom {c : Commit O R} {o : O} :
    o ∈ c.learnedFrom ↔ o ∈ c.taken ∨ o ∈ c.kept ∨ o ∈ seenOf c.queries := by
  simp [learnedFrom]


end Commit

/-- A commit is enabled at a store. -/
structure Enabled (label : O → R) (store : Finset O) (c : Commit O R) : Prop where
  taken_subset : c.taken ⊆ store
  kept_subset : c.kept ⊆ store
  apart : Disjoint c.taken c.kept
  fresh : Disjoint c.made store
  queries_hold : ∀ read ∈ c.queries, read.Holds label store

/-- Enabling is decidable: every condition is a finite check. -/
instance (label : O → R) (store : Finset O) (c : Commit O R) : Decidable (Enabled label store c) :=
  decidable_of_iff (c.taken ⊆ store ∧ c.kept ⊆ store ∧ Disjoint c.taken c.kept ∧
      Disjoint c.made store ∧ ∀ read ∈ c.queries, read.Holds label store)
    ⟨fun ⟨a, b, d, e, f⟩ => ⟨a, b, d, e, f⟩, fun h => ⟨h.1, h.2, h.3, h.4, h.5⟩⟩

/-- A commit **writes** a region when it takes or makes an occurrence inside it. A per-region epoch
moves exactly on such commits (`CommitProtocol.commitState`), a commit spoils a predicate query of
the region exactly so (`Exactness.writesInto_iff`), and the region index of parked firings wakes
on them (`Liveness.regionIndex`). -/
def Writes (label : O → R) (c : Commit O R) (region : R → Bool) : Prop :=
  ∃ o ∈ c.taken ∪ c.made, region (label o) = true

instance (label : O → R) (c : Commit O R) (region : R → Bool) : Decidable (Writes label c region) := by
  unfold Writes; infer_instance

/-- Firing: remove what is taken, add what is made. -/
def fire (store : Finset O) (c : Commit O R) : Finset O := (store \ c.taken) ∪ c.made

theorem mem_fire {store : Finset O} {c : Commit O R} {o : O} :
    o ∈ fire store c ↔ (o ∈ store ∧ o ∉ c.taken) ∨ o ∈ c.made := by
  simp [fire, Finset.mem_sdiff]

omit [DecidableEq O] in
theorem mem_regionOf {label : O → R} {store : Finset O} {region : R → Bool} {o : O} :
    o ∈ regionOf label store region ↔ o ∈ store ∧ region (label o) = true := by
  simp [regionOf]

section Laws

variable {label : O → R} {store : Finset O} {c : Commit O R}

/-- What a commit keeps survives its firing. -/
theorem kept_subset_fire (enabled : Enabled label store c) : c.kept ⊆ fire store c := by
  intro o kept
  refine mem_fire.mpr (Or.inl ⟨enabled.kept_subset kept, fun taken => ?_⟩)
  exact Finset.disjoint_left.mp enabled.apart taken kept

/-- What a commit takes is gone after its firing. -/
theorem disjoint_taken_fire (enabled : Enabled label store c) : Disjoint c.taken (fire store c) := by
  refine Finset.disjoint_left.mpr fun o taken inFire => ?_
  rcases mem_fire.mp inFire with ⟨_, notTaken⟩ | made
  · exact notTaken taken
  · exact Finset.disjoint_left.mp enabled.fresh made (enabled.taken_subset taken)

/-- What a commit makes is present after its firing. -/
theorem made_subset_fire : c.made ⊆ fire store c := fun _ made => mem_fire.mpr (Or.inr made)

omit [DecidableEq O] in
/-- A predicate query that holds sees only occurrences of the store. -/
theorem PredicateQuery.seen_subset {read : PredicateQuery O R} (holds : read.Holds label store) :
    read.seen ⊆ store := by
  intro o member
  rw [← holds] at member
  exact (mem_regionOf.mp member).1

/-- What the predicate queries of an enabled commit saw is in the store: a predicate query binds
what it saw, so the commit learns from it as from what it keeps. -/
theorem Enabled.seenOf_subset (enabled : Enabled label store c) : seenOf c.queries ⊆ store := by
  intro o seen
  obtain ⟨read, member, inSeen⟩ := mem_seenOf.mp seen
  exact PredicateQuery.seen_subset (enabled.queries_hold read member) inSeen

/-- **Everything an enabled commit learns from is in the store.** -/
theorem Enabled.learnedFrom_subset (enabled : Enabled label store c) : c.learnedFrom ⊆ store := by
  intro o used
  rcases Commit.mem_learnedFrom.mp used with taken | kept | seen
  · exact enabled.taken_subset taken
  · exact enabled.kept_subset kept
  · exact enabled.seenOf_subset seen

/-- **A commit that makes nothing in a region only shrinks it.** The facet, polarity, wait-index
and owned-read laws over regions are instances (`restrict_fire_subset_of_makesOutside`,
`InteractionTypes.restrict_fire_subset_of_noSend`, `positive_woken_by_make`). -/
theorem regionOf_fire_subset_of_no_make {region : R → Bool}
    (noMake : ∀ o ∈ c.made, region (label o) = false) :
    regionOf label (fire store c) region ⊆ regionOf label store region := by
  intro o member
  obtain ⟨inFire, inRegion⟩ := mem_regionOf.mp member
  rcases mem_fire.mp inFire with ⟨inStore, _⟩ | made
  · exact mem_regionOf.mpr ⟨inStore, inRegion⟩
  · rw [noMake o made] at inRegion; exact absurd inRegion (by decide)

/-- **A commit that takes nothing from a region only grows it** (`restrict_subset_fire_of_takesOutside`,
`InteractionTypes.restrict_subset_fire_of_noReceive`, `absence_woken_by_take`). -/
theorem regionOf_subset_fire_of_no_take {region : R → Bool}
    (noTake : ∀ o ∈ c.taken, region (label o) = false) :
    regionOf label store region ⊆ regionOf label (fire store c) region := by
  intro o member
  obtain ⟨inStore, inRegion⟩ := mem_regionOf.mp member
  refine mem_regionOf.mpr ⟨mem_fire.mpr (Or.inl ⟨inStore, fun taken => ?_⟩), inRegion⟩
  rw [noTake o taken] at inRegion; exact absurd inRegion (by decide)

/-- **A commit that writes nothing in a region leaves it as it was.** -/
theorem regionOf_fire_of_no_write {region : R → Bool}
    (noWrite : ∀ o ∈ c.taken ∪ c.made, region (label o) = false) :
    regionOf label (fire store c) region = regionOf label store region :=
  Finset.Subset.antisymm
    (regionOf_fire_subset_of_no_make fun o made => noWrite o (Finset.mem_union_right _ made))
    (regionOf_subset_fire_of_no_take fun o taken => noWrite o (Finset.mem_union_left _ taken))

/-- A monotone commit only adds. -/
theorem subset_fire_of_monotone (monotone : c.Monotone) : store ⊆ fire store c := by
  intro o member
  exact mem_fire.mpr (Or.inl ⟨member, by simp [monotone.1]⟩)

/-- **The frame law for a positive commit.** A commit stays enabled when the store grows by
occurrences that it does not make and that lie outside the regions of its predicate queries. A
positive commit has no predicate query, so only the first condition remains. -/
theorem Enabled.frame (enabled : Enabled label store c) {frame : Finset O}
    (apartMade : Disjoint c.made frame)
    (outsideQueries : ∀ read ∈ c.queries, ∀ o ∈ frame, read.region (label o) = false) :
    Enabled label (store ∪ frame) c where
  taken_subset := enabled.taken_subset.trans Finset.subset_union_left
  kept_subset := enabled.kept_subset.trans Finset.subset_union_left
  apart := enabled.apart
  fresh := Finset.disjoint_union_right.mpr ⟨enabled.fresh, apartMade⟩
  queries_hold := by
    intro read member
    have holds := enabled.queries_hold read member
    unfold PredicateQuery.Holds at holds ⊢
    rw [← holds]
    ext o
    simp only [mem_regionOf, Finset.mem_union]
    constructor
    · rintro ⟨inStore | inFrame, inRegion⟩
      · exact ⟨inStore, inRegion⟩
      · rw [outsideQueries read member o inFrame] at inRegion
        exact absurd inRegion (by decide)
    · rintro ⟨inStore, inRegion⟩
      exact ⟨Or.inl inStore, inRegion⟩

/-- A positive commit stays enabled under any growth of the store that avoids what it makes. -/
theorem Enabled.frame_of_positive (enabled : Enabled label store c) (positive : c.Positive)
    {frame : Finset O} (apartMade : Disjoint c.made frame) :
    Enabled label (store ∪ frame) c :=
  enabled.frame apartMade (by simp [show c.queries = [] from positive])

/-- Firing in a larger store adds the frame to the result, when the frame is not taken. -/
theorem fire_union_frame {frame : Finset O} (apartTaken : Disjoint c.taken frame) :
    fire (store ∪ frame) c = fire store c ∪ frame := by
  ext o
  simp only [mem_fire, Finset.mem_union]
  constructor
  · rintro (⟨inStore | inFrame, notTaken⟩ | made)
    · exact Or.inl (Or.inl ⟨inStore, notTaken⟩)
    · exact Or.inr inFrame
    · exact Or.inl (Or.inr made)
  · rintro ((⟨inStore, notTaken⟩ | made) | inFrame)
    · exact Or.inl ⟨Or.inl inStore, notTaken⟩
    · exact Or.inr made
    · exact Or.inl ⟨Or.inr inFrame, fun taken => Finset.disjoint_left.mp apartTaken taken inFrame⟩

end Laws

/-! ## Counting -/

/-- The labels of a set of occurrences, as a bag. It is the bag of the double-pushout model,
`ResourceInteraction.System.labels` (`Exactness.labels_eq_system_labels`). -/
def labels (label : O → R) (X : Finset O) : Multiset R := X.val.map label

omit [DecidableEq O] in
/-- More occurrences carry more labels. -/
theorem labels_mono {label : O → R} {X Y : Finset O} (sub : X ⊆ Y) : labels label X ≤ labels label Y :=
  Multiset.map_le_map (Finset.val_le_iff.mpr sub)

theorem labels_union_of_disjoint (label : O → R) {X Y : Finset O} (apart : Disjoint X Y) :
    labels label (X ∪ Y) = labels label X + labels label Y := by
  unfold labels
  rw [← Finset.disjUnion_eq_union X Y apart, ← Multiset.map_add]
  rfl

theorem labels_sdiff_of_subset [DecidableEq R] (label : O → R) {X Y : Finset O} (sub : Y ⊆ X) :
    labels label (X \ Y) = labels label X - labels label Y := by
  have split : labels label X = labels label Y + labels label (X \ Y) := by
    rw [← labels_union_of_disjoint label Finset.disjoint_sdiff, Finset.union_sdiff_of_subset sub]
  rw [split, add_tsub_cancel_left]

/-- **Counted, a firing is the resource-system firing**: the labels of the result are the labels
of the store, minus the labels taken, plus the labels made. -/
theorem labels_fire [DecidableEq R] {label : O → R} {store : Finset O} {c : Commit O R}
    (enabled : Enabled label store c) :
    labels label (fire store c) = labels label store - labels label c.taken + labels label c.made := by
  unfold fire
  rw [labels_union_of_disjoint label (Finset.disjoint_left.mpr fun o inLeft made =>
      Finset.disjoint_left.mp enabled.fresh made (Finset.mem_sdiff.mp inLeft).1),
    labels_sdiff_of_subset label enabled.taken_subset]

/-! ## The fold view of predicate queries

A predicate query is answered from the **matches** of its region: the occurrences of the store
inside it (`regionOf`). Collected with their labels they form one bag, `matchBag`, which is the
answer of `all`. Every order-blind fold of the matches, a fold through a commutative monoid, is
computed from that bag alone (`sum_regionOf_eq_matchBag`). A count is the size of the bag
(`card_regionOf_eq_card_matchBag`), absence is the empty bag (`regionOf_eq_empty_iff`), and
uniqueness is a bag of size one (`exists_regionOf_eq_singleton_iff`). A predicate query that holds
fixes the bag to the labels of what it saw (`PredicateQuery.matchBag_eq_of_holds`), and so fixes
every such fold; this is why any take or make inside the region spoils it. -/

/-- The labels of the matches of a region at a store, as a bag: the answer of `all`. -/
def matchBag (label : O → R) (store : Finset O) (region : R → Bool) : Multiset R :=
  labels label (regionOf label store region)

omit [DecidableEq O] in
/-- **Every order-blind fold of the matches factors through the bag of their labels.** -/
theorem sum_regionOf_eq_matchBag {M : Type*} [AddCommMonoid M] (label : O → R)
    (store : Finset O) (region : R → Bool) (f : R → M) :
    ∑ o ∈ regionOf label store region, f (label o) =
      ((matchBag label store region).map f).sum := by
  unfold matchBag labels
  rw [Multiset.map_map, Finset.sum_eq_multiset_sum]
  rfl

omit [DecidableEq O] in
/-- **A count is the size of the bag.** -/
theorem card_regionOf_eq_card_matchBag (label : O → R) (store : Finset O) (region : R → Bool) :
    (regionOf label store region).card = Multiset.card (matchBag label store region) := by
  simp [matchBag, labels]

omit [DecidableEq O] in
/-- **Absence is the empty bag.** -/
theorem regionOf_eq_empty_iff (label : O → R) (store : Finset O) (region : R → Bool) :
    regionOf label store region = ∅ ↔ matchBag label store region = 0 := by
  rw [← Finset.card_eq_zero, card_regionOf_eq_card_matchBag, Multiset.card_eq_zero]

omit [DecidableEq O] in
/-- **Uniqueness is a bag of size one.** -/
theorem exists_regionOf_eq_singleton_iff (label : O → R) (store : Finset O)
    (region : R → Bool) :
    (∃ o, regionOf label store region = {o}) ↔ Multiset.card (matchBag label store region) = 1 := by
  rw [← card_regionOf_eq_card_matchBag, Finset.card_eq_one]

omit [DecidableEq O] in
/-- **A predicate query that holds fixes the bag of its region** to the labels of what it saw. -/
theorem PredicateQuery.matchBag_eq_of_holds {label : O → R} {store : Finset O}
    {read : PredicateQuery O R} (holds : read.Holds label store) :
    matchBag label store read.region = labels label read.seen := by
  unfold matchBag
  rw [show regionOf label store read.region = read.seen from holds]

/-! ## Controls -/

namespace Controls

/-- Three atoms. -/
inductive Atom where
  | tok
  | lock
  | out
  deriving DecidableEq, Repr

open Atom

/-- Occurrence `0` is a token, `1` a lock, everything else an output. -/
def label : ℕ → Atom
  | 0 => tok
  | 1 => lock
  | _ => out

/-- Read the token. -/
def reader : Commit ℕ Atom := ⟨∅, {0}, {5}, []⟩

/-- Take the token. -/
def taker : Commit ℕ Atom := ⟨{0}, ∅, {6}, []⟩

/-- Read and take the same token. -/
def readTakeSame : Commit ℕ Atom := ⟨{0}, {0}, {7}, []⟩

/-- The region of locks. -/
def isLock : Atom → Bool
  | lock => true
  | _ => false

/-- Add an output when no lock is present. -/
def unlessLocked : Commit ℕ Atom := ⟨∅, ∅, {8}, [⟨isLock, ∅⟩]⟩

theorem reader_enabled : Enabled label {0} reader where
  taken_subset := by decide
  kept_subset := by decide
  apart := by decide
  fresh := by decide
  queries_hold := by simp [reader]

theorem taker_enabled : Enabled label {0} taker where
  taken_subset := by decide
  kept_subset := by decide
  apart := by decide
  fresh := by decide
  queries_hold := by simp [taker]

/-- Negative identification control: one occurrence cannot be both read and taken. -/
theorem read_take_same_not_enabled (store : Finset ℕ) : ¬ Enabled label store readTakeSame :=
  fun enabled => by
    have := enabled.apart
    simp [readTakeSame] at this

/-- Positive absence control: the absence read holds at a store without a lock. -/
theorem absence_holds_empty : Enabled label {0} unlessLocked where
  taken_subset := by decide
  kept_subset := by decide
  apart := by decide
  fresh := by decide
  queries_hold := by
    intro read member
    simp only [unlessLocked, List.mem_singleton] at member
    subst member
    decide

/-- **Negative frame control**: adding a lock to the store disables the absence read. The frame
law fails for predicate queries. -/
theorem absence_not_framed : ¬ Enabled label ({0} ∪ {1}) unlessLocked := fun enabled => by
  have holds := enabled.queries_hold ⟨isLock, ∅⟩ (by simp [unlessLocked])
  revert holds
  decide

/-- The positive commits do obey the frame law: the reader stays enabled with the lock added. -/
theorem reader_framed : Enabled label ({0} ∪ {1}) reader :=
  reader_enabled.frame_of_positive rfl (by decide)

/-! ### Positive, monotone, writes -/

/-- **Positive control**: the reader has no predicate query. -/
theorem reader_positive : reader.Positive := rfl

/-- **Negative control**: the lock-absence commit has a predicate query, so it is not positive. -/
theorem unlessLocked_not_positive : ¬ unlessLocked.Positive := by
  simp [Commit.Positive, unlessLocked]

/-- **Positive control**: the reader takes nothing and has no predicate query: it is monotone. -/
theorem reader_monotone : reader.Monotone := ⟨rfl, rfl⟩

/-- **Negative control**: the taker has no predicate query but takes the token. -/
theorem taker_not_monotone : ¬ taker.Monotone := by
  simp [Commit.Monotone, taker]

/-- **Negative control**: the lock-absence commit takes nothing but has a predicate query. -/
theorem unlessLocked_not_monotone : ¬ unlessLocked.Monotone := by
  simp [Commit.Monotone, unlessLocked]

/-- **Positive control**: making a lock (occurrence `1`) writes the lock region. -/
theorem makeLock_writes_lock : Writes label (Commit.makeOne 1 : Commit ℕ Atom) isLock := by decide

/-- **Negative control**: the taker takes a token and makes an output; it writes nothing in the
lock region. -/
theorem taker_not_writes_lock : ¬ Writes label taker isLock := by decide

/-! ### The fold view, concretely -/

/-- The region of outputs. -/
def isOutput : Atom → Bool
  | out => true
  | _ => false

/-- **Uniqueness, positive**: at `{0, 1}` the lock region has exactly one match. -/
theorem lock_region_unique : ∃ o, regionOf label ({0, 1} : Finset ℕ) isLock = {o} :=
  ⟨1, by decide⟩

/-- **Uniqueness, negative**: at `{0, 5, 6}` the output region has two matches; its bag has size
two, not one. -/
theorem output_region_not_unique : ¬ ∃ o, regionOf label ({0, 5, 6} : Finset ℕ) isOutput = {o} :=
  (exists_regionOf_eq_singleton_iff label _ _).not.mpr (by decide)

/-- **A count as a fold of the bag**: summing one per label of the output region's bag gives the
count two, the size of the region. -/
theorem output_count_by_fold :
    ((matchBag label ({0, 5, 6} : Finset ℕ) isOutput).map fun _ => (1 : ℕ)).sum = 2 ∧
      (regionOf label ({0, 5, 6} : Finset ℕ) isOutput).card = 2 := by
  decide

end Controls

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
