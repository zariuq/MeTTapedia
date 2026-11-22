import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Commits
import Mettapedia.GSLT.Causality.DiscreteDoublePushout

/-!
# Exactness of occurrence-level independence with predicate queries

Two commits are enabled at one store. When may they run in parallel, or in either order, without
changing what the program means? This module gives a relation that is computed from the two
commits alone, and proves that it is exactly the commutation relation, at every store.

## The static relation

* Two commits **clash** when they take a common occurrence, or claim a common fresh identity
  (`Clash`). A clash is symmetric: neither commit survives the other.
* A commit `d` **spoils** a commit `c` when `d` takes something `c` keeps, or writes (takes or
  makes) an occurrence inside the region of a predicate query of `c` (`Spoils`, `WritesInto`).
* Two commits are **independent** when they do not clash and neither spoils the other
  (`Independent`). The relation mentions no store.

## Exactness

* **One order** (`enabled_fire_iff`): for commits `c` and `d` enabled at a store, `c` is still
  enabled after `d` fires exactly when they do not clash and `d` does not spoil `c`.
* **Both orders** (`independent_iff_both_orders`): two enabled commits are independent exactly when
  each stays enabled after the other. Then both orders reach one store (`fire_comm`).
* **The pairs that are not independent** split in two (`clash_blocks_both_orders`,
  `spoils_blocks_one_order`): a clash blocks both orders, so no serialization runs both; a spoil
  in one direction blocks exactly one order, so the pair runs only with the spoiled commit first.
  The second kind is why a wave can be finer than mutual independence (`Waves`).

The maximal half holds at every store where both are enabled, not only at some store: the
static relation loses nothing.

## Predicate queries by identity and by value

A predicate query here observes the identities of the occurrences in its region: it is the query
that a per-region epoch validates. A query of the region's **labels** only
(`PredicateQuery.HoldsValue`) observes less. Its exact spoiling relation compares the labels a
commit takes from the region with the labels it makes there (`holdsValue_fire_iff`): a commit that
replaces a cell by an equal value leaves a value query valid and spoils an identity query
(`Controls.same_value_replace`). The identity relation is therefore a sound, conservative
approximation of the value relation; `Waves` shows that only the identity relation is decided pair
by pair.

## The double-pushout bridge

For commits without predicate queries, independence is the parallel independence of double-pushout
rewriting (`independent_iff_dpo`), so the counting theorem
`ResourceInteraction.System.concurrent_iff_exists_independent` reads: two rule instances are
concurrent at a bag exactly when some pair of their commits is independent. The bags of labels
are the same in both models (`labels_eq_system_labels`).

## Controls

A reader and a taker of one token (`Controls.reader_taker`): the reader first runs both, the
taker first blocks the reader. Two takers clash (`Controls.takers_clash`). Two readers are
independent (`Controls.readers_independent`). An absence read is spoiled by a commit that makes
inside its region (`Controls.maker_spoils_absence`), and not by a commit that takes outside it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

universe u v

variable {O : Type u} [DecidableEq O] {R : Type v}

/-- `d` writes, by taking or making, an occurrence inside the region of a predicate query of `c`. -/
def WritesInto (label : O → R) (d c : Commit O R) : Prop :=
  ∃ read ∈ c.queries, ∃ o ∈ d.taken ∪ d.made, read.region (label o) = true

/-- `WritesInto` is `Writes` at the region of some predicate query of `c`: `d` writes into `c`'s
queried regions exactly when it writes the region of one of `c`'s predicate queries. -/
theorem writesInto_iff {label : O → R} {d c : Commit O R} :
    WritesInto label d c ↔ ∃ read ∈ c.queries, Writes label d read.region := Iff.rfl

/-- `c` and `d` take a common occurrence or claim a common fresh identity. -/
def Clash (c d : Commit O R) : Prop :=
  ¬ Disjoint c.taken d.taken ∨ ¬ Disjoint c.made d.made

/-- `d` spoils `c`: it takes what `c` keeps, or writes inside the region of a predicate query of
`c`. -/
def Spoils (label : O → R) (d c : Commit O R) : Prop :=
  ¬ Disjoint d.taken c.kept ∨ WritesInto label d c

/-- **Independence**: no clash, and neither commit spoils the other. -/
def Independent (label : O → R) (c d : Commit O R) : Prop :=
  ¬ Clash c d ∧ ¬ Spoils label c d ∧ ¬ Spoils label d c

omit [DecidableEq O] in
theorem Clash.symm {c d : Commit O R} (clash : Clash c d) : Clash d c := by
  unfold Clash at *
  rcases clash with taken | made
  · exact Or.inl fun apart => taken apart.symm
  · exact Or.inr fun apart => made apart.symm

theorem Independent.symm {label : O → R} {c d : Commit O R} (independent : Independent label c d) :
    Independent label d c :=
  ⟨fun clash => independent.1 clash.symm, independent.2.2, independent.2.1⟩

section Exactness

variable {label : O → R} {store : Finset O} {c d : Commit O R}

/-- **Exactness, one order.** For commits enabled at one store, `c` stays enabled after `d` fires
exactly when they do not clash and `d` does not spoil `c`. -/
theorem enabled_fire_iff (enabledC : Enabled label store c) (enabledD : Enabled label store d) :
    Enabled label (fire store d) c ↔ ¬ Clash c d ∧ ¬ Spoils label d c := by
  constructor
  · intro after
    refine ⟨?_, ?_⟩
    · rintro (taken | made)
      · obtain ⟨o, inC, inD⟩ := Finset.not_disjoint_iff.mp taken
        exact Finset.disjoint_left.mp (disjoint_taken_fire enabledD) inD (after.taken_subset inC)
      · obtain ⟨o, inC, inD⟩ := Finset.not_disjoint_iff.mp made
        exact Finset.disjoint_left.mp after.fresh inC (made_subset_fire inD)
    · rintro (kept | ⟨read, member, o, written, inRegion⟩)
      · obtain ⟨o, inD, inC⟩ := Finset.not_disjoint_iff.mp kept
        exact Finset.disjoint_left.mp (disjoint_taken_fire enabledD) inD (after.kept_subset inC)
      · have before := enabledC.queries_hold read member
        have later := after.queries_hold read member
        unfold PredicateQuery.Holds at before later
        rcases Finset.mem_union.mp written with taken | made
        · have inSeen : o ∈ read.seen := by
            rw [← before]
            exact mem_regionOf.mpr ⟨enabledD.taken_subset taken, inRegion⟩
          rw [← later] at inSeen
          exact Finset.disjoint_left.mp (disjoint_taken_fire enabledD) taken
            (mem_regionOf.mp inSeen).1
        · have inSeen : o ∈ read.seen := by
            rw [← later]
            exact mem_regionOf.mpr ⟨made_subset_fire made, inRegion⟩
          rw [← before] at inSeen
          exact Finset.disjoint_left.mp enabledD.fresh made (mem_regionOf.mp inSeen).1
  · rintro ⟨noClash, noSpoil⟩
    unfold Clash at noClash
    unfold Spoils at noSpoil
    push Not at noClash noSpoil
    obtain ⟨takenApart, madeApart⟩ := noClash
    obtain ⟨keptApart, noWrite⟩ := noSpoil
    refine
      { taken_subset := fun o taken => mem_fire.mpr (Or.inl ⟨enabledC.taken_subset taken,
          fun inD => Finset.disjoint_left.mp takenApart taken inD⟩)
        kept_subset := fun o kept => mem_fire.mpr (Or.inl ⟨enabledC.kept_subset kept,
          fun inD => Finset.disjoint_left.mp keptApart inD kept⟩)
        apart := enabledC.apart
        fresh := ?_
        queries_hold := ?_ }
    · refine Finset.disjoint_left.mpr fun o made inFire => ?_
      rcases mem_fire.mp inFire with ⟨inStore, _⟩ | madeD
      · exact Finset.disjoint_left.mp enabledC.fresh made inStore
      · exact Finset.disjoint_left.mp madeApart made madeD
    · intro read member
      have before := enabledC.queries_hold read member
      unfold PredicateQuery.Holds at before ⊢
      rw [← before]
      ext o
      simp only [mem_regionOf, mem_fire]
      constructor
      · rintro ⟨⟨inStore, _⟩ | made, inRegion⟩
        · exact ⟨inStore, inRegion⟩
        · exact absurd ⟨read, member, o, Finset.mem_union_right _ made, inRegion⟩ noWrite
      · rintro ⟨inStore, inRegion⟩
        refine ⟨Or.inl ⟨inStore, fun taken => ?_⟩, inRegion⟩
        exact noWrite ⟨read, member, o, Finset.mem_union_left _ taken, inRegion⟩

/-- **Exactness, both orders.** Two commits enabled at one store are independent exactly when
each stays enabled after the other. -/
theorem independent_iff_both_orders (enabledC : Enabled label store c)
    (enabledD : Enabled label store d) :
    Independent label c d ↔ Enabled label (fire store c) d ∧ Enabled label (fire store d) c := by
  rw [enabled_fire_iff enabledD enabledC, enabled_fire_iff enabledC enabledD]
  constructor
  · rintro ⟨noClash, noSpoilCD, noSpoilDC⟩
    exact ⟨⟨fun clash => noClash clash.symm, noSpoilCD⟩, ⟨noClash, noSpoilDC⟩⟩
  · rintro ⟨⟨_, noSpoilCD⟩, ⟨noClash, noSpoilDC⟩⟩
    exact ⟨noClash, noSpoilCD, noSpoilDC⟩

/-- **The diamond.** Two commits enabled at one store reach one store in either order, whenever
both orders are executable: the composite removes both takings and adds both productions. What
independence adds is that both orders *are* executable. -/
theorem fire_comm (enabledC : Enabled label store c) (enabledD : Enabled label store d) :
    fire (fire store c) d = fire (fire store d) c := by
  ext o
  simp only [mem_fire]
  have madeNotTakenC : o ∈ d.made → o ∉ c.taken := fun made taken =>
    Finset.disjoint_left.mp enabledD.fresh made (enabledC.taken_subset taken)
  have madeNotTakenD : o ∈ c.made → o ∉ d.taken := fun made taken =>
    Finset.disjoint_left.mp enabledC.fresh made (enabledD.taken_subset taken)
  constructor
  · rintro (⟨⟨inStore, notC⟩ | madeC, notD⟩ | madeD)
    · exact Or.inl ⟨Or.inl ⟨inStore, notD⟩, notC⟩
    · exact Or.inr madeC
    · exact Or.inl ⟨Or.inr madeD, madeNotTakenC madeD⟩
  · rintro (⟨⟨inStore, notD⟩ | madeD, notC⟩ | madeC)
    · exact Or.inl ⟨Or.inl ⟨inStore, notC⟩, notD⟩
    · exact Or.inr madeD
    · exact Or.inl ⟨Or.inr madeC, madeNotTakenD madeC⟩

/-- **A clash blocks both orders**: after either commit, the other is disabled. -/
theorem clash_blocks_both_orders (enabledC : Enabled label store c)
    (enabledD : Enabled label store d) (clash : Clash c d) :
    ¬ Enabled label (fire store c) d ∧ ¬ Enabled label (fire store d) c :=
  ⟨fun after => ((enabled_fire_iff enabledD enabledC).mp after).1 clash.symm,
    fun after => ((enabled_fire_iff enabledC enabledD).mp after).1 clash⟩

/-- **A spoil in one direction blocks exactly one order**: the spoiled commit must go first. -/
theorem spoils_blocks_one_order (enabledC : Enabled label store c)
    (enabledD : Enabled label store d) (noClash : ¬ Clash c d) (spoils : Spoils label d c)
    (notBack : ¬ Spoils label c d) :
    Enabled label (fire store c) d ∧ ¬ Enabled label (fire store d) c :=
  ⟨(enabled_fire_iff enabledD enabledC).mpr ⟨fun clash => noClash clash.symm, notBack⟩,
    fun after => ((enabled_fire_iff enabledC enabledD).mp after).2 spoils⟩

end Exactness

/-! ## Predicate queries by value -/

/-- A predicate query of the region's labels: the bag of labels in the region equals `bag`. -/
def PredicateQuery.HoldsValue (label : O → R) (store : Finset O) (region : R → Bool)
    (bag : Multiset R) : Prop :=
  labels label (regionOf label store region) = bag

theorem regionOf_fire (label : O → R) (store : Finset O) (d : Commit O R) (region : R → Bool) :
    regionOf label (fire store d) region =
      (regionOf label store region \ regionOf label d.taken region) ∪ regionOf label d.made region := by
  ext o
  simp only [mem_regionOf, mem_fire, Finset.mem_union, Finset.mem_sdiff]
  constructor
  · rintro ⟨⟨inStore, notTaken⟩ | made, inRegion⟩
    · exact Or.inl ⟨⟨inStore, inRegion⟩, fun ⟨taken, _⟩ => notTaken taken⟩
    · exact Or.inr ⟨made, inRegion⟩
  · rintro (⟨⟨inStore, inRegion⟩, notTaken⟩ | ⟨made, inRegion⟩)
    · exact ⟨Or.inl ⟨inStore, fun taken => notTaken ⟨taken, inRegion⟩⟩, inRegion⟩
    · exact ⟨Or.inr made, inRegion⟩

/-- **Exactness of the value relation.** A value query that holds before `d` holds after it exactly
when `d` takes from the region the same bag of labels that it makes there. -/
theorem holdsValue_fire_iff [DecidableEq R] {label : O → R} {store : Finset O} {d : Commit O R}
    (takenInStore : d.taken ⊆ store) (fresh : Disjoint d.made store) {region : R → Bool}
    {bag : Multiset R} (holds : PredicateQuery.HoldsValue label store region bag) :
    PredicateQuery.HoldsValue label (fire store d) region bag ↔
      labels label (regionOf label d.taken region) = labels label (regionOf label d.made region) := by
  unfold PredicateQuery.HoldsValue at holds ⊢
  have takenSub : regionOf label d.taken region ⊆ regionOf label store region := fun o member => by
    obtain ⟨taken, inRegion⟩ := mem_regionOf.mp member
    exact mem_regionOf.mpr ⟨takenInStore taken, inRegion⟩
  have apart : Disjoint (regionOf label store region \ regionOf label d.taken region)
      (regionOf label d.made region) := by
    refine Finset.disjoint_left.mpr fun o left right => ?_
    exact Finset.disjoint_left.mp fresh (mem_regionOf.mp right).1
      (mem_regionOf.mp (Finset.mem_sdiff.mp left).1).1
  rw [regionOf_fire, labels_union_of_disjoint label apart, labels_sdiff_of_subset label takenSub, holds]
  have le : labels label (regionOf label d.taken region) ≤ bag := by
    rw [← holds]
    exact Multiset.map_le_map (Finset.val_le_iff.mpr takenSub)
  constructor
  · intro equal
    have := congrArg (· + labels label (regionOf label d.taken region)) equal
    rw [add_right_comm, tsub_add_cancel_of_le le] at this
    exact (add_left_cancel this).symm
  · intro equal
    rw [← equal, tsub_add_cancel_of_le le]

/-! ## The double-pushout bridge -/

section Bridge

open Mettapedia.GSLT.Causality.ResourceInteraction

variable {Sys : System R} {label : O → R} {state : Finset O}

omit [DecidableEq O] in
/-- The bag of labels of a set of occurrences is the one of the double-pushout model, so
`labels_mono` and `System.labels_mono` are one law. -/
theorem labels_eq_system_labels (label : O → R) (X : Finset O) :
    labels label X = System.labels label X := rfl

/-- A commit whose labels are an instance's consumption and reads is a double-pushout match of
that instance. -/
def Enabled.toMatch {c : Commit O R} (enabled : Enabled label state c) {site : Sys.Site}
    {i : Sys.Instance site} (takenLabels : labels label c.taken = Sys.consume i)
    (keptLabels : labels label c.kept = Sys.read i) : Sys.Match label state i where
  taken := c.taken
  kept := c.kept
  taken_sub := enabled.taken_subset
  kept_sub := enabled.kept_subset
  taken_labels := takenLabels
  kept_labels := keptLabels
  identification := enabled.apart

/-- **For positive commits, independence is double-pushout parallel independence** (apart from the
choice of fresh identities, which double-pushout rewriting makes separately). -/
theorem independent_iff_dpo {c d : Commit O R} (positiveC : c.Positive) (positiveD : d.Positive)
    (enabledC : Enabled label state c) (enabledD : Enabled label state d) {site₁ site₂ : Sys.Site}
    {i : Sys.Instance site₁} {j : Sys.Instance site₂}
    (takenC : labels label c.taken = Sys.consume i) (keptC : labels label c.kept = Sys.read i)
    (takenD : labels label d.taken = Sys.consume j) (keptD : labels label d.kept = Sys.read j)
    (madeApart : Disjoint c.made d.made) :
    Independent label c d ↔
      System.Independent (enabledC.toMatch takenC keptC) (enabledD.toMatch takenD keptD) := by
  rw [System.independent_iff]
  simp only [Enabled.toMatch]
  have noWriteC : ∀ x : Commit O R, ¬ WritesInto label x c := by
    rintro x ⟨read, member, -⟩
    simp [show c.queries = [] from positiveC] at member
  have noWriteD : ∀ x : Commit O R, ¬ WritesInto label x d := by
    rintro x ⟨read, member, -⟩
    simp [show d.queries = [] from positiveD] at member
  unfold Independent Clash Spoils
  simp only [noWriteC, noWriteD, or_false, Finset.disjoint_union_right, not_not]
  constructor
  · rintro ⟨noClash, keptD', keptC'⟩
    push Not at noClash
    exact ⟨⟨noClash.1, keptD'⟩, ⟨noClash.1.symm, keptC'⟩⟩
  · rintro ⟨⟨takenApart, keptD'⟩, ⟨_, keptC'⟩⟩
    refine ⟨?_, keptD', keptC'⟩
    rintro (taken | made)
    · exact taken takenApart
    · exact made madeApart

end Bridge

/-! ## Controls -/

namespace Controls

open Atom

/-- Take the lock. -/
def lockTaker : Commit ℕ Atom := ⟨{1}, ∅, {9}, []⟩

/-- Make a second lock. -/
def lockMaker : Commit ℕ Atom := ⟨∅, ∅, {1}, []⟩

/-- A second reader of the token. -/
def reader₂ : Commit ℕ Atom := ⟨∅, {0}, {10}, []⟩

/-- A second taker of the token. -/
def taker₂ : Commit ℕ Atom := ⟨{0}, ∅, {11}, []⟩

theorem reader₂_enabled : Enabled label {0} reader₂ where
  taken_subset := by decide
  kept_subset := by decide
  apart := by decide
  fresh := by decide
  queries_hold := by simp [reader₂]

theorem taker₂_enabled : Enabled label {0} taker₂ where
  taken_subset := by decide
  kept_subset := by decide
  apart := by decide
  fresh := by decide
  queries_hold := by simp [taker₂]

/-- **A reader and a taker of one token**: the reader first runs both; the taker first blocks
the reader. -/
theorem reader_taker :
    Enabled label (fire {0} reader) taker ∧ ¬ Enabled label (fire {0} taker) reader :=
  spoils_blocks_one_order reader_enabled taker_enabled
    (by unfold Clash; simp [reader, taker])
    (Or.inl (by simp [taker, reader]))
    (by unfold Spoils WritesInto; simp [reader, taker])

/-- **Two takers of one token clash**: neither order runs both. -/
theorem takers_clash :
    ¬ Enabled label (fire {0} taker) taker₂ ∧ ¬ Enabled label (fire {0} taker₂) taker :=
  clash_blocks_both_orders taker_enabled taker₂_enabled (Or.inl (by simp [taker, taker₂]))

/-- **Two readers of one token are independent**, so both orders run, to one store. -/
theorem readers_independent : Independent label reader reader₂ := by
  refine (independent_iff_both_orders reader_enabled reader₂_enabled).mpr ⟨?_, ?_⟩
  · exact (enabled_fire_iff reader₂_enabled reader_enabled).mpr
      ⟨by unfold Clash; simp [reader, reader₂], by unfold Spoils WritesInto; simp [reader, reader₂]⟩
  · exact (enabled_fire_iff reader_enabled reader₂_enabled).mpr
      ⟨by unfold Clash; simp [reader, reader₂], by unfold Spoils WritesInto; simp [reader, reader₂]⟩

theorem lockMaker_enabled : Enabled label {0} lockMaker where
  taken_subset := by decide
  kept_subset := by decide
  apart := by decide
  fresh := by decide
  queries_hold := by simp [lockMaker]

/-- **A maker inside an absence region spoils the absence read**: making a lock first disables
"add unless locked"; the other order runs both. -/
theorem maker_spoils_absence :
    Enabled label (fire {0} unlessLocked) lockMaker ∧
      ¬ Enabled label (fire {0} lockMaker) unlessLocked :=
  spoils_blocks_one_order absence_holds_empty lockMaker_enabled
    (by unfold Clash; simp [unlessLocked, lockMaker])
    (Or.inr ⟨⟨isLock, ∅⟩, by simp [unlessLocked], 1, by simp [lockMaker], rfl⟩)
    (by unfold Spoils WritesInto; simp [unlessLocked, lockMaker])

/-- A commit that writes only outside the absence region does not spoil it: the absence read and
a reader of the token are independent. -/
theorem reader_and_absence_independent : Independent label reader unlessLocked := by
  refine ⟨by unfold Clash; simp [reader, unlessLocked], ?_, ?_⟩
  · unfold Spoils WritesInto
    simp [reader, unlessLocked, label, isLock]
  · unfold Spoils WritesInto
    simp [reader, unlessLocked]

/-! ### Identity queries are conservative: a same-value replacement -/

/-- The label of the cell control: occurrences `20` and `21` both hold the value `tok`. -/
def cellLabel : ℕ → Atom
  | 20 => tok
  | 21 => tok
  | _ => out

/-- The region of `tok`. -/
def isTok : Atom → Bool
  | tok => true
  | _ => false

/-- Replace occurrence `20` by a fresh occurrence `21` with the same value. -/
def sameValueReplace : Commit ℕ Atom := ⟨{20}, ∅, {21}, []⟩

/-- **A same-value replacement keeps the value query and breaks the identity query.** At the
store `{20}`, the region `tok` holds `{20}`; after the replacement its labels are unchanged (the
value query still holds), while its occurrences are `{21}` (the identity query, which an epoch
validates, fails). -/
theorem same_value_replace :
    PredicateQuery.HoldsValue cellLabel (fire {20} sameValueReplace) isTok {tok} ∧
      ¬ (⟨isTok, {20}⟩ : PredicateQuery ℕ Atom).Holds cellLabel (fire {20} sameValueReplace) := by
  constructor
  · unfold PredicateQuery.HoldsValue labels
    decide
  · decide

/-! ### Writing into a queried region, and spoiling -/

/-- **Positive control**: making a lock writes into the region of the lock-absence query. -/
theorem lockMaker_writesInto_unlessLocked : WritesInto label lockMaker unlessLocked := by
  unfold WritesInto; decide

/-- **Negative control**: the taker takes a token and makes an output, both outside the lock
region that `unlessLocked` queries. -/
theorem taker_not_writesInto_unlessLocked : ¬ WritesInto label taker unlessLocked := by
  unfold WritesInto; decide

/-- **Positive control, by a take**: the taker takes the token the reader keeps. -/
theorem taker_spoils_reader : Spoils label taker reader := by
  unfold Spoils WritesInto; decide

/-- **Positive control, by a write**: making a lock spoils the lock-absence query. -/
theorem lockMaker_spoils_unlessLocked : Spoils label lockMaker unlessLocked := by
  unfold Spoils WritesInto; decide

/-- **Negative control**: a second reader of the token takes nothing and makes an output; it takes
nothing the reader keeps and the reader has no predicate query to write into. -/
theorem reader₂_not_spoils_reader : ¬ Spoils label reader₂ reader := by
  unfold Spoils WritesInto; decide

end Controls

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
