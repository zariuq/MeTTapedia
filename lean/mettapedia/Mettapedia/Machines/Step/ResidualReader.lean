import Mettapedia.Machines.Step.Seeker
import Mathlib.Order.Interval.Finset.Nat

/-!
# The residual reader: a key and an entry stamp

An ordered index keeps, for each key it holds, a birth stamp and, once the key
is removed, a death stamp.  A key is visible at a time when it was born by then
and had not died by then.  The index holds a key until it is reclaimed, which
may be long after its death.

A reader is two words: the bound it has reached (`Bound`) and the time it
entered (`Reader`).  It holds no pointer into the index.  One step searches the
index from the bound and passes the keys that are not visible at its time
(`Seeker.filter`, `readerSeeker`).

* `Seeker.filterSeek_spec`: a seeker filtered by a predicate is a lawful
  seeker of the keys that satisfy it.  Visibility is one such predicate; a
  guard on the key is another.
* `Index.view_apply`: an insertion, a removal, and a reclamation up to a
  horizon at or below the reader's time leave the reader's view as it was.
* `interleave_entry_view`, `interleave_complete`: under any schedule of the
  reader's steps and such writes, the keys the reader yields followed by what
  it has yet to yield are what it had to yield when it started; when it
  reports the end it has yielded exactly the entry view above its bound,
  ascending, each key once.
* `rewind_entry_view`: a reader set back to `Bound.all` after any writes
  yields the whole entry view again.  Copying a reader copies two words;
  nothing in the index knows how many readers there are.
* `physical_irrelevant`: any lawful index holding the same keys gives the
  reader the same answers.
* `Index.physical_seek_kill`: a removal moves nothing, so a place reached in
  the physical index stays valid across removals; a reader may keep it as a
  hint and fall back to one search from its key after an insertion or a
  reclamation.
* `Index.pinned_card_le`: the dead keys an index must keep for a reader are at
  most the writes made since the reader entered; `Index.reclaim_clears`: a
  reclamation at the oldest reader's time leaves no other dead key.
* `Seeker.filterSeeks_exact`, `Seeker.filterDrainSeeks_le`: one step costs
  exactly one search for each key the index holds from the reader's bound up
  to the answer, visible or not; a whole drain costs at most one search for
  each key the index holds above the bound, and one more.

* `Index.revive_kill`, `Controls.revive_changes_a_view`: erasing a death stamp
  restores the store as it is now, and changes the view of every reader that
  entered while the row was dead.  Removals that a search may take back are
  not to be stamped in a store other readers enter.

Positive example: `Controls.reader_keeps_entry_view`.  Negative examples:
`Controls.early_reclaim_loses_a_key` (reclaiming past the reader's time),
`Controls.current_view_sees_the_insert` (a reader that takes its time from the
clock at each step), `Controls.revive_changes_a_view`.

The store-level reader in row order (`Cursor.StampedSnapshots`) is the case
where the key is the slot number.  This file does not restate it; it gives the
same law over any ordered key, which is what a keyed or priority reader needs.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Step

namespace Seeker

variable {K : Type*} [LinearOrder K]

/-- Search, and pass the keys that fail the predicate. -/
def filterSeek (X : Seeker K) (p : K → Prop) [DecidablePred p] (b : Bound K) : Option K :=
  match _ : X.seek b with
  | none => none
  | some k => if p k then some k else filterSeek X p (.gt k)
termination_by (X.keys.filter b.admits).card
decreasing_by exact card_gt_lt X ‹_›

theorem filterSeek_of_none (X : Seeker K) (p : K → Prop) [DecidablePred p] {b : Bound K}
    (hx : X.seek b = none) : filterSeek X p b = none := by
  rw [filterSeek]
  split
  · rfl
  · rename_i k h; rw [hx] at h; cases h

theorem filterSeek_of_some (X : Seeker K) (p : K → Prop) [DecidablePred p] {b : Bound K}
    {k : K} (hx : X.seek b = some k) :
    filterSeek X p b = if p k then some k else filterSeek X p (.gt k) := by
  rw [filterSeek]
  split
  · rename_i h; rw [hx] at h; cases h
  · rename_i k' h
    rw [hx] at h
    cases h
    rfl

theorem filterSeek_spec (X : Seeker K) (p : K → Prop) [DecidablePred p] (b : Bound K) :
    (filterSeek X p b = none → ∀ z ∈ X.keys.filter p, ¬ b.admits z) ∧
    (∀ z, filterSeek X p b = some z →
      z ∈ X.keys.filter p ∧ b.admits z ∧ ∀ w ∈ X.keys.filter p, b.admits w → z ≤ w) := by
  induction b using bound_induction X with
  | step b ih =>
    cases hx : X.seek b with
    | none =>
      rw [filterSeek_of_none X p hx]
      refine ⟨fun _ z hz hb => ?_, fun z h => by cases h⟩
      exact X.seek_none b hx z (Finset.mem_filter.mp hz).1 hb
    | some k =>
      have sk := X.seek_some b k hx
      rw [filterSeek_of_some X p hx]
      by_cases pk : p k
      · rw [if_pos pk]
        refine ⟨fun h => (by cases h), fun z h => ?_⟩
        cases h
        exact ⟨Finset.mem_filter.mpr ⟨sk.1, pk⟩, sk.2.1,
          fun w hw hb => sk.2.2 w (Finset.mem_filter.mp hw).1 hb⟩
      · rw [if_neg pk]
        have onward := ih k hx
        have past : ∀ w ∈ X.keys.filter p, b.admits w → k < w := by
          intro w hw hb
          have mem := Finset.mem_filter.mp hw
          rcases lt_or_eq_of_le (sk.2.2 w mem.1 hb) with lt | rfl
          · exact lt
          · exact absurd mem.2 pk
        refine ⟨fun h z hz hb => onward.1 h z hz (past z hz hb), fun z h => ?_⟩
        have hz := onward.2 z h
        exact ⟨hz.1, Bound.admits_mono sk.2.1 (le_of_lt hz.2.1),
          fun w hw hb => hz.2.2 w hw (past w hw hb)⟩

/-- **A filtered seeker is a seeker** of the keys that satisfy the predicate. -/
def filter (X : Seeker K) (p : K → Prop) [DecidablePred p] : Seeker K where
  keys := X.keys.filter p
  seek := filterSeek X p
  seek_none b := (filterSeek_spec X p b).1
  seek_some b := (filterSeek_spec X p b).2

@[simp] theorem filter_keys (X : Seeker K) (p : K → Prop) [DecidablePred p] :
    (X.filter p).keys = X.keys.filter p := rfl

/-- The searches one filtered search makes in the underlying index. -/
def filterSeeks (X : Seeker K) (p : K → Prop) [DecidablePred p] (b : Bound K) : Nat :=
  match _ : X.seek b with
  | none => 1
  | some k => if p k then 1 else 1 + filterSeeks X p (.gt k)
termination_by (X.keys.filter b.admits).card
decreasing_by exact card_gt_lt X ‹_›

theorem filterSeeks_of_none (X : Seeker K) (p : K → Prop) [DecidablePred p] {b : Bound K}
    (hx : X.seek b = none) : filterSeeks X p b = 1 := by
  rw [filterSeeks]
  split
  · rfl
  · rename_i k h; rw [hx] at h; cases h

theorem filterSeeks_of_some (X : Seeker K) (p : K → Prop) [DecidablePred p] {b : Bound K}
    {k : K} (hx : X.seek b = some k) :
    filterSeeks X p b = if p k then 1 else 1 + filterSeeks X p (.gt k) := by
  rw [filterSeeks]
  split
  · rename_i h; rw [hx] at h; cases h
  · rename_i k' h
    rw [hx] at h
    cases h
    rfl

/-- **The exact cost of one filtered search**: one search for each key of the
index from the bound up to the answer, the answer included; and when there is
no answer, one for each key the bound admits and one more. -/
theorem filterSeeks_exact (X : Seeker K) (p : K → Prop) [DecidablePred p] (b : Bound K) :
    (filterSeek X p b = none → filterSeeks X p b = (X.keys.filter b.admits).card + 1) ∧
    (∀ z, filterSeek X p b = some z →
      filterSeeks X p b + (X.keys.filter (Bound.gt z).admits).card =
        (X.keys.filter b.admits).card) := by
  induction b using bound_induction X with
  | step b ih =>
    cases hx : X.seek b with
    | none =>
      rw [filterSeek_of_none X p hx, filterSeeks_of_none X p hx, card_admits_of_none X hx]
      exact ⟨fun _ => rfl, fun z h => by cases h⟩
    | some k =>
      have one := card_gt_succ X hx
      rw [filterSeek_of_some X p hx, filterSeeks_of_some X p hx]
      by_cases pk : p k
      · rw [if_pos pk, if_pos pk]
        refine ⟨fun h => (by cases h), fun z h => ?_⟩
        cases h
        omega
      · rw [if_neg pk, if_neg pk]
        have onward := ih k hx
        refine ⟨fun h => ?_, fun z h => ?_⟩
        · have := onward.1 h
          omega
        · have := onward.2 z h
          omega

/-- The account of one filtered search, as bounds. -/
theorem filterSeeks_account (X : Seeker K) (p : K → Prop) [DecidablePred p] (b : Bound K) :
    (filterSeek X p b = none → filterSeeks X p b ≤ (X.keys.filter b.admits).card + 1) ∧
    (∀ z, filterSeek X p b = some z →
      filterSeeks X p b + (X.keys.filter (Bound.gt z).admits).card ≤
        (X.keys.filter b.admits).card) :=
  ⟨fun h => le_of_eq ((filterSeeks_exact X p b).1 h),
    fun z h => le_of_eq ((filterSeeks_exact X p b).2 z h)⟩

/-- A filtered search answers as the reference search of the filtered keys. -/
theorem filterSeek_eq_ofFinset (X : Seeker K) (p : K → Prop) [DecidablePred p] (b : Bound K) :
    X.filterSeek p b = (ofFinset (X.keys.filter p)).seek b :=
  seek_eq_ofFinset (X.filter p) b

/-- The searches a whole drain of the filtered seeker makes. -/
def filterDrainSeeks (X : Seeker K) (p : K → Prop) [DecidablePred p] (b : Bound K) : Nat :=
  match _ : filterSeek X p b with
  | none => filterSeeks X p b
  | some z => filterSeeks X p b + filterDrainSeeks X p (.gt z)
termination_by ((X.filter p).keys.filter b.admits).card
decreasing_by exact card_gt_lt (X.filter p) ‹_›

/-- **A drain costs at most one search for each key the index holds above the
bound, and one more**, whether the key passes the predicate or not. -/
theorem filterDrainSeeks_le (X : Seeker K) (p : K → Prop) [DecidablePred p] (b : Bound K) :
    filterDrainSeeks X p b ≤ (X.keys.filter b.admits).card + 1 := by
  induction b using bound_induction (X.filter p) with
  | step b ih =>
    rw [filterDrainSeeks]
    split
    · rename_i h
      exact (filterSeeks_account X p b).1 h
    · rename_i z h
      have := (filterSeeks_account X p b).2 z h
      have := ih z h
      omega

end Seeker

/-- An ordered index with stamps: the keys it holds (live, or dead and not yet
reclaimed), each key's birth stamp, and its death stamp once removed. -/
structure Index (K : Type*) where
  clock : Nat
  held : Finset K
  born : K → Nat
  died : K → Option Nat

namespace Index

variable {K : Type*} [LinearOrder K]

/-- The empty index. -/
def empty : Index K := ⟨0, ∅, fun _ => 0, fun _ => none⟩

/-- Born by time `t` and not dead by then. -/
def Visible (idx : Index K) (t : Nat) (k : K) : Prop :=
  idx.born k ≤ t ∧ ∀ d ∈ idx.died k, t < d

instance (idx : Index K) (t : Nat) : DecidablePred (idx.Visible t) := fun k => by
  unfold Visible
  infer_instance

/-- What a reader that entered at time `t` is owed. -/
def view (idx : Index K) (t : Nat) : Finset K := idx.held.filter (idx.Visible t)

/-- One write by anyone. -/
inductive Write (K : Type*) where
  | insert (k : K)
  | kill (k : K)
  | reclaim (horizon : Nat)

/-- An insertion stamps a birth, a removal stamps a death and leaves the key
held, a reclamation drops the keys dead at or before the horizon. -/
def apply : Write K → Index K → Index K
  | .insert k, idx =>
    if k ∈ idx.held then idx
    else ⟨idx.clock + 1, insert k idx.held, Function.update idx.born k (idx.clock + 1),
      Function.update idx.died k none⟩
  | .kill k, idx =>
    if k ∈ idx.held ∧ idx.died k = none then
      ⟨idx.clock + 1, idx.held, idx.born, Function.update idx.died k (some (idx.clock + 1))⟩
    else idx
  | .reclaim h, idx => { idx with held := idx.held.filter fun k => ∀ d ∈ idx.died k, h < d }

/-- A write a reader of time `t` allows: any insertion, any removal, and a
reclamation whose horizon is not past `t`. -/
def Safe (t : Nat) : Write K → Prop
  | .reclaim h => h ≤ t
  | _ => True

@[simp] theorem apply_insert (k : K) (idx : Index K) :
    apply (.insert k) idx =
      if k ∈ idx.held then idx
      else ⟨idx.clock + 1, insert k idx.held, Function.update idx.born k (idx.clock + 1),
        Function.update idx.died k none⟩ := rfl

@[simp] theorem apply_kill (k : K) (idx : Index K) :
    apply (.kill k) idx =
      if k ∈ idx.held ∧ idx.died k = none then
        ⟨idx.clock + 1, idx.held, idx.born, Function.update idx.died k (some (idx.clock + 1))⟩
      else idx := rfl

@[simp] theorem apply_reclaim (h : Nat) (idx : Index K) :
    apply (.reclaim h) idx =
      { idx with held := idx.held.filter fun k => ∀ d ∈ idx.died k, h < d } := rfl

theorem clock_apply (w : Write K) (idx : Index K) : idx.clock ≤ (apply w idx).clock := by
  cases w with
  | insert k =>
    rw [apply_insert]
    split_ifs
    · exact le_rfl
    · exact Nat.le_succ _
  | kill k =>
    rw [apply_kill]
    split_ifs
    · exact Nat.le_succ _
    · exact le_rfl
  | reclaim h => exact le_rfl

/-- **A reader's view does not change under writes.** -/
theorem view_apply (w : Write K) (idx : Index K) (t : Nat) (entered : t ≤ idx.clock)
    (safe : Safe t w) : view (apply w idx) t = view idx t := by
  cases w with
  | insert k =>
    rw [apply_insert]
    split_ifs with held
    · rfl
    · ext x
      simp only [view, Finset.mem_filter, Finset.mem_insert, Visible]
      by_cases eq : x = k
      · rw [eq]
        constructor
        · rintro ⟨_, born, _⟩
          rw [Function.update_self] at born
          omega
        · rintro ⟨mem, _⟩
          exact absurd mem held
      · simp only [Function.update_of_ne eq, eq, false_or]
  | kill k =>
    rw [apply_kill]
    split_ifs with live
    · ext x
      simp only [view, Finset.mem_filter, Visible]
      by_cases eq : x = k
      · rw [eq]
        constructor
        · rintro ⟨mem, born, _⟩
          refine ⟨mem, born, fun d hd => ?_⟩
          rw [live.2] at hd
          cases hd
        · rintro ⟨mem, born, _⟩
          refine ⟨mem, born, fun d hd => ?_⟩
          rw [Function.update_self] at hd
          cases hd
          omega
      · simp only [Function.update_of_ne eq]
    · rfl
  | reclaim h =>
    have le : h ≤ t := safe
    change (idx.held.filter fun k => ∀ d ∈ idx.died k, h < d).filter (idx.Visible t) =
      idx.held.filter (idx.Visible t)
    ext x
    simp only [Finset.mem_filter]
    constructor
    · exact fun hx => ⟨hx.1.1, hx.2⟩
    · exact fun hx => ⟨⟨hx.1, fun d hd => lt_of_le_of_lt le (hx.2.2 d hd)⟩, hx.2⟩

/-- **A removal moves nothing.**  The keys held are the same after it, so every
position a reader reached in the physical index is still that position. -/
theorem held_kill (k : K) (idx : Index K) : (apply (.kill k) idx).held = idx.held := by
  rw [apply_kill]
  split_ifs <;> rfl

/-- After a removal every search of the physical index answers as before.  A
reader may therefore keep the place it reached as a hint across removals; only
insertions and reclamations change what a search finds. -/
theorem physical_seek_kill (k : K) (idx : Index K) (b : Bound K) :
    (Seeker.ofFinset (apply (.kill k) idx).held).seek b = (Seeker.ofFinset idx.held).seek b := by
  rw [held_kill]

/-- Undo a removal by erasing the death stamp. -/
def revive (k : K) (idx : Index K) : Index K := { idx with died := Function.update idx.died k none }

/-- Erasing the stamp restores the keys held and every stamp but the clock:
for the store as it is now, the removal never happened. -/
theorem revive_kill (k : K) (idx : Index K) (live : k ∈ idx.held ∧ idx.died k = none) :
    (revive k (apply (.kill k) idx)).held = idx.held ∧
      (revive k (apply (.kill k) idx)).born = idx.born ∧
      (revive k (apply (.kill k) idx)).died = idx.died := by
  rw [apply_kill, if_pos live]
  refine ⟨rfl, rfl, ?_⟩
  funext x
  by_cases eq : x = k
  · rw [eq]
    simp [revive, live.2]
  · simp [revive, Function.update_of_ne eq]

/-- A sequence of writes. -/
def run (ws : List (Write K)) (idx : Index K) : Index K := ws.foldl (fun i w => apply w i) idx

theorem view_run (ws : List (Write K)) (idx : Index K) (t : Nat) (entered : t ≤ idx.clock)
    (safe : ∀ w ∈ ws, Safe t w) : view (run ws idx) t = view idx t := by
  induction ws generalizing idx with
  | nil => rfl
  | cons w ws ih =>
    have step := view_apply w idx t entered (safe w (List.mem_cons_self ..))
    have rest := ih (apply w idx) (entered.trans (clock_apply w idx))
      (fun w' h => safe w' (List.mem_cons_of_mem _ h))
    exact rest.trans step

/-- The stamps of an index reached by writes: deaths are not in the future,
and no two held keys died at the same tick. -/
structure WF (idx : Index K) : Prop where
  diedLe : ∀ k ∈ idx.held, ∀ d ∈ idx.died k, d ≤ idx.clock
  diedInj : ∀ k ∈ idx.held, ∀ k' ∈ idx.held, ∀ d, idx.died k = some d → idx.died k' = some d →
    k = k'

omit [LinearOrder K] in
theorem wf_empty : WF (empty : Index K) :=
  ⟨fun _ h => absurd h (Finset.notMem_empty _), fun _ h => absurd h (Finset.notMem_empty _)⟩

theorem WF.apply {idx : Index K} (wf : WF idx) (w : Write K) : WF (apply w idx) := by
  cases w with
  | insert k =>
    rw [apply_insert]
    split_ifs with held
    · exact wf
    · have other : ∀ x ∈ insert k idx.held, x ≠ k → x ∈ idx.held := fun x hx ne =>
        (Finset.mem_insert.mp hx).resolve_left ne
      refine ⟨fun x hx d hd => ?_, fun x hx y hy d hxd hyd => ?_⟩
      · by_cases eq : x = k
        · rw [eq] at hd
          change d ∈ Function.update idx.died k none k at hd
          rw [Function.update_self] at hd
          cases hd
        · change d ∈ Function.update idx.died k none x at hd
          rw [Function.update_of_ne eq] at hd
          exact (wf.diedLe x (other x hx eq) d hd).trans (Nat.le_succ _)
      · change Function.update idx.died k none x = some d at hxd
        change Function.update idx.died k none y = some d at hyd
        by_cases ex : x = k
        · rw [ex, Function.update_self] at hxd
          cases hxd
        · by_cases ey : y = k
          · rw [ey, Function.update_self] at hyd
            cases hyd
          · rw [Function.update_of_ne ex] at hxd
            rw [Function.update_of_ne ey] at hyd
            exact wf.diedInj x (other x hx ex) y (other y hy ey) d hxd hyd
  | kill k =>
    rw [apply_kill]
    split_ifs with live
    · refine ⟨fun x hx d hd => ?_, fun x hx y hy d hxd hyd => ?_⟩
      · change d ∈ Function.update idx.died k (some (idx.clock + 1)) x at hd
        by_cases eq : x = k
        · rw [eq, Function.update_self] at hd
          cases hd
          exact le_rfl
        · rw [Function.update_of_ne eq] at hd
          exact (wf.diedLe x hx d hd).trans (Nat.le_succ _)
      · change Function.update idx.died k (some (idx.clock + 1)) x = some d at hxd
        change Function.update idx.died k (some (idx.clock + 1)) y = some d at hyd
        by_cases ex : x = k
        · by_cases ey : y = k
          · rw [ex, ey]
          · rw [ex, Function.update_self] at hxd
            cases hxd
            rw [Function.update_of_ne ey] at hyd
            exact absurd (wf.diedLe y hy _ hyd) (Nat.not_succ_le_self _)
        · by_cases ey : y = k
          · rw [ey, Function.update_self] at hyd
            cases hyd
            rw [Function.update_of_ne ex] at hxd
            exact absurd (wf.diedLe x hx _ hxd) (Nat.not_succ_le_self _)
          · rw [Function.update_of_ne ex] at hxd
            rw [Function.update_of_ne ey] at hyd
            exact wf.diedInj x hx y hy d hxd hyd
    · exact wf
  | reclaim h =>
    refine ⟨fun x hx d hd => ?_, fun x hx y hy d hxd hyd => ?_⟩
    · exact wf.diedLe x (Finset.mem_filter.mp hx).1 d hd
    · exact wf.diedInj x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1 d hxd hyd

theorem wf_run (ws : List (Write K)) {idx : Index K} (wf : WF idx) : WF (run ws idx) := by
  induction ws generalizing idx with
  | nil => exact wf
  | cons w ws ih => exact ih (wf.apply w)

/-- The dead keys a reader of time `t` may still be owed: held, and dead after
`t`. -/
def pinned (idx : Index K) (t : Nat) : Finset K := idx.held.filter fun k => ∃ d ∈ idx.died k, t < d

omit [LinearOrder K] in
/-- **The garbage a reader pins is bounded by the writes during its life.** -/
theorem pinned_card_le {idx : Index K} (wf : WF idx) (t : Nat) :
    (pinned idx t).card ≤ idx.clock - t := by
  have maps : ∀ k ∈ pinned idx t, (idx.died k).getD 0 ∈ Finset.Ioc t idx.clock := by
    intro k hk
    obtain ⟨held, d, hd, lt⟩ := Finset.mem_filter.mp hk
    have eq : idx.died k = some d := hd
    rw [eq, Option.getD_some, Finset.mem_Ioc]
    exact ⟨lt, wf.diedLe k held d hd⟩
  have inj : Set.InjOn (fun k => (idx.died k).getD 0) (pinned idx t) := by
    intro k hk k' hk' same
    obtain ⟨held, d, hd, _⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hk)
    obtain ⟨held', d', hd', _⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hk')
    have eq : idx.died k = some d := hd
    have eq' : idx.died k' = some d' := hd'
    simp only [eq, eq', Option.getD_some] at same
    subst same
    exact wf.diedInj k held k' held' d eq eq'
  have := Finset.card_le_card_of_injOn _ maps inj
  rwa [Nat.card_Ioc] at this

/-- **After a reclamation at a horizon, every dead key still held died after
it.**  At the oldest reader's time that leaves exactly the pinned keys. -/
theorem reclaim_clears (idx : Index K) (h : Nat) :
    ∀ k ∈ (apply (.reclaim h) idx).held, ∀ d ∈ (apply (.reclaim h) idx).died k, h < d :=
  fun _ hk d hd => (Finset.mem_filter.mp hk).2 d hd

end Index

open Index in
/-- The reader's search: any lawful index of the held keys, passing the keys
not visible at the reader's time. -/
def readerSeeker {K : Type*} [LinearOrder K] (idx : Index K) (t : Nat) : Seeker K :=
  (Seeker.ofFinset idx.held).filter (idx.Visible t)

/-- A reader: the bound it has reached and the time it entered.  Two words. -/
structure Reader (K : Type*) where
  bound : Bound K
  time : Nat

section Schedules

variable {K : Type*} [LinearOrder K]

open Index

theorem readerSeeker_keys (idx : Index K) (t : Nat) : (readerSeeker idx t).keys = view idx t :=
  rfl

/-- **The physical index does not matter.**  Any lawful seeker of the held
keys, filtered by visibility, answers a reader as the reference one does. -/
theorem physical_irrelevant (idx : Index K) (t : Nat) (phys : Seeker K)
    (holds : phys.keys = idx.held) (b : Bound K) :
    (phys.filter (idx.Visible t)).seek b = (readerSeeker idx t).seek b :=
  Seeker.seek_eq_of_keys_eq _ _ (by simp [readerSeeker, holds]) b

/-- One step of a reader: a key and the reader past it, or the end. -/
def Reader.next (idx : Index K) (rd : Reader K) : Option K × Reader K :=
  match (readerSeeker idx rd.time).seek rd.bound with
  | none => (none, rd)
  | some k => (some k, { rd with bound := .gt k })

/-- A schedule: writes by anyone (`some`), and steps of the reader (`none`).
It returns the keys the reader yielded, the reader, and the index. -/
def interleave : List (Option (Write K)) → Reader K → Index K → List K × Reader K × Index K
  | [], rd, idx => ([], rd, idx)
  | some w :: rest, rd, idx => interleave rest rd (apply w idx)
  | none :: rest, rd, idx =>
    match (readerSeeker idx rd.time).seek rd.bound with
    | none => interleave rest rd idx
    | some k =>
      let out := interleave rest { rd with bound := .gt k } idx
      (k :: out.1, out.2)

/-- **The reader law.**  Under any schedule of its own steps and safe writes,
what the reader yields, followed by what a reader at its final bound has yet to
yield from the entry view, is what it had to yield from the entry view when it
started.  Its time is unchanged and the final index shows it the same view. -/
theorem interleave_entry_view (sched : List (Option (Write K))) (rd : Reader K)
    (idx : Index K) (entered : rd.time ≤ idx.clock)
    (safe : ∀ w, some w ∈ sched → Safe rd.time w) :
    (readerSeeker idx rd.time).drain rd.bound =
        (interleave sched rd idx).1 ++
          (readerSeeker idx rd.time).drain (interleave sched rd idx).2.1.bound ∧
      (interleave sched rd idx).2.1.time = rd.time ∧
      view (interleave sched rd idx).2.2 rd.time = view idx rd.time := by
  induction sched generalizing rd idx with
  | nil => exact ⟨by simp [interleave], rfl, rfl⟩
  | cons step rest ih =>
    cases step with
    | some w =>
      have same := view_apply w idx rd.time entered (safe w (List.mem_cons_self ..))
      have onward := ih rd (apply w idx) (entered.trans (clock_apply w idx))
        (fun w' h => safe w' (List.mem_cons_of_mem _ h))
      have keys : (readerSeeker (apply w idx) rd.time).keys = (readerSeeker idx rd.time).keys :=
        same
      simp only [interleave]
      refine ⟨?_, onward.2.1, onward.2.2.trans same⟩
      rw [← Seeker.drain_eq_of_keys_eq _ _ keys, ← Seeker.drain_eq_of_keys_eq _ _ keys]
      exact onward.1
    | none =>
      simp only [interleave]
      cases found : (readerSeeker idx rd.time).seek rd.bound with
      | none => exact ih rd idx entered (fun w' h => safe w' (List.mem_cons_of_mem _ h))
      | some k =>
        have onward := ih { rd with bound := .gt k } idx entered
          (fun w' h => safe w' (List.mem_cons_of_mem _ h))
        refine ⟨?_, onward.2.1, onward.2.2⟩
        rw [Seeker.drain_of_some _ found]
        exact congrArg (k :: ·) onward.1

/-- **A reader that reports the end has yielded exactly its entry view above
its bound**, ascending, each key once, whatever was written meanwhile. -/
theorem interleave_complete (sched : List (Option (Write K))) (rd : Reader K)
    (idx : Index K) (entered : rd.time ≤ idx.clock)
    (safe : ∀ w, some w ∈ sched → Safe rd.time w)
    (ended : (readerSeeker (interleave sched rd idx).2.2 rd.time).seek
      (interleave sched rd idx).2.1.bound = none) :
    (interleave sched rd idx).1 = (readerSeeker idx rd.time).drain rd.bound := by
  obtain ⟨split, _, same⟩ := interleave_entry_view sched rd idx entered safe
  have keys : (readerSeeker (interleave sched rd idx).2.2 rd.time).keys =
      (readerSeeker idx rd.time).keys := same
  have done : (readerSeeker idx rd.time).drain (interleave sched rd idx).2.1.bound = [] := by
    rw [← Seeker.drain_eq_of_keys_eq _ _ keys]
    exact Seeker.drain_of_none _ ended
  rw [split, done, List.append_nil]

/-- **Rewinding is free and exact.**  After any safe writes a reader set back
to the beginning yields the whole entry view. -/
theorem rewind_entry_view (ws : List (Write K)) (idx : Index K) (t : Nat)
    (entered : t ≤ idx.clock) (safe : ∀ w ∈ ws, Safe t w) (k : K) :
    k ∈ (readerSeeker (run ws idx) t).drain .all ↔ k ∈ view idx t := by
  rw [Seeker.mem_drain, readerSeeker_keys, view_run ws idx t entered safe]
  exact ⟨fun h => h.1, fun h => ⟨h, trivial⟩⟩

end Schedules

namespace Index.Controls

/-- Keys `1`, `3`, `5`, inserted at ticks `1`, `2`, `3`. -/
def three : Index Nat := run [.insert 1, .insert 3, .insert 5] empty

/-- Positive: a reader that entered at tick `3` is owed `1`, `3`, `5` after `3`
is removed and `4` inserted. -/
theorem reader_keeps_entry_view :
    view (run [.kill 3, .insert 4] three) 3 = {1, 3, 5} := by
  rw [view_run _ _ _ (by decide)
    (by intro w hw; simp at hw; rcases hw with rfl | rfl <;> exact True.intro)]
  decide

/-- Negative: a reclamation with horizon `4`, past the reader's time `3`, drops
the key the reader was owed. -/
theorem early_reclaim_loses_a_key :
    view (run [.kill 3, .reclaim 4] three) 3 = {1, 5} := by
  decide

/-- Negative: a reader that takes its time from the clock at each step sees the
inserted key and misses the removed one. -/
theorem current_view_sees_the_insert :
    view (run [.kill 3, .insert 4] three) 5 = {1, 4, 5} := by
  decide

/-- Negative: undoing a removal by erasing its stamp changes the view of a
reader that entered after the removal.  The reader of time `4` did not see `3`;
after the stamp is erased it does.  A take that may be undone must stay private
to the search that made it until it commits. -/
theorem revive_changes_a_view :
    view (run [.kill 3] three) 4 = {1, 5} ∧
      view (revive 3 (run [.kill 3] three)) 4 = {1, 3, 5} := by
  decide

/-- The removed key is pinned for the reader of time `3`, and one write (the
removal) was made since: the bound `pinned_card_le` is met. -/
theorem pinned_example : pinned (run [.kill 3] three) 3 = {3} := by
  decide

end Index.Controls

end Mettapedia.Machines.Step
