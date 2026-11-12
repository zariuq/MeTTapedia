import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Pairwise
import Mathlib.Tactic

/-!
# Lawful seekers: a reader whose whole state is a bound

An ordered index answers one question: the least key it holds that a bound
admits.  A bound admits every key (`Bound.all`), the keys from a key on
(`Bound.ge`), or the keys past a key (`Bound.gt`).  A *seeker* is a finite set
of keys together with such a `seek`, and the two laws that make the answer the
least admitted key (`Seeker.seek_none`, `Seeker.seek_some`).  Nothing else is
assumed of the index: a sorted array with binary search, a balanced tree, a
trie read in key order and a skip list are all seekers.

A reader over a seeker holds no pointer into it.  Its state is the bound: it
opens at `Bound.all`, and after yielding `x` it stands at `Bound.gt x`.

* `Seeker.seek_eq_ofFinset`: the laws determine `seek` from the keys, so two
  indexes holding the same keys answer every search alike.
* `Seeker.mem_drain`, `Seeker.drain_pairwise`: draining from a bound yields
  exactly the admitted keys, ascending, each once.
* `Seeker.drain_resume`: a drain stopped after any prefix resumes from the last
  key it yielded, and yields exactly the rest.  A copy of the reader is a copy
  of the bound; rewinding is `Bound.all`.
* `Seeker.drainSeeks_eq`, `Seeker.drain_length`: a drain makes one search per
  answer and one more to learn that it is exhausted, and its answers are as
  many as the keys the bound admits.

Positive example: `Controls.drain_example`, `Controls.resume_example`.
Negative examples: `Controls.offset_resume_replays` (a reader that keeps a
count of the answers it gave, instead of the key it reached, yields a key twice
once a smaller key appears) and `Controls.unlawful_seek_skips` (a `seek` that
answers an admitted key which is not the least one loses a key in the drain).

The model counts searches.  It does not price one: a search costs what the
index it stands for charges, a logarithm of comparisons in a balanced tree.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Step

/-- What a reader has reached: nothing yet, a key it may still yield, or a key
it has passed. -/
inductive Bound (K : Type*) where
  | all
  | ge (k : K)
  | gt (k : K)
  deriving DecidableEq, Repr

namespace Bound

variable {K : Type*} [LinearOrder K]

/-- The keys a bound still admits. -/
def admits : Bound K → K → Prop
  | all, _ => True
  | ge k, x => k ≤ x
  | gt k, x => k < x

instance (b : Bound K) : DecidablePred b.admits := fun x => by
  cases b <;> simp only [admits] <;> infer_instance

@[simp] theorem admits_all (x : K) : (all : Bound K).admits x := trivial

@[simp] theorem admits_ge (k x : K) : (ge k).admits x ↔ k ≤ x := Iff.rfl

@[simp] theorem admits_gt (k x : K) : (gt k).admits x ↔ k < x := Iff.rfl

/-- A bound admits an upper set. -/
theorem admits_mono {b : Bound K} {x y : K} (hx : b.admits x) (hxy : x ≤ y) : b.admits y := by
  cases b with
  | all => trivial
  | ge k => exact le_trans hx hxy
  | gt k => exact lt_of_lt_of_le hx hxy

end Bound

/-- An ordered index as its readers use it: the keys it holds, and the search
for the least key a bound admits. -/
structure Seeker (K : Type*) [LinearOrder K] where
  /-- The keys held.  Specification only: a reader never enumerates them. -/
  keys : Finset K
  /-- One index search. -/
  seek : Bound K → Option K
  seek_none : ∀ b, seek b = none → ∀ x ∈ keys, ¬ b.admits x
  seek_some : ∀ b x, seek b = some x →
    x ∈ keys ∧ b.admits x ∧ ∀ y ∈ keys, b.admits y → x ≤ y

namespace Seeker

variable {K : Type*} [LinearOrder K]

/-- The reference seeker of a finite set of keys. -/
def ofFinset (s : Finset K) : Seeker K where
  keys := s
  seek b := (s.filter b.admits).min
  seek_none b h x hx hb := by
    have empty : s.filter b.admits = ∅ := Finset.min_eq_top.mp h
    have : x ∈ s.filter b.admits := Finset.mem_filter.mpr ⟨hx, hb⟩
    simp [empty] at this
  seek_some b x h := by
    have mem : x ∈ s.filter b.admits := Finset.mem_of_min h
    refine ⟨(Finset.mem_filter.mp mem).1, (Finset.mem_filter.mp mem).2, fun y hy hb => ?_⟩
    exact Finset.min_le_of_eq (Finset.mem_filter.mpr ⟨hy, hb⟩) h

@[simp] theorem ofFinset_keys (s : Finset K) : (ofFinset s).keys = s := rfl

/-- A search answers exactly when some key is admitted. -/
theorem seek_isSome_iff (S : Seeker K) (b : Bound K) :
    (S.seek b).isSome ↔ ∃ x ∈ S.keys, b.admits x := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp h
    exact ⟨x, (S.seek_some b x hx).1, (S.seek_some b x hx).2.1⟩
  · rintro ⟨x, hx, hb⟩
    cases h : S.seek b with
    | none => exact absurd hb (S.seek_none b h x hx)
    | some y => rfl

/-- **The laws determine the search.**  Two seekers with the same keys answer
every bound alike, whatever their representation. -/
theorem seek_eq_of_keys_eq (S T : Seeker K) (same : S.keys = T.keys) (b : Bound K) :
    S.seek b = T.seek b := by
  cases hs : S.seek b with
  | none =>
    cases ht : T.seek b with
    | none => rfl
    | some y =>
      have hy := T.seek_some b y ht
      exact absurd hy.2.1 (S.seek_none b hs y (same ▸ hy.1))
  | some x =>
    have hx := S.seek_some b x hs
    cases ht : T.seek b with
    | none => exact absurd hx.2.1 (T.seek_none b ht x (same ▸ hx.1))
    | some y =>
      have hy := T.seek_some b y ht
      exact congrArg some
        (le_antisymm (hx.2.2 y (same ▸ hy.1) hy.2.1) (hy.2.2 x (same ▸ hx.1) hx.2.1))

theorem seek_eq_ofFinset (S : Seeker K) (b : Bound K) :
    S.seek b = (ofFinset S.keys).seek b :=
  seek_eq_of_keys_eq S (ofFinset S.keys) rfl b

/-- The keys still admitted after `x` was found are fewer. -/
theorem card_gt_lt (S : Seeker K) {b : Bound K} {x : K} (h : S.seek b = some x) :
    (S.keys.filter (Bound.gt x).admits).card < (S.keys.filter b.admits).card := by
  have hx := S.seek_some b x h
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨fun y hy => ?_, fun eq => ?_⟩
  · have := Finset.mem_filter.mp hy
    exact Finset.mem_filter.mpr ⟨this.1, Bound.admits_mono hx.2.1 (le_of_lt this.2)⟩
  · have mem : x ∈ S.keys.filter b.admits := Finset.mem_filter.mpr ⟨hx.1, hx.2.1⟩
    rw [← eq] at mem
    exact lt_irrefl x (Finset.mem_filter.mp mem).2

/-- The keys a bound admits are the key found and the keys past it. -/
theorem filter_admits_eq_insert (S : Seeker K) {b : Bound K} {x : K} (h : S.seek b = some x) :
    S.keys.filter b.admits = insert x (S.keys.filter (Bound.gt x).admits) := by
  have hx := S.seek_some b x h
  ext y
  simp only [Finset.mem_filter, Finset.mem_insert, Bound.admits_gt]
  constructor
  · rintro ⟨hy, hb⟩
    rcases eq_or_lt_of_le (hx.2.2 y hy hb) with rfl | lt
    · exact Or.inl rfl
    · exact Or.inr ⟨hy, lt⟩
  · rintro (rfl | ⟨hy, lt⟩)
    · exact ⟨hx.1, hx.2.1⟩
    · exact ⟨hy, Bound.admits_mono hx.2.1 (le_of_lt lt)⟩

theorem card_gt_succ (S : Seeker K) {b : Bound K} {x : K} (h : S.seek b = some x) :
    (S.keys.filter b.admits).card = (S.keys.filter (Bound.gt x).admits).card + 1 := by
  rw [filter_admits_eq_insert S h, Finset.card_insert_of_notMem]
  simp

theorem card_admits_of_none (S : Seeker K) {b : Bound K} (h : S.seek b = none) :
    (S.keys.filter b.admits).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  exact fun x hx => S.seek_none b h x hx

/-- Every key a reader at bound `b` has yet to yield, in the order it yields
them: search, yield, stand past the key, repeat. -/
def drain (S : Seeker K) (b : Bound K) : List K :=
  match _ : S.seek b with
  | none => []
  | some x => x :: drain S (.gt x)
termination_by (S.keys.filter b.admits).card
decreasing_by exact card_gt_lt S ‹_›

theorem drain_of_none (S : Seeker K) {b : Bound K} (h : S.seek b = none) : S.drain b = [] := by
  rw [drain]
  split
  · rfl
  · rename_i x hx
    rw [h] at hx
    cases hx

theorem drain_of_some (S : Seeker K) {b : Bound K} {x : K} (h : S.seek b = some x) :
    S.drain b = x :: S.drain (.gt x) := by
  rw [drain]
  split
  · rename_i hn
    rw [h] at hn
    cases hn
  · rename_i y hy
    rw [h] at hy
    cases hy
    rfl

/-- Strong induction on the keys a bound still admits. -/
theorem bound_induction (S : Seeker K) {motive : Bound K → Prop}
    (step : ∀ b, (∀ x, S.seek b = some x → motive (.gt x)) → motive b) (b : Bound K) :
    motive b := by
  induction h : (S.keys.filter b.admits).card using Nat.strong_induction_on generalizing b with
  | _ n ih =>
    apply step
    intro x hx
    exact ih _ (h ▸ card_gt_lt S hx) _ rfl

/-- A drain yields exactly the admitted keys. -/
theorem mem_drain (S : Seeker K) (b : Bound K) (y : K) :
    y ∈ S.drain b ↔ y ∈ S.keys ∧ b.admits y := by
  induction b using bound_induction S with
  | step b ih =>
    cases h : S.seek b with
    | none =>
      rw [drain_of_none S h]
      simpa using fun hy => S.seek_none b h y hy
    | some x =>
      have hx := S.seek_some b x h
      rw [drain_of_some S h, List.mem_cons, ih x h]
      constructor
      · rintro (rfl | ⟨hy, hlt⟩)
        · exact ⟨hx.1, hx.2.1⟩
        · exact ⟨hy, Bound.admits_mono hx.2.1 (le_of_lt hlt)⟩
      · rintro ⟨hy, hb⟩
        rcases eq_or_lt_of_le (hx.2.2 y hy hb) with rfl | hlt
        · exact Or.inl rfl
        · exact Or.inr ⟨hy, hlt⟩

/-- A drain is strictly ascending: each key once, in key order. -/
theorem drain_pairwise (S : Seeker K) (b : Bound K) : (S.drain b).Pairwise (· < ·) := by
  induction b using bound_induction S with
  | step b ih =>
    cases h : S.seek b with
    | none => rw [drain_of_none S h]; exact List.Pairwise.nil
    | some x =>
      rw [drain_of_some S h]
      exact List.Pairwise.cons (fun y hy => ((mem_drain S (.gt x) y).mp hy).2) (ih x h)

/-- A drain yields as many keys as the bound admits. -/
theorem drain_length (S : Seeker K) (b : Bound K) :
    (S.drain b).length = (S.keys.filter b.admits).card := by
  have nodup : (S.drain b).Nodup := (drain_pairwise S b).imp ne_of_lt
  rw [← List.toFinset_card_of_nodup nodup]
  congr 1
  ext y
  rw [List.mem_toFinset, mem_drain, Finset.mem_filter]

/-- **A reader resumes from its last key alone.**  If a drain has yielded a
prefix ending in `x`, then the reader that knows only `x` yields exactly what
remained.  The prefix is not kept, and neither is a position in the index. -/
theorem drain_resume (S : Seeker K) (b : Bound K) (pre post : List K) (x : K)
    (split : S.drain b = pre ++ x :: post) : S.drain (.gt x) = post := by
  induction pre generalizing b with
  | nil =>
    cases h : S.seek b with
    | none => rw [drain_of_none S h] at split; cases split
    | some y =>
      rw [drain_of_some S h] at split
      injection split with hy hrest
      subst hy
      exact hrest
  | cons p pre ih =>
    cases h : S.seek b with
    | none => rw [drain_of_none S h] at split; cases split
    | some y =>
      rw [drain_of_some S h] at split
      injection split with _ hrest
      exact ih (.gt y) hrest

/-- The searches a drain makes. -/
def drainSeeks (S : Seeker K) (b : Bound K) : Nat :=
  match _ : S.seek b with
  | none => 1
  | some x => 1 + drainSeeks S (.gt x)
termination_by (S.keys.filter b.admits).card
decreasing_by exact card_gt_lt S ‹_›

/-- One search per answer, and one to find the end. -/
theorem drainSeeks_eq (S : Seeker K) (b : Bound K) :
    S.drainSeeks b = (S.drain b).length + 1 := by
  induction b using bound_induction S with
  | step b ih =>
    cases h : S.seek b with
    | none =>
      rw [drain_of_none S h, drainSeeks]
      split
      · rfl
      · rename_i x hx; rw [h] at hx; cases hx
    | some x =>
      rw [drain_of_some S h, drainSeeks]
      split
      · rename_i hn; rw [h] at hn; cases hn
      · rename_i y hy
        rw [h] at hy
        cases hy
        rw [ih x h, List.length_cons]
        omega

/-- Two seekers with the same keys drain alike. -/
theorem drain_eq_of_keys_eq (S T : Seeker K) (same : S.keys = T.keys) (b : Bound K) :
    S.drain b = T.drain b := by
  induction b using bound_induction S with
  | step b ih =>
    cases h : S.seek b with
    | none =>
      rw [drain_of_none S h, drain_of_none T (seek_eq_of_keys_eq S T same b ▸ h)]
    | some x =>
      rw [drain_of_some S h, drain_of_some T (seek_eq_of_keys_eq S T same b ▸ h), ih x h]

namespace Controls

/-- Positive: the keys from 3 on, ascending. -/
example : (ofFinset ({5, 1, 9, 3} : Finset Nat)).drain (.ge 3) = [3, 5, 9] := by
  rw [drain_of_some _ (x := 3) (by decide), drain_of_some _ (x := 5) (by decide),
    drain_of_some _ (x := 9) (by decide), drain_of_none _ (by decide)]

theorem drain_example : (ofFinset ({5, 1, 9, 3} : Finset Nat)).drain .all = [1, 3, 5, 9] := by
  rw [drain_of_some _ (x := 1) (by decide), drain_of_some _ (x := 3) (by decide),
    drain_of_some _ (x := 5) (by decide), drain_of_some _ (x := 9) (by decide),
    drain_of_none _ (by decide)]

/-- Positive: stopped after `3`, the reader that knows only `3` yields the rest. -/
theorem resume_example : (ofFinset ({5, 1, 9, 3} : Finset Nat)).drain (.gt 3) = [5, 9] :=
  drain_resume _ .all [1] [5, 9] 3 drain_example

/-- A reader that remembers how many answers it gave, and resumes by dropping
that many from a fresh drain. -/
def offsetResume (s : Finset Nat) (given : Nat) : List Nat :=
  ((ofFinset s).drain .all).drop given

/-- Negative: after yielding `1` and `3` from `{1, 3, 5}`, a key `0` is added.
Resuming by count yields `3` again; resuming by key does not. -/
theorem offset_resume_replays :
    offsetResume {0, 1, 3, 5} 2 = [3, 5] ∧
      (ofFinset ({0, 1, 3, 5} : Finset Nat)).drain (.gt 3) = [5] := by
  constructor
  · unfold offsetResume
    rw [drain_of_some _ (x := 0) (by decide), drain_of_some _ (x := 1) (by decide),
      drain_of_some _ (x := 3) (by decide), drain_of_some _ (x := 5) (by decide),
      drain_of_none _ (by decide)]
    rfl
  · rw [drain_of_some _ (x := 5) (by decide), drain_of_none _ (by decide)]

/-- A search that answers the greatest admitted key instead of the least. -/
def greatestSeek (s : Finset Nat) (b : Bound Nat) : Option Nat := (s.filter b.admits).max

/-- Negative: such a search violates `seek_some`, and a drain driven by it
yields `9` first and never yields `1`, `3` or `5`. -/
theorem unlawful_seek_skips :
    greatestSeek {5, 1, 9, 3} .all = some 9 ∧ greatestSeek {5, 1, 9, 3} (.gt 9) = none ∧
      ¬ (∀ y ∈ ({5, 1, 9, 3} : Finset Nat), (Bound.all : Bound Nat).admits y → 9 ≤ y) := by
  refine ⟨by decide, by decide, fun h => ?_⟩
  have := h 1 (by decide) trivial
  omega

end Controls

end Seeker

end Mettapedia.Machines.Step
