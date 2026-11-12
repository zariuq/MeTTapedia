import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
# Region stamps: validating a condition that has no rows

A condition such as `absent`, `unique` or `collect` depends on every row of a
region of the store (the rows a pattern can match), present or not.  It cannot
be validated by the stamps of the rows it met, because it may have met none.

Keep, for a region, the tick of the last write that touched it (`stamp`).  The
store is a history of writes, each one tick; its content is the set of keys
inserted and not removed since.

* `content_append_of_quiet`: writes that do not touch a region leave every key
  of the region as it was.
* `stamp_le_iff_quiet`: the region's stamp is at most `t` exactly when no write
  after tick `t` touched the region.
* `condition_holds_of_stamp_le`: so any condition that depends only on the
  region's content has, now, the value it had at tick `t`, whenever the stamp
  is at most `t`.  One comparison validates the condition; nothing is
  enumerated and no row of the region is visited.
* `delta_eq`: the writes of the region after tick `t` are the writes whose
  stamp exceeds `t`: the region's stamp says whether that list is empty.

The test is conservative: a write that touches the region and leaves the
condition's value as it was still raises the stamp
(`Controls.stamp_is_conservative`), and the condition must then be evaluated
again.  It is never wrong in the other direction.

Positive example: `Controls.quiet_region_validates`.  Negative examples:
`Controls.stamp_is_conservative`, `Controls.content_alone_misses_a_cycle` (a
key removed and inserted again leaves the content equal while the occurrence
changed, which only the stamp records).

Not modelled: the data structure that keeps a stamp for every region a
pattern can name.  In an ordered index or a trie it is the maximum of the
write ticks below a node, kept on the path of each write.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Step.RegionStamps

variable {K : Type*} [DecidableEq K]

/-- One write: the key it touches, and whether it inserts or removes. -/
structure Write (K : Type*) where
  key : K
  insert : Bool

/-- The content after a history of writes, from a given content. -/
def contentFrom (s : Finset K) (ws : List (Write K)) : Finset K :=
  ws.foldl (fun acc w => if w.insert then insert w.key acc else acc.erase w.key) s

/-- The content after a history of writes, from the empty store. -/
def content (ws : List (Write K)) : Finset K := contentFrom ∅ ws

theorem contentFrom_append (s : Finset K) (ws vs : List (Write K)) :
    contentFrom s (ws ++ vs) = contentFrom (contentFrom s ws) vs := by
  simp [contentFrom, List.foldl_append]

/-- A write to another key leaves a key as it was. -/
theorem mem_contentFrom_of_untouched (s : Finset K) (ws : List (Write K)) (k : K)
    (untouched : ∀ w ∈ ws, w.key ≠ k) : k ∈ contentFrom s ws ↔ k ∈ s := by
  induction ws generalizing s with
  | nil => rfl
  | cons w ws ih =>
    have ne : w.key ≠ k := untouched w (List.mem_cons_self ..)
    have rest : ∀ v ∈ ws, v.key ≠ k := fun v hv => untouched v (List.mem_cons_of_mem _ hv)
    change k ∈ contentFrom (if w.insert then insert w.key s else s.erase w.key) ws ↔ k ∈ s
    rw [ih _ rest]
    cases w.insert
    · simp [Finset.mem_erase, Ne.symm ne]
    · simp [Finset.mem_insert, Ne.symm ne]

/-- **Writes outside a region leave the region as it was.** -/
theorem content_append_of_quiet (region : K → Prop) (ws vs : List (Write K))
    (quiet : ∀ w ∈ vs, ¬ region w.key) (k : K) (inside : region k) :
    k ∈ content (ws ++ vs) ↔ k ∈ content ws := by
  unfold content
  rw [contentFrom_append]
  exact mem_contentFrom_of_untouched _ vs k fun w hw eq => quiet w hw (eq ▸ inside)

/-- The tick of the last write that touched the region, counting from `tick`;
`0` if none did. -/
def stampFrom (region : K → Prop) [DecidablePred region] (tick : ℕ) : List (Write K) → ℕ
  | [] => 0
  | w :: ws =>
    max (if region w.key then tick + 1 else 0) (stampFrom region (tick + 1) ws)

/-- The region's stamp after a history: the tick of its last write. -/
def stamp (region : K → Prop) [DecidablePred region] (ws : List (Write K)) : ℕ :=
  stampFrom region 0 ws

omit [DecidableEq K] in
theorem stampFrom_le_iff (region : K → Prop) [DecidablePred region] (tick t : ℕ)
    (ws : List (Write K)) (reached : tick ≤ t) :
    stampFrom region tick ws ≤ t ↔ ∀ w ∈ ws.drop (t - tick), ¬ region w.key := by
  induction ws generalizing tick with
  | nil => simp [stampFrom]
  | cons w ws ih =>
    unfold stampFrom
    rw [max_le_iff]
    by_cases eq : tick = t
    · subst eq
      simp only [Nat.sub_self, List.drop_zero, List.mem_cons, forall_eq_or_imp]
      constructor
      · rintro ⟨first, rest⟩
        have notIn : ¬ region w.key := by
          intro inside
          rw [if_pos inside] at first
          omega
        refine ⟨notIn, ?_⟩
        have below : ∀ (n : ℕ) (vs : List (Write K)), tick < n → stampFrom region n vs ≤ tick →
            ∀ v ∈ vs, ¬ region v.key := by
          intro n vs
          induction vs generalizing n with
          | nil => exact fun _ _ v hv => by cases hv
          | cons v vs ihv =>
            intro lt le u hu
            unfold stampFrom at le
            rw [max_le_iff] at le
            rcases List.mem_cons.mp hu with rfl | hu
            · intro inside
              rw [if_pos inside] at le
              omega
            · exact ihv (n + 1) (by omega) le.2 u hu
        exact below (tick + 1) ws (by omega) rest
      · rintro ⟨notIn, rest⟩
        refine ⟨by rw [if_neg notIn]; exact Nat.zero_le _, ?_⟩
        have quiet : ∀ (n : ℕ) (vs : List (Write K)), (∀ v ∈ vs, ¬ region v.key) →
            stampFrom region n vs = 0 := by
          intro n vs
          induction vs generalizing n with
          | nil => exact fun _ => rfl
          | cons v vs ihv =>
            intro h
            unfold stampFrom
            rw [if_neg (h v (List.mem_cons_self ..)),
              ihv (n + 1) fun u hu => h u (List.mem_cons_of_mem _ hu)]
            rfl
        rw [quiet (tick + 1) ws rest]
        exact Nat.zero_le _
    · have lt : tick < t := lt_of_le_of_ne reached eq
      have step : t - tick = (t - (tick + 1)) + 1 := by omega
      rw [step, List.drop_succ_cons, ← ih (tick + 1) (by omega)]
      constructor
      · exact fun h => h.2
      · intro h
        refine ⟨?_, h⟩
        split
        · omega
        · exact Nat.zero_le _

omit [DecidableEq K] in
/-- **The stamp is at most `t` exactly when the region was not written after
tick `t`.** -/
theorem stamp_le_iff_quiet (region : K → Prop) [DecidablePred region] (ws : List (Write K))
    (t : ℕ) : stamp region ws ≤ t ↔ ∀ w ∈ ws.drop t, ¬ region w.key := by
  have := stampFrom_le_iff region 0 t ws (Nat.zero_le _)
  simpa [stamp] using this

/-- **One comparison validates a condition on a region.**  If the region's
stamp is at most `t`, a condition that depends only on the region's content
holds now exactly when it held at tick `t`. -/
theorem condition_holds_of_stamp_le (region : K → Prop) [DecidablePred region]
    (ws : List (Write K)) (t : ℕ) (unchanged : stamp region ws ≤ t)
    (condition : Finset K → Prop)
    (regional : ∀ s s' : Finset K, (∀ k, region k → (k ∈ s ↔ k ∈ s')) →
      (condition s ↔ condition s')) :
    condition (content ws) ↔ condition (content (ws.take t)) := by
  apply regional
  intro k inside
  have quiet := (stamp_le_iff_quiet region ws t).mp unchanged
  have := content_append_of_quiet region (ws.take t) (ws.drop t) quiet k inside
  rwa [List.take_append_drop] at this

/-- The writes of the region after tick `t`. -/
def delta (region : K → Prop) [DecidablePred region] (ws : List (Write K)) (t : ℕ) :
    List (Write K) :=
  (ws.drop t).filter fun w => region w.key

omit [DecidableEq K] in
/-- **The stamp says whether anything of the region is new**: its delta since
tick `t` is empty exactly when its stamp is at most `t`. -/
theorem delta_eq (region : K → Prop) [DecidablePred region] (ws : List (Write K)) (t : ℕ) :
    delta region ws t = [] ↔ stamp region ws ≤ t := by
  rw [stamp_le_iff_quiet, delta, List.filter_eq_nil_iff]
  simp

namespace Controls

/-- The keys below `10`. -/
def low : ℕ → Prop := fun k => k < 10

instance : DecidablePred low := fun k => by
  unfold low
  infer_instance

/-- Insert `3`, then insert `50`: the second write is outside the region. -/
def history : List (Write ℕ) := [⟨3, true⟩, ⟨50, true⟩]

/-- Positive: the region was last written at tick `1`, so a condition on it
evaluated at tick `1` stands at tick `2`. -/
theorem quiet_region_validates :
    stamp low history = 1 ∧ (3 ∈ content history ↔ 3 ∈ content (history.take 1)) := by
  refine ⟨by decide, ?_⟩
  exact condition_holds_of_stamp_le low history 1 (by decide) (fun s => 3 ∈ s)
    (fun s s' h => h 3 (by decide))

/-- Negative: a write inside the region that leaves "`7` is absent" true
raises the stamp past tick `1`: the comparison refuses, and the condition has
to be evaluated again. -/
theorem stamp_is_conservative :
    stamp low [⟨3, true⟩, ⟨4, true⟩] = 2 ∧ (7 ∉ content [⟨3, true⟩, ⟨4, true⟩]) ∧
      7 ∉ content (([⟨3, true⟩, ⟨4, true⟩] : List (Write ℕ)).take 1) := by
  decide

/-- Negative: removing `3` and inserting it again leaves the content as it was
at tick `1`; a validation that compares contents accepts, though the row a
branch met is gone.  The stamp records the two writes. -/
theorem content_alone_misses_a_cycle :
    content ([⟨3, true⟩, ⟨3, false⟩, ⟨3, true⟩] : List (Write ℕ)) = content [⟨3, true⟩] ∧
      stamp low [⟨3, true⟩, ⟨3, false⟩, ⟨3, true⟩] = 3 := by
  decide

end Controls

end Mettapedia.Machines.Step.RegionStamps
