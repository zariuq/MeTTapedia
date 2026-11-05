import Mathlib.Tactic

/-!
# Placement in an open-addressed table: crafted homes cost quadratic probes

The term universe's tables (records, integers, symbols, index keys) place an
entry at a home slot computed from its content and probe linearly from there.
With a placement fixed by the content alone, terms crafted to share a home
make every insertion and lookup walk the whole cluster: the `i`-th such entry
probes `i + 1` slots.  Placing by the content mixed with a key of the table's
own takes that choice away from whoever writes the terms; the flood gates
(`test-integer-flood`, `test-symbol-flood`) measure the result.

The model: a run of insertions into a table large enough never to wrap, each
probing from its home to the first free slot.  This file proves:
* `shared_home_probes`: `n` entries sharing one home probe `n (n + 1) / 2`
  slots in all;
* `spread_homes_probes`: `n` entries with pairwise distinct homes probe one
  slot each, `n` in all;
* `shared_exceeds_spread`: from two entries on, sharing a home costs more,
  and the gap grows quadratically.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.KeyedPlacementCost

/-- The slot an entry with home `h` takes when the slots in `used` are taken:
the first free one from `h` on (linear probing), searched over a window of
`fuel` slots. -/
def firstFree (used : Finset ℕ) (h : ℕ) : ℕ → ℕ
  | 0 => h
  | fuel + 1 => if h ∈ used then firstFree used (h + 1) fuel else h

/-- Insert entries with the homes `homes`, in order: the slots taken and the
probes paid (one per slot looked at). -/
def insertAll (fuel : ℕ) : List ℕ → Finset ℕ × ℕ
  | [] => (∅, 0)
  | h :: rest =>
    let (used, probes) := insertAll fuel rest
    let slot := firstFree used h fuel
    (insert slot used, probes + (slot - h + 1))

/-- With the slots `h, …, h + i - 1` taken, an entry homed at `h` takes
`h + i`. -/
theorem firstFree_run (h i fuel : ℕ) (hfuel : i ≤ fuel) :
    firstFree ((Finset.range i).image (h + ·)) h fuel = h + i := by
  induction i generalizing h fuel with
  | zero =>
    cases fuel with
    | zero => simp [firstFree]
    | succ fuel => simp [firstFree]
  | succ i ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have hmem : h ∈ (Finset.range (i + 1)).image (h + ·) := by
        simp
      simp only [firstFree, hmem, if_true]
      have hset : (Finset.range (i + 1)).image (h + ·) =
          insert h ((Finset.range i).image ((h + 1) + ·)) := by
        ext x
        simp only [Finset.mem_image, Finset.mem_range, Finset.mem_insert]
        constructor
        · rintro ⟨j, hj, rfl⟩
          rcases j with _ | j
          · left; rfl
          · right; exact ⟨j, by omega, by omega⟩
        · rintro (rfl | ⟨j, hj, rfl⟩)
          · exact ⟨0, by omega, by omega⟩
          · exact ⟨j + 1, by omega, by omega⟩
      have hnext : firstFree (insert h ((Finset.range i).image ((h + 1) + ·)))
          (h + 1) fuel = (h + 1) + i := by
        have hnot : ∀ y, y ≠ h → (y ∈ insert h ((Finset.range i).image ((h + 1) + ·)) ↔
            y ∈ (Finset.range i).image ((h + 1) + ·)) := by
          intro y hy
          simp [hy]
        -- slots from h + 1 on see only the run above h
        have key : ∀ (s : ℕ) (f : ℕ), h < s →
            firstFree (insert h ((Finset.range i).image ((h + 1) + ·))) s f =
              firstFree ((Finset.range i).image ((h + 1) + ·)) s f := by
          intro s f hs
          induction f generalizing s with
          | zero => simp [firstFree]
          | succ f ihf =>
            simp only [firstFree]
            by_cases hin : s ∈ (Finset.range i).image ((h + 1) + ·)
            · have hin' : s ∈ insert h ((Finset.range i).image ((h + 1) + ·)) :=
                Finset.mem_insert_of_mem hin
              rw [if_pos hin', if_pos hin]
              exact ihf (s + 1) (by omega)
            · have hin' : s ∉ insert h ((Finset.range i).image ((h + 1) + ·)) := by
                rw [hnot s (by omega)]
                exact hin
              rw [if_neg hin', if_neg hin]
        rw [key (h + 1) fuel (by omega)]
        exact ih (h + 1) fuel (by omega)
      rw [hset, hnext]
      omega

/-- `n` entries sharing the home `h`: they take `h, …, h + n - 1`. -/
theorem shared_home_insert (h n fuel : ℕ) (hfuel : n ≤ fuel) :
    insertAll fuel (List.replicate n h) =
      ((Finset.range n).image (h + ·), n * (n + 1) / 2) := by
  induction n with
  | zero => simp [insertAll]
  | succ n ih =>
    simp only [List.replicate_succ, insertAll]
    rw [ih (by omega)]
    simp only
    rw [firstFree_run h n fuel (by omega)]
    have hset : insert (h + n) ((Finset.range n).image (h + ·)) =
        (Finset.range (n + 1)).image (h + ·) := by
      ext x
      simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_range]
      constructor
      · rintro (rfl | ⟨j, hj, rfl⟩)
        · exact ⟨n, by omega, rfl⟩
        · exact ⟨j, by omega, rfl⟩
      · rintro ⟨j, hj, rfl⟩
        by_cases hjn : j = n
        · left; rw [hjn]
        · right; exact ⟨j, by omega, rfl⟩
    rw [hset]
    congr 1
    have h2 : (n + 1) * (n + 1 + 1) / 2 = n * (n + 1) / 2 + (n + 1) := by
      have := Nat.div_add_mod (n * (n + 1)) 2
      have hev : n * (n + 1) % 2 = 0 := by
        rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩ <;> ring_nf <;> omega
      rw [show (n + 1) * (n + 1 + 1) = n * (n + 1) + 2 * (n + 1) by ring]
      omega
    omega

theorem shared_home_probes (h n fuel : ℕ) (hfuel : n ≤ fuel) :
    2 * (insertAll fuel (List.replicate n h)).2 = n * (n + 1) := by
  rw [shared_home_insert h n fuel hfuel]
  simp only
  have hev : n * (n + 1) % 2 = 0 := by
    rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩ <;> ring_nf <;> omega
  omega

/-- Entries with pairwise distinct homes each find their home free: they take
their homes and probe one slot each. -/
theorem spread_homes_insert (fuel : ℕ) (homes : List ℕ) (hd : homes.Nodup) :
    insertAll fuel homes = (homes.toFinset, homes.length) := by
  induction homes with
  | nil => simp [insertAll]
  | cons h rest ih =>
    rw [List.nodup_cons] at hd
    simp only [insertAll]
    rw [ih hd.2]
    simp only
    have hfree : firstFree rest.toFinset h fuel = h := by
      cases fuel with
      | zero => simp [firstFree]
      | succ fuel =>
        simp only [firstFree]
        rw [if_neg (by simpa using hd.1)]
    rw [hfree]
    simp [List.toFinset_cons]

theorem spread_homes_probes (fuel : ℕ) (homes : List ℕ) (hd : homes.Nodup) :
    (insertAll fuel homes).2 = homes.length := by
  rw [spread_homes_insert fuel homes hd]

/-- From two entries on, `n` entries sharing a home probe more than `n`
entries with distinct homes, by `n (n - 1) / 2`. -/
theorem shared_exceeds_spread (h n fuel : ℕ) (hfuel : n ≤ fuel) (hn : 2 ≤ n)
    (homes : List ℕ) (hd : homes.Nodup) (hlen : homes.length = n) :
    (insertAll fuel homes).2 < (insertAll fuel (List.replicate n h)).2 := by
  have hs := shared_home_probes h n fuel hfuel
  rw [spread_homes_probes fuel homes hd, hlen]
  nlinarith

end Mettapedia.Machines.KeyedPlacementCost
