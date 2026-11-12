import Mathlib.Tactic

/-!
# The walk of a drain over interleaved lanes

Rows are the numbers `0, 1, 2, ...`, ordered by value, and row `r` belongs to
lane `r % L`. A drain takes, lane by lane, the least row its lane still holds:
after lane `l'` has given up its `t l'` least rows, row `r` remains exactly when
`t (r % L) ≤ r / L`. A read of lane `l` walks the order from its least remaining
row to lane `l`'s least row `l + L * t l`.

`lane_walk_bound`: when the lane read has given up no more rows than any other
lane (as in a drain that visits the lanes in turn), the walk passes at most `l`
rows of other lanes, fewer than `L`, whatever the number of rows. So such a
read never walks as far as a gather of its lane would cost once the lane holds
`L` rows or more, and the break-even rule never gathers for it.

`switch_partition`: when a read that walked the order up to position `p` turns
to an index's rows, keeping only those standing after `p`, every answer is
given exactly once: the answers at or before `p` were given by the walk.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Order.InterleavedLanes

/-- Rows remaining below lane `l`'s least row are rows `l' + L * t l` of lanes
`l' < l`: at most `l` of them. -/
theorem lane_walk_bound (L : ℕ) (hL : 0 < L) (t : ℕ → ℕ) (l : ℕ) (hl : l < L)
    (hmin : ∀ l' < L, t l ≤ t l') :
    ((Finset.range (l + L * t l)).filter (fun r => t (r % L) ≤ r / L)).card ≤ l := by
  calc ((Finset.range (l + L * t l)).filter (fun r => t (r % L) ≤ r / L)).card
      ≤ ((Finset.range l).image (fun l' => l' + L * t l)).card := by
        apply Finset.card_le_card
        intro r hr
        simp only [Finset.mem_filter, Finset.mem_range] at hr
        obtain ⟨hlt, hrem⟩ := hr
        have hdiv : r % L + L * (r / L) = r := Nat.mod_add_div r L
        have hmod : r % L < L := Nat.mod_lt r hL
        have hj : t l ≤ r / L := le_trans (hmin (r % L) hmod) hrem
        -- the row's place in its lane is exactly `t l`
        have heq : r / L = t l := by
          by_contra hne
          have hgt : t l + 1 ≤ r / L := by omega
          have hmul : L * (t l + 1) ≤ L * (r / L) := Nat.mul_le_mul_left L hgt
          have : L * (t l + 1) = L * t l + L := by ring
          omega
        simp only [Finset.mem_image, Finset.mem_range]
        refine ⟨r % L, ?_, ?_⟩
        · rw [heq] at hdiv; omega
        · rw [← heq]; exact hdiv
    _ ≤ (Finset.range l).card := Finset.card_image_le
    _ = l := Finset.card_range l

/-- The rows walked before the read reaches its lane: fewer than `L`. -/
theorem lane_walk_lt_lanes (L : ℕ) (hL : 0 < L) (t : ℕ → ℕ) (l : ℕ) (hl : l < L)
    (hmin : ∀ l' < L, t l ≤ t l') :
    ((Finset.range (l + L * t l)).filter (fun r => t (r % L) ≤ r / L)).card < L :=
  lt_of_le_of_lt (lane_walk_bound L hL t l hl hmin) hl

/-- Turning from the walk to an index at position `p`: the answers the walk gave
and the index's answers kept after `p` are all the answers, and none twice. -/
theorem switch_partition {ι : Type*} [DecidableEq ι] (answers : Finset ι)
    (pos : ι → ℕ) (p : ℕ) :
    answers.filter (fun a => pos a ≤ p) ∪ answers.filter (fun a => p < pos a) = answers ∧
      Disjoint (answers.filter (fun a => pos a ≤ p))
        (answers.filter (fun a => p < pos a)) := by
  constructor
  · ext a
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro h
      rcases le_or_gt (pos a) p with hp | hp
      · exact Or.inl ⟨h, hp⟩
      · exact Or.inr ⟨h, hp⟩
  · rw [Finset.disjoint_left]
    intro a ha hb
    simp only [Finset.mem_filter] at ha hb
    omega

end Mettapedia.Machines.Order.InterleavedLanes
