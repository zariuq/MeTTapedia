import Mettapedia.Machines.NameSupplies.SharedSupplies
import Mettapedia.Machines.NameSupplies.PositionBounds
import Mathlib.Data.Nat.Log

/-!
# Balanced pieces: a fork into `k` parts in ⌈log₂ k⌉ halvings

`Share.piece` forks a share into `k` parts linearly: the first part takes the left half and the
others share the right half, so the last part lies `k - 1` halvings down
(`linear_last_piece`).  A **balanced** fork halves the share and gives the first ⌈k/2⌉ parts the left
half and the others the right half, recursively (`balancedPath`, `balancedPiece`, along `shareAt`).

* **A splitter** (`balancedSplitter`).  The pieces are normal and nonempty (`shareAt_normal`), inside
  the share (`shareAt_owns`), pairwise disjoint (`balancedPieces_disjoint`), and together they cover the
  share (`balancedPieces_cover`).  So the share discipline with balanced pieces keeps pools well shared
  and draws no name twice (`balanced_exact`, an instance of `shares_exact_with`).
* **Placement.**  Part `i` of a fork into `k` parts is `balancedPiece share k i` at the forking supply's
  clock (`balancedDiscipline_piece`): a function of the forking supply, `k` and `i` only.
* **Depth and size.**  A balanced part lies at most ⌈log₂ k⌉ halvings and `2⌈log₂ k⌉` nodes beyond
  the share (`balancedPiece_depth_le`, `balancedPiece_size_le`); a part of a dyadic interval is the
  dyadic interval one path further (`balancedPiece_interval`).
* **One word** (`wide_fork_word`).  A 64-bit word holds a dyadic interval as a start bit and a path of
  at most 62 halvings.  Forking the whole interval into 640 parts, the last linear part is an interval
  639 halvings deep, while every balanced part is an interval at most 10 halvings deep.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.NameSupplies

/-! ## Walking down a share -/

theorem shareAt_append (share : Share) (first second : List Bool) :
    shareAt share (first ++ second) = shareAt (shareAt share first) second := by
  induction first generalizing share with
  | nil => rfl
  | cons bit rest ih => cases bit <;> exact ih _

theorem shareAt_owns {share : Share} {path : List Bool} {point : ℕ → Bool}
    (inside : (shareAt share path).Owns point) : share.Owns point := by
  induction path generalizing share with
  | nil => exact inside
  | cons bit rest ih =>
      cases bit
      · exact Share.owns_of_split_fst (ih inside)
      · exact Share.owns_of_split_snd (ih inside)

theorem shareAt_normal {share : Share} (normal : share.Normal) (nonempty : share ≠ .none)
    (path : List Bool) : (shareAt share path).Normal ∧ shareAt share path ≠ .none := by
  induction path generalizing share with
  | nil => exact ⟨normal, nonempty⟩
  | cons bit rest ih =>
      obtain ⟨n₁, n₂, e₁, e₂⟩ := Share.split_normal normal nonempty
      cases bit
      · exact ih n₁ e₁
      · exact ih n₂ e₂

theorem shareAt_depth_le (share : Share) (path : List Bool) :
    (shareAt share path).depth ≤ share.depth + path.length := by
  induction path generalizing share with
  | nil => simp [shareAt]
  | cons bit rest ih =>
      obtain ⟨left, right⟩ := Share.depth_split_le share
      cases bit
      · have := ih (Share.split share).1
        simp only [shareAt, List.length_cons]
        omega
      · have := ih (Share.split share).2
        simp only [shareAt, List.length_cons]
        omega

theorem shareAt_interval (path more : List Bool) :
    shareAt (Share.interval path) more = Share.interval (path ++ more) := by
  induction more generalizing path with
  | nil => simp [shareAt]
  | cons bit rest ih =>
      cases bit
      · simp only [shareAt, Share.split_interval]
        rw [ih]
        simp
      · simp only [shareAt, Share.split_interval]
        rw [ih]
        simp

/-- **Parts down different halves are disjoint.** -/
theorem shareAt_diverge (share : Share) (common first second : List Bool) :
    ¬ (shareAt share (common ++ false :: first)).Overlap (shareAt share (common ++ true :: second)) := by
  rintro ⟨point, inFirst, inSecond⟩
  rw [shareAt_append] at inFirst inSecond
  exact Share.split_disjoint (shareAt share common)
    ⟨point, shareAt_owns (path := first) inFirst, shareAt_owns (path := second) inSecond⟩

/-! ## The balanced path -/

/-- The path of part `i` among `k` parts: the first ⌈k/2⌉ parts go to the left half, the others to
the right half, recursively. -/
def balancedPath (k i : ℕ) : List Bool :=
  if small : k ≤ 1 then [] else
    if i < (k + 1) / 2 then false :: balancedPath ((k + 1) / 2) i
    else true :: balancedPath (k / 2) (i - (k + 1) / 2)
termination_by k
decreasing_by all_goals omega

theorem balancedPath_small {k : ℕ} (small : k ≤ 1) (i : ℕ) : balancedPath k i = [] := by
  rw [balancedPath, dif_pos small]

theorem balancedPath_left {k i : ℕ} (large : 1 < k) (early : i < (k + 1) / 2) :
    balancedPath k i = false :: balancedPath ((k + 1) / 2) i := by
  rw [balancedPath, dif_neg (by omega), if_pos early]

theorem balancedPath_right {k i : ℕ} (large : 1 < k) (late : ¬ i < (k + 1) / 2) :
    balancedPath k i = true :: balancedPath (k / 2) (i - (k + 1) / 2) := by
  rw [balancedPath, dif_neg (by omega), if_neg late]

/-- **A balanced path has at most ⌈log₂ k⌉ halvings.** -/
theorem balancedPath_length (k i : ℕ) : (balancedPath k i).length ≤ Nat.clog 2 k := by
  induction k using Nat.strong_induction_on generalizing i with
  | _ k ih =>
      by_cases small : k ≤ 1
      · simp [balancedPath_small small]
      · have halving : Nat.clog 2 k = Nat.clog 2 ((k + 1) / 2) + 1 := by
          have recursion := Nat.clog_of_one_lt (b := 2) (n := k) (by omega) (by omega)
          rwa [show (k + 2 - 1) / 2 = (k + 1) / 2 by omega] at recursion
        by_cases early : i < (k + 1) / 2
        · rw [balancedPath_left (by omega) early, List.length_cons, halving]
          have := ih ((k + 1) / 2) (by omega) i
          omega
        · rw [balancedPath_right (by omega) early, List.length_cons, halving]
          have := ih (k / 2) (by omega) (i - (k + 1) / 2)
          have := Nat.clog_mono_right 2 (show k / 2 ≤ (k + 1) / 2 by omega)
          omega

/-! ## Balanced pieces -/

/-- **Part `i` of a balanced fork of `share` into `k` parts.** -/
def balancedPiece (share : Share) (k i : ℕ) : Share := shareAt share (balancedPath k i)

/-- **Balanced pieces are pairwise disjoint.** -/
theorem balancedPieces_disjoint (share : Share) {k i j : ℕ} (iBelow : i < k) (jBelow : j < k)
    (distinct : i ≠ j) : ¬ (balancedPiece share k i).Overlap (balancedPiece share k j) := by
  induction k using Nat.strong_induction_on generalizing share i j with
  | _ k ih =>
      have large : 1 < k := by omega
      unfold balancedPiece
      by_cases iEarly : i < (k + 1) / 2 <;> by_cases jEarly : j < (k + 1) / 2
      · rw [balancedPath_left large iEarly, balancedPath_left large jEarly]
        exact ih ((k + 1) / 2) (by omega) (Share.split share).1 iEarly jEarly distinct
      · rw [balancedPath_left large iEarly, balancedPath_right large jEarly]
        simpa using shareAt_diverge share [] (balancedPath ((k + 1) / 2) i)
          (balancedPath (k / 2) (j - (k + 1) / 2))
      · rw [balancedPath_right large iEarly, balancedPath_left large jEarly]
        intro overlap
        exact shareAt_diverge share [] (balancedPath ((k + 1) / 2) j)
          (balancedPath (k / 2) (i - (k + 1) / 2)) (by simpa using overlap.symm)
      · rw [balancedPath_right large iEarly, balancedPath_right large jEarly]
        exact ih (k / 2) (by omega) (Share.split share).2 (by omega) (by omega) (by omega)

/-- **Balanced pieces cover the share.** -/
theorem balancedPieces_cover {share : Share} {point : ℕ → Bool} (owned : share.Owns point)
    {k : ℕ} (positive : 0 < k) : ∃ i < k, (balancedPiece share k i).Owns point := by
  induction k using Nat.strong_induction_on generalizing share with
  | _ k ih =>
      by_cases small : k ≤ 1
      · exact ⟨0, positive, by rw [balancedPiece, balancedPath_small small]; exact owned⟩
      · rcases (Share.owns_split share point).mpr owned with left | right
        · obtain ⟨i, below, inside⟩ := ih ((k + 1) / 2) (by omega) left (by omega)
          refine ⟨i, by omega, ?_⟩
          rw [balancedPiece, balancedPath_left (by omega) below]
          exact inside
        · obtain ⟨i, below, inside⟩ := ih (k / 2) (by omega) right (by omega)
          refine ⟨(k + 1) / 2 + i, by omega, ?_⟩
          rw [balancedPiece, balancedPath_right (by omega) (by omega), Nat.add_sub_cancel_left]
          exact inside

/-- **The balanced splitter.** -/
def balancedSplitter : Splitter where
  piece := balancedPiece
  piece_normal normal nonempty _ _ := shareAt_normal normal nonempty _
  piece_owns inside := shareAt_owns inside
  pieces_disjoint share _ _ _ iBelow jBelow distinct :=
    balancedPieces_disjoint share iBelow jBelow distinct

/-- **The share discipline with balanced forks.** -/
def balancedDiscipline : Discipline ShareSupply ShareName := splitDiscipline balancedSplitter

/-- **Placement**: part `i` of a balanced fork into `k` parts is a function of the forking supply,
`k` and `i` only. -/
theorem balancedDiscipline_piece (supply : ShareSupply) (k i : ℕ) :
    balancedDiscipline.piece supply k i = ⟨balancedPiece supply.share k i, supply.clock⟩ := rfl

/-- **Balanced forks keep names exact**: from a well-shared pool, no valid run draws a name twice. -/
theorem balanced_exact (pool : Pool ShareSupply ShareName) (shared : WellShared pool) :
    Exact balancedDiscipline pool :=
  shares_exact_with balancedSplitter pool shared

/-! ## Depth and size -/

/-- **A balanced part lies at most ⌈log₂ k⌉ halvings beyond the share.** -/
theorem balancedPiece_depth_le (share : Share) (k i : ℕ) :
    (balancedPiece share k i).depth ≤ share.depth + Nat.clog 2 k :=
  (shareAt_depth_le share _).trans (Nat.add_le_add_left (balancedPath_length k i) _)

/-- **A balanced part has at most `2⌈log₂ k⌉` nodes more than the share.** -/
theorem balancedPiece_size_le (share : Share) (k i : ℕ) :
    (balancedPiece share k i).size ≤ share.size + 2 * Nat.clog 2 k :=
  (shareAt_size share _).trans (by have := balancedPath_length k i; omega)

/-- A balanced part of a dyadic interval is the dyadic interval one balanced path further. -/
theorem balancedPiece_interval (path : List Bool) (k i : ℕ) :
    balancedPiece (Share.interval path) k i = Share.interval (path ++ balancedPath k i) :=
  shareAt_interval path _

/-- **The last linear part of a dyadic interval lies `k` halvings down**, along the right halves. -/
theorem linear_last_piece (path : List Bool) (k : ℕ) :
    Share.piece (Share.interval path) (k + 1) k = Share.interval (path ++ List.replicate k true) := by
  induction k generalizing path with
  | zero => simp [Share.piece]
  | succ k ih =>
      rw [show Share.piece (Share.interval path) (k + 2) (k + 1) =
          Share.piece (Share.split (Share.interval path)).2 (k + 1) k from rfl,
        Share.split_interval, ih]
      simp [List.replicate_succ]

/-- **A wide fork in one word.**  A 64-bit word holds a dyadic interval at most 62 halvings deep.
Forking the whole interval into 640 parts, the last linear part is an interval 639 halvings deep,
while every balanced part is an interval at most 10 halvings deep. -/
theorem wide_fork_word :
    Share.piece .all 640 639 = Share.interval (List.replicate 639 true) ∧
      62 < (Share.piece .all 640 639).depth ∧
      ∀ i < 640, ∃ path : List Bool, balancedPiece .all 640 i = Share.interval path ∧
        path.length ≤ 10 := by
  have linear : Share.piece .all 640 639 = Share.interval (List.replicate 639 true) := by
    have last := linear_last_piece [] 639
    rw [Share.interval_nil, List.nil_append] at last
    exact last
  have balanced : ∀ i, balancedPiece .all 640 i = Share.interval (balancedPath 640 i) := by
    intro i
    have part := balancedPiece_interval [] 640 i
    rw [Share.interval_nil, List.nil_append] at part
    exact part
  refine ⟨linear, by rw [linear, Share.depth_interval, List.length_replicate]; omega,
    fun i _ => ⟨balancedPath 640 i, balanced i, ?_⟩⟩
  exact (balancedPath_length 640 i).trans (Nat.clog_le_of_le_pow (by decide))

end Mettapedia.Machines.NameSupplies
