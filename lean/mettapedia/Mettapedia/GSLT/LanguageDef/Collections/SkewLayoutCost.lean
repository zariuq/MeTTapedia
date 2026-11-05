import Mettapedia.GSLT.LanguageDef.Collections.SkewLayout
import Mettapedia.Machines.SharedPrependCost
import Mathlib.Data.Nat.Log

/-!
# The cost model of the skew layout

Each operation of `SkewLayout` is replayed with a count of its steps, and the
replay returns exactly the operation's result (`settleCounted_fst`,
`consCounted_fst`, `Body.nthCounted_fst`). A step is one element written into
a new array, one tree linked into the forest, one delta allocated or read, or
one node visited. These are theorems of a cost model, not measured running
times.

* **Prepend is constant in the worst case**: on every value satisfying the
  shape invariants, a prepend takes at most
  `prependBound P = 2 small + 2 block + 3 deltas + 2` steps (`consCost_le`).
  Values are immutable, so this holds for every prepend onto a shared value,
  however many holders prepend onto it.
* **Lookup is logarithmic**: indexing a valid value of `n` explicit elements
  takes at most `deltas + 2 log₂ (n + 1) + 2` steps (`nthCost_le`). The
  forest of a valid value has at most `log₂ (b + 1) + 1` trees of rank below
  `log₂ (b + 1)` when it holds `b` blocks (`length_le_log`, `rank_lt_log`).
* **Shared prepends cost a linear total.** Two prepends onto the accumulator
  at every step, as in `Machines.SharedPrependCost`, cost at most
  `2 · prependBound P · n` steps in all (`sharedSkew_total`), while a flat
  array with front slack pays `n (n + 3) / 2`
  (`Machines.SharedPrependCost.sharedFlat_total`): past
  `n = 4 c · prependBound P` the flat array pays more than `c` times as much,
  for every `c` (`flat_exceeds_skew`). Both carry the same lists
  (`sharedSkew_elements`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.SkewLayout

universe u

variable {A : Type u}

/-! ## Settling a front -/

section Settle

variable (P : Params)

/-- `settleWith` with the number of trees it links. -/
def settleCounted : ℕ → List A → Forest A P.block → (List A × Forest A P.block) × ℕ
  | 0, front, forest => ((front, forest), 0)
  | fuel + 1, front, forest =>
      if enough : P.block ≤ front.length then
        let rest := settleCounted fuel (front.take (front.length - P.block))
          (Forest.link (lastBlock P front enough) forest)
        (rest.1, rest.2 + 1)
      else ((front, forest), 0)

theorem settleCounted_fst : ∀ (fuel : ℕ) (front : List A) (forest : Forest A P.block),
    (settleCounted P fuel front forest).1 = settleWith P fuel front forest
  | 0, _, _ => rfl
  | fuel + 1, front, forest => by
      simp only [settleCounted, settleWith]
      split
      · exact settleCounted_fst fuel _ _
      · rfl

/-- One link per full block of the front. -/
theorem settleCounted_snd : ∀ (fuel : ℕ) (front : List A) (forest : Forest A P.block),
    front.length ≤ fuel → (settleCounted P fuel front forest).2 = front.length / P.block
  | 0, front, forest, bounded => by
      have empty : front.length = 0 := by omega
      simp [settleCounted, empty]
  | fuel + 1, front, forest, bounded => by
      simp only [settleCounted]
      split
      · next enough =>
          have positive := P.block_pos
          rw [settleCounted_snd fuel _ _ (by simp only [List.length_take]; omega)]
          simp only [List.length_take, Nat.min_eq_left (Nat.sub_le _ _)]
          exact (Nat.div_eq_sub_div positive enough).symm
      · next short => exact (Nat.div_eq_of_lt (Nat.lt_of_not_le short)).symm

end Settle

/-! ## Prepend -/

section Prepend

variable (P : Params)

/-- `fold` with its steps: one per delta read, one per element written into
the settled front and blocks, one per link. -/
def foldCounted : List A → Body A P.block → Body A P.block × ℕ
  | ys, .small xs =>
      let settled := settleCounted P (ys ++ xs).length (ys ++ xs) []
      (.packed settled.1.1 settled.1.2, (ys ++ xs).length + settled.2)
  | ys, .packed front forest =>
      let settled := settleCounted P (ys ++ front).length (ys ++ front) forest
      (.packed settled.1.1 settled.1.2, (ys ++ front).length + settled.2)
  | ys, .delta x rest =>
      let folded := foldCounted (ys ++ [x]) rest
      (folded.1, folded.2 + 1)

/-- `cons` with its steps: a small prepend copies the array, a delta is one
step, and a fold is counted by `foldCounted`. -/
def consCounted (x : A) : Body A P.block → Body A P.block × ℕ
  | .small xs =>
      if xs.length < P.small then (.small (x :: xs), xs.length + 1) else foldCounted P [x] (.small xs)
  | .packed front forest =>
      if (Body.packed front forest : Body A P.block).depth < P.deltas then
        (.delta x (.packed front forest), 1)
      else foldCounted P [x] (.packed front forest)
  | .delta y rest =>
      if (Body.delta y rest).depth < P.deltas then (.delta x (.delta y rest), 1)
      else foldCounted P [x] (.delta y rest)

theorem foldCounted_fst : ∀ (ys : List A) (body : Body A P.block),
    (foldCounted P ys body).1 = fold P ys body
  | ys, .small xs => by simp [foldCounted, fold, settle, settleCounted_fst]
  | ys, .packed front forest => by simp [foldCounted, fold, settle, settleCounted_fst]
  | ys, .delta x rest => by
      simp only [foldCounted, fold]
      exact foldCounted_fst (ys ++ [x]) rest

theorem consCounted_fst (x : A) (body : Body A P.block) : (consCounted P x body).1 = cons P x body := by
  cases body with
  | small xs =>
      simp only [consCounted, cons]
      split
      · rfl
      · exact foldCounted_fst P _ _
  | packed front forest =>
      simp only [consCounted, cons]
      split
      · rfl
      · exact foldCounted_fst P _ _
  | delta y rest =>
      simp only [consCounted, cons]
      split
      · rfl
      · exact foldCounted_fst P _ _

/-- A fold writes at most twice the elements it settles. -/
theorem settled_steps (front : List A) (forest : Forest A P.block) :
    front.length + (settleCounted P front.length front forest).2 ≤ 2 * front.length := by
  rw [settleCounted_snd P _ _ _ (Nat.le_refl _)]
  have := Nat.div_le_self front.length P.block
  omega

/-- A fold over a valid long value reads its deltas and settles at most the
folded elements, the deltas and a short front. -/
theorem foldCost_le : ∀ (ys : List A) (body : Body A P.block), body.IsLong → Valid P body →
    (foldCounted P ys body).2 ≤ body.depth + 2 * (ys.length + body.depth + P.block)
  | _, .small _, long, _ => long.elim
  | ys, .packed front forest, _, ⟨short, _⟩ => by
      have steps := settled_steps P (ys ++ front) forest
      simp only [foldCounted, Body.depth, List.length_append] at steps ⊢
      omega
  | ys, .delta x rest, _, ⟨_, long, valid⟩ => by
      have steps := foldCost_le (ys ++ [x]) rest long valid
      simp only [foldCounted, Body.depth, List.length_append, List.length_singleton] at steps ⊢
      omega

/-- The constant that bounds every prepend. -/
def prependBound : ℕ := 2 * P.small + 2 * P.block + 3 * P.deltas + 2

theorem depth_le_of_valid : ∀ body : Body A P.block, Valid P body → body.depth ≤ P.deltas
  | .small _, _ => Nat.zero_le _
  | .packed _ _, _ => Nat.zero_le _
  | .delta _ rest, ⟨room, _, _⟩ => by simp only [Body.depth]; omega

/-- **Prepend is constant in the worst case.** -/
theorem consCost_le (x : A) (body : Body A P.block) (valid : Valid P body) :
    (consCounted P x body).2 ≤ prependBound P := by
  unfold prependBound
  cases body with
  | small xs =>
      simp only [consCounted]
      split
      · next room => omega
      · have steps := settled_steps P ([x] ++ xs) []
        have bounded : xs.length ≤ P.small := valid
        simp only [foldCounted, List.length_append, List.length_singleton] at steps ⊢
        omega
  | packed front forest =>
      simp only [consCounted]
      split
      · omega
      · next full =>
          have noDeltas : P.deltas = 0 := by simp only [Body.depth] at full; omega
          have steps := foldCost_le P [x] (.packed front forest) trivial valid
          simp only [Body.depth, List.length_singleton] at steps
          omega
  | delta y rest =>
      simp only [consCounted]
      split
      · omega
      · next full =>
          have deep := depth_le_of_valid P (.delta y rest) valid
          have steps := foldCost_le P [x] (.delta y rest) trivial valid
          simp only [List.length_singleton] at steps
          omega

end Prepend

/-! ## Lookup -/

section Lookup

variable {n : ℕ}

/-- `Tree.get?` with the nodes it visits. -/
def Tree.getCounted : {r : ℕ} → Tree A n r → ℕ → Option A × ℕ
  | _, .leaf b, i => (b.val[i]?, 1)
  | _, .node (r := r) b left right, i =>
      if i < n then (b.val[i]?, 1)
      else if i - n < n * treeBlocks r then
        let found := left.getCounted (i - n)
        (found.1, found.2 + 1)
      else
        let found := right.getCounted (i - n - n * treeBlocks r)
        (found.1, found.2 + 1)

theorem Tree.getCounted_fst : ∀ {r : ℕ} (t : Tree A n r) (i : ℕ), (t.getCounted i).1 = t.get? i
  | _, .leaf _, _ => rfl
  | _, .node (r := r) b left right, i => by
      simp only [getCounted, get?]
      split
      · rfl
      · split
        · exact getCounted_fst left _
        · exact getCounted_fst right _

/-- A descent visits one node per rank. -/
theorem Tree.getCounted_snd : ∀ {r : ℕ} (t : Tree A n r) (i : ℕ), (t.getCounted i).2 ≤ r + 1
  | _, .leaf _, _ => le_rfl
  | _, .node (r := r) b left right, i => by
      simp only [getCounted]
      split
      · omega
      · split
        · have := getCounted_snd left (i - n); omega
        · have := getCounted_snd right (i - n - n * treeBlocks r); omega

/-- The largest rank of a forest. -/
def Forest.maxRank (forest : Forest A n) : ℕ := forest.ranks.foldr max 0

/-- `Forest.get?` with the trees it passes and the nodes it visits. -/
def Forest.getCounted : Forest A n → ℕ → Option A × ℕ
  | [], _ => (none, 1)
  | ⟨r, t⟩ :: forest, i =>
      if i < n * treeBlocks r then
        let found := t.getCounted i
        (found.1, found.2 + 1)
      else
        let found := Forest.getCounted forest (i - n * treeBlocks r)
        (found.1, found.2 + 1)

theorem Forest.getCounted_fst : ∀ (forest : Forest A n) (i : ℕ),
    (Forest.getCounted forest i).1 = forest.get? i
  | [], _ => rfl
  | ⟨r, t⟩ :: forest, i => by
      simp only [getCounted, get?]
      split
      · exact Tree.getCounted_fst t i
      · exact getCounted_fst forest _

theorem le_foldr_max {ranks : List ℕ} {r : ℕ} (member : r ∈ ranks) : r ≤ ranks.foldr max 0 := by
  induction ranks with
  | nil => cases member
  | cons s rest ih =>
      rcases List.mem_cons.mp member with rfl | later
      · exact le_max_left _ _
      · exact (ih later).trans (le_max_right _ _)

theorem rank_le_maxRank {forest : Forest A n} {r : ℕ} (member : r ∈ forest.ranks) :
    r ≤ Forest.maxRank forest :=
  le_foldr_max member

theorem maxRank_cons (r : ℕ) (t : Tree A n r) (forest : Forest A n) :
    Forest.maxRank (⟨r, t⟩ :: forest) = max r (Forest.maxRank forest) := rfl

/-- Lookup passes each tree once and descends one of them. -/
theorem Forest.getCounted_snd : ∀ (forest : Forest A n) (i : ℕ),
    (Forest.getCounted forest i).2 ≤ forest.length + Forest.maxRank forest + 1
  | [], _ => le_rfl
  | ⟨r, t⟩ :: forest, i => by
      rw [maxRank_cons]
      simp only [getCounted, List.length_cons]
      split
      · have := Tree.getCounted_snd t i
        have := le_max_left r (Forest.maxRank forest)
        omega
      · have := getCounted_snd forest (i - n * treeBlocks r)
        have := le_max_right r (Forest.maxRank forest)
        omega

/-- A strictly increasing list of ranks has at most one more entry than its
largest rank. -/
theorem length_le_of_increasing {ranks : List ℕ} (increasing : ranks.Pairwise (· < ·)) (bound : ℕ)
    (below : ∀ r ∈ ranks, r ≤ bound) : ranks.length ≤ bound + 1 := by
  have nodup : ranks.Nodup := increasing.imp (fun h => Nat.ne_of_lt h)
  have subset : ranks.toFinset ⊆ Finset.range (bound + 1) := by
    intro r member
    simp only [List.mem_toFinset] at member
    simpa [Finset.mem_range] using Nat.lt_succ_of_le (below r member)
  calc ranks.length = ranks.toFinset.card := (List.toFinset_card_of_nodup nodup).symm
    _ ≤ (Finset.range (bound + 1)).card := Finset.card_le_card subset
    _ = bound + 1 := Finset.card_range _

/-- **A skew forest has at most two more trees than its largest rank.** -/
theorem length_le_maxRank (forest : Forest A n) (skew : SkewRanks forest.ranks) :
    forest.length ≤ Forest.maxRank forest + 2 := by
  match forest, skew with
  | [], _ => simp
  | [_], _ => simp
  | ⟨r₁, t₁⟩ :: ⟨r₂, t₂⟩ :: rest, ⟨_, increasing⟩ =>
      have bounded := length_le_of_increasing increasing (Forest.maxRank (⟨r₁, t₁⟩ :: ⟨r₂, t₂⟩ :: rest))
        (fun r member => rank_le_maxRank (forest := ⟨r₁, t₁⟩ :: ⟨r₂, t₂⟩ :: rest)
          (List.mem_cons_of_mem _ member))
      simp only [List.length_cons, List.length_map] at bounded ⊢
      omega

/-- **Every rank of a forest is below `log₂ (b + 1)`** for its `b` blocks. -/
theorem rank_lt_log (forest : Forest A n) {r : ℕ} (member : r ∈ forest.ranks) :
    r + 1 ≤ Nat.log 2 (forest.blocks + 1) := by
  apply Nat.le_log_of_pow_le (by norm_num)
  rw [← treeBlocks_add_one]
  have within : treeBlocks r ≤ forest.blocks := by
    unfold Forest.blocks
    exact List.le_sum_of_mem (List.mem_map_of_mem member)
  omega

/-- The largest entry of a nonempty list of ranks is one of them. -/
theorem foldr_max_mem : ∀ {ranks : List ℕ}, ranks ≠ [] → ranks.foldr max 0 ∈ ranks
  | [], nonempty => (nonempty rfl).elim
  | [s], _ => by simp
  | s :: s' :: later, _ => by
      have inner := foldr_max_mem (ranks := s' :: later) (by simp)
      simp only [List.foldr_cons] at inner ⊢
      rcases le_total s (max s' (later.foldr max 0)) with below | above
      · rw [max_eq_right below]
        exact List.mem_cons_of_mem _ inner
      · rw [max_eq_left above]
        exact List.mem_cons_self

/-- The largest rank of a nonempty forest is below `log₂ (b + 1)`. -/
theorem maxRank_lt_log (forest : Forest A n) (nonempty : forest ≠ []) :
    Forest.maxRank forest + 1 ≤ Nat.log 2 (forest.blocks + 1) :=
  rank_lt_log forest (foldr_max_mem (by simpa [Forest.ranks] using nonempty))

/-- **A skew forest of `b` blocks has at most `log₂ (b + 1) + 1` trees.** -/
theorem length_le_log (forest : Forest A n) (skew : SkewRanks forest.ranks) :
    forest.length ≤ Nat.log 2 (forest.blocks + 1) + 1 := by
  by_cases empty : forest = []
  · subst empty
    simp
  · have := maxRank_lt_log forest empty
    have := length_le_maxRank forest skew
    omega

/-- **Forest lookup is logarithmic.** -/
theorem Forest.getCounted_le_log (forest : Forest A n) (skew : SkewRanks forest.ranks) (i : ℕ) :
    (Forest.getCounted forest i).2 ≤ 2 * Nat.log 2 (forest.blocks + 1) + 1 := by
  have steps := Forest.getCounted_snd forest i
  by_cases empty : forest = []
  · subst empty
    simp only [Forest.maxRank, Forest.ranks, List.length_nil, List.map_nil, List.foldr_nil] at steps
    omega
  · have top := maxRank_lt_log forest empty
    have count := length_le_maxRank forest skew
    omega

/-- `Body.nth` with its steps. -/
def Body.nthCounted : Body A n → ℕ → Option A × ℕ
  | .small xs, i => (xs[i]?, 1)
  | .packed front forest, i =>
      if i < front.length then (front[i]?, 1)
      else
        let found := Forest.getCounted forest (i - front.length)
        (found.1, found.2 + 1)
  | .delta x _, 0 => (some x, 1)
  | .delta _ rest, i + 1 =>
      let found := rest.nthCounted i
      (found.1, found.2 + 1)

theorem Body.nthCounted_fst : ∀ (body : Body A n) (i : ℕ), (body.nthCounted i).1 = body.nth i
  | .small _, _ => rfl
  | .packed front forest, i => by
      simp only [nthCounted, nth]
      split
      · rfl
      · exact Forest.getCounted_fst forest _
  | .delta _ _, 0 => rfl
  | .delta _ rest, i + 1 => nthCounted_fst rest i

end Lookup

section LookupBound

variable (P : Params)

theorem blocks_le_knownLength (front : List A) (forest : Forest A P.block) :
    forest.blocks ≤ (Body.packed front forest).knownLength := by
  simp only [Body.knownLength]
  have := Nat.le_mul_of_pos_left forest.blocks P.block_pos
  omega

theorem nthCost_le_depth : ∀ (body : Body A P.block), Valid P body → ∀ i,
    (body.nthCounted i).2 ≤ body.depth + 2 * Nat.log 2 (body.knownLength + 1) + 2
  | .small _, _, _ => by simp [Body.nthCounted]
  | .packed front forest, ⟨_, skew⟩, i => by
      simp only [Body.nthCounted, Body.depth]
      split
      · omega
      · have steps := Forest.getCounted_le_log forest skew (i - front.length)
        have grows := Nat.log_mono_right (b := 2)
          (Nat.add_le_add_right (blocks_le_knownLength P front forest) 1)
        omega
  | .delta _ _, _, 0 => by simp [Body.nthCounted]
  | .delta x rest, ⟨_, _, valid⟩, i + 1 => by
      have steps := nthCost_le_depth rest valid i
      have grows := Nat.log_mono_right (b := 2)
        (show rest.knownLength + 1 ≤ (Body.delta x rest : Body A P.block).knownLength + 1 by
          simp [Body.knownLength])
      simp only [Body.nthCounted, Body.depth]
      omega

/-- **Lookup is logarithmic in the worst case**: `deltas + 2 log₂ (n + 1) + 2`
steps for a valid value of `n` explicit elements. -/
theorem nthCost_le (body : Body A P.block) (valid : Valid P body) (i : ℕ) :
    (body.nthCounted i).2 ≤ P.deltas + 2 * Nat.log 2 (body.knownLength + 1) + 2 := by
  have := nthCost_le_depth P body valid i
  have := depth_le_of_valid P body valid
  omega

end LookupBound

/-! ## Shared prepends -/

section Shared

open Mettapedia.Machines.SharedPrependCost (sharedFlat sharedChunked sharedFlat_total sharedChunked_total)

variable (P : Params)

/-- Two prepends at every step onto one accumulator: the accumulator continues
with the first, and another holder keeps the second (as in
`Machines.SharedPrependCost.sharedFlat`). The final accumulator and the steps
in all. -/
def sharedSkew : ℕ → Body ℕ P.block × ℕ
  | 0 => (.small [], 0)
  | k + 1 =>
      let previous := sharedSkew k
      ((consCounted P k previous.1).1,
        previous.2 + (consCounted P k previous.1).2 + (consCounted P 0 previous.1).2)

theorem sharedSkew_valid : ∀ k, Valid P (sharedSkew P k).1
  | 0 => valid_empty P
  | k + 1 => by
      simp only [sharedSkew, consCounted_fst]
      exact valid_cons P k _ (sharedSkew_valid k)

/-- The accumulator is the same list as in the other layouts. -/
theorem sharedSkew_elements : ∀ k, (sharedSkew P k).1.elements = (sharedChunked k).1
  | 0 => rfl
  | k + 1 => by
      simp only [sharedSkew, consCounted_fst, Body.elements_cons, sharedChunked,
        Mettapedia.Machines.SharedPrependCost.chunkedPrepend]
      rw [sharedSkew_elements k]

/-- **Shared prepends cost a linear total.** -/
theorem sharedSkew_total : ∀ k, (sharedSkew P k).2 ≤ 2 * prependBound P * k
  | 0 => le_refl _
  | k + 1 => by
      have previous := sharedSkew_total k
      have valid := sharedSkew_valid P k
      have first := consCost_le P k _ valid
      have second := consCost_le P 0 _ valid
      simp only [sharedSkew]
      rw [Nat.mul_succ]
      omega

/-- **The flat array's cliff**: past `n = 4 c · prependBound P`, two prepends
per step onto one accumulator cost the flat array with front slack more than
`c` times what they cost the skew layout, for every `c`. -/
theorem flat_exceeds_skew (c n : ℕ) (large : 4 * c * prependBound P < n) :
    c * (sharedSkew P n).2 < (sharedFlat n).2 := by
  have skewTotal := sharedSkew_total P n
  have flatTotal := sharedFlat_total n
  have scaled : c * (sharedSkew P n).2 ≤ c * (2 * prependBound P * n) := Nat.mul_le_mul_left c skewTotal
  have square : 4 * c * prependBound P * n < n * n := Nat.mul_lt_mul_of_pos_right large (by omega)
  have : 2 * (c * (2 * prependBound P * n)) = 4 * c * prependBound P * n := by ring
  nlinarith

end Shared

end Mettapedia.GSLT.LanguageDef.Collections.SkewLayout
