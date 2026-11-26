import Mettapedia.Machines.NameSupplies.BalancedPieces
import Mathlib.Tactic

/-!
# Pushing siblings one at a time

A task that pushes children one at a time does not know how many it will push.  A splitter whose
part `i` does not depend on the number of parts can hand its parts out one push at a time
(`Splitter.CountOblivious`).

* **Halving** (`halvingChild`): the pusher keeps the left half and hands the right half on.  The
  `n`-th child of the whole interval is an interval `n + 1` halvings deep (`halvingChild_whole`), so
  62 pushes fill a word (`halving_pushes_word`).
* **Counted pushes** (`countedChild`): the pusher counts its pushes, and push `n` takes the part at
  `countedPath n`: `j = ⌊log₂(n+1)⌋` right halvings, one left halving into the block of `2^j`
  pushes, then the balanced path of `n + 1 - 2^j` among them.  The children are normal, nonempty,
  pairwise disjoint parts of the pool (`countedChildren_disjoint`), so counted pushes are a
  count-oblivious splitter whose names stay exact (`countedSplitter`, `counted_exact`).  Push `n`
  lies at most `2⌊log₂(n+1)⌋ + 1` halvings down (`countedChild_depth_le`): a million siblings of the
  whole interval fit in 39 halvings (`million_pushes_word`).
* **No count, no balance** (`count_oblivious_unbalanced`): no count-oblivious splitter keeps every
  part `i` within `⌈log₂(i+1)⌉ + c` halvings, for any constant `c`.  Pairwise disjoint shares have
  measures summing to at most one (`kraft`), a share `d` halvings deep has measure at least `2⁻ᵈ`
  (`Share.measure_ge_depth`), and the bound would make the first `2^M` measures sum to at least
  `2⁻ᶜ(1 + M/2)` (`no_balanced_pushes`).  So the `⌈log₂ k⌉` of a balanced fork needs the count `k`
  in advance; counted pushes are within a factor of two of it without the count.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.NameSupplies

/-! ## Halving pushes -/

/-- The share a pusher keeps after `n` pushes that each keep the left half. -/
def halvingKept (share : Share) : ℕ → Share
  | 0 => share
  | n + 1 => (Share.split (halvingKept share n)).1

/-- The share of the child of push number `n`: the right half of what the pusher kept. -/
def halvingChild (share : Share) (n : ℕ) : Share := (Share.split (halvingKept share n)).2

theorem halvingKept_whole (n : ℕ) :
    halvingKept .all n = Share.interval (List.replicate n false) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [halvingKept, ih, Share.split_interval, List.replicate_succ']

/-- **The `n`-th halving push from the whole interval lies `n + 1` halvings down.** -/
theorem halvingChild_whole (n : ℕ) :
    halvingChild .all n = Share.interval (List.replicate n false ++ [true]) := by
  rw [halvingChild, halvingKept_whole, Share.split_interval]

/-- **Halving pushes fill a word after 62 pushes.** -/
theorem halving_pushes_word : 62 < (halvingChild .all 62).depth := by
  rw [halvingChild_whole, Share.depth_interval]
  simp

/-! ## Counted pushes -/

/-- The block of push number `n`: `⌊log₂(n+1)⌋`. -/
def pushBlock (n : ℕ) : ℕ := Nat.log 2 (n + 1)

/-- The path of push number `n`: right halvings to its block, a left halving into it, and the
balanced path of its offset among the block's `2^j` pushes. -/
def countedPath (n : ℕ) : List Bool :=
  List.replicate (pushBlock n) true ++
    false :: balancedPath (2 ^ pushBlock n) (n + 1 - 2 ^ pushBlock n)

/-- **The share of push number `n` from a pool.** -/
def countedChild (pool : Share) (n : ℕ) : Share := shareAt pool (countedPath n)

theorem pushBlock_bounds (n : ℕ) : 2 ^ pushBlock n ≤ n + 1 ∧ n + 1 < 2 ^ (pushBlock n + 1) :=
  ⟨Nat.pow_log_le_self 2 (by omega), Nat.lt_pow_succ_log_self (by omega) _⟩

theorem countedPath_length (n : ℕ) : (countedPath n).length ≤ 2 * pushBlock n + 1 := by
  have balanced := balancedPath_length (2 ^ pushBlock n) (n + 1 - 2 ^ pushBlock n)
  rw [Nat.clog_pow 2 _ (by omega)] at balanced
  simp only [countedPath, List.length_append, List.length_replicate, List.length_cons]
  omega

private theorem countedChild_in_block (pool : Share) (n : ℕ) :
    countedChild pool n =
      balancedPiece (shareAt pool (List.replicate (pushBlock n) true ++ [false]))
        (2 ^ pushBlock n) (n + 1 - 2 ^ pushBlock n) := by
  rw [countedChild, countedPath, balancedPiece, ← shareAt_append]
  simp

private theorem replicate_split {j j' : ℕ} (below : j < j') :
    List.replicate j' true = List.replicate j true ++ true :: List.replicate (j' - j - 1) true := by
  rw [show j' = j + (1 + (j' - j - 1)) by omega, List.replicate_add, List.replicate_add]
  simp

/-- **Distinct pushes take disjoint parts.** -/
theorem countedChildren_disjoint (pool : Share) {m n : ℕ} (distinct : m ≠ n) :
    ¬ (countedChild pool m).Overlap (countedChild pool n) := by
  obtain ⟨mLow, mHigh⟩ := pushBlock_bounds m
  obtain ⟨nLow, nHigh⟩ := pushBlock_bounds n
  rcases lt_trichotomy (pushBlock m) (pushBlock n) with before | same | after
  · rw [countedChild, countedChild, countedPath, countedPath, replicate_split before,
      List.append_assoc, List.cons_append]
    exact shareAt_diverge pool _ _ _
  · rw [countedChild_in_block, countedChild_in_block, same]
    rw [pow_succ] at mHigh nHigh
    exact balancedPieces_disjoint _ (by rw [same] at mLow mHigh; omega)
      (by omega) (by rw [same] at mLow mHigh; omega)
  · intro overlap
    rw [countedChild, countedChild, countedPath, countedPath, replicate_split after,
      List.append_assoc, List.cons_append] at overlap
    exact shareAt_diverge pool _ _ _ overlap.symm

/-- **Push `n` lies at most `2⌊log₂(n+1)⌋ + 1` halvings below the pool.** -/
theorem countedChild_depth_le (pool : Share) (n : ℕ) :
    (countedChild pool n).depth ≤ pool.depth + 2 * Nat.log 2 (n + 1) + 1 := by
  have := shareAt_depth_le pool (countedPath n)
  have := countedPath_length n
  simp only [countedChild, pushBlock] at *
  omega

/-- **Counted pushes as a splitter**: part `i` is push `i`, whatever the number of parts. -/
def countedSplitter : Splitter where
  piece share _ i := countedChild share i
  piece_normal normal nonempty _ _ := shareAt_normal normal nonempty _
  piece_owns inside := shareAt_owns inside
  pieces_disjoint share _ _ _ _ _ distinct := countedChildren_disjoint share distinct

/-- **Counted pushes keep names exact.** -/
theorem counted_exact (pool : Pool ShareSupply ShareName) (shared : WellShared pool) :
    Exact (splitDiscipline countedSplitter) pool :=
  shares_exact_with countedSplitter pool shared

/-- **A million counted pushes from the whole interval fit in one word**: each is a dyadic interval
at most 39 halvings deep (a word holds 62). -/
theorem million_pushes_word (n : ℕ) (below : n < 10 ^ 6) :
    ∃ path : List Bool, countedChild .all n = Share.interval path ∧ path.length ≤ 39 := by
  refine ⟨countedPath n, ?_, ?_⟩
  · have part := shareAt_interval [] (countedPath n)
    rw [Share.interval_nil, List.nil_append] at part
    exact part
  · have block : pushBlock n < 20 :=
      (Nat.log_lt_iff_lt_pow (by omega) (by omega)).mpr (by
        have : (10 : ℕ) ^ 6 < 2 ^ 20 := by decide
        omega)
    have := countedPath_length n
    omega

/-! ## Without the count, no balance -/

/-- A splitter is count-oblivious when part `i` does not depend on the number of parts, so its parts
can be handed out one push at a time. -/
def Splitter.CountOblivious (splitter : Splitter) : Prop :=
  ∀ share k k' i, splitter.piece share k i = splitter.piece share k' i

theorem countedSplitter_countOblivious : countedSplitter.CountOblivious :=
  fun _ _ _ _ => rfl

/-- Control: the balanced splitter needs the count. -/
theorem balancedSplitter_not_countOblivious : ¬ balancedSplitter.CountOblivious := by
  intro oblivious
  have := oblivious .all 1 2 0
  simp [balancedSplitter, balancedPiece, balancedPath_small, balancedPath_left, shareAt,
    Share.split] at this

namespace Share

/-- The measure of a share: the length of the part of the unit interval it owns. -/
def measure : Share → ℚ
  | none => 0
  | all => 1
  | node left right => (left.measure + right.measure) / 2

theorem measure_nonneg (share : Share) : 0 ≤ share.measure := by
  induction share with
  | none => simp [measure]
  | all => simp [measure]
  | node left right ihLeft ihRight => simp only [measure]; positivity

theorem measure_le_one (share : Share) : share.measure ≤ 1 := by
  induction share with
  | none => simp [measure]
  | all => simp [measure]
  | node left right ihLeft ihRight => simp only [measure]; linarith

theorem measure_eq_zero {share : Share} (empty : ∀ point, ¬ share.Owns point) :
    share.measure = 0 := by
  induction share with
  | none => rfl
  | all => exact absurd trivial (empty fun _ => false)
  | node left right ihLeft ihRight =>
      have leftEmpty : ∀ point, ¬ left.Owns point :=
        fun point owned => empty (push false point) (by simpa [Owns] using owned)
      have rightEmpty : ∀ point, ¬ right.Owns point :=
        fun point owned => empty (push true point) (by simpa [Owns] using owned)
      simp [measure, ihLeft leftEmpty, ihRight rightEmpty]

theorem measure_node' (left right : Share) :
    (node' left right).measure = (node left right).measure := by
  cases left <;> cases right <;> simp [node', measure]

/-- **The measure of a join of disjoint shares is the sum of their measures.** -/
theorem measure_join {first second : Share} (disjoint : ¬ first.Overlap second) :
    (join first second).measure = first.measure + second.measure := by
  induction first generalizing second with
  | none => simp [join, measure]
  | all =>
      have empty : ∀ point, ¬ second.Owns point := fun point owned => disjoint ⟨point, trivial, owned⟩
      simp [measure, measure_eq_zero empty]
  | node left right ihLeft ihRight =>
      cases second with
      | none => simp [measure]
      | all =>
          have empty : ∀ point, ¬ (node left right).Owns point :=
            fun point owned => disjoint ⟨point, owned, trivial⟩
          rw [show join (node left right) all = all from rfl, measure_eq_zero empty]
          simp [measure]
      | node left' right' =>
          have leftApart : ¬ left.Overlap left' := fun ⟨point, l, l'⟩ =>
            disjoint ⟨push false point, by simpa [Owns] using l, by simpa [Owns] using l'⟩
          have rightApart : ¬ right.Overlap right' := fun ⟨point, r, r'⟩ =>
            disjoint ⟨push true point, by simpa [Owns] using r, by simpa [Owns] using r'⟩
          rw [show join (node left right) (node left' right') =
              node' (join left left') (join right right') from rfl, measure_node']
          simp only [measure, ihLeft leftApart, ihRight rightApart]
          ring

private theorem half_bound {d m : ℕ} {measure : ℚ} (le : d ≤ m) (bound : 1 / 2 ^ d ≤ measure) :
    (1 : ℚ) / 2 ^ (m + 1) ≤ measure / 2 := by
  have deeper : (1 : ℚ) / 2 ^ (m + 1) ≤ 1 / 2 ^ (d + 1) :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega))
  have halved : (1 : ℚ) / 2 ^ (d + 1) = (1 / 2 ^ d) / 2 := by rw [pow_succ]; field_simp
  linarith

/-- **A nonempty normal share `d` halvings deep has measure at least `2⁻ᵈ`.** -/
theorem measure_ge_depth {share : Share} (normal : share.Normal) (nonempty : share ≠ none) :
    1 / 2 ^ share.depth ≤ share.measure := by
  induction share with
  | none => exact absurd rfl nonempty
  | all => simp [measure, depth]
  | node left right ihLeft ihRight =>
      obtain ⟨normalLeft, normalRight, notBoth, -⟩ := normal
      simp only [depth, measure]
      by_cases leftNone : left = none
      · have rightNonempty : right ≠ none := fun same => notBoth ⟨leftNone, same⟩
        have := half_bound (le_max_right left.depth right.depth) (ihRight normalRight rightNonempty)
        have := measure_nonneg left
        linarith
      · have := half_bound (le_max_left left.depth right.depth) (ihLeft normalLeft leftNone)
        have := measure_nonneg right
        linarith

end Share

/-- The union of a list of shares. -/
def unionOf : List Share → Share
  | [] => .none
  | share :: rest => share.join (unionOf rest)

private theorem overlap_unionOf {share : Share} {shares : List Share}
    (overlap : share.Overlap (unionOf shares)) : ∃ other ∈ shares, share.Overlap other := by
  induction shares with
  | nil => obtain ⟨point, -, owned⟩ := overlap; exact absurd owned id
  | cons head rest ih =>
      rcases (Share.overlap_join head (unionOf rest) share).mp overlap.symm with here | later
      · exact ⟨head, List.mem_cons_self .., here.symm⟩
      · obtain ⟨other, member, apart⟩ := ih later.symm
        exact ⟨other, List.mem_cons_of_mem _ member, apart⟩

/-- **Kraft's inequality for shares**: pairwise disjoint shares have measures summing to at most
one. -/
theorem kraft (shares : List Share) (disjoint : shares.Pairwise fun a b => ¬ a.Overlap b) :
    (shares.map Share.measure).sum ≤ 1 := by
  have total : (unionOf shares).measure = (shares.map Share.measure).sum := by
    induction shares with
    | nil => rfl
    | cons head rest ih =>
        obtain ⟨headApart, restApart⟩ := List.pairwise_cons.mp disjoint
        have apart : ¬ head.Overlap (unionOf rest) := fun overlap =>
          let ⟨other, member, both⟩ := overlap_unionOf overlap
          headApart other member both
        simp [unionOf, Share.measure_join apart, ih restApart]
  rw [← total]
  exact Share.measure_le_one _

/-- The first `2^M` pushes weighted by `2^-⌈log₂(n+1)⌉` sum to at least `1 + M/2`. -/
theorem sum_clog_ge (M : ℕ) :
    1 + (M : ℚ) / 2 ≤ ∑ n ∈ Finset.range (2 ^ M), (1 : ℚ) / 2 ^ Nat.clog 2 (n + 1) := by
  induction M with
  | zero => simp
  | succ M ih =>
      rw [pow_succ, mul_two, Finset.sum_range_add]
      have block : ∀ x ∈ Finset.range (2 ^ M),
          (1 : ℚ) / 2 ^ (M + 1) ≤ 1 / 2 ^ Nat.clog 2 (2 ^ M + x + 1) := by
        intro x member
        rw [Finset.mem_range] at member
        refine one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) ?_)
        exact Nat.clog_le_of_le_pow (by rw [pow_succ]; omega)
      have later := Finset.sum_le_sum block
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at later
      push_cast at later
      have half : (2 ^ M : ℚ) * (1 / 2 ^ (M + 1)) = 1 / 2 := by
        rw [pow_succ]; field_simp
      push_cast
      linarith

/-- **No balance without the count**: no sequence of pairwise disjoint nonempty normal shares keeps
its `n`-th member within `⌈log₂(n+1)⌉ + c` halvings. -/
theorem no_balanced_pushes (c : ℕ) (pieces : ℕ → Share)
    (normal : ∀ n, (pieces n).Normal ∧ pieces n ≠ .none)
    (disjoint : ∀ m n, m ≠ n → ¬ (pieces m).Overlap (pieces n)) :
    ¬ ∀ n, (pieces n).depth ≤ Nat.clog 2 (n + 1) + c := by
  intro bounded
  let M := 2 ^ (c + 1)
  have total := kraft ((List.range (2 ^ M)).map pieces) (by
    rw [List.pairwise_map]
    exact (List.nodup_range).imp fun distinct => disjoint _ _ distinct)
  rw [List.map_map, ← List.sum_toFinset _ List.nodup_range, List.toFinset_range] at total
  have each : ∀ n ∈ Finset.range (2 ^ M),
      (1 : ℚ) / 2 ^ c * (1 / 2 ^ Nat.clog 2 (n + 1)) ≤ (Share.measure ∘ pieces) n := by
    intro n _
    have least := Share.measure_ge_depth (normal n).1 (normal n).2
    have : (1 : ℚ) / 2 ^ (Nat.clog 2 (n + 1) + c) ≤ 1 / 2 ^ (pieces n).depth :=
      one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (bounded n))
    calc (1 : ℚ) / 2 ^ c * (1 / 2 ^ Nat.clog 2 (n + 1))
        = 1 / 2 ^ (Nat.clog 2 (n + 1) + c) := by rw [pow_add]; field_simp
      _ ≤ (pieces n).measure := this.trans least
  have lower := Finset.sum_le_sum each
  rw [← Finset.mul_sum] at lower
  have harmonic := sum_clog_ge M
  have positive : (0 : ℚ) < 1 / 2 ^ c := by positivity
  have grown : (1 : ℚ) / 2 ^ c * (1 + (M : ℚ) / 2) = 1 / 2 ^ c + 1 := by
    have cast : (M : ℚ) = 2 ^ c * 2 := by simp only [M]; push_cast; ring
    rw [cast]
    field_simp
  have scaled := mul_le_mul_of_nonneg_left harmonic positive.le
  linarith

/-- **A count-oblivious splitter is not balanced**: some part `i` lies deeper than
`⌈log₂(i+1)⌉ + c` halvings, for every constant `c`. -/
theorem count_oblivious_unbalanced (splitter : Splitter) (oblivious : splitter.CountOblivious)
    (c : ℕ) : ¬ ∀ i, (splitter.piece .all (i + 1) i).depth ≤ Nat.clog 2 (i + 1) + c := by
  apply no_balanced_pushes c (fun i => splitter.piece .all (i + 1) i)
  · exact fun n => splitter.piece_normal (share := .all) trivial nofun _ _
  · intro m n distinct
    rw [oblivious .all (m + 1) (max m n + 1) m, oblivious .all (n + 1) (max m n + 1) n]
    exact splitter.pieces_disjoint .all (by omega) (by omega) distinct

end Mettapedia.Machines.NameSupplies
