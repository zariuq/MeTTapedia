import Mettapedia.InformationTheory.RelationStoreFloors

/-!
# Elias–Fano rows: sparse relations a few bits above the floor

A row of `N` identifiers below `B · 2 ^ L` splits each identifier into its
bucket, the high part `x / 2 ^ L`, and its low `L` bits.  The Elias–Fano store
keeps, for each of the `B` buckets, how many identifiers it holds, and the low
bits of every identifier, bucket by bucket.  Counts in unary and lows in `L`
bits each take `N · (L + 1) + B` bits.

* `efDecode_efEncode` : the store gives the row back exactly;
* `efBits_efEncode` : it takes `N · (L + 1) + B` bits, every low below `2 ^ L`;
* `efBits_le_and_floor` : with `2 ^ L · N ≤ M < 2 ^ (L + 1) · N` it takes at
  most `N · L + 3 · N` bits against a floor of at least
  `N · L - log₂ (M + 1)`: at most three bits an identifier above the floor.
-/

namespace Mettapedia.InformationTheory.RelationStoreFloors

open Finset

variable (L : ℕ)

/-- The identifiers of `s` in bucket `j`, in order. -/
noncomputable def efBlock (s : Finset ℕ) (j : ℕ) : List ℕ :=
  (s.filter fun x => x / 2 ^ L = j).sort (· ≤ ·)

/-- The Elias–Fano store of `s` over `B` buckets: each bucket's count, and the
low bits of every identifier, bucket by bucket. -/
noncomputable def efEncode (B : ℕ) (s : Finset ℕ) : List ℕ × List ℕ :=
  ((List.range B).map fun j => (efBlock L s j).length,
   (List.range B).flatMap fun j => (efBlock L s j).map fun x => x % 2 ^ L)

/-- Read the blocks back: bucket `j` takes the next `c` lows. -/
def efDecodeFrom : ℕ → List ℕ → List ℕ → List ℕ
  | _, [], _ => []
  | j, c :: cs, lows =>
      ((lows.take c).map fun l => j * 2 ^ L + l) ++ efDecodeFrom (j + 1) cs (lows.drop c)

/-- Read a store back as the row it holds. -/
def efDecode (code : List ℕ × List ℕ) : Finset ℕ :=
  (efDecodeFrom L 0 code.1 code.2).toFinset

/-- The store's size in bits: each count in unary and one terminator, and `L`
bits for each low. -/
def efBits (code : List ℕ × List ℕ) : ℕ :=
  (code.1.map fun c => c + 1).sum + code.2.length * L

/-- An identifier of bucket `j` is `j · 2 ^ L` plus its low bits. -/
theorem map_low_efBlock (s : Finset ℕ) (j : ℕ) :
    ((efBlock L s j).map fun x => x % 2 ^ L).map (fun l => j * 2 ^ L + l) =
      efBlock L s j := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id (efBlock L s j)]
  refine List.map_congr_left fun x hx => ?_
  have hj : x / 2 ^ L = j := by
    have := (Finset.mem_sort _).mp hx
    exact (mem_filter.mp this).2
  simp only [Function.comp, id]
  rw [← hj, mul_comm]
  exact Nat.div_add_mod x (2 ^ L)

/-- Reading the blocks of the buckets `j₀, …, j₀ + k - 1` back from their counts
and lows gives the blocks. -/
theorem efDecodeFrom_blocks (s : Finset ℕ) (k : ℕ) :
    ∀ (j₀ : ℕ) (rest : List ℕ),
      efDecodeFrom L j₀ ((List.range' j₀ k).map fun j => (efBlock L s j).length)
          (((List.range' j₀ k).flatMap fun j => (efBlock L s j).map fun x => x % 2 ^ L) ++
            rest) =
        (List.range' j₀ k).flatMap fun j => efBlock L s j := by
  induction k with
  | zero => intro j₀ rest; simp [efDecodeFrom]
  | succ k ih =>
    intro j₀ rest
    have hlen : ((efBlock L s j₀).map fun x => x % 2 ^ L).length =
        (efBlock L s j₀).length := List.length_map _
    simp only [List.range'_succ, List.map_cons, List.flatMap_cons, List.append_assoc,
      efDecodeFrom]
    rw [List.take_left' hlen, List.drop_left' hlen, map_low_efBlock, ih]

/-- The store gives the row back exactly, when every identifier lies below
`B · 2 ^ L`. -/
theorem efDecode_efEncode {B : ℕ} {s : Finset ℕ} (hs : ∀ x ∈ s, x < B * 2 ^ L) :
    efDecode L (efEncode L B s) = s := by
  have h := efDecodeFrom_blocks L s B 0 []
  rw [List.append_nil] at h
  unfold efDecode efEncode
  simp only [List.range_eq_range']
  rw [h]
  ext x
  simp only [List.mem_toFinset, List.mem_flatMap, List.mem_range'_1, efBlock,
    Finset.mem_sort, mem_filter]
  constructor
  · rintro ⟨j, _, hx, _⟩
    exact hx
  · intro hx
    refine ⟨x / 2 ^ L, ⟨Nat.zero_le _, ?_⟩, hx, rfl⟩
    rw [zero_add, Nat.div_lt_iff_lt_mul (pow_pos (by norm_num) L)]
    exact hs x hx

/-- Every low is below `2 ^ L`, so `L` bits hold it. -/
theorem lt_of_mem_efEncode_lows {B : ℕ} {s : Finset ℕ} {l : ℕ}
    (hl : l ∈ (efEncode L B s).2) : l < 2 ^ L := by
  simp only [efEncode, List.mem_flatMap, List.mem_map] at hl
  obtain ⟨_, _, x, _, rfl⟩ := hl
  exact Nat.mod_lt x (pow_pos (by norm_num) L)

/-- The blocks of the `B` buckets hold the row's identifiers once each. -/
theorem sum_length_efBlock {B : ℕ} {s : Finset ℕ} (hs : ∀ x ∈ s, x < B * 2 ^ L) :
    ((List.range B).map fun j => (efBlock L s j).length).sum = s.card := by
  have hblock : ∀ j, (efBlock L s j).length = (s.filter fun x => x / 2 ^ L = j).card :=
    fun j => Finset.length_sort _
  simp only [hblock]
  rw [← List.sum_toFinset _ (List.nodup_range), List.toFinset_range]
  rw [← Finset.card_biUnion]
  · congr 1
    ext x
    simp only [mem_biUnion, mem_range, mem_filter]
    constructor
    · rintro ⟨_, _, hx, _⟩
      exact hx
    · intro hx
      refine ⟨x / 2 ^ L, ?_, hx, rfl⟩
      rw [Nat.div_lt_iff_lt_mul (pow_pos (by norm_num) L)]
      exact hs x hx
  · intro i _ j _ hij
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro x hxi hxj
    exact hij ((mem_filter.mp hxi).2.symm.trans (mem_filter.mp hxj).2)

/-- The store of a row of `N` identifiers over `B` buckets takes
`N · (L + 1) + B` bits. -/
theorem efBits_efEncode {B : ℕ} {s : Finset ℕ} (hs : ∀ x ∈ s, x < B * 2 ^ L) :
    efBits L (efEncode L B s) = s.card * (L + 1) + B := by
  have hlows : (efEncode L B s).2.length = s.card := by
    simp only [efEncode, List.length_flatMap, List.length_map]
    exact sum_length_efBlock L hs
  have hcounts : ((efEncode L B s).1.map fun c => c + 1).sum = s.card + B := by
    simp only [efEncode, List.map_map, Function.comp_def]
    rw [List.sum_map_add, sum_length_efBlock L hs]
    simp
  unfold efBits
  rw [hcounts, hlows]
  ring

/-- Elias–Fano against the floor.  With `2 ^ L · N ≤ M < 2 ^ (L + 1) · N`, the
store of an `N`-element row of identifiers below `M` takes at most
`N · L + 3 · N` bits, while `2 ^ (N · L) ≤ (M + 1) · C(M, N)`: the floor is at
least `N · L - log₂ (M + 1)` bits, so the store is at most
`3 · N + log₂ (M + 1)` bits above it. -/
theorem efBits_le_and_floor {M N : ℕ} {s : Finset ℕ} (hs : ∀ x ∈ s, x < M)
    (hcard : s.card = N) (hlow : 2 ^ L * N ≤ M) (hhigh : M < 2 ^ (L + 1) * N) :
    efBits L (efEncode L (M / 2 ^ L + 1) s) ≤ N * L + 3 * N ∧
      2 ^ (N * L) ≤ (M + 1) * M.choose N := by
  have hpow : 0 < 2 ^ L := pow_pos (by norm_num) L
  have hs' : ∀ x ∈ s, x < (M / 2 ^ L + 1) * 2 ^ L := by
    intro x hx
    have := Nat.lt_mul_div_succ M hpow
    calc x < M := hs x hx
      _ < 2 ^ L * (M / 2 ^ L + 1) := this
      _ = (M / 2 ^ L + 1) * 2 ^ L := mul_comm _ _
  have hNM : N ≤ M := by
    rw [← hcard]
    calc s.card ≤ (range M).card :=
          card_le_card fun x hx => mem_range.mpr (hs x hx)
      _ = M := card_range M
  constructor
  · rw [efBits_efEncode L hs', hcard]
    have hbuckets : M / 2 ^ L < 2 * N := by
      rw [Nat.div_lt_iff_lt_mul hpow]
      calc M < 2 ^ (L + 1) * N := hhigh
        _ = 2 * N * 2 ^ L := by rw [pow_succ]; ring
    nlinarith
  · have hfloor := pow_le_succ_mul_choose_mul_pow (M := M) hNM
    have hbase : (2 ^ L * N) ^ N ≤ M ^ N := Nat.pow_le_pow_left hlow N
    have hNN : 0 < N ^ N := by
      rcases Nat.eq_zero_or_pos N with h0 | hN
      · simp [h0]
      · exact pow_pos hN N
    have : 2 ^ (N * L) * N ^ N ≤ (M + 1) * M.choose N * N ^ N := by
      calc 2 ^ (N * L) * N ^ N = (2 ^ L * N) ^ N := by
            rw [mul_pow, ← pow_mul, mul_comm L N]
        _ ≤ M ^ N := hbase
        _ ≤ (M + 1) * (M.choose N * N ^ N) := hfloor
        _ = (M + 1) * M.choose N * N ^ N := by ring
    exact Nat.le_of_mul_le_mul_right this hNN

/-- A row of three identifiers below 32 in buckets of four (two low bits):
eight buckets, so `3 · 3 + 8 = 17` bits, and the row comes back. -/
example : efDecode 2 (efEncode 2 8 {1, 9, 30}) = {1, 9, 30} ∧
    efBits 2 (efEncode 2 8 {1, 9, 30}) = 17 := by
  have hs : ∀ x ∈ ({1, 9, 30} : Finset ℕ), x < 8 * 2 ^ 2 := by decide
  refine ⟨efDecode_efEncode 2 hs, ?_⟩
  rw [efBits_efEncode 2 hs]
  rfl

end Mettapedia.InformationTheory.RelationStoreFloors
