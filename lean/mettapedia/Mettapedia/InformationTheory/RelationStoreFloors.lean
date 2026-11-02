import Mathlib
import Mettapedia.InformationTheory.BinomialEntropy

/-!
# Memory floors for stored relations

A store for a relation is a description of it: a string from which a reading
procedure recovers the relation.  Whatever the procedure, computable or not,
the information in the relation sets a floor on the description's length.

For the `N`-element subsets of a universe of `M` possible tuples:

* `exists_subset_not_describedBelow` : under any decoder, some subset has no
  description shorter than `L` symbols as soon as `q ^ L ≤ C(M, N)`, for an
  alphabet of `q ≥ 2` symbols; with bits, `L = ⌊log₂ C(M, N)⌋`.
* `card_describedBelow_mul_lt` : if `q ^ (L + c) ≤ C(M, N)`, fewer than a
  `q⁻ᶜ` share of the subsets have descriptions shorter than `L`: almost every
  relation is incompressible.

Two representations meet the floor:

* rows of bits (`bitmapEncode`) spend `M` bits on any relation.  At half
  density they exceed the floor by at most `log₂ (M + 1) + 1` bits
  (`le_log_choose_half_add`); at density `d` they spend `M` bits against a
  floor of `M · h(d)` up to `log (M + 1)`
  (`log_choose_le_mul_binEntropy`, `mul_binEntropy_le_log_choose_add`), so
  their ratio to the floor tends to `log 2 / h(d)` (`bitmap_le_ratio_mul_floor`);
* sorted rows of identifiers (`sortedEncode`) spend `N` identifiers, each one
  symbol of an alphabet of `M`, against a floor of at least
  `N · log (M / N) - log (M + 1)` (`pow_le_succ_mul_choose_mul_pow`).
-/

namespace Mettapedia.InformationTheory.RelationStoreFloors

open Finset

/-! ## Descriptions under any decoder -/

section Descriptions

variable {σ β : Type*} [Fintype σ]

/-- `x` has a description under the decoder `D` of fewer than `L` symbols. -/
def DescribedBelow (D : List σ → Option β) (L : ℕ) (x : β) : Prop :=
  ∃ p : List σ, D p = some x ∧ p.length < L

/-- The strings over `σ` of fewer than `L` symbols. -/
noncomputable def stringsBelow (L : ℕ) : Finset (List σ) := by
  classical
  exact (range L).biUnion fun l => (univ : Finset (Fin l → σ)).image List.ofFn

theorem mem_stringsBelow {L : ℕ} {p : List σ} :
    p ∈ stringsBelow (σ := σ) L ↔ p.length < L := by
  classical
  unfold stringsBelow
  simp only [mem_biUnion, mem_range, mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨l, hl, f, rfl⟩
    simpa using hl
  · intro hp
    exact ⟨p.length, hp, p.get, List.ofFn_get p⟩

theorem card_stringsBelow_le (L : ℕ) :
    (stringsBelow (σ := σ) L).card ≤ ∑ l ∈ range L, Fintype.card σ ^ l := by
  classical
  unfold stringsBelow
  refine (card_biUnion_le).trans (sum_le_sum fun l _ => ?_)
  refine card_image_le.trans ?_
  simp

/-- Fewer than `q ^ L` strings over an alphabet of `q ≥ 2` symbols are shorter
than `L`. -/
theorem card_stringsBelow_lt (hσ : 2 ≤ Fintype.card σ) (L : ℕ) :
    (stringsBelow (σ := σ) L).card < Fintype.card σ ^ L :=
  (card_stringsBelow_le L).trans_lt
    (Nat.geomSum_lt hσ fun _ hl => mem_range.mp hl)

/-- Fewer than `q ^ L` values have descriptions shorter than `L` symbols, under
any decoder whatever. -/
theorem card_describedBelow_lt (D : List σ → Option β) (hσ : 2 ≤ Fintype.card σ)
    (F : Finset β) (L : ℕ) [DecidablePred (DescribedBelow D L)] :
    (F.filter (DescribedBelow D L)).card < Fintype.card σ ^ L := by
  classical
  let code : β → List σ := fun x =>
    if h : DescribedBelow D L x then Classical.choose h else []
  have hcode : ∀ x, DescribedBelow D L x → D (code x) = some x ∧ (code x).length < L := by
    intro x hx
    simp only [code, dif_pos hx]
    exact Classical.choose_spec hx
  have hmaps : ∀ x ∈ F.filter (DescribedBelow D L), code x ∈ stringsBelow (σ := σ) L := by
    intro x hx
    exact mem_stringsBelow.mpr (hcode x (mem_filter.mp hx).2).2
  have hinj : Set.InjOn code (F.filter (DescribedBelow D L) : Set β) := by
    intro x hx y hy hxy
    have hx' := (hcode x (mem_filter.mp hx).2).1
    have hy' := (hcode y (mem_filter.mp hy).2).1
    rw [hxy] at hx'
    exact Option.some_injective _ (hx'.symm.trans hy')
  exact (card_le_card_of_injOn code hmaps hinj).trans_lt (card_stringsBelow_lt hσ L)

end Descriptions

/-! ## The floor for relations of a given size -/

section Floor

variable {σ α : Type*} [Fintype σ] [Fintype α]

/-- Worst case: as soon as `q ^ L ≤ C(M, N)`, some `N`-element relation has no
description shorter than `L` symbols, whatever the decoder. -/
theorem exists_subset_not_describedBelow (D : List σ → Option (Finset α))
    (hσ : 2 ≤ Fintype.card σ) {N L : ℕ}
    (hL : Fintype.card σ ^ L ≤ (Fintype.card α).choose N) :
    ∃ s : Finset α, s.card = N ∧ ¬ DescribedBelow D L s := by
  classical
  have hlt := card_describedBelow_lt D hσ ((univ : Finset α).powersetCard N) L
  have hcard : (((univ : Finset α).powersetCard N).filter (DescribedBelow D L)).card <
      ((univ : Finset α).powersetCard N).card := by
    rw [card_powersetCard, card_univ]
    exact hlt.trans_le hL
  obtain ⟨s, hs, hns⟩ := exists_mem_notMem_of_card_lt_card hcard
  exact ⟨s, (mem_powersetCard.mp hs).2, fun hd => hns (mem_filter.mpr ⟨hs, hd⟩)⟩

/-- Incompressibility: if `q ^ (L + c) ≤ C(M, N)`, the `N`-element relations with
a description shorter than `L` number fewer than `C(M, N) / q ^ c`. -/
theorem card_describedBelow_mul_lt (D : List σ → Option (Finset α))
    (hσ : 2 ≤ Fintype.card σ) {N L c : ℕ}
    (hL : Fintype.card σ ^ (L + c) ≤ (Fintype.card α).choose N)
    [DecidablePred (DescribedBelow D L)] :
    (((univ : Finset α).powersetCard N).filter (DescribedBelow D L)).card *
        Fintype.card σ ^ c < (Fintype.card α).choose N := by
  have hlt := card_describedBelow_lt D hσ ((univ : Finset α).powersetCard N) L
  have hq : 0 < Fintype.card σ ^ c := pow_pos (by omega) c
  calc (((univ : Finset α).powersetCard N).filter (DescribedBelow D L)).card *
          Fintype.card σ ^ c
      < Fintype.card σ ^ L * Fintype.card σ ^ c := Nat.mul_lt_mul_of_pos_right hlt hq
    _ = Fintype.card σ ^ (L + c) := (pow_add _ _ _).symm
    _ ≤ (Fintype.card α).choose N := hL

/-- With bits: some `N`-element relation over `M` tuples has no description
shorter than `⌊log₂ C(M, N)⌋` bits. -/
theorem exists_subset_needs_log_choose (D : List Bool → Option (Finset α)) {N : ℕ}
    (hN : N ≤ Fintype.card α) :
    ∃ s : Finset α, s.card = N ∧
      ¬ DescribedBelow D (Nat.log 2 ((Fintype.card α).choose N)) s := by
  refine exists_subset_not_describedBelow D (by simp) ?_
  rw [Fintype.card_bool]
  exact Nat.pow_log_le_self 2 (Nat.choose_pos hN).ne'

end Floor

/-! ## Rows of bits -/

section Bitmap

variable {M : ℕ}

/-- A relation over `M` possible tuples as `M` bits, one a tuple. -/
def bitmapEncode (s : Finset (Fin M)) : List Bool :=
  List.ofFn fun i => decide (i ∈ s)

/-- Read `M` bits back as the relation they hold. -/
def bitmapDecode (p : List Bool) : Option (Finset (Fin M)) :=
  if h : p.length = M then some (univ.filter fun i => p.get (i.cast h.symm) = true)
  else none

theorem length_bitmapEncode (s : Finset (Fin M)) : (bitmapEncode s).length = M := by
  simp [bitmapEncode]

theorem bitmapDecode_encode (s : Finset (Fin M)) :
    bitmapDecode (bitmapEncode s) = some s := by
  have hlen := length_bitmapEncode s
  unfold bitmapDecode
  rw [dif_pos hlen]
  congr 1
  ext i
  simp only [mem_filter, mem_univ, true_and, bitmapEncode, List.get_ofFn,
    decide_eq_true_eq]
  exact Iff.rfl

/-- A bitmap description is never shorter than `M` bits: rows of bits do not
compress. -/
theorem length_of_bitmapDecode {p : List Bool} {s : Finset (Fin M)}
    (h : bitmapDecode p = some s) : p.length = M := by
  unfold bitmapDecode at h
  split_ifs at h with hlen
  exact hlen

theorem not_describedBelow_bitmap (s : Finset (Fin M)) :
    ¬ DescribedBelow (bitmapDecode (M := M)) M s := by
  rintro ⟨p, hp, hlen⟩
  rw [length_of_bitmapDecode hp] at hlen
  exact lt_irrefl M hlen

/-- Every relation over `M` tuples has a description of exactly `M` bits. -/
theorem bitmap_describes (s : Finset (Fin M)) :
    bitmapDecode (bitmapEncode s) = some s ∧ (bitmapEncode s).length = M :=
  ⟨bitmapDecode_encode s, length_bitmapEncode s⟩

/-- The `M + 1` binomial coefficients of `M` sum to `2 ^ M`, and the middle one
is the largest. -/
theorem two_pow_le_succ_mul_choose_half (M : ℕ) :
    2 ^ M ≤ (M + 1) * M.choose (M / 2) := by
  calc 2 ^ M = ∑ k ∈ range (M + 1), M.choose k := (Nat.sum_range_choose M).symm
    _ ≤ ∑ _k ∈ range (M + 1), M.choose (M / 2) :=
        sum_le_sum fun k _ => Nat.choose_le_middle k M
    _ = (M + 1) * M.choose (M / 2) := by rw [sum_const, card_range, smul_eq_mul]

/-- At half density rows of bits sit at the floor: their `M` bits exceed
`⌊log₂ C(M, M/2)⌋` by at most `⌊log₂ (M + 1)⌋ + 1`. -/
theorem le_log_choose_half_add (M : ℕ) :
    M ≤ Nat.log 2 (M.choose (M / 2)) + Nat.log 2 (M + 1) + 1 := by
  have hchoose : 0 < M.choose (M / 2) := Nat.choose_pos (Nat.div_le_self M 2)
  have h1 : M + 1 < 2 ^ (Nat.log 2 (M + 1) + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have h2 : M.choose (M / 2) < 2 ^ (Nat.log 2 (M.choose (M / 2)) + 1) :=
    Nat.lt_pow_succ_log_self (by norm_num) _
  have hprod : 2 ^ M < 2 ^ (Nat.log 2 (M.choose (M / 2)) + Nat.log 2 (M + 1) + 2) := by
    calc 2 ^ M ≤ (M + 1) * M.choose (M / 2) := two_pow_le_succ_mul_choose_half M
      _ < 2 ^ (Nat.log 2 (M + 1) + 1) * 2 ^ (Nat.log 2 (M.choose (M / 2)) + 1) :=
          Nat.mul_lt_mul'' h1 h2
      _ = 2 ^ (Nat.log 2 (M.choose (M / 2)) + Nat.log 2 (M + 1) + 2) := by
          rw [← pow_add]; congr 1; omega
  have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hprod
  omega

end Bitmap

/-! ## The floor in entropy form -/

section Entropy

open Real

/-- `M · h(N/M) = M log M - N log N - (M - N) log (M - N)`, natural logarithms. -/
theorem mul_binEntropy_eq {M N : ℕ} (hM : 0 < M) (hN : N ≤ M) :
    (M : ℝ) * binEntropy ((N : ℝ) / M) =
      M * log M - N * log N - ((M : ℝ) - N) * log ((M : ℝ) - N) := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hMne : (M : ℝ) ≠ 0 := hMr.ne'
  have hone : 1 - (N : ℝ) / M = ((M : ℝ) - N) / M := by field_simp
  rw [binEntropy_eq_negMulLog_add_negMulLog_one_sub, hone]
  simp only [negMulLog, mul_add]
  rcases Nat.eq_zero_or_pos N with rfl | hNpos
  · simp
  rcases eq_or_lt_of_le hN with rfl | hNM
  · simp
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hNpos.ne'
  have hMN : (M : ℝ) - N ≠ 0 := by
    have : (N : ℝ) < M := by exact_mod_cast hNM
    linarith
  rw [log_div hNr hMne, log_div hMN hMne]
  field_simp
  ring

/-- The floor is at most the entropy: `log C(M, N) ≤ M · h(N/M)`. -/
theorem log_choose_le_mul_binEntropy {M N : ℕ} (hM : 0 < M) (hN : N ≤ M) :
    log (M.choose N) ≤ M * binEntropy ((N : ℝ) / M) := by
  rw [mul_binEntropy_eq hM hN]
  have hnat := InformationTheory.choose_mul_pow_pow_le hN
  have hreal : ((M.choose N : ℕ) : ℝ) * ((N : ℝ) ^ N * ((M : ℝ) - N) ^ (M - N)) ≤
      (M : ℝ) ^ M := by
    have := (Nat.cast_le (α := ℝ)).mpr hnat
    push_cast [Nat.cast_sub hN] at this
    exact this
  have hC : (0 : ℝ) < M.choose N := by exact_mod_cast Nat.choose_pos hN
  have hNN : (0 : ℝ) < (N : ℝ) ^ N := by
    rcases Nat.eq_zero_or_pos N with rfl | hNpos
    · simp
    · exact pow_pos (by exact_mod_cast hNpos) N
  have hMN : (0 : ℝ) < ((M : ℝ) - N) ^ (M - N) := by
    rcases eq_or_lt_of_le hN with rfl | hNM
    · simp
    · have hlt : (N : ℝ) < M := by exact_mod_cast hNM
      exact pow_pos (by linarith) _
  have hlog := log_le_log (by positivity) hreal
  rw [log_mul hC.ne' (mul_pos hNN hMN).ne', log_mul hNN.ne' hMN.ne', log_pow, log_pow,
    log_pow] at hlog
  push_cast [Nat.cast_sub hN] at hlog
  linarith

/-- The floor is at least the entropy less `log (M + 1)`:
`M · h(N/M) ≤ log C(M, N) + log (M + 1)`. -/
theorem mul_binEntropy_le_log_choose_add {M N : ℕ} (hM : 0 < M) (hN : N ≤ M) :
    M * binEntropy ((N : ℝ) / M) ≤ log (M.choose N) + log ((M : ℝ) + 1) := by
  rw [mul_binEntropy_eq hM hN]
  have hnat := InformationTheory.pow_le_succ_mul_choose_mul hN
  have hreal : (M : ℝ) ^ M ≤ ((M : ℝ) + 1) *
      ((M.choose N : ℝ) * ((N : ℝ) ^ N * ((M : ℝ) - N) ^ (M - N))) := by
    have := (Nat.cast_le (α := ℝ)).mpr hnat
    push_cast [Nat.cast_sub hN] at this
    exact this
  have hC : (0 : ℝ) < M.choose N := by exact_mod_cast Nat.choose_pos hN
  have hNN : (0 : ℝ) < (N : ℝ) ^ N := by
    rcases Nat.eq_zero_or_pos N with rfl | hNpos
    · simp
    · exact pow_pos (by exact_mod_cast hNpos) N
  have hMN : (0 : ℝ) < ((M : ℝ) - N) ^ (M - N) := by
    rcases eq_or_lt_of_le hN with rfl | hNM
    · simp
    · have hlt : (N : ℝ) < M := by exact_mod_cast hNM
      exact pow_pos (by linarith) _
  have hM1 : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have hMpow : (0 : ℝ) < (M : ℝ) ^ M := pow_pos (by exact_mod_cast hM) M
  have hlog := log_le_log hMpow hreal
  rw [log_mul hM1.ne' (mul_pos hC (mul_pos hNN hMN)).ne', log_mul hC.ne' (mul_pos hNN hMN).ne',
    log_mul hNN.ne' hMN.ne', log_pow, log_pow, log_pow] at hlog
  push_cast [Nat.cast_sub hN] at hlog
  linarith

/-- Rows of bits against the floor: at density `d = N / M` with `h(d) > 0`, the
bitmap's `M` bits, `M · log 2` nats, are at most `log 2 / h(d)` times the
floor `log C(M, N)` plus `log (M + 1)`. -/
theorem bitmap_le_ratio_mul_floor {M N : ℕ} (hM : 0 < M) (hN : N ≤ M)
    (hh : 0 < binEntropy ((N : ℝ) / M)) :
    (M : ℝ) * log 2 ≤
      log 2 / binEntropy ((N : ℝ) / M) * (log (M.choose N) + log ((M : ℝ) + 1)) := by
  have hfloor := mul_binEntropy_le_log_choose_add hM hN
  rw [div_mul_eq_mul_div, le_div_iff₀ hh]
  have hlog2 : (0 : ℝ) < log 2 := log_pos (by norm_num)
  nlinarith [mul_le_mul_of_nonneg_left hfloor hlog2.le]

end Entropy

/-! ## Sorted rows of identifiers -/

section Sorted

variable {M : ℕ}

/-- A relation as the sorted list of its tuples' identifiers. -/
def sortedEncode (s : Finset (Fin M)) : List (Fin M) :=
  s.sort (· ≤ ·)

/-- Read a list of identifiers back as the relation they name. -/
def sortedDecode (p : List (Fin M)) : Option (Finset (Fin M)) :=
  some p.toFinset

/-- Every `N`-element relation has a description of exactly `N` identifiers. -/
theorem sorted_describes (s : Finset (Fin M)) :
    sortedDecode (sortedEncode s) = some s ∧ (sortedEncode s).length = s.card := by
  constructor
  · simp [sortedDecode, sortedEncode]
  · simp [sortedEncode]

/-- The floor for sparse relations: `M ^ N ≤ (M + 1) · C(M, N) · N ^ N`, so the
floor is at least `N · log (M / N) - log (M + 1)`. -/
theorem pow_le_succ_mul_choose_mul_pow {N : ℕ} (hN : N ≤ M) :
    M ^ N ≤ (M + 1) * (M.choose N * N ^ N) := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · have : N = 0 := by omega
    subst this
    simp
  have hbase := InformationTheory.pow_le_succ_mul_choose_mul hN
  have hrest : (M - N) ^ (M - N) ≤ M ^ (M - N) := Nat.pow_le_pow_left (by omega) _
  have hsplit : M ^ M = M ^ N * M ^ (M - N) := by
    rw [← pow_add, Nat.add_sub_cancel' hN]
  have hpos : 0 < M ^ (M - N) := pow_pos hM _
  have : M ^ N * M ^ (M - N) ≤ (M + 1) * (M.choose N * N ^ N) * M ^ (M - N) := by
    calc M ^ N * M ^ (M - N) = M ^ M := hsplit.symm
      _ ≤ (M + 1) * (M.choose N * (N ^ N * (M - N) ^ (M - N))) := hbase
      _ ≤ (M + 1) * (M.choose N * (N ^ N * M ^ (M - N))) := by gcongr
      _ = (M + 1) * (M.choose N * N ^ N) * M ^ (M - N) := by ring
  exact Nat.le_of_mul_le_mul_right this hpos

end Sorted

/-! ## Examples -/

/-- Of the six pairs drawn from four tuples, some pair has no description of
fewer than two bits, under any decoder: `2 ^ 2 ≤ C(4, 2)`. -/
example (D : List Bool → Option (Finset (Fin 4))) :
    ∃ s : Finset (Fin 4), s.card = 2 ∧ ¬ DescribedBelow D 2 s :=
  exists_subset_not_describedBelow D (by simp) (by simp [Nat.choose])

/-- The bitmap describes the relation `{0, 2}` over four tuples in four bits. -/
example : bitmapDecode (bitmapEncode ({0, 2} : Finset (Fin 4))) =
      some ({0, 2} : Finset (Fin 4)) ∧
    (bitmapEncode ({0, 2} : Finset (Fin 4))).length = 4 :=
  bitmap_describes _

/-- The identifiers `[1, 3]` describe the relation `{1, 3}`. -/
example : sortedDecode ([1, 3] : List (Fin 5)) = some ({1, 3} : Finset (Fin 5)) := by
  simp [sortedDecode]

/-- The relation `{3, 1}` takes two identifiers. -/
example : (sortedEncode ({3, 1} : Finset (Fin 5))).length = 2 := by
  simp [sortedEncode]

end Mettapedia.InformationTheory.RelationStoreFloors
