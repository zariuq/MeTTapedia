import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-!
# Cardinalities of take/read selections over one eligible occurrence class

Take ports choose distinct physical rows and read ports choose with repetition
from the remaining rows. Their combined selection type has cardinality
`m.descFactorial t * (m - t) ^ r`. The Stirling expansion records how read
ports may share an occurrence; rendering every read as a distinct take loses
these alternatives.

The eligible row class is supplied explicitly. This counts physical port
selections, not projected substitutions or distinct answer values. No
partition of open labels by an unsolved equation store is assumed.
The rational control concerns a separately chosen match-uniform scheduler
with one competing match; it is not a universal probability law.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ResourceOccupationCounting

open Finset

/-- One read port more: `(m - t)·(m)_(t+j) = (m)_(t+j+1) + j·(m)_(t+j)`. -/
theorem sub_mul_descFactorial (m t j : ℕ) :
    (m - t) * m.descFactorial (t + j) = m.descFactorial (t + j + 1) + j * m.descFactorial (t + j) := by
  by_cases h : t + j ≤ m
  · have split : m - t = (m - (t + j)) + j := by omega
    rw [Nat.descFactorial_succ, split, Nat.add_mul]
  · have zero : m.descFactorial (t + j) = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
    simp [zero]

/-- **Reads are the Stirling sum of renderings.** With `t` takes and `r` aliasable reads over
`m` rows of one label, the match count is the sum over the number `j` of distinct rows read, of
`S(r, j)` gluings times the matches of the rendered rule with `t + j` take ports. -/
theorem reads_eq_stirling_sum (m t r : ℕ) :
    m.descFactorial t * (m - t) ^ r =
      ∑ j ∈ range (r + 1), Nat.stirlingSecond r j * m.descFactorial (t + j) := by
  induction r with
  | zero => simp
  | succ r ih =>
    -- the right side for `r + 1`, split at `j = 0`
    have shift : ∑ j ∈ range (r + 1 + 1), Nat.stirlingSecond (r + 1) j * m.descFactorial (t + j) =
        ∑ j ∈ range (r + 1), Nat.stirlingSecond (r + 1) (j + 1) * m.descFactorial (t + (j + 1)) := by
      rw [sum_range_succ']
      simp
    -- the weighted sum `∑ j·S(r,j)·(m)_(t+j)` shifted by one
    have weighted : ∑ j ∈ range (r + 1), (j + 1) * Nat.stirlingSecond r (j + 1) *
          m.descFactorial (t + (j + 1)) =
        ∑ j ∈ range (r + 1), j * Nat.stirlingSecond r j * m.descFactorial (t + j) := by
      have full := sum_range_succ' (fun i => i * Nat.stirlingSecond r i * m.descFactorial (t + i))
        (r + 1)
      have top := sum_range_succ (fun i => i * Nat.stirlingSecond r i * m.descFactorial (t + i))
        (r + 1)
      have vanish : (r + 1) * Nat.stirlingSecond r (r + 1) * m.descFactorial (t + (r + 1)) = 0 := by
        rw [Nat.stirlingSecond_eq_zero_of_lt (Nat.lt_succ_self r)]
        simp

      rw [vanish, add_zero] at top
      rw [← top, full]
      simp
    calc m.descFactorial t * (m - t) ^ (r + 1)
        = (m - t) * (m.descFactorial t * (m - t) ^ r) := by ring
      _ = ∑ j ∈ range (r + 1), Nat.stirlingSecond r j * ((m - t) * m.descFactorial (t + j)) := by
          rw [ih, mul_sum]
          refine sum_congr rfl fun j _ => by ring
      _ = ∑ j ∈ range (r + 1), (Nat.stirlingSecond r j * m.descFactorial (t + j + 1) +
            j * Nat.stirlingSecond r j * m.descFactorial (t + j)) := by
          refine sum_congr rfl fun j _ => ?_
          rw [sub_mul_descFactorial]
          ring
      _ = ∑ j ∈ range (r + 1), Nat.stirlingSecond r j * m.descFactorial (t + j + 1) +
            ∑ j ∈ range (r + 1), (j + 1) * Nat.stirlingSecond r (j + 1) *
              m.descFactorial (t + (j + 1)) := by
          rw [sum_add_distrib, weighted]
      _ = ∑ j ∈ range (r + 1), Nat.stirlingSecond (r + 1) (j + 1) * m.descFactorial (t + (j + 1)) := by
          rw [← sum_add_distrib]
          refine sum_congr rfl fun j _ => ?_
          rw [Nat.stirlingSecond_succ_succ]
          ring_nf
      _ = ∑ j ∈ range (r + 1 + 1), Nat.stirlingSecond (r + 1) j * m.descFactorial (t + j) :=
          shift.symm

/-! ## The counts are counts of selections -/

/-- Read selections: every read port picks any of the available rows. -/
theorem card_read_selections {α : Type*} (rows : Finset α) (r : ℕ) :
    Fintype.card (Fin r → rows) = rows.card ^ r := by
  classical
  simp

/-- Take selections: the take ports pick distinct rows. -/
theorem card_take_selections {α : Type*} (rows : Finset α) (t : ℕ) :
    Fintype.card (Fin t ↪ rows) = rows.card.descFactorial t := by
  classical
  simp [Fintype.card_embedding_eq]

/-- With no takes, read selections are the Stirling sum of rendered (injective) selections. -/
theorem read_selections_stirling {α : Type*} (rows : Finset α) (r : ℕ) :
    Fintype.card (Fin r → rows) =
      ∑ j ∈ range (r + 1), Nat.stirlingSecond r j * Fintype.card (Fin j ↪ rows) := by
  rw [card_read_selections]
  simp_rw [card_take_selections]
  simpa using reads_eq_stirling_sum rows.card 0 r

/-- Mixed selections, as the identification condition allows them: the take ports embed into
the rows, and each read port picks any row that is not taken (reads may alias each other). -/
abbrev MixedSelection {α : Type*} (rows : Finset α) (t r : ℕ) :=
  Σ e : Fin t ↪ rows, Fin r → {x : rows // ∀ i, e i ≠ x}

theorem card_mixed_selections {α : Type*} [DecidableEq α] (rows : Finset α) (t r : ℕ) :
    Fintype.card (MixedSelection rows t r) = rows.card.descFactorial t * (rows.card - t) ^ r := by
  rw [Fintype.card_sigma]
  have each : ∀ e : Fin t ↪ rows,
      Fintype.card (Fin r → {x : rows // ∀ i, e i ≠ x}) = (rows.card - t) ^ r := by
    intro e
    rw [Fintype.card_fun, Fintype.card_fin]
    congr 1
    classical
    have same : Fintype.card {x : rows // ∀ i, e i ≠ x} =
        Fintype.card {x : rows // x ∉ Set.range e} :=
      Fintype.card_congr (Equiv.subtypeEquivRight fun x => by simp [Set.mem_range])
    rw [same, Fintype.card_subtype_compl]
    have range : Fintype.card {x : rows // x ∈ Set.range e} = t := by
      have h1 := Set.card_range_of_injective (f := e) e.injective
      rw [Fintype.card_fin] at h1
      exact (Fintype.card_congr (Equiv.refl _)).trans h1
    rw [range]
    simp
  simp_rw [each]
  rw [sum_const, card_univ, card_take_selections, smul_eq_mul]

/-- **The selection form of the law.** The selections of a rule with `t` takes and `r`
aliasable reads are counted by the Stirling sum of the rendered rules with `t + j` takes. -/
theorem mixed_selections_stirling {α : Type*} [DecidableEq α] (rows : Finset α) (t r : ℕ) :
    Fintype.card (MixedSelection rows t r) =
      ∑ j ∈ range (r + 1), Nat.stirlingSecond r j * Fintype.card (Fin (t + j) ↪ rows) := by
  rw [card_mixed_selections]
  simp_rw [card_take_selections]
  exact reads_eq_stirling_sum rows.card t r

/-- Reads and their rendering agree exactly when there is at most one read port or no row is
left after the takes. -/
theorem reads_eq_rendered_iff (m t r : ℕ) :
    m.descFactorial t * (m - t) ^ r = m.descFactorial (t + r) ↔ t ≤ m → (r ≤ 1 ∨ m ≤ t) := by
  have split : m.descFactorial (t + r) = (m - t).descFactorial r * m.descFactorial t := by
    have := Nat.descFactorial_mul_descFactorial (n := m) (k := t) (m := t + r) (by omega)
    simpa using this.symm
  rw [split]
  constructor
  · intro eq le
    by_contra hcon
    have r2 : 2 ≤ r := by omega
    have mt : m - t ≠ 0 := by omega
    have pos : 0 < m.descFactorial t := Nat.descFactorial_pos.mpr le
    have lt := Nat.descFactorial_lt_pow mt r2
    have hlt : (m - t).descFactorial r * m.descFactorial t < m.descFactorial t * (m - t) ^ r := by
      calc (m - t).descFactorial r * m.descFactorial t
          < (m - t) ^ r * m.descFactorial t := mul_lt_mul_of_pos_right lt pos
        _ = m.descFactorial t * (m - t) ^ r := by ring
    rw [eq] at hlt
    exact lt_irrefl _ hlt
  · intro h
    by_cases le : t ≤ m
    · rcases h le with r1 | mt
      · interval_cases r <;> simp [mul_comm]
      · have : m - t = 0 := by omega
        rw [this]
        rcases Nat.eq_zero_or_pos r with rfl | rpos
        · simp
        · obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
          simp
    · have zero : m.descFactorial t = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
      simp [zero]

/-! ## Controls -/

/-- Two read ports over two equal-valued rows: 4 read matches, 2 rendered. -/
theorem four_vs_two :
    Fintype.card (Fin 2 → Fin 2) = 4 ∧ Fintype.card (Fin 2 ↪ Fin 2) = 2 := by
  constructor
  · simp
  · simp

/-- With one competing match, a match-uniform scheduler starts the reader with probability
`4/5` with reads and `2/3` after rendering. -/
theorem reader_share_changes : ((4 : ℚ) / (4 + 1)) = 4 / 5 ∧ ((2 : ℚ) / (2 + 1)) = 2 / 3 ∧
    ((4 : ℚ) / 5) ≠ 2 / 3 := by
  norm_num

/-- A rendering that keeps every glued rule once, instead of `S(r, j)` times, miscounts:
three read ports over two rows have 8 matches, while the glued rules with multiplicity one give
`2 + 2 + 0 = 4`. -/
theorem multiplicity_matters :
    (2 : ℕ) ^ 3 = 8 ∧
      ∑ j ∈ range (3 + 1), Nat.stirlingSecond 3 j * (2 : ℕ).descFactorial j = 8 ∧
      ∑ j ∈ Icc 1 3, (2 : ℕ).descFactorial j = 4 := by
  refine ⟨by norm_num, ?_, ?_⟩
  · simp [sum_range_succ, Nat.stirlingSecond, Nat.descFactorial]
  · decide

/-- One available row and two read ports: the reads alias it (one match), the rendering finds
none. This is the `[7, 7]` case. -/
theorem one_row_two_reads :
    Fintype.card (Fin 2 → Fin 1) = 1 ∧ Fintype.card (Fin 2 ↪ Fin 1) = 0 := by
  constructor
  · simp
  · simp

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ResourceOccupationCounting
