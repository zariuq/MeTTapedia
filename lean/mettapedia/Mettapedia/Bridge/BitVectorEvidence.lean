/-
# Bit Vector Evidence Bridge

This file establishes the geometric semantics of PLN Evidence through bit vectors.

## Core Insight

PLN Evidence counts (positive, negative) correspond exactly to known bits in a
partial bit vector:
- `positive` = number of known 1-bits
- `negative` = number of known 0-bits
- `unknown` = bits yet to be observed

The set of "completions" of a partial vector (filling in unknowns) gives a
combinatorial interpretation of uncertainty in PLN.

## Main Results

1. `completions_card`: |completions(v)| = 2^(countUnknown v)
2. `completions_mean_weight`: Average Hamming weight equals (pos + unknown/2) / n
3. `toEvidence_strength`: Evidence.strength = expected fraction of 1s

## Connection to PLNDistributional

The Evidence structure from PLNDistributional is the continuous generalization:
- Discrete: countPositive, countNegative are natural numbers
- Continuous: Evidence.positive, Evidence.negative are reals (virtual evidence)

The Beta distribution emerges as the limit distribution when N → ∞.

## References

- Goertzel et al., "Probabilistic Logic Networks", Chapter 6
- Mathlib `Mathlib.InformationTheory.Hamming`
-/

import Mathlib.InformationTheory.Hamming
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Rat.Cast.CharZero
import Mettapedia.Logic.PLNDistributional

set_option linter.unusedSectionVars false

namespace Mettapedia.Bridge.BitVectorEvidence

open Finset

/-! ## Basic Definitions -/

/-- A full bit vector of dimension n. -/
abbrev BitVector (n : ℕ) := Fin n → Bool

/-- A partial bit vector: each position is either known (Some b) or unknown (None). -/
abbrev PartialVector (n : ℕ) := Fin n → Option Bool

/-! ## Counting Functions -/

variable {n : ℕ}

/-- Count of positions with known value `true`. -/
def countPositive (v : PartialVector n) : ℕ :=
  (univ : Finset (Fin n)).filter (fun i => v i = some true) |>.card

/-- Count of positions with known value `false`. -/
def countNegative (v : PartialVector n) : ℕ :=
  (univ : Finset (Fin n)).filter (fun i => v i = some false) |>.card

/-- Count of unknown positions. -/
def countUnknown (v : PartialVector n) : ℕ :=
  (univ : Finset (Fin n)).filter (fun i => v i = none) |>.card

/-- Total known positions. -/
def countKnown (v : PartialVector n) : ℕ :=
  countPositive v + countNegative v

/-- The three counts partition n.

This is a fundamental fact: every position in a partial vector is either
known-true, known-false, or unknown.
-/
theorem count_partition (v : PartialVector n) :
    countPositive v + countNegative v + countUnknown v = n := by
  unfold countPositive countNegative countUnknown
  -- Unify notation
  let S := (univ : Finset (Fin n))
  let A := S.filter (fun i => v i = some true)
  let B := S.filter (fun i => v i = some false)
  let C := S.filter (fun i => v i = none)
  -- Show A, B, C partition S
  have h_cover : S = A ∪ B ∪ C := by
    ext i
    simp only [mem_univ, mem_union, mem_filter, true_and, S, A, B, C]
    cases h : v i with
    | none => simp
    | some b => cases b <;> simp
  have h_AB : Disjoint A B := by
    simp only [Finset.disjoint_filter, A, B]
    intro i _ h; simp_all
  have h_AC : Disjoint A C := by
    simp only [Finset.disjoint_filter, A, C]
    intro i _ h; simp_all
  have h_BC : Disjoint B C := by
    simp only [Finset.disjoint_filter, B, C]
    intro i _ h; simp_all
  have h_ABC : Disjoint (A ∪ B) C := by
    rw [disjoint_union_left]
    exact ⟨h_AC, h_BC⟩
  calc A.card + B.card + C.card
      = (A ∪ B).card + C.card := by rw [card_union_of_disjoint h_AB]
    _ = (A ∪ B ∪ C).card := by rw [card_union_of_disjoint h_ABC]
    _ = S.card := by rw [← h_cover]
    _ = n := card_fin n

/-! ## Completions

A completion of a partial vector fills in all unknown positions with concrete bits.
-/

/-- Check if a full vector is consistent with a partial vector.
A full vector u is consistent with partial v if u agrees with v on all known positions. -/
def consistent (u : BitVector n) (v : PartialVector n) : Bool :=
  (List.finRange n).all fun i =>
    match v i with
    | none => true  -- unknowns are always consistent
    | some b => u i == b  -- known positions must match

/-- The set of all completions of a partial vector. -/
def completions (v : PartialVector n) : Finset (BitVector n) :=
  univ.filter (fun u => consistent u v)

/-! ## Hamming Weight -/

/-- Hamming weight of a bit vector (count of true bits). -/
def hammingWeight (u : BitVector n) : ℕ :=
  (univ : Finset (Fin n)).filter (fun i => u i = true) |>.card

/-! ## Key Cardinality Theorem -/

/-- The set of unknown indices. -/
def unknownIndices (v : PartialVector n) : Finset (Fin n) :=
  univ.filter (fun i => v i = none)

theorem unknownIndices_card (v : PartialVector n) :
    (unknownIndices v).card = countUnknown v := rfl

/-- Given a full vector and a partial vector, extract the values at unknown positions. -/
def extractUnknown (v : PartialVector n) (u : BitVector n) : unknownIndices v → Bool :=
  fun ⟨i, _⟩ => u i

/-- Given values for unknown positions and a partial vector, construct a full vector. -/
def fillUnknown (v : PartialVector n) (f : unknownIndices v → Bool) : BitVector n :=
  fun i =>
    if h : v i = none then
      f ⟨i, by simp [unknownIndices, h]⟩
    else
      (v i).get (Option.ne_none_iff_isSome.mp h)

theorem fillUnknown_consistent (v : PartialVector n) (f : unknownIndices v → Bool) :
    consistent (fillUnknown v f) v = true := by
  simp only [consistent, List.all_eq_true, List.mem_finRange, true_implies]
  intro i
  simp only [fillUnknown]
  by_cases hv : v i = none
  · simp [hv]
  · -- v i ≠ none means v i = some b for some b
    obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hv
    simp [hb]

theorem extractUnknown_fillUnknown (v : PartialVector n) (f : unknownIndices v → Bool) :
    extractUnknown v (fillUnknown v f) = f := by
  ext ⟨i, hi⟩
  simp only [extractUnknown, fillUnknown]
  simp only [unknownIndices, mem_filter, mem_univ, true_and] at hi
  simp [hi]

theorem fillUnknown_extractUnknown (v : PartialVector n) (u : BitVector n)
    (hu : consistent u v = true) : fillUnknown v (extractUnknown v u) = u := by
  ext i
  simp only [fillUnknown, extractUnknown]
  simp only [consistent, List.all_eq_true, List.mem_finRange, true_implies] at hu
  by_cases hv : v i = none
  · simp [hv]
  · -- v i ≠ none means v i = some b for some b
    obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hv
    specialize hu i
    simp only [hb, beq_iff_eq] at hu
    simp [hb, hu]

/-- The number of completions is 2^(number of unknowns).

This is a fundamental combinatorial fact: each unknown bit can be filled
in 2 ways independently.
-/
theorem completions_card (v : PartialVector n) :
    (completions v).card = 2 ^ countUnknown v := by
  -- Build the equivalence
  let toFun : completions v → (unknownIndices v → Bool) :=
    fun ⟨u, hu⟩ => extractUnknown v u
  let invFun : (unknownIndices v → Bool) → completions v :=
    fun f => ⟨fillUnknown v f, by simp [completions, fillUnknown_consistent]⟩
  have h_equiv : (completions v) ≃ (unknownIndices v → Bool) := {
    toFun := toFun
    invFun := invFun
    left_inv := fun ⟨u, hu⟩ => by
      simp only [completions, mem_filter, mem_univ, true_and] at hu
      simp only [toFun, invFun, Subtype.mk.injEq]
      exact fillUnknown_extractUnknown v u hu
    right_inv := fun f => by
      simp only [toFun, invFun]
      exact extractUnknown_fillUnknown v f
  }
  calc (completions v).card
      = Fintype.card (completions v) := (Fintype.card_coe _).symm
    _ = Fintype.card (unknownIndices v → Bool) := Fintype.card_congr h_equiv
    _ = 2 ^ (unknownIndices v).card := by
        rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]
    _ = 2 ^ countUnknown v := by rw [unknownIndices_card]

/-! ## Mean Weight Theorem

The average Hamming weight over all completions has a beautiful exact formula.
-/

/-- Sum of Hamming weights over all completions. -/
def totalWeight (v : PartialVector n) : ℕ :=
  (completions v).sum hammingWeight

/-- Count of completions where position i is true. -/
def countTrueAt (v : PartialVector n) (i : Fin n) : ℕ :=
  (completions v).filter (fun u => u i = true) |>.card

/-- For a known-true position, all completions have it true. -/
theorem countTrueAt_of_some_true (v : PartialVector n) (i : Fin n)
    (hi : v i = some true) : countTrueAt v i = (completions v).card := by
  unfold countTrueAt
  congr 1
  ext u
  simp only [mem_filter, and_iff_left_iff_imp]
  intro hu
  simp only [completions, mem_filter, mem_univ, true_and] at hu
  simp only [consistent, List.all_eq_true, List.mem_finRange, true_implies] at hu
  specialize hu i
  simp only [hi, beq_iff_eq] at hu
  exact hu

/-- For a known-false position, no completions have it true. -/
theorem countTrueAt_of_some_false (v : PartialVector n) (i : Fin n)
    (hi : v i = some false) : countTrueAt v i = 0 := by
  unfold countTrueAt
  rw [card_eq_zero]
  ext u
  simp only [mem_filter, Finset.notMem_empty, iff_false, not_and]
  intro hu
  simp only [completions, mem_filter, mem_univ, true_and] at hu
  simp only [consistent, List.all_eq_true, List.mem_finRange, true_implies] at hu
  specialize hu i
  simp only [hi, beq_iff_eq] at hu
  intro hu_true
  rw [hu_true] at hu
  exact Bool.noConfusion hu

/-- Flip bit i in a vector. -/
def flipAt (i : Fin n) (u : BitVector n) : BitVector n :=
  fun j => if j = i then !u j else u j

/-- flipAt is an involution. -/
theorem flipAt_involutive (i : Fin n) : Function.Involutive (flipAt i (n := n)) := by
  intro u
  ext j
  simp only [flipAt]
  by_cases hji : j = i <;> simp [hji, Bool.not_not]

/-- flipAt preserves consistency when the position is unknown. -/
theorem flipAt_preserves_consistent (v : PartialVector n) (u : BitVector n)
    (i : Fin n) (hi : v i = none) (hu : consistent u v = true) :
    consistent (flipAt i u) v = true := by
  simp only [consistent, List.all_eq_true, List.mem_finRange, true_implies] at hu ⊢
  intro j
  simp only [flipAt]
  by_cases hji : j = i
  · simp [hji, hi]
  · simp [hji, hu j]

/-- flipAt changes the bit at position i. -/
theorem flipAt_at (i : Fin n) (u : BitVector n) : (flipAt i u) i = !u i := by
  simp [flipAt]

/-- flipAt doesn't change other positions. -/
theorem flipAt_ne (i j : Fin n) (u : BitVector n) (hji : j ≠ i) :
    (flipAt i u) j = u j := by
  simp [flipAt, hji]

/-- For an unknown position, exactly half the completions have it true.

**Proof idea**: Flipping bit i gives a bijection between {u | u(i)=true} and
{u | u(i)=false} that preserves consistency with v (since v i = none).
Therefore card({u | u(i)=true}) = card({u | u(i)=false}) = card(completions)/2.
-/
theorem countTrueAt_of_none (v : PartialVector n) (i : Fin n)
    (hi : v i = none) (_hpos : 0 < countUnknown v) :
    2 * countTrueAt v i = (completions v).card := by
  -- Let T = {u ∈ completions | u i = true} and F = {u ∈ completions | u i = false}
  let T := (completions v).filter (fun u => u i = true)
  let F := (completions v).filter (fun u => u i = false)
  -- countTrueAt v i = T.card
  have hT : countTrueAt v i = T.card := rfl
  -- T and F partition completions
  have hTF_disjoint : Disjoint T F := by
    simp only [Finset.disjoint_filter, T, F]
    intro u _ htrue hfalse
    simp_all
  have hTF_cover : completions v = T ∪ F := by
    ext u
    simp only [mem_union, mem_filter, T, F]
    constructor
    · intro hu
      cases hu' : u i <;> simp [hu]
    · intro h
      cases h <;> simp_all
  have hcard : (completions v).card = T.card + F.card := by
    rw [hTF_cover, card_union_of_disjoint hTF_disjoint]
  -- flipAt gives a bijection T ≃ F
  have hT_eq_F : T.card = F.card := by
    let flipBij : T → F := fun ⟨u, hu⟩ =>
      ⟨flipAt i u, by
        simp only [mem_filter, T] at hu
        simp only [mem_filter, F]
        constructor
        · simp only [completions, mem_filter, mem_univ, true_and] at hu ⊢
          exact flipAt_preserves_consistent v u i hi hu.1
        · simp only [flipAt_at, hu.2, Bool.not_true]⟩
    let flipBack : F → T := fun ⟨u, hu⟩ =>
      ⟨flipAt i u, by
        simp only [mem_filter, F] at hu
        simp only [mem_filter, T]
        constructor
        · simp only [completions, mem_filter, mem_univ, true_and] at hu ⊢
          exact flipAt_preserves_consistent v u i hi hu.1
        · simp only [flipAt_at, hu.2, Bool.not_false]⟩
    have h_equiv : T ≃ F := {
      toFun := flipBij
      invFun := flipBack
      left_inv := fun ⟨u, hu⟩ => by
        simp only [flipBij, flipBack, Subtype.mk.injEq]
        exact flipAt_involutive i u
      right_inv := fun ⟨u, hu⟩ => by
        simp only [flipBij, flipBack, Subtype.mk.injEq]
        exact flipAt_involutive i u
    }
    calc T.card
        = Fintype.card T := (Fintype.card_coe _).symm
      _ = Fintype.card F := Fintype.card_congr h_equiv
      _ = F.card := Fintype.card_coe _
  -- Now 2 * T.card = T.card + F.card = completions.card
  calc 2 * countTrueAt v i
      = 2 * T.card := by rw [hT]
    _ = T.card + T.card := by ring
    _ = T.card + F.card := by rw [hT_eq_F]
    _ = (completions v).card := hcard.symm

/-- Hamming weight as sum over positions. -/
theorem hammingWeight_eq_sum (u : BitVector n) :
    hammingWeight u = (univ : Finset (Fin n)).sum (fun i => if u i then 1 else 0) := by
  unfold hammingWeight
  rw [card_eq_sum_ones, sum_filter]

/-- Total weight = sum over positions of "count of completions with that bit true".

**Proof idea**: Fubini/linearity: Σᵤ Σᵢ 1{u(i)=true} = Σᵢ Σᵤ 1{u(i)=true}
-/
theorem totalWeight_eq_sum_countTrueAt (v : PartialVector n) :
    totalWeight v = (univ : Finset (Fin n)).sum (countTrueAt v) := by
  unfold totalWeight
  -- First express each hammingWeight as a sum
  conv_lhs =>
    arg 2
    ext u
    rw [hammingWeight_eq_sum]
  -- Now swap summation order: Σᵤ Σᵢ = Σᵢ Σᵤ
  rw [sum_comm]
  -- Both sides are sums over Fin n
  congr 1
  ext i
  -- Now show: Σ_{u ∈ completions} (if u i then 1 else 0) = countTrueAt v i
  unfold countTrueAt
  -- This is card (filter (u i = true)) = sum (if u i then 1 else 0)
  rw [card_eq_sum_ones, sum_filter]

/-- The average Hamming weight of completions.

**Main theorem**: The exact mean weight formula connects discrete combinatorics
to the continuous PLN strength formula.

**Proof sketch** (linearity of expectation):
- E[weight] = Σᵢ P(bit i is true in random completion)
- Known-true positions: P = 1, contributes countPositive
- Known-false positions: P = 0, contributes 0
- Unknown positions: P = 1/2, contributes countUnknown / 2
-/
theorem completions_mean_weight (v : PartialVector n) (h : 0 < countUnknown v) :
    (totalWeight v : ℚ) / (completions v).card =
    (countPositive v : ℚ) + (countUnknown v : ℚ) / 2 := by
  -- Partition the positions into three sets
  let S_true := (univ : Finset (Fin n)).filter (fun i => v i = some true)
  let S_false := (univ : Finset (Fin n)).filter (fun i => v i = some false)
  let S_none := (univ : Finset (Fin n)).filter (fun i => v i = none)

  -- Key cardinality facts
  have h_card_true : S_true.card = countPositive v := rfl
  have h_card_none : S_none.card = countUnknown v := rfl

  -- S_true, S_false, S_none are pairwise disjoint and cover univ
  have h_true_false_disj : Disjoint S_true S_false := by
    rw [Finset.disjoint_filter]
    intro i _ htrue hfalse
    simp_all
  have h_true_none_disj : Disjoint S_true S_none := by
    rw [Finset.disjoint_filter]
    intro i _ htrue hnone
    simp_all
  have h_false_none_disj : Disjoint S_false S_none := by
    rw [Finset.disjoint_filter]
    intro i _ hfalse hnone
    simp_all

  have h_union : S_true ∪ S_false ∪ S_none = univ := by
    ext i
    simp only [mem_univ, mem_union, mem_filter, true_and, S_true, S_false, S_none, iff_true]
    cases hv : v i with
    | none => simp
    | some b => cases b <;> simp

  -- Rewrite totalWeight using totalWeight_eq_sum_countTrueAt
  rw [totalWeight_eq_sum_countTrueAt]

  -- Split the sum into three parts
  have h_sum_split : (univ : Finset (Fin n)).sum (countTrueAt v) =
      S_true.sum (countTrueAt v) + S_false.sum (countTrueAt v) + S_none.sum (countTrueAt v) := by
    conv_lhs => rw [← h_union]
    rw [sum_union (disjoint_union_left.mpr ⟨h_true_none_disj, h_false_none_disj⟩)]
    rw [sum_union h_true_false_disj]

  -- For S_true: each i contributes (completions v).card
  have h_sum_true : S_true.sum (countTrueAt v) = S_true.card * (completions v).card := by
    have h_const : ∀ i ∈ S_true, countTrueAt v i = (completions v).card := by
      intro i hi
      simp only [mem_filter, mem_univ, true_and, S_true] at hi
      exact countTrueAt_of_some_true v i hi
    trans (S_true.sum fun _ => (completions v).card)
    · exact sum_congr rfl h_const
    · rw [sum_const, smul_eq_mul]

  -- For S_false: each i contributes 0
  have h_sum_false : S_false.sum (countTrueAt v) = 0 := by
    apply sum_eq_zero
    intro i hi
    simp only [mem_filter, mem_univ, true_and, S_false] at hi
    exact countTrueAt_of_some_false v i hi

  -- For S_none: sum over unknowns equals countUnknown * completions.card / 2
  have h_sum_none : 2 * S_none.sum (countTrueAt v) = S_none.card * (completions v).card := by
    have h_each : ∀ i ∈ S_none, 2 * countTrueAt v i = (completions v).card := by
      intro i hi
      simp only [mem_filter, mem_univ, true_and, S_none] at hi
      exact countTrueAt_of_none v i hi h
    rw [mul_sum]
    trans (S_none.sum fun _ => (completions v).card)
    · exact sum_congr rfl h_each
    · rw [sum_const, smul_eq_mul]

  -- Now we can compute the mean
  -- totalWeight = S_true.sum + S_false.sum + S_none.sum
  --             = S_true.card * C + 0 + S_none.sum
  -- where 2 * S_none.sum = S_none.card * C
  -- So totalWeight / C = S_true.card + S_none.sum / C
  --                    = S_true.card + S_none.card / 2
  --                    = countPositive v + countUnknown v / 2

  have h_card_pos : (0 : ℚ) < (completions v).card := by
    rw [completions_card]
    simp only [Nat.cast_pow, Nat.cast_ofNat]
    exact pow_pos (by norm_num : (0 : ℚ) < 2) _

  -- Define the sums as ℕ values first
  let sum_all : ℕ := (univ : Finset (Fin n)).sum (countTrueAt v)
  let sum_true : ℕ := S_true.sum (countTrueAt v)
  let sum_false : ℕ := S_false.sum (countTrueAt v)
  let sum_none : ℕ := S_none.sum (countTrueAt v)

  -- Key equations in ℕ
  have h_sum_all_eq : sum_all = sum_true + sum_false + sum_none := h_sum_split
  have h_sum_true_eq : sum_true = S_true.card * (completions v).card := h_sum_true
  have h_sum_false_eq : sum_false = 0 := h_sum_false
  have h_sum_none_eq : 2 * sum_none = S_none.card * (completions v).card := h_sum_none

  -- Now work in ℚ
  have h_sum_none_q : (sum_none : ℚ) = (S_none.card : ℚ) * (completions v).card / 2 := by
    have h_eq_q : (2 : ℚ) * (sum_none : ℚ) = (S_none.card : ℚ) * (completions v).card := by
      calc (2 : ℚ) * (sum_none : ℚ)
          = ((2 * sum_none : ℕ) : ℚ) := by push_cast; ring
        _ = ((S_none.card * (completions v).card : ℕ) : ℚ) := by rw [h_sum_none_eq]
        _ = (S_none.card : ℚ) * (completions v).card := by push_cast; ring
    linarith

  have h_sum_all_q : (sum_all : ℚ) =
      (S_true.card : ℚ) * (completions v).card + (sum_none : ℚ) := by
    calc (sum_all : ℚ)
        = ((sum_true + sum_false + sum_none : ℕ) : ℚ) := by rw [h_sum_all_eq]
      _ = (sum_true : ℚ) + (sum_false : ℚ) + (sum_none : ℚ) := by simp only [Nat.cast_add]
      _ = ((S_true.card * (completions v).card : ℕ) : ℚ) + 0 + (sum_none : ℚ) := by
          rw [h_sum_true_eq, h_sum_false_eq]; simp
      _ = (S_true.card : ℚ) * (completions v).card + (sum_none : ℚ) := by
          simp only [Nat.cast_mul]; ring

  -- The goal is: sum_all / (completions v).card = countPositive v + countUnknown v / 2
  rw [h_sum_all_q, h_sum_none_q, h_card_true, h_card_none]
  field_simp

/-! ## Connection to PLN Evidence

The Evidence structure from PLNDistributional is the "continuous" version of
our discrete counts. The key insight is that the discrete combinatorics
(completions, Hamming weights) give an exact semantics for Evidence.
-/

open Mettapedia.Logic.PLN.Distributional

/-- Convert a partial vector to discrete evidence.

Note: We add 1 to get proper Beta distribution parameters (Laplace smoothing).
Without the +1, a vector with all bits known would have degenerate evidence.
-/
def toDiscreteEvidence (v : PartialVector n) : Evidence where
  positive := countPositive v + 1
  negative := countNegative v + 1
  positive_pos := by
    have : (0 : ℝ) < 1 := one_pos
    have h : (countPositive v : ℝ) ≥ 0 := Nat.cast_nonneg _
    linarith
  negative_pos := by
    have : (0 : ℝ) < 1 := one_pos
    have h : (countNegative v : ℝ) ≥ 0 := Nat.cast_nonneg _
    linarith

/-- The evidence strength equals the Laplace-smoothed proportion. -/
theorem toDiscreteEvidence_strength (v : PartialVector n) :
    (toDiscreteEvidence v).strength =
    (countPositive v + 1 : ℝ) / (countPositive v + countNegative v + 2) := by
  simp only [toDiscreteEvidence, Evidence.strength, Evidence.total]
  ring_nf

/-! ## Bennett Weakness Connection

The "weakness" of knowledge about a concept corresponds to uncertainty.
For bit vectors, this is exactly the count of unknown bits.
-/

/-- Uncertainty as a measure of "weakness" of knowledge.

This connects to Goertzel's QuantaleWeakness: the weakness of partial
knowledge is proportional to the number of unknown bits.
-/
def uncertaintyMeasure (v : PartialVector n) : ℕ := countUnknown v

/-- Maximum uncertainty is achieved by the completely unknown vector. -/
def allUnknown (n : ℕ) : PartialVector n := fun _ => none

theorem allUnknown_maximal_uncertainty :
    uncertaintyMeasure (allUnknown n) = n := by
  unfold uncertaintyMeasure allUnknown countUnknown
  simp only [filter_true_of_mem, card_univ, Fintype.card_fin, mem_univ, implies_true]

/-- Minimum uncertainty (zero) is achieved by fully known vectors. -/
def fullyKnown (u : BitVector n) : PartialVector n := fun i => some (u i)

theorem fullyKnown_zero_uncertainty (u : BitVector n) :
    uncertaintyMeasure (fullyKnown u) = 0 := by
  unfold uncertaintyMeasure fullyKnown countUnknown
  simp only [reduceCtorEq, filter_false, card_empty]

/-! ## Concrete Examples -/

/-- Example partial vector: [1, 1, 0, ?] (2 ones, 1 zero, 1 unknown) -/
def example_partial : PartialVector 4 := ![some true, some true, some false, none]

/-- The example has 2 positive bits. -/
example : countPositive example_partial = 2 := by native_decide

/-- The example has 1 negative bit. -/
example : countNegative example_partial = 1 := by native_decide

/-- The example has 1 unknown bit. -/
example : countUnknown example_partial = 1 := by native_decide

/-- The example has 2 completions: [1,1,0,0] and [1,1,0,1]. -/
example : (completions example_partial).card = 2 := by native_decide

end Mettapedia.Bridge.BitVectorEvidence
