/-
LLM Context:
- worldToAssignment n w i := (w.val / 2^i.val) % 2 = 1 (bit extraction)
- ENNReal tsub: (a - b) needs care; a + (1 - a) = 1 iff a ≤ 1 via add_tsub_cancel_of_le
- countWorld sums E w for worlds where predicate holds
- totalMass is Finset.univ.sum (worldWeight p)
-/
import Mettapedia.Logic.ProbLogDistributionSemantics
import Mettapedia.Logic.PLNNoisyOr

/-!
# Concrete Biological Instantiation of the ProbLog–WM Bridge

This module instantiates the generic `ProbLogDistributionSemantics` at `n = 3`
for the rejuve-bio gene–SNP hypothesis generation task and proves the
**noisy-OR probability theorem**: for independent probabilistic facts with
probabilities `p_i ≤ 1`, the query probability of "at least one fact is true"
equals the noisy-OR formula `1 - Π(1 - p_i)`.

## Three Biological Mechanisms

The rejuve-bio hypothesis-generation demo uses three independent mechanisms
to predict gene–SNP relevance:

| Index | Mechanism              | ProbLog Weight |
|-------|------------------------|----------------|
| 0     | regulatory_effect      | 0.34           |
| 1     | eQTL_association       | 0.0176         |
| 2     | activity_by_contact    | 0.021          |

A gene is "relevant" to a SNP if **any** mechanism fires → noisy-OR.

## Key Result

```
queryProb_anyTrue_full :
  queryProb p (anyTrue (List.finRange n)) = 1 - Finset.univ.prod (fun i => 1 - p i)
```

This connects the ProbLog distribution semantics (Layer 1) to the concrete
biological model (Layer 2), with the empirical benchmark (Layer 3) consuming
both via the paper.
-/

namespace Mettapedia.Logic.PLNBioHypothesisGeneration

open scoped ENNReal

open Mettapedia.Logic.CompletePLN
open Mettapedia.Logic.PLNJointEvidence
open Mettapedia.Logic.PLNJointEvidence.JointEvidence
open Mettapedia.Logic.ProbLogDistributionSemantics
open Mettapedia.Logic.PLNNoisyOr

/-! ## §1 Bio Model Definitions -/

/-- The three biological mechanisms in the rejuve-bio hypothesis generation demo. -/
abbrev bioN : ℕ := 3

/-- Mechanism 0: regulatory effect (enhancer overlap with gene). -/
abbrev regulatoryEffect : Fin 3 := ⟨0, by omega⟩

/-- Mechanism 1: eQTL association (GTEx tissue-level). -/
abbrev eqtlAssociation : Fin 3 := ⟨1, by omega⟩

/-- Mechanism 2: activity-by-contact (ABC biosample-level). -/
abbrev activityByContact : Fin 3 := ⟨2, by omega⟩

/-- The three ProbLog weights from the rejuve-bio benchmark.
    regulatory_effect: 0.34, eQTL: 0.0176, ABC: 0.021. -/
noncomputable def bioWeights : ProbAssignment 3 := fun i =>
  match i with
  | ⟨0, _⟩ => (34 : ℝ≥0∞) / 100
  | ⟨1, _⟩ => (176 : ℝ≥0∞) / 10000
  | ⟨2, _⟩ => (21 : ℝ≥0∞) / 1000

/-- Gene relevance query: at least one mechanism fires. -/
def geneRelevantQuery : Fin (2 ^ 3) → Bool :=
  anyTrue [regulatoryEffect, eqtlAssociation, activityByContact]

/-- The bio model compiled to a JointEvidence state via ProbLog bridge. -/
noncomputable def bioJointEvidence : JointEvidence 3 :=
  probLogToJointEvidence bioWeights

/-! ## §2 World-Partition Infrastructure

Any Boolean predicate on worlds partitions the total mass into two parts.
This generalizes `propEvidence_total` from single propositions to arbitrary predicates. -/

theorem queryMass_partition (p : ProbAssignment n) (P : Fin (2 ^ n) → Bool) :
    queryMass p P + queryMass p (fun w => !P w) = totalMass p := by
  classical
  let f : Fin (2 ^ n) → ℝ≥0∞ := fun w =>
    if P w then probLogToJointEvidence p w else 0
  let g : Fin (2 ^ n) → ℝ≥0∞ := fun w =>
    if !P w then probLogToJointEvidence p w else 0
  have hfg : (fun w => f w + g w) = probLogToJointEvidence p := by
    funext w
    by_cases hP : P w <;> simp [f, g, hP]
  unfold queryMass totalMass probLogToJointEvidence countWorld total
  calc
    (Finset.univ.sum f + Finset.univ.sum g)
        = Finset.univ.sum (fun w => f w + g w) := by
          simp [Finset.sum_add_distrib]
    _ = Finset.univ.sum (probLogToJointEvidence p) := by simp [hfg]

/-- anyTrue and allFalse partition the worlds (corollary of `queryMass_partition`
    via `anyTrue_eq_not_allFalse`). -/
theorem queryMass_anyTrue_add_allFalse (p : ProbAssignment n)
    (facts : List (Fin n)) :
    queryMass p (anyTrue facts) + queryMass p (allFalse facts) = totalMass p := by
  have h : allFalse facts = fun w => !(anyTrue facts w) := by
    funext w
    rw [anyTrue_eq_not_allFalse]
    simp [Bool.not_not]
  rw [h]
  exact queryMass_partition p (anyTrue facts)

/-! ## §3 Hypercube Infrastructure

To prove `totalMass p = 1` we need the sum-product interchange over the binary
hypercube: the sum of products of independent factor weights equals the product
of marginal sums. -/

/-- World 0 assigns `false` to every proposition. -/
theorem worldToAssignment_zero (n : ℕ) (hn : 0 < 2 ^ n) (i : Fin n) :
    worldToAssignment n ⟨0, hn⟩ i = false := by
  unfold worldToAssignment
  simp

/-- `factWeight` at world 0 yields the complement `1 - p i`. -/
theorem factWeight_zero (p : ProbAssignment n) (hn : 0 < 2 ^ n) (i : Fin n) :
    factWeight p i ⟨0, hn⟩ = 1 - p i := by
  unfold factWeight
  rw [worldToAssignment_zero n hn i]
  simp

/-- `worldWeight` at world 0 is the product of complements. -/
theorem worldWeight_zero (p : ProbAssignment n) (hn : 0 < 2 ^ n) :
    worldWeight p ⟨0, hn⟩ = Finset.univ.prod (fun i => 1 - p i) := by
  unfold worldWeight
  congr 1
  funext i
  exact factWeight_zero p hn i

/-! ### Hypercube decomposition

We decompose `Fin (2^(n+1))` into two halves: worlds where bit `n` is 0 and
worlds where bit `n` is 1. This lets us prove the sum-product interchange
by induction on `n`. -/

/-- The low half embedding: `Fin (2^n) → Fin (2^(n+1))` via identity (bit n = 0). -/
def lowHalf (n : ℕ) (w : Fin (2 ^ n)) : Fin (2 ^ (n + 1)) :=
  ⟨w.val, by omega⟩

/-- The high half embedding: `Fin (2^n) → Fin (2^(n+1))` by adding `2^n` (bit n = 1). -/
def highHalf (n : ℕ) (w : Fin (2 ^ n)) : Fin (2 ^ (n + 1)) :=
  ⟨w.val + 2 ^ n, by omega⟩

/-- Low-half worlds have bit `n` = false. -/
theorem worldToAssignment_lowHalf (n : ℕ) (w : Fin (2 ^ n)) :
    worldToAssignment (n + 1) (lowHalf n w) ⟨n, Nat.lt_succ_iff.mpr le_rfl⟩ = false := by
  unfold worldToAssignment lowHalf
  simp only
  -- Goal: (w.val / 2^n) % 2 = 1 ↔ ... (after decide on Bool)
  -- w.val < 2^n, so w.val / 2^n = 0
  have hw := w.isLt
  have : w.val / 2 ^ n = 0 := Nat.div_eq_of_lt hw
  simp [this]

/-- High-half worlds have bit `n` = true. -/
theorem worldToAssignment_highHalf (n : ℕ) (w : Fin (2 ^ n)) :
    worldToAssignment (n + 1) (highHalf n w) ⟨n, Nat.lt_succ_iff.mpr le_rfl⟩ = true := by
  unfold worldToAssignment highHalf
  simp only
  have hw := w.isLt
  have h2n : 0 < 2 ^ n := Nat.pos_of_ne_zero (by positivity)
  -- (w.val + 2^n) / 2^n = w.val / 2^n + 1 = 0 + 1 = 1
  have hdiv : (w.val + 2 ^ n) / 2 ^ n = 1 := by
    have h1 : w.val / 2 ^ n = 0 := Nat.div_eq_of_lt hw
    rw [Nat.add_div_right _ h2n]
    exact h1 ▸ by omega
  simp [hdiv]

/-- Low-half worlds agree with the original world on bits below `n`. -/
theorem worldToAssignment_lowHalf_lt (n : ℕ) (w : Fin (2 ^ n))
    (i : Fin (n + 1)) (hi : i.val < n) :
    worldToAssignment (n + 1) (lowHalf n w) i =
      worldToAssignment n w ⟨i.val, hi⟩ := by
  unfold worldToAssignment lowHalf
  simp

/-- High-half worlds agree with the original world on bits below `n`. -/
theorem worldToAssignment_highHalf_lt (n : ℕ) (w : Fin (2 ^ n))
    (i : Fin (n + 1)) (hi : i.val < n) :
    worldToAssignment (n + 1) (highHalf n w) i =
      worldToAssignment n w ⟨i.val, hi⟩ := by
  -- Both sides are `decide ((val / 2^i) % 2 = 1)`, just with different val
  unfold worldToAssignment highHalf
  simp only
  -- Goal: decide ((w.val + 2^n) / 2^i.val % 2 = 1) = decide (w.val / 2^i.val % 2 = 1)
  -- After simp, goal involves decide on both sides. Need to show the conditions are the same.
  -- The key: (w.val + 2^n) and w.val have the same bit at position i when i < n
  suffices h : (w.val + 2 ^ n) / 2 ^ i.val % 2 = w.val / 2 ^ i.val % 2 by
    simp [h]
  have h2i : 2 ^ i.val ∣ 2 ^ n := Nat.pow_dvd_pow 2 (by omega)
  rw [Nat.add_div_of_dvd_left h2i]
  -- 2^n / 2^i is even when i < n
  have heven : 2 ∣ (2 ^ n / 2 ^ i.val) := by
    rw [Nat.pow_div (by omega) (by omega)]
    exact dvd_pow_self 2 (by omega)
  obtain ⟨k, hk⟩ := heven
  rw [hk]
  omega

/-- Low and high halves are injective. -/
theorem lowHalf_injective (n : ℕ) : Function.Injective (lowHalf n) := by
  intro a b h
  simp [lowHalf, Fin.ext_iff] at h
  exact Fin.ext h

theorem highHalf_injective (n : ℕ) : Function.Injective (highHalf n) := by
  intro a b h
  simp [highHalf, Fin.ext_iff] at h
  exact Fin.ext (by omega)

/-- Low and high halves are disjoint (different ranges). -/
theorem lowHalf_ne_highHalf (n : ℕ) (a b : Fin (2 ^ n)) :
    lowHalf n a ≠ highHalf n b := by
  simp [lowHalf, highHalf, Fin.ext_iff]
  omega

/-- Every element of `Fin (2^(n+1))` is either in the low or high half. -/
theorem mem_lowHalf_or_highHalf (n : ℕ) (w : Fin (2 ^ (n + 1))) :
    (∃ v : Fin (2 ^ n), lowHalf n v = w) ∨
    (∃ v : Fin (2 ^ n), highHalf n v = w) := by
  by_cases h : w.val < 2 ^ n
  · left; exact ⟨⟨w.val, h⟩, by simp [lowHalf]⟩
  · right
    have hw : w.val - 2 ^ n < 2 ^ n := by omega
    exact ⟨⟨w.val - 2 ^ n, hw⟩, by simp [highHalf, Fin.ext_iff]; omega⟩

/-- `factWeight` for the new bit `n` at a low-half world. -/
theorem factWeight_lowHalf_last (p : ProbAssignment (n + 1)) (w : Fin (2 ^ n)) :
    factWeight p ⟨n, Nat.lt_succ_iff.mpr le_rfl⟩ (lowHalf n w) = 1 - p ⟨n, Nat.lt_succ_iff.mpr le_rfl⟩ := by
  unfold factWeight
  rw [worldToAssignment_lowHalf n w]
  simp

/-- `factWeight` for the new bit `n` at a high-half world. -/
theorem factWeight_highHalf_last (p : ProbAssignment (n + 1)) (w : Fin (2 ^ n)) :
    factWeight p ⟨n, Nat.lt_succ_iff.mpr le_rfl⟩ (highHalf n w) = p ⟨n, Nat.lt_succ_iff.mpr le_rfl⟩ := by
  unfold factWeight
  rw [worldToAssignment_highHalf n w]
  simp

/-- `factWeight` for bits below `n` at a low-half world. -/
theorem factWeight_lowHalf_lt (p : ProbAssignment (n + 1)) (w : Fin (2 ^ n))
    (i : Fin (n + 1)) (hi : i.val < n) :
    factWeight p i (lowHalf n w) =
      factWeight (fun j : Fin n => p ⟨j.val, by omega⟩) ⟨i.val, hi⟩ w := by
  unfold factWeight
  rw [worldToAssignment_lowHalf_lt n w i hi]

/-- `factWeight` for bits below `n` at a high-half world. -/
theorem factWeight_highHalf_lt (p : ProbAssignment (n + 1)) (w : Fin (2 ^ n))
    (i : Fin (n + 1)) (hi : i.val < n) :
    factWeight p i (highHalf n w) =
      factWeight (fun j : Fin n => p ⟨j.val, by omega⟩) ⟨i.val, hi⟩ w := by
  unfold factWeight
  rw [worldToAssignment_highHalf_lt n w i hi]

/-! ### Product decomposition

The worldWeight of a low/high-half world decomposes as the product over the
first `n` bits times the factor for bit `n`. -/

/-- Product over `Fin (n+1)` splits as product over first `n` times the last factor. -/
theorem Finset.prod_fin_succ {α : Type*} [CommMonoid α] (f : Fin (n + 1) → α) :
    Finset.univ.prod f =
      (Finset.univ.prod (fun i : Fin n => f ⟨i.val, by omega⟩)) *
        f ⟨n, Nat.lt_succ_iff.mpr le_rfl⟩ := by
  rw [Fin.prod_univ_castSucc]
  congr 1

/-- worldWeight at a low-half world = (product of first n factors) × (1 - p_n). -/
theorem worldWeight_lowHalf (p : ProbAssignment (n + 1)) (w : Fin (2 ^ n)) :
    worldWeight p (lowHalf n w) =
      worldWeight (fun j : Fin n => p ⟨j.val, by omega⟩) w *
        (1 - p ⟨n, Nat.lt_succ_iff.mpr le_rfl⟩) := by
  unfold worldWeight
  rw [Finset.prod_fin_succ, factWeight_lowHalf_last]
  congr 1

/-- worldWeight at a high-half world = (product of first n factors) × p_n. -/
theorem worldWeight_highHalf (p : ProbAssignment (n + 1)) (w : Fin (2 ^ n)) :
    worldWeight p (highHalf n w) =
      worldWeight (fun j : Fin n => p ⟨j.val, by omega⟩) w *
        p ⟨n, Nat.lt_succ_iff.mpr le_rfl⟩ := by
  unfold worldWeight
  rw [Finset.prod_fin_succ, factWeight_highHalf_last]
  congr 1; congr 1; funext i; exact factWeight_highHalf_lt p w ⟨i.val, by omega⟩ i.isLt

/-! ## §3 Normalization: totalMass = 1

The core theorem: for independent probabilistic facts with `p_i ≤ 1`,
the total mass over all worlds sums to 1. -/

/-- Sum over `Fin (2^(n+1))` decomposes into sum over low half + sum over high half. -/
theorem totalMass_split (p : ProbAssignment (n + 1)) :
    totalMass p =
      (Finset.univ.sum fun w : Fin (2 ^ n) =>
        worldWeight p (lowHalf n w)) +
      (Finset.univ.sum fun w : Fin (2 ^ n) =>
        worldWeight p (highHalf n w)) := by
  unfold totalMass total probLogToJointEvidence
  -- Partition Fin(2^(n+1)) into low half (bit n = 0) and high half (bit n = 1)
  have hdisj : Disjoint (Finset.univ.image (lowHalf n)) (Finset.univ.image (highHalf n)) := by
    rw [Finset.disjoint_iff_ne]
    intro a ha b hb
    rw [Finset.mem_image] at ha hb
    obtain ⟨x, _, hx⟩ := ha
    obtain ⟨y, _, hy⟩ := hb
    rw [← hx, ← hy]
    exact lowHalf_ne_highHalf n x y
  have hcover : Finset.univ.image (lowHalf n) ∪ Finset.univ.image (highHalf n) =
      (Finset.univ : Finset (Fin (2 ^ (n + 1)))) := by
    ext w
    constructor
    · intro _; exact Finset.mem_univ w
    · intro _
      rw [Finset.mem_union, Finset.mem_image, Finset.mem_image]
      rcases mem_lowHalf_or_highHalf n w with ⟨v, hv⟩ | ⟨v, hv⟩
      · left; exact ⟨v, Finset.mem_univ v, hv⟩
      · right; exact ⟨v, Finset.mem_univ v, hv⟩
  rw [← hcover, Finset.sum_union hdisj]
  congr 1 <;>
    rw [Finset.sum_image (by intro a _ b _ h; first | exact lowHalf_injective n h | exact highHalf_injective n h)]

/-- The key inductive step: totalMass factors as (totalMass of first n bits) × (p_n + (1-p_n)). -/
theorem totalMass_factor (p : ProbAssignment (n + 1)) :
    totalMass p =
      totalMass (fun j : Fin n => p ⟨j.val, by omega⟩) *
        (p ⟨n, Nat.lt_succ_iff.mpr le_rfl⟩ + (1 - p ⟨n, Nat.lt_succ_iff.mpr le_rfl⟩)) := by
  rw [totalMass_split]
  simp_rw [worldWeight_lowHalf, worldWeight_highHalf]
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  rw [← mul_add]
  unfold totalMass total probLogToJointEvidence
  ring

/-- For `p_i ≤ 1`: `p_i + (1 - p_i) = 1` in `ℝ≥0∞`. -/
theorem ENNReal_add_tsub_cancel {a : ℝ≥0∞} (ha : a ≤ 1) : a + (1 - a) = 1 := by
  rw [add_comm]
  exact tsub_add_cancel_of_le ha

/-- **Normalization theorem**: The ProbLog total mass equals 1 when all
    probabilities are at most 1. -/
theorem totalMass_eq_one : ∀ (n : ℕ) (p : ProbAssignment n) (_ : ∀ i, p i ≤ 1),
    totalMass p = 1 := by
  intro n
  induction n with
  | zero =>
    intro p _
    unfold totalMass total probLogToJointEvidence worldWeight
    simp [Finset.univ_unique]
  | succ n ih =>
    intro p hp
    rw [totalMass_factor]
    have hpn := hp ⟨n, Nat.lt_succ_iff.mpr le_rfl⟩
    rw [ENNReal_add_tsub_cancel hpn, mul_one]
    exact ih (fun j => p ⟨j.val, by omega⟩) (fun j => hp ⟨j.val, by omega⟩)

/-! ## §4 All-False World Factorization -/

/-- If `worldToAssignment n w i = false` for all `i`, then `w = 0`.
    (Bit-representation uniqueness: the only number with all bits 0 is 0.) -/
-- Helper: if all bits 0..n-1 of a natural number m < 2^n are zero, then m = 0.
private theorem allBitsZero_imp_zero : ∀ (n : ℕ) (m : ℕ), m < 2 ^ n →
    (∀ i : Fin n, (m / 2 ^ i.val) % 2 ≠ 1) → m = 0 := by
  intro n
  induction n with
  | zero => intro m hm _; omega
  | succ n ih =>
    intro m hm hbits
    -- bit 0 is zero: m % 2 ≠ 1
    have hbit0 := hbits ⟨0, Nat.zero_lt_succ n⟩
    simp at hbit0
    -- So m is even: m = 2 * (m / 2)
    have heven : m % 2 = 0 := by omega
    -- m / 2 < 2^n
    have hdiv : m / 2 < 2 ^ n := by
      rw [Nat.div_lt_iff_lt_mul (by norm_num)]
      rw [show 2 ^ n * 2 = 2 ^ (n + 1) from by ring]
      exact hm
    -- All higher bits of m/2 are also zero
    have hbits' : ∀ i : Fin n, (m / 2 / 2 ^ i.val) % 2 ≠ 1 := by
      intro ⟨i, hi⟩
      have h1 := hbits ⟨i + 1, by omega⟩
      -- h1 : (m / 2 ^ (i + 1)) % 2 ≠ 1
      -- 2^(i+1) = 2 * 2^i, so m / 2^(i+1) = m / (2 * 2^i) = m / 2 / 2^i
      simp only at h1
      -- h1 : m / (2^i * 2) % 2 ≠ 1
      -- Goal: m / 2 / 2^i % 2 ≠ 1
      -- These are equal: m / (2^i * 2) = m / (2 * 2^i) = m / 2 / 2^i
      rw [show m / 2 / 2 ^ i = m / (2 ^ i * 2) from by
        rw [mul_comm, Nat.div_div_eq_div_mul]]
      exact h1
    have := ih (m / 2) hdiv hbits'
    omega

theorem world_allFalse_eq_zero (n : ℕ) (hn : 0 < 2 ^ n) (w : Fin (2 ^ n))
    (h : ∀ i : Fin n, worldToAssignment n w i = false) :
    w = ⟨0, hn⟩ := by
  ext
  apply allBitsZero_imp_zero n w.val w.isLt
  intro i
  have := h i
  unfold worldToAssignment at this
  simp at this
  omega

/-- `allFalse` with all facts selects exactly world 0. -/
theorem allFalse_finRange_iff (n : ℕ) (hn : 0 < 2 ^ n) (w : Fin (2 ^ n)) :
    allFalse (List.finRange n) w = true ↔ w = ⟨0, hn⟩ := by
  constructor
  · intro h
    apply world_allFalse_eq_zero n hn w
    intro i
    -- allFalse checks that all listed facts are false in world w
    unfold allFalse at h
    rw [List.all_eq_true] at h
    have hi := h i (List.mem_finRange i)
    -- hi : !(worldToAssignment n w i) = true
    simpa using hi
  · intro h
    subst h
    simp only [allFalse, List.all_eq_true]
    intro i _
    -- Goal: !(worldToAssignment n 0 i) = true, i.e., worldToAssignment n 0 i = false
    unfold worldToAssignment
    simp

/-- The mass of worlds where all facts (from `finRange n`) are false equals
    the world weight at world 0, which is `Π(1 - p_i)`. -/
theorem queryMass_allFalse_finRange (p : ProbAssignment n) (hn : 0 < 2 ^ n) :
    queryMass p (allFalse (List.finRange n)) =
      Finset.univ.prod (fun i => 1 - p i) := by
  unfold queryMass countWorld probLogToJointEvidence
  -- Rewrite using the iff characterization of allFalse
  have key : ∀ w : Fin (2 ^ n),
      (if allFalse (List.finRange n) w = true then worldWeight p w else 0) =
      (if w = ⟨0, hn⟩ then worldWeight p w else 0) := by
    intro w
    congr 1
    exact propext (allFalse_finRange_iff n hn w)
  simp_rw [key]
  rw [Finset.sum_eq_single ⟨0, hn⟩
    (fun w _ hw => by split_ifs with h <;> [exact absurd h hw; rfl])
    (fun h => absurd (Finset.mem_univ _) h)]
  simp
  exact worldWeight_zero p hn

/-! ## §5 Main Noisy-OR Probability Theorem -/

/-- **Main theorem**: For independent probabilistic facts with `p_i ≤ 1`,
    the probability that at least one fact is true equals the noisy-OR formula.

    `queryProb p (anyTrue all) = 1 - Π(1 - p_i)` -/
theorem queryProb_anyTrue_full (p : ProbAssignment n) (hp : ∀ i, p i ≤ 1)
    (hn : 0 < 2 ^ n) :
    queryProb p (anyTrue (List.finRange n)) =
      1 - Finset.univ.prod (fun i => 1 - p i) := by
  -- Step 1: totalMass = 1
  have htot : totalMass p = 1 := totalMass_eq_one n p hp
  -- Step 2: anyTrue mass + allFalse mass = totalMass = 1
  have hpart := queryMass_anyTrue_add_allFalse p (List.finRange n)
  -- Step 3: allFalse mass = Π(1 - p_i)
  have hallf := queryMass_allFalse_finRange p hn
  -- Step 4: queryProb = queryMass / totalMass = queryMass / 1 = queryMass
  unfold queryProb
  rw [htot, div_one]
  -- Step 5: queryMass(anyTrue) = 1 - Π(1 - p_i)
  -- From hpart: queryMass(anyTrue) + Π(1-p_i) = 1
  rw [hallf, htot] at hpart
  -- From hpart: queryMass(anyTrue) + Π(1-p_i) = 1
  -- We need: 1 - Π(1-p_i) + Π(1-p_i) = 1, then use injectivity
  -- Actually: a + b = c → a = c - b when b ≤ c (in ENNReal)
  have hprod_le : Finset.univ.prod (fun i => 1 - p i) ≤ 1 := by
    calc Finset.univ.prod (fun i => 1 - p i)
        = queryMass p (allFalse (List.finRange n)) := hallf.symm
      _ ≤ totalMass p := by
          rw [← queryMass_anyTrue_add_allFalse p (List.finRange n)]
          exact le_add_left le_rfl
      _ = 1 := htot
  -- From: queryMass + prod = 1 and prod ≤ 1:
  -- queryMass = 1 - prod
  -- hpart : queryMass + prod = 1
  -- Goal : queryMass = 1 - prod
  -- Prove: prod ≤ 1
  have hprod_le : Finset.univ.prod (fun i => 1 - p i) ≤ 1 := by
    calc Finset.univ.prod (fun i => 1 - p i)
        = queryMass p (allFalse (List.finRange n)) := hallf.symm
      _ ≤ totalMass p := by
          rw [← queryMass_anyTrue_add_allFalse p (List.finRange n)]
          exact le_add_left le_rfl
      _ = 1 := htot
  -- Use WithTop.add_right_cancel (ENNReal = WithTop NNReal)
  -- queryMass + prod = 1 and (1 - prod) + prod = 1, prod ≠ ⊤
  have hprod_ne_top : Finset.univ.prod (fun i => 1 - p i) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hprod_le
  have key : (1 : ℝ≥0∞) - Finset.univ.prod (fun i => 1 - p i) +
      Finset.univ.prod (fun i => 1 - p i) = 1 :=
    tsub_add_cancel_of_le hprod_le
  exact WithTop.add_right_cancel hprod_ne_top (hpart.trans key.symm)

/-! ## §6 Concrete Bio Instantiation -/

theorem bioWeights_le_one : ∀ i : Fin 3, bioWeights i ≤ 1 := by
  intro i
  fin_cases i <;> simp [bioWeights]
  · -- 34 / 100 ≤ 1 in ℝ≥0∞
    exact ENNReal.div_le_of_le_mul (by norm_num : (34 : ℝ≥0∞) ≤ 1 * 100)
  · exact ENNReal.div_le_of_le_mul (by norm_num : (176 : ℝ≥0∞) ≤ 1 * 10000)
  · exact ENNReal.div_le_of_le_mul (by norm_num : (21 : ℝ≥0∞) ≤ 1 * 1000)

/-- The gene-relevance probability for the bio model satisfies the noisy-OR formula. -/
theorem bioGeneRelevance_eq_noisyOr :
    queryProb bioWeights geneRelevantQuery =
      1 - Finset.univ.prod (fun i : Fin 3 => 1 - bioWeights i) := by
  -- geneRelevantQuery = anyTrue [0, 1, 2] and [0, 1, 2] = List.finRange 3
  have hq : geneRelevantQuery = anyTrue (List.finRange 3) := by
    unfold geneRelevantQuery regulatoryEffect eqtlAssociation activityByContact
    unfold anyTrue
    funext w
    simp [List.finRange, List.any]
  rw [hq]
  exact queryProb_anyTrue_full bioWeights bioWeights_le_one (by norm_num)

/-- The bio model's WM queryStrength (via the ProbLog bridge) equals its noisy-OR probability. -/
theorem bioQueryStrength_eq_noisyOr :
    Mettapedia.Logic.EvidenceQuantale.BinaryEvidence.toStrength
      (propEvidence (n := 3) (E := bioJointEvidence) regulatoryEffect) =
    queryProb bioWeights (fun w => worldToAssignment 3 w regulatoryEffect) := by
  exact queryStrength_prop_eq_queryProb bioWeights regulatoryEffect

/-! ## §7 toReal Bridge: ℝ≥0∞ → ℝ

Connect the ℝ≥0∞-valued `queryProb` to the ℝ-valued `noisyOrMulti` from PLNNoisyOr. -/

/-- The complement product `Π(1 - p_i)` is at most 1 and hence finite. -/
private theorem prod_compl_le_one (p : ProbAssignment n) (_ : ∀ i, p i ≤ 1) :
    Finset.univ.prod (fun i => 1 - p i) ≤ 1 :=
  Finset.prod_le_one (fun i _ => zero_le _) (fun i _ => tsub_le_self)

private theorem prod_compl_ne_top (p : ProbAssignment n) (hp : ∀ i, p i ≤ 1) :
    Finset.univ.prod (fun i => 1 - p i) ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (prod_compl_le_one p hp)

/-- `List.foldl (· * (1-·)) 1` over `List.ofFn f` equals `Finset.univ.prod (1 - f ·)`. -/
theorem foldl_oneSub_ofFn_eq_prod (f : Fin n → ℝ) :
    (List.ofFn f).foldl (fun acc s => acc * (1 - s)) 1 =
      Finset.univ.prod (fun i : Fin n => 1 - f i) := by
  induction n with
  | zero => simp [List.ofFn, Finset.univ_eq_empty]
  | succ n ih =>
    rw [List.ofFn_succ, List.foldl_cons]
    rw [foldl_mul_one_sub_init]
    rw [ih (fun i => f i.succ)]
    rw [Fin.prod_univ_succ]
    ring

/-- `noisyOrMulti` applied to `List.ofFn` equals the complement-product formula. -/
theorem noisyOrMulti_ofFn_eq (f : Fin n → ℝ) :
    noisyOrMulti (List.ofFn f) = 1 - Finset.univ.prod (fun i => 1 - f i) := by
  unfold noisyOrMulti
  rw [foldl_oneSub_ofFn_eq_prod]

/-- **toReal bridge**: The ℝ≥0∞ query probability, converted to ℝ, equals `noisyOrMulti`
    applied to the real-valued probabilities. -/
theorem queryProb_anyTrue_toReal_eq_noisyOrMulti
    (p : ProbAssignment n) (hp : ∀ i, p i ≤ 1) (hn : 0 < 2 ^ n) :
    (queryProb p (anyTrue (List.finRange n))).toReal =
      noisyOrMulti (List.ofFn (fun i : Fin n => (p i).toReal)) := by
  rw [queryProb_anyTrue_full p hp hn]
  rw [noisyOrMulti_ofFn_eq]
  -- Goal: (1 - Π(1 - p_i)).toReal = 1 - Π(1 - (p_i).toReal)
  have hprod_le : Finset.univ.prod (fun i => 1 - p i) ≤ 1 := prod_compl_le_one p hp
  rw [ENNReal.toReal_sub_of_le hprod_le ENNReal.one_ne_top]
  simp only [ENNReal.toReal_one, ENNReal.toReal_prod]
  congr 1
  congr 1
  funext i
  exact ENNReal.toReal_sub_of_le (hp i) ENNReal.one_ne_top

/-! ## §8 Parameter-Learning Bridge

When ProbLog weights match PLN evidence strengths, the distribution-semantics
query probability equals the noisy-OR computed directly from evidence counts. -/

open Mettapedia.Logic.EvidenceQuantale in
/-- When ProbLog weights equal empirical evidence strengths, the distribution-semantics
    noisy-OR probability agrees with the evidence-calculus noisy-OR. -/
theorem queryProb_from_evidence
    (evidence : Fin n → BinaryEvidence)
    (p : ProbAssignment n)
    (hp_match : ∀ i, p i = BinaryEvidence.toStrength (evidence i))
    (hp_le : ∀ i, p i ≤ 1) (hn : 0 < 2 ^ n) :
    (queryProb p (anyTrue (List.finRange n))).toReal =
      noisyOrMulti (List.ofFn (fun i => (BinaryEvidence.toStrength (evidence i)).toReal)) := by
  have h := queryProb_anyTrue_toReal_eq_noisyOrMulti p hp_le hn
  simp only [hp_match] at h
  exact h

open Mettapedia.Logic.EvidenceQuantale in
/-- Concrete bio instantiation: when the 3 ProbLog weights match evidence strengths,
    the WM noisy-OR score equals the PLN benchmark's noisy-OR. -/
theorem bio_queryProb_from_evidence
    (evidence : Fin 3 → BinaryEvidence)
    (hp_match : ∀ i, bioWeights i = BinaryEvidence.toStrength (evidence i)) :
    (queryProb bioWeights geneRelevantQuery).toReal =
      noisyOrMulti (List.ofFn (fun i : Fin 3 => (BinaryEvidence.toStrength (evidence i)).toReal)) := by
  have hq : geneRelevantQuery = anyTrue (List.finRange 3) := by
    unfold geneRelevantQuery regulatoryEffect eqtlAssociation activityByContact anyTrue
    funext w; simp [List.finRange, List.any]
  rw [hq]
  exact queryProb_from_evidence evidence bioWeights hp_match bioWeights_le_one (by norm_num)

#check @queryProb_anyTrue_full
#check @totalMass_eq_one
#check @bioGeneRelevance_eq_noisyOr
#check @queryProb_anyTrue_toReal_eq_noisyOrMulti
#check @queryProb_from_evidence

end Mettapedia.Logic.PLNBioHypothesisGeneration
