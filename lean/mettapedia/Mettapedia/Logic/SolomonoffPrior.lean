import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Pairwise.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Solomonoff Prior and Algorithmic Probability

This file formalizes the Solomonoff prior (algorithmic probability), following:
- Catt & Norrish (CPP 2021): "On the Formalisation of Kolmogorov Complexity" (HOL4)
- Forster et al. (ITP 2022): "Synthetic Kolmogorov Complexity in Coq"
- Solomonoff (1964): "A Formal Theory of Inductive Inference"

## Overview

The Solomonoff prior M(x) assigns probability to binary strings by summing over
all programs that produce x:

  M(x) = Σ_{p : U(p) = x*} 2^{-|p|}

## References

- Li & Vitányi, "An Introduction to Kolmogorov Complexity and Its Applications"
- Scholarpedia: http://www.scholarpedia.org/article/Algorithmic_probability
-/

namespace Mettapedia.Logic.SolomonoffPrior

open scoped Classical

/-! ## Part 1: Prefix-Free Codes -/

/-- A binary string is a list of booleans -/
abbrev BinString := List Bool

/-- A set of strings is prefix-free if no element is a prefix of another -/
def PrefixFree (S : Set BinString) : Prop :=
  ∀ s ∈ S, ∀ t ∈ S, s ≠ t → ¬(s <+: t)

/-- The empty set is prefix-free -/
theorem prefixFree_empty : PrefixFree ∅ := by
  intro s hs
  exact absurd hs (Set.notMem_empty s)

/-- A singleton is prefix-free -/
theorem prefixFree_singleton (s : BinString) : PrefixFree {s} := by
  intro x hx y hy hne
  simp only [Set.mem_singleton_iff] at hx hy
  rw [hx, hy] at hne
  exact absurd rfl hne

/-- Two disjoint non-prefix strings form a prefix-free set -/
theorem prefixFree_pair (s t : BinString) (hne : s ≠ t)
    (hst : ¬(s <+: t)) (hts : ¬(t <+: s)) : PrefixFree {s, t} := by
  intro x hx y hy hxy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact absurd rfl hxy
  · exact hst
  · exact hts
  · exact absurd rfl hxy

/-! ## Part 2: The Kraft Inequality -/

/-- The Kraft sum for a finite set of strings -/
noncomputable def kraftSum (S : Finset BinString) : ℝ :=
  S.sum (fun s => (2 : ℝ)^(-(s.length : ℤ)))

/-- Kraft sum is nonnegative -/
theorem kraftSum_nonneg (S : Finset BinString) : 0 ≤ kraftSum S := by
  unfold kraftSum
  apply Finset.sum_nonneg
  intro s _
  exact zpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _

/-- Kraft sum of empty set is 0 -/
theorem kraftSum_empty : kraftSum ∅ = 0 := by
  unfold kraftSum
  simp

/-- Kraft sum of singleton -/
theorem kraftSum_singleton (s : BinString) :
    kraftSum {s} = (2 : ℝ)^(-(s.length : ℤ)) := by
  unfold kraftSum
  simp

/-- Each term in Kraft sum is ≤ 1 (since length ≥ 0 means exponent ≤ 0) -/
theorem kraftTerm_le_one (s : BinString) : (2 : ℝ)^(-(s.length : ℤ)) ≤ 1 := by
  have h : (-(s.length : ℤ)) ≤ 0 := by omega
  have h2ge1 : (1 : ℝ) ≤ 2 := by norm_num
  exact zpow_le_one_of_nonpos₀ h2ge1 h

/-- Kraft sum of singleton is ≤ 1 -/
theorem kraftSum_singleton_le_one (s : BinString) : kraftSum {s} ≤ 1 := by
  rw [kraftSum_singleton]
  exact kraftTerm_le_one s

/-! ### Binary Expansion and Interval Mapping -/

open MeasureTheory

/-- Convert a binary string to its real value in [0,1) via binary expansion.
    For s = [b₀, b₁, ..., bₙ₋₁], returns Σᵢ bᵢ · 2^{-(i+1)} -/
noncomputable def binToReal (s : BinString) : ℝ :=
  s.foldr (fun b acc => acc / 2 + if b then (1 : ℝ) / 2 else 0) 0

/-- The dyadic interval corresponding to binary string s -/
noncomputable def dyadicInterval (s : BinString) : Set ℝ :=
  Set.Ico (binToReal s) (binToReal s + (2 : ℝ)^(-(s.length : ℤ)))

/-- binToReal is nonnegative -/
theorem binToReal_nonneg (s : BinString) : 0 ≤ binToReal s := by
  unfold binToReal
  induction s with
  | nil => norm_num
  | cons b t ih =>
    simp only [List.foldr]
    cases b <;> simp <;> linarith [ih]

/-- binToReal is less than 1 -/
theorem binToReal_lt_one (s : BinString) : binToReal s < 1 := by
  unfold binToReal
  induction s with
  | nil => norm_num
  | cons b t ih =>
    simp only [List.foldr]
    cases b <;> simp <;> linarith [ih]

/-- binToReal produces a value in [0, 1) -/
theorem binToReal_bounds (s : BinString) : 0 ≤ binToReal s ∧ binToReal s < 1 := by
  exact ⟨binToReal_nonneg s, binToReal_lt_one s⟩

/-- The dyadic interval fits within [0, 1) -/
theorem binToReal_plus_kraftTerm_le_one (s : BinString) :
    binToReal s + (2 : ℝ)^(-(s.length : ℤ)) ≤ 1 := by
  unfold binToReal
  induction s with
  | nil =>
    simp only [List.foldr, List.length_nil]
    norm_num
  | cons b s ih =>
    simp only [List.foldr, List.length_cons]
    have len_eq : (-(↑(s.length + 1) : ℤ)) = -(s.length : ℤ) + (-1 : ℤ) := by omega
    rw [len_eq, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    simp only [zpow_neg, zpow_one]
    cases b
    · -- b = false: show (r / 2) + (2^(-n) * (1/2)) ≤ 1
      have h1 : (List.foldr (fun b acc => acc / 2 + if b then 1 / 2 else 0) 0 s / 2 +
                 (2 : ℝ)^(-(s.length : ℤ)) * (1 / 2)) =
                (List.foldr (fun b acc => acc / 2 + if b then 1 / 2 else 0) 0 s +
                 (2 : ℝ)^(-(s.length : ℤ))) / 2 := by ring
      calc (List.foldr (fun b acc => acc / 2 + if b then 1 / 2 else 0) 0 s / 2 + 0) +
           (2 ^ s.length)⁻¹ * 2⁻¹
          = List.foldr (fun b acc => acc / 2 + if b then 1 / 2 else 0) 0 s / 2 +
            (2 : ℝ)^(-(s.length : ℤ)) * (1 / 2) := by
              rw [zpow_neg]
              simp only [zpow_natCast]
              ring
        _ = (List.foldr (fun b acc => acc / 2 + if b then 1 / 2 else 0) 0 s +
             (2 : ℝ)^(-(s.length : ℤ))) / 2 := h1
        _ ≤ 1 / 2 := by
            apply div_le_div_of_nonneg_right
            exact ih
            norm_num
        _ ≤ 1 := by norm_num
    · -- b = true: show (r / 2) + (1/2) + (2^(-n) * (1/2)) ≤ 1
      have h2 : (List.foldr (fun b acc => acc / 2 + if b then 1 / 2 else 0) 0 s / 2 + 1 / 2 +
                 (2 : ℝ)^(-(s.length : ℤ)) * (1 / 2)) =
                (List.foldr (fun b acc => acc / 2 + if b then 1 / 2 else 0) 0 s +
                 (2 : ℝ)^(-(s.length : ℤ))) / 2 + 1 / 2 := by ring
      simp only [ite_true]
      calc List.foldr (fun b acc => acc / 2 + if b then 1 / 2 else 0) 0 s / 2 + 1 / 2 +
           (2 ^ s.length)⁻¹ * 2⁻¹
          = List.foldr (fun b acc => acc / 2 + if b then 1 / 2 else 0) 0 s / 2 + 1 / 2 +
            (2 : ℝ)^(-(s.length : ℤ)) * (1 / 2) := by
              rw [zpow_neg]
              simp only [zpow_natCast]
              ring
        _ = (List.foldr (fun b acc => acc / 2 + if b then 1 / 2 else 0) 0 s +
             (2 : ℝ)^(-(s.length : ℤ))) / 2 + 1 / 2 := h2
        _ ≤ 1 / 2 + 1 / 2 := by
            apply add_le_add_right
            apply div_le_div_of_nonneg_right
            exact ih
            norm_num
        _ = 1 := by norm_num

/-- Helper: binToReal is related to append via scaling -/
theorem binToReal_append (s t : BinString) :
    binToReal (s ++ t) = binToReal s + (2 : ℝ)^(-(s.length : ℤ)) * binToReal t := by
  unfold binToReal
  induction s with
  | nil =>
    simp only [List.nil_append, List.length_nil, List.foldr]
    ring
  | cons b s ih =>
    simp only [List.cons_append, List.foldr, List.length_cons]
    rw [ih]
    -- Algebraic manipulation: distribute the /2 through the sum
    have len_eq : (-(↑(s.length + 1) : ℤ)) = -(s.length : ℤ) + (-1 : ℤ) := by omega
    rw [len_eq, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    cases b <;> simp <;> ring

/-- Key lemma: if s is a prefix of t, then interval(t) ⊆ interval(s) -/
theorem prefix_implies_interval_subset (s t : BinString) (h : s <+: t) :
    dyadicInterval t ⊆ dyadicInterval s := by
  unfold dyadicInterval Set.Ico
  intro x hx
  simp only [Set.mem_setOf_eq] at hx ⊢
  obtain ⟨suffix, ht⟩ := h
  -- Rewrite t with s ++ suffix
  rw [← ht, binToReal_append, List.length_append] at hx
  constructor
  · -- Lower bound: binToReal s ≤ binToReal s + 2^{-|s|} * binToReal suffix
    have : 0 ≤ (2 : ℝ)^(-(s.length : ℤ)) * binToReal suffix := by
      apply mul_nonneg
      · exact zpow_nonneg (by norm_num) _
      · exact binToReal_nonneg suffix
    linarith
  · -- Upper bound: x < binToReal s + 2^{-|s|} * binToReal suffix + 2^{-|s ++ suffix|}
    --            → x < binToReal s + 2^{-|s|}
    have key : binToReal suffix + (2 : ℝ)^(-(suffix.length : ℤ)) ≤ 1 := by
      exact binToReal_plus_kraftTerm_le_one suffix
    have mul_bound : (2 : ℝ)^(-(s.length : ℤ)) * (binToReal suffix + (2 : ℝ)^(-(suffix.length : ℤ))) ≤
           (2 : ℝ)^(-(s.length : ℤ)) := by
      apply mul_le_of_le_one_right
      · exact zpow_nonneg (by norm_num) _
      · exact key
    -- Need to show that the exponent in hx.2 equals the product of exponents
    have len_add : (-(↑(s.length + suffix.length) : ℤ)) = -(s.length : ℤ) + -(suffix.length : ℤ) := by omega
    rw [len_add, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)] at hx
    calc x < binToReal s + (2 : ℝ)^(-(s.length : ℤ)) * binToReal suffix +
             (2 : ℝ)^(-(s.length : ℤ)) * (2 : ℝ)^(-(suffix.length : ℤ)) := hx.2
      _ = binToReal s + (2 : ℝ)^(-(s.length : ℤ)) * (binToReal suffix + (2 : ℝ)^(-(suffix.length : ℤ))) := by ring
      _ ≤ binToReal s + (2 : ℝ)^(-(s.length : ℤ)) := by linarith [mul_bound]

/-- If two strings are incomparable, they diverge at some position -/
theorem incomparable_diverge (s t : BinString) (hs : ¬s <+: t) (ht : ¬t <+: s) :
    ∃ (pre : BinString) (bs bt : Bool), bs ≠ bt ∧ (pre ++ [bs]) <+: s ∧ (pre ++ [bt]) <+: t := by
  -- Induction on s generalizing t
  induction s generalizing t with
  | nil =>
    -- s = nil is prefix of everything, contradiction
    exfalso
    exact hs List.nil_prefix
  | cons b₁ s_tail ih =>
    cases t with
    | nil =>
      -- t = nil is prefix of everything, contradiction
      exfalso
      exact ht List.nil_prefix
    | cons b₂ t_tail =>
      by_cases h : b₁ = b₂
      · -- Same first bit, recurse on tails
        subst h
        have hs' : ¬s_tail <+: t_tail := by
          intro hpre
          apply hs
          obtain ⟨w, hw⟩ := hpre
          exact ⟨w, by simp [hw]⟩
        have ht' : ¬t_tail <+: s_tail := by
          intro hpre
          apply ht
          obtain ⟨w, hw⟩ := hpre
          exact ⟨w, by simp [hw]⟩
        obtain ⟨pre, bs, bt, hne, hpres, hpret⟩ := ih t_tail hs' ht'
        refine ⟨b₁ :: pre, bs, bt, hne, ?_, ?_⟩
        · obtain ⟨w1, hw1⟩ := hpres
          exact ⟨w1, by simp [List.cons_append, hw1]⟩
        · obtain ⟨w2, hw2⟩ := hpret
          exact ⟨w2, by simp [List.cons_append, hw2]⟩
      · -- Different first bits - they diverge immediately
        exact ⟨[], b₁, b₂, h,
               ⟨s_tail, by simp⟩,
               ⟨t_tail, by simp⟩⟩

/-- Prefix-free strings have disjoint intervals -/
theorem prefixFree_implies_disjoint (S : Finset BinString) (hpf : PrefixFree ↑S) :
    Set.PairwiseDisjoint (↑S : Set BinString) dyadicInterval := by
  intro s hs t ht hst
  -- Key insight: if intervals overlap, one must be prefix of other
  -- But prefix-free means no string is prefix of another
  by_contra h_not_disjoint
  simp only [Set.disjoint_iff_inter_eq_empty, Set.eq_empty_iff_forall_notMem,
             Set.mem_inter_iff, not_forall, not_not] at h_not_disjoint
  obtain ⟨x, ⟨hxs, hxt⟩⟩ := h_not_disjoint
  -- x is in both intervals
  unfold dyadicInterval Set.Ico at hxs hxt
  simp only [Set.mem_setOf_eq] at hxs hxt
  -- One of s, t must be a prefix of the other
  by_cases h_prefix : s <+: t ∨ t <+: s
  · cases h_prefix with
    | inl hst_prefix =>
      -- s is prefix of t, contradicts prefix-free
      have := hpf s (Finset.mem_coe.mpr hs) t (Finset.mem_coe.mpr ht) hst
      exact this hst_prefix
    | inr hts_prefix =>
      -- t is prefix of s, contradicts prefix-free
      have := hpf t (Finset.mem_coe.mpr ht) s (Finset.mem_coe.mpr hs) (Ne.symm hst)
      exact this hts_prefix
  · -- Neither is prefix of the other: they diverge at some position
    push_neg at h_prefix
    -- Get the divergence point
    obtain ⟨pre, bs, bt, hne, hpres, hpret⟩ := incomparable_diverge s t h_prefix.1 h_prefix.2
    -- The intervals are in different halves after the common prefix
    -- Specifically: s's interval is contained in pre++[bs]'s interval
    --               t's interval is contained in pre++[bt]'s interval
    --               These two intervals are disjoint (one has bit 0, other has bit 1)
    have hs_sub : dyadicInterval s ⊆ dyadicInterval (pre ++ [bs]) :=
      prefix_implies_interval_subset _ _ hpres
    have ht_sub : dyadicInterval t ⊆ dyadicInterval (pre ++ [bt]) :=
      prefix_implies_interval_subset _ _ hpret
    -- Now we need that intervals for pre++[false] and pre++[true] are disjoint
    have disj_01 : Disjoint (dyadicInterval (pre ++ [false])) (dyadicInterval (pre ++ [true])) := by
      rw [Set.disjoint_iff_inter_eq_empty]
      unfold dyadicInterval Set.Ico
      simp only [Set.eq_empty_iff_forall_notMem, Set.mem_inter_iff, Set.mem_setOf_eq, not_and]
      intro y hy
      -- Expand binToReal for singleton lists
      have br_false : binToReal [false] = 0 := by
        unfold binToReal; simp only [List.foldr]; norm_num
      have br_true : binToReal [true] = 1 / 2 := by
        unfold binToReal; simp only [List.foldr]; norm_num
      -- The intervals [a, a+ε/2) and [a+ε/2, a+ε) are disjoint
      rw [binToReal_append, br_false] at hy
      rw [mul_zero, add_zero] at hy
      intro hy_true
      rw [binToReal_append, br_true] at hy_true
      simp only [List.length_append, List.length_cons, List.length_nil] at hy hy_true
      -- The upper bound of [false] interval is the lower bound of [true] interval
      have len_match : (-(↑(List.length pre + (0 + 1)) : ℤ)) = -(pre.length : ℤ) + (-1 : ℤ) := by omega
      rw [len_match, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_neg_one] at hy
      -- y < pre + ε/2 and pre + ε/2 ≤ y leads to contradiction
      linarith [hy.2, hy_true]
    -- Apply disjointness
    -- We know bs ≠ bt, so one is false and one is true
    cases h : bs <;> cases h' : bt
    · -- bs = false, bt = false: contradiction with hne
      simp [h, h'] at hne
    · -- bs = false, bt = true: use disj_01 directly
      simp only [h, h'] at hs_sub ht_sub
      have : x ∈ dyadicInterval (pre ++ [false]) ∩ dyadicInterval (pre ++ [true]) := ⟨hs_sub hxs, ht_sub hxt⟩
      rw [Set.disjoint_iff_inter_eq_empty] at disj_01
      rw [disj_01] at this
      exact this
    · -- bs = true, bt = false: use disj_01.symm
      simp only [h, h'] at hs_sub ht_sub
      have : x ∈ dyadicInterval (pre ++ [true]) ∩ dyadicInterval (pre ++ [false]) := ⟨hs_sub hxs, ht_sub hxt⟩
      rw [Set.disjoint_iff_inter_eq_empty] at disj_01
      rw [Set.inter_comm, disj_01] at this
      exact this
    · -- bs = true, bt = true: contradiction with hne
      simp [h, h'] at hne

/-- Volume of a dyadic interval equals 2^{-|s|} -/
theorem volume_dyadicInterval (s : BinString) :
    volume (dyadicInterval s) = ENNReal.ofReal ((2 : ℝ)^(-(s.length : ℤ))) := by
  unfold dyadicInterval
  rw [Real.volume_Ico]
  simp only [add_sub_cancel_left]

/-- Kraft inequality for prefix-free codes

    **Proof**: Map each string s to dyadic interval [binToReal(s), binToReal(s) + 2^{-|s|}).
    Prefix-free ⟹ disjoint intervals ⟹ sum of measures ≤ volume([0,1)) = 1.
-/
theorem kraft_inequality (S : Finset BinString) (hpf : PrefixFree ↑S) :
    kraftSum S ≤ 1 := by
  -- Strategy: Sum of 2^{-|s|} equals measure of union of disjoint dyadic intervals
  unfold kraftSum

  -- Get disjoint intervals from prefix-free property
  have disj : Set.PairwiseDisjoint (↑S : Set BinString) dyadicInterval :=
    prefixFree_implies_disjoint S hpf

  -- The union of intervals is contained in [0, 1)
  have union_sub : (⋃ s ∈ S, dyadicInterval s) ⊆ Set.Ico (0 : ℝ) 1 := by
    intro x hx
    simp only [Set.mem_iUnion, Set.mem_Ico] at hx ⊢
    obtain ⟨s, hs, hxs⟩ := hx
    unfold dyadicInterval Set.Ico at hxs
    simp only [Set.mem_setOf_eq] at hxs
    have bounds := binToReal_bounds s
    constructor
    · linarith [hxs.1, bounds.1]
    · -- Need: x < binToReal s + 2^{-|s|} ≤ 1
      have key := binToReal_plus_kraftTerm_le_one s
      linarith [hxs.2, key]

  -- Calculate: ∑ s ∈ S, 2^{-|s|} = measure(⋃ s ∈ S, interval(s))
  have sum_eq_measure : (∑ s ∈ S, (2 : ℝ)^(-(s.length : ℤ))) =
      (volume (⋃ s ∈ S, dyadicInterval s)).toReal := by
    -- Use measure_biUnion_finset for disjoint union
    have meas : ∀ s ∈ S, MeasurableSet (dyadicInterval s) := by
      intro s _
      exact measurableSet_Ico
    have meas_union := @MeasureTheory.measure_biUnion_finset ℝ _ _ volume S dyadicInterval disj meas
    have h_ne_top : ∀ a ∈ S, volume (dyadicInterval a) ≠ ⊤ := by
      intro a _
      rw [volume_dyadicInterval]
      exact ENNReal.ofReal_ne_top
    rw [meas_union, ENNReal.toReal_sum h_ne_top]
    congr 1 with s
    rw [volume_dyadicInterval]
    have h_nonneg : 0 ≤ (2 : ℝ)^(-(s.length : ℤ)) := zpow_nonneg (by norm_num) _
    exact (ENNReal.toReal_ofReal h_nonneg).symm

  -- Apply sum_eq_measure and measure bound
  rw [sum_eq_measure]
  -- Measure of union ≤ measure of [0, 1) = 1
  have : volume (⋃ s ∈ S, dyadicInterval s) ≤ volume (Set.Ico (0 : ℝ) 1) :=
    MeasureTheory.measure_mono union_sub
  rw [Real.volume_Ico] at this
  simp only [sub_zero] at this
  have : (volume (⋃ s ∈ S, dyadicInterval s)).toReal ≤ (ENNReal.ofReal 1).toReal := by
    have h_ne_top : ENNReal.ofReal 1 ≠ ⊤ := ENNReal.ofReal_ne_top
    exact ENNReal.toReal_mono h_ne_top this
  simpa using this

/-! ## Part 3: Prefix-Free Machine -/

/-- A partial function from programs to outputs -/
def PartialFun (α β : Type*) := α → Option β

/-- A prefix-free machine: if U(p) halts, no extension of p halts -/
structure PrefixFreeMachine where
  compute : PartialFun BinString BinString
  prefix_free : ∀ p q : BinString, p <+: q → p ≠ q →
    compute p ≠ none → compute q = none

/-- The set of halting programs for a machine is prefix-free -/
theorem haltingPrograms_prefixFree (U : PrefixFreeMachine) :
    PrefixFree { p | U.compute p ≠ none } := by
  intro s hs t ht hne hpref
  simp only [Set.mem_setOf_eq] at hs ht
  exact ht (U.prefix_free s t hpref hne hs)

/-- A universal prefix-free machine can simulate any other -/
class UniversalPFM (U : PrefixFreeMachine) where
  universal : ∀ M : PrefixFreeMachine, ∃ c : ℕ, ∀ p x,
    M.compute p = some x → ∃ q : BinString, U.compute q = some x ∧ q.length ≤ p.length + c

/-! ## Part 4: Algorithmic Probability -/

/-- Algorithmic probability of x given a finite set of programs -/
noncomputable def algorithmicProbability (U : PrefixFreeMachine)
    (programs : Finset BinString) (x : BinString) : ℝ :=
  (programs.filter (fun p => U.compute p = some x)).sum
    (fun p => (2 : ℝ)^(-(p.length : ℤ)))

/-- Algorithmic probability is nonnegative -/
theorem algorithmicProbability_nonneg (U : PrefixFreeMachine)
    (programs : Finset BinString) (x : BinString) :
    0 ≤ algorithmicProbability U programs x := by
  unfold algorithmicProbability
  apply Finset.sum_nonneg
  intro p _
  exact zpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _

/-- Adding a halting program increases algorithmic probability -/
theorem algorithmicProbability_add_program (U : PrefixFreeMachine)
    (programs : Finset BinString) (p : BinString) (x : BinString)
    (hp : p ∉ programs) (hpx : U.compute p = some x) :
    algorithmicProbability U (insert p programs) x =
    algorithmicProbability U programs x + (2 : ℝ)^(-(p.length : ℤ)) := by
  unfold algorithmicProbability
  simp only [Finset.filter_insert, hpx, ↓reduceIte]
  rw [Finset.sum_insert]
  ring
  simp only [Finset.mem_filter]
  intro ⟨hp', _⟩
  exact hp hp'

/-! ## Part 5: Kolmogorov Complexity -/

/-- Programs that compute x -/
def programsFor (U : PrefixFreeMachine) (x : BinString) : Set BinString :=
  { p | U.compute p = some x }

/-- Predicate: there exists a program of length ≤ n that computes x -/
def hasShortProgram (U : PrefixFreeMachine) (x : BinString) (n : ℕ) : Prop :=
  ∃ p : BinString, U.compute p = some x ∧ p.length ≤ n

/-- hasShortProgram is decidable (classically) -/
noncomputable instance : DecidablePred (hasShortProgram U x) := Classical.decPred _

/-- Minimum program length for x (if any program exists) -/
noncomputable def minProgramLength (U : PrefixFreeMachine) (x : BinString)
    (h : ∃ p, U.compute p = some x) : ℕ :=
  Nat.find (p := hasShortProgram U x) ⟨(Classical.choose h).length,
    Classical.choose h, Classical.choose_spec h, le_refl _⟩

/-- Kolmogorov complexity: length of shortest program -/
noncomputable def kolmogorovComplexity (U : PrefixFreeMachine) (x : BinString) : ℕ :=
  if h : ∃ p, U.compute p = some x
  then minProgramLength U x h
  else 0

/-- There exists a program of length K(x) that computes x -/
theorem exists_program_of_complexity (U : PrefixFreeMachine) (x : BinString)
    (h : ∃ p, U.compute p = some x) :
    ∃ p, U.compute p = some x ∧ p.length = kolmogorovComplexity U x := by
  unfold kolmogorovComplexity minProgramLength
  rw [dif_pos h]
  have hfind := Nat.find_spec (p := hasShortProgram U x) ⟨(Classical.choose h).length,
    Classical.choose h, Classical.choose_spec h, le_refl _⟩
  unfold hasShortProgram at hfind
  obtain ⟨p, hp_comp, hp_len⟩ := hfind
  refine ⟨p, hp_comp, ?_⟩
  apply le_antisymm hp_len
  apply Nat.find_min'
  exact ⟨p, hp_comp, le_refl _⟩

/-- Any program for x has length ≥ K(x) -/
theorem complexity_le_program_length (U : PrefixFreeMachine) (x : BinString)
    (p : BinString) (hp : U.compute p = some x) :
    kolmogorovComplexity U x ≤ p.length := by
  unfold kolmogorovComplexity minProgramLength
  rw [dif_pos ⟨p, hp⟩]
  apply Nat.find_min'
  exact ⟨p, hp, le_refl _⟩

/-- M(x) ≥ 2^{-K(x)} when a shortest program is in the set

    The shortest program contributes at least 2^{-K(x)} to the sum.
-/
theorem complexity_probability_bound (U : PrefixFreeMachine)
    (programs : Finset BinString) (x : BinString)
    (_hx : ∃ p, U.compute p = some x)
    (hmin : ∃ p ∈ programs, U.compute p = some x ∧ p.length = kolmogorovComplexity U x) :
    algorithmicProbability U programs x ≥ (2 : ℝ)^(-(kolmogorovComplexity U x : ℤ)) := by
  obtain ⟨prog, hprog_mem, hprog_comp, hprog_len⟩ := hmin
  unfold algorithmicProbability
  rw [ge_iff_le, ← hprog_len]
  have hmem : prog ∈ programs.filter (fun q => U.compute q = some x) := by
    simp only [Finset.mem_filter]; exact ⟨hprog_mem, hprog_comp⟩
  have hnneg : ∀ q ∈ programs.filter (fun q => U.compute q = some x),
      0 ≤ (2 : ℝ)^(-(q.length : ℤ)) := by
    intro q _
    exact zpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  exact Finset.single_le_sum hnneg hmem

/-! ## Part 6: Invariance Theorem -/

/-- Invariance: universal machines agree up to a constant -/
theorem invariance (U V : PrefixFreeMachine) [hU : UniversalPFM U] [hV : UniversalPFM V] :
    ∃ c : ℕ, ∀ x : BinString, ∀ (hx : ∃ p, V.compute p = some x),
      kolmogorovComplexity U x ≤ kolmogorovComplexity V x + c := by
  -- U can simulate V with constant overhead c
  obtain ⟨c, hc⟩ := hU.universal V
  use c
  intro x hx
  -- Get a shortest program for x in V
  obtain ⟨p, hp_comp, hp_len⟩ := exists_program_of_complexity V x hx
  -- U can simulate this program with overhead c
  obtain ⟨q, hq_comp, hq_len⟩ := hc p x hp_comp
  -- So K_U(x) ≤ |q| ≤ |p| + c = K_V(x) + c
  calc kolmogorovComplexity U x
      ≤ q.length := complexity_le_program_length U x q hq_comp
    _ ≤ p.length + c := hq_len
    _ = kolmogorovComplexity V x + c := by rw [hp_len]

/-- Symmetric invariance -/
theorem invariance_symmetric (U V : PrefixFreeMachine)
    [hU : UniversalPFM U] [hV : UniversalPFM V] :
    ∃ c : ℕ, ∀ x : BinString,
      (∃ p, U.compute p = some x) → (∃ q, V.compute q = some x) →
      |((kolmogorovComplexity U x : ℤ) - kolmogorovComplexity V x)| ≤ c := by
  obtain ⟨c1, h1⟩ := invariance U V
  obtain ⟨c2, h2⟩ := invariance V U
  use max c1 c2
  intro x hU_comp hV_comp
  have h1' := h1 x hV_comp
  have h2' := h2 x hU_comp
  rw [abs_le]
  constructor
  · -- K_U - K_V ≥ -c
    have hcast : (kolmogorovComplexity V x : ℤ) ≤ kolmogorovComplexity U x + c2 := by
      exact_mod_cast h2'
    have hmax : (c2 : ℤ) ≤ max c1 c2 := by exact_mod_cast le_max_right c1 c2
    omega
  · -- K_U - K_V ≤ c
    have hcast : (kolmogorovComplexity U x : ℤ) ≤ kolmogorovComplexity V x + c1 := by
      exact_mod_cast h1'
    have hmax : (c1 : ℤ) ≤ max c1 c2 := by exact_mod_cast le_max_left c1 c2
    omega

/-! ## Part 7: Semimeasure Structure

Two formulations exist:
1. **Prefix-free machines on finite strings** (this file): Computable, sum ≤ 1 by Kraft
2. **Monotone machines on infinite strings** (classical Solomonoff): Natural semimeasure

Both are valuable: (1) for computational theory, (2) for prediction theory.
-/

/-- A semimeasure on binary strings (classical definition for infinite strings)

    For finite strings with prefix-free machines, we get additional structure:
    the sum over all strings equals 1, making it a proper probability measure.
-/
structure Semimeasure where
  μ : BinString → ℝ
  nonneg : ∀ x, 0 ≤ μ x
  root_le_one : μ [] ≤ 1
  subadditive : ∀ x, μ x ≥ μ (x ++ [false]) + μ (x ++ [true])

/-- Algorithmic probability forms a semimeasure (requires Kraft inequality) -/
theorem algorithmicProbability_semimeasure (U : PrefixFreeMachine)
    (programs : Finset BinString)
    (hpf : PrefixFree { p ∈ programs | U.compute p ≠ none }) :
    ∃ sm : Semimeasure, ∀ x, sm.μ x ≤ algorithmicProbability U programs x := by
  -- Construct the semimeasure using algorithmic probability itself
  -- The key is showing it satisfies the semimeasure axioms via Kraft inequality
  refine ⟨⟨algorithmicProbability U programs, ?nonneg, ?root, ?sub⟩, fun x => le_refl _⟩
  case nonneg => exact algorithmicProbability_nonneg U programs
  case root =>
    -- μ([]) ≤ 1 follows from Kraft inequality
    unfold algorithmicProbability
    have h_halting := hpf
    -- The set of halting programs is prefix-free
    have programs_pf : PrefixFree { p ∈ programs | U.compute p ≠ none } := hpf
    -- Filter to halting programs
    let halting := programs.filter (fun p => U.compute p ≠ none)
    have halting_pf : PrefixFree (↑halting : Set BinString) := by
      intro s hs t ht hst hpref
      exact programs_pf s hs t ht hst hpref
    -- Apply Kraft inequality
    have kraft := kraft_inequality halting halting_pf
    -- The sum over programs computing [] is ≤ the sum over all halting programs
    calc (halting.filter (fun p => U.compute p = some [])).sum (fun p => (2 : ℝ)^(-(p.length : ℤ)))
        ≤ halting.sum (fun p => (2 : ℝ)^(-(p.length : ℤ))) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact Finset.filter_subset _ _
          · intro p _ _
            exact zpow_nonneg (by norm_num) _
      _ = kraftSum halting := rfl
      _ ≤ 1 := kraft
  case sub =>
    -- μ(x) ≥ μ(x++[false]) + μ(x++[true])
    intro x
    -- NOTE: Subadditivity is subtle for finite strings with prefix-free machines!
    --
    -- Two interpretations:
    -- 1. INFINITE SEQUENCES (classical Solomonoff): Programs output infinite bitstrings,
    --    μ(x) = Σ{p | output(p) starts with x} 2^{-|p|}
    --    Then subadditivity holds naturally: strings starting with x split into
    --    those starting with x++[0] and x++[1]
    --
    -- 2. FINITE OUTPUTS (our current definition): Programs output exact finite strings,
    --    μ(x) = Σ{p | output(p) = x} 2^{-|p|}
    --    Here the relationship is different: a program outputting x cannot output x++[b]
    --    So we need a different formulation or switch to interpretation (1)
    --
    -- For the PLN hypercube, interpretation (1) is more natural.
    -- TODO: Add infinite sequence formulation alongside finite one
    sorry

/-! ## Summary

### Proven (Finite Version - Prefix-Free Machines)
- `prefixFree_empty`, `prefixFree_singleton`, `prefixFree_pair`
- `kraftSum_nonneg`, `kraftSum_empty`, `kraftSum_singleton`, `kraftSum_singleton_le_one`
- `kraftTerm_le_one`
- `binToReal_nonneg`, `binToReal_lt_one`, `binToReal_bounds`, `binToReal_plus_kraftTerm_le_one`
- `binToReal_append` - relates concatenation to binary expansion
- `prefix_implies_interval_subset`, `incomparable_diverge`
- `prefixFree_implies_disjoint` - dyadic intervals are pairwise disjoint
- **`kraft_inequality`** ✅ - Σ 2^{-|s|} ≤ 1 for prefix-free codes (FULLY PROVEN!)
- `haltingPrograms_prefixFree`
- `algorithmicProbability_nonneg`, `algorithmicProbability_add_program`
- `exists_program_of_complexity`, `complexity_le_program_length`
- `complexity_probability_bound` (M(x) ≥ 2^{-K(x)})
- `invariance`, `invariance_symmetric` (universal machines agree up to constant)

### Proven (Infinite Version - Monotone Machines)
- `InfBinString` - coinductive infinite binary sequences
- `cylinder_mono` - cylinder nesting property
- `cylinder_disjoint_bit` - cylinders [x++0] and [x++1] are disjoint
- `cylinder_partition` - [x] = [x++0] ∪ [x++1]
- `cylinderMeasure` - properly defined as sum over producing programs
- `cylinderMeasure_nonneg` - non-negativity
- `produces_append_implies_produces` - monotonicity of production
- `produces_append_disjoint` - programs can't produce both x++0 and x++1
- **`cylinderMeasure_subadditive`** ✅ - μ([x]) ≥ μ([x++0]) + μ([x++1]) (FULLY PROVEN!)
- **`universal_semimeasure`** ✅ - monotone machines yield semimeasures (FULLY PROVEN!)

### Remaining Sorries (1)
- `algorithmicProbability_semimeasure` (finite version) - subadditivity case requires infinite formulation
  - Note: This is resolved by `universal_semimeasure` in Part 8!
-/

/-! ## Part 8: Infinite Sequences and the Universal Semimeasure

Following the "Council's Wisdom":

**The Problem with Finite Strings**: The discrete algorithmic probability μ(x) over finite
strings is useless for prediction because all conditional probabilities are zero.

**The Solution**: Extend to *infinite sequences* using *monotone machines* that continuously
output bits without erasing. This gives:
  1. Natural cylinder sets [x] = {ω : ω starts with x} forming the Scott topology
  2. Automatic subadditivity: [x] ⊇ [x++0] ∪ [x++1]
  3. Constructive measure: μ([x]) = Σ_{p : U(p) extends x} 2^{-|p|}
  4. Practical prediction: P(next bit is b | saw x) = μ([x++b]) / μ([x])

**Bishop's Requirement**: All definitions must be constructive with computational content.
We use coinductive types to observe infinite sequences at finite depth, and define measures
as explicit limits of finite approximations.

**References**:
- Solomonoff (1964): "A Formal Theory of Inductive Inference"
- Hutter (2005): "Universal Artificial Intelligence" (AIXI)
- Li & Vitányi: "An Introduction to Kolmogorov Complexity" (Chapter on semimeasures)
- Weihrauch (2000): "Computable Analysis" (on constructive topology)
-/

/-- Infinite binary sequences (coinductive/lazy streams)

In Lean, we use coinductive types to represent potentially infinite data.
This is constructive: we can observe any finite prefix, but the full sequence
may be infinite.
-/
coinductive InfBinString : Type where
  | cons : Bool → InfBinString → InfBinString

namespace InfBinString

/-- Extract the n-th bit (0-indexed) from an infinite sequence -/
def nth : InfBinString → ℕ → Bool
  | cons b _, 0 => b
  | cons _ tail, n+1 => nth tail n

/-- Check if a finite string is a prefix of an infinite sequence -/
def isPrefixOf (x : BinString) (ω : InfBinString) : Prop :=
  ∀ i : Fin x.length, x[i] = ω.nth i

/-- The cylinder set [x] = {ω ∈ {0,1}^ℕ : x is a prefix of ω}

This is the basic open set in the Scott topology on infinite binary sequences.
In constructive topology, this is a *semidecidable* property: we can confirm
membership by observing enough bits, but may never rule it out.
-/
def Cylinder (x : BinString) : Set InfBinString :=
  {ω | isPrefixOf x ω}

/-- Cylinders are nested: if x extends y, then [x] ⊆ [y] -/
theorem cylinder_mono {x y : BinString} (h : y <+: x) :
    Cylinder x ⊆ Cylinder y := by
  intro ω hω
  unfold Cylinder isPrefixOf at *
  intro i
  obtain ⟨suffix, rfl⟩ := h
  simp only [List.getElem_append]
  have : (i : ℕ) < y.length := i.isLt
  rw [List.getElem_append_left this]
  exact hω ⟨i, by simp only [List.length_append]; omega⟩

/-- Cylinders are disjoint if the strings differ at the last bit -/
theorem cylinder_disjoint_bit (x : BinString) :
    Disjoint (Cylinder (x ++ [false])) (Cylinder (x ++ [true])) := by
  rw [Set.disjoint_iff_inter_eq_empty, Set.eq_empty_iff_forall_notMem]
  intro ω ⟨h0, h1⟩
  unfold Cylinder isPrefixOf at h0 h1
  have : x.length < (x ++ [false]).length := by simp [List.length_append]
  have eq0 : false = ω.nth x.length := h0 ⟨x.length, this⟩
  have eq1 : true = ω.nth x.length := h1 ⟨x.length, by simp [List.length_append]⟩
  simp only [List.getElem_append_right (le_refl x.length),
             Nat.sub_self, List.getElem_cons_zero] at eq0 eq1
  rw [←eq0] at eq1
  exact Bool.false_ne_true eq1

/-- The cylinders form a partition: [x] = [x++0] ∪ [x++1] -/
theorem cylinder_partition (x : BinString) :
    Cylinder x = Cylinder (x ++ [false]) ∪ Cylinder (x ++ [true]) := by
  ext ω
  constructor
  · intro h
    unfold Cylinder isPrefixOf at *
    by_cases hb : ω.nth x.length = false
    · left
      intro ⟨i, hi⟩
      simp only [List.length_append, List.length_cons, List.length_nil] at hi
      by_cases hi' : i < x.length
      · rw [List.getElem_append_left hi']
        exact h ⟨i, hi'⟩
      · have : i = x.length := by omega
        subst this
        simpa [List.getElem_append_right (le_refl _), Nat.sub_self]
    · right
      push_neg at hb
      cases Bool.eq_false_or_eq_true (ω.nth x.length) with
      | inl h' => contradiction
      | inr h' =>
        intro ⟨i, hi⟩
        simp only [List.length_append, List.length_cons, List.length_nil] at hi
        by_cases hi' : i < x.length
        · rw [List.getElem_append_left hi']
          exact h ⟨i, hi'⟩
        · have : i = x.length := by omega
          subst this
          simpa [List.getElem_append_right (le_refl _), Nat.sub_self]
  · intro h
    cases h with
    | inl h0 => exact fun i => h0 ⟨i, by simp at i; omega⟩
    | inr h1 => exact fun i => h1 ⟨i, by simp at i; omega⟩

end InfBinString

/-! ### Monotone Machines

A monotone (or process) machine continuously outputs bits and never erases.
The output is an infinite stream (or stops if the machine halts).

**Constructive Content**: A monotone machine is an algorithm that, given:
  - input program p
  - observation depth n
produces either:
  - some b (the n-th output bit exists and equals b)
  - none (the machine halted or hasn't produced the n-th bit yet)

**Monotonicity**: Once a bit is output, it never changes.
-/
structure MonotoneMachine where
  /-- Compute the n-th bit of output for program p (0-indexed) -/
  step : BinString → ℕ → Option Bool
  /-- Monotonicity: if the n-th bit is produced, earlier bits must be produced -/
  monotone : ∀ p n m b, n < m → step p m = some b → ∃ b', step p n = some b'
  /-- Output never changes: if we've seen bit i, it stays the same -/
  stable : ∀ p n b, step p n = some b → ∀ m ≥ n, ∃ b', step p m = some b' ∧ b' = b

namespace MonotoneMachine

variable (U : MonotoneMachine)

/-- The finite output after n steps -/
def outputPrefix (p : BinString) (n : ℕ) : BinString :=
  List.ofFn (fun i : Fin n => (U.step p i).getD false)

/-- Check if program p produces (at least) output x -/
def produces (p : BinString) (x : BinString) : Prop :=
  ∀ i : Fin x.length, U.step p i = some x[i]

/-- The cylinder measure: sum over programs producing x
    Given a finite set of programs, sum 2^{-|p|} over those producing x -/
noncomputable def cylinderMeasure (programs : Finset BinString) (x : BinString) : ℝ :=
  (programs.filter (fun p => U.produces p x)).sum (fun p => (2 : ℝ)^(-(p.length : ℤ)))

/-- cylinderMeasure is non-negative -/
theorem cylinderMeasure_nonneg (programs : Finset BinString) (x : BinString) :
    0 ≤ U.cylinderMeasure programs x := by
  unfold cylinderMeasure
  apply Finset.sum_nonneg
  intro p _
  exact zpow_nonneg (by norm_num) _

end MonotoneMachine

/-! ### The Universal Semimeasure (Infinite Version)

**Definition**: For monotone machine U and finite string x:
```
  μ([x]) = Σ_{p : U produces x} 2^{-|p|}
```

This is the measure of the cylinder [x] = {ω : ω starts with x}.

**Key Properties** (all provable constructively):
1. **Non-negative**: Obvious from definition
2. **Bounded**: μ([ε]) ≤ 1 by Kraft inequality
3. **Subadditive**: μ([x]) ≥ μ([x++0]) + μ([x++1])
   - Proof: Programs producing x++0 or x++1 are subsets of programs producing x
   - This is AUTOMATIC from monotonicity + cylinder partition!

4. **Prediction**: P(next bit is b | saw x) = μ([x++b]) / μ([x])
   - This is the WHOLE POINT of the construction!
-/

/-- If a program produces x++[b], it must produce x -/
theorem produces_append_implies_produces (U : MonotoneMachine) (p x : BinString) (b : Bool) :
    U.produces p (x ++ [b]) → U.produces p x := by
  intro h
  unfold MonotoneMachine.produces at *
  intro i
  have : i.val < (x ++ [b]).length := by simp; omega
  have := h ⟨i.val, this⟩
  simp only [List.length_append, List.length_cons, List.length_nil,
             List.getElem_append_left i.isLt] at this
  exact this

/-- Programs producing x++0 and x++1 are disjoint -/
theorem produces_append_disjoint (U : MonotoneMachine) (p x : BinString) :
    ¬(U.produces p (x ++ [false]) ∧ U.produces p (x ++ [true])) := by
  intro ⟨h0, h1⟩
  unfold MonotoneMachine.produces at h0 h1
  have : x.length < (x ++ [false]).length := by simp
  have eq0 := h0 ⟨x.length, this⟩
  have eq1 := h1 ⟨x.length, by simp⟩
  simp only [List.getElem_append_right (le_refl _), Nat.sub_self,
             List.getElem_cons_zero] at eq0 eq1
  rw [←eq0] at eq1
  exact Bool.false_ne_true eq1

/-- The subadditivity property for monotone machines -/
theorem cylinderMeasure_subadditive (U : MonotoneMachine) (programs : Finset BinString) (x : BinString) :
    U.cylinderMeasure programs x ≥
    U.cylinderMeasure programs (x ++ [false]) + U.cylinderMeasure programs (x ++ [true]) := by
  unfold MonotoneMachine.cylinderMeasure
  -- The programs producing x++0 are a subset of programs producing x
  have sub0 : programs.filter (fun p => U.produces p (x ++ [false])) ⊆
              programs.filter (fun p => U.produces p x) := by
    intro p hp
    simp only [Finset.mem_filter] at hp ⊢
    exact ⟨hp.1, produces_append_implies_produces U p x false hp.2⟩
  -- Similarly for x++1
  have sub1 : programs.filter (fun p => U.produces p (x ++ [true])) ⊆
              programs.filter (fun p => U.produces p x) := by
    intro p hp
    simp only [Finset.mem_filter] at hp ⊢
    exact ⟨hp.1, produces_append_implies_produces U p x true hp.2⟩
  -- The two program sets are disjoint
  have disj : Disjoint (programs.filter (fun p => U.produces p (x ++ [false])))
                       (programs.filter (fun p => U.produces p (x ++ [true]))) := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    ext p
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.not_mem_empty, iff_false]
    intro ⟨⟨_, h0⟩, ⟨_, h1⟩⟩
    exact produces_append_disjoint U p x ⟨h0, h1⟩
  -- Therefore the sum over x is ≥ sum over x++0 plus sum over x++1
  calc (programs.filter fun p => U.produces p x).sum (fun p => (2 : ℝ) ^ (-(p.length : ℤ)))
      ≥ (programs.filter fun p => U.produces p (x ++ [false]) ∨ U.produces p (x ++ [true])).sum
          (fun p => (2 : ℝ) ^ (-(p.length : ℤ))) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro p hp
          simp only [Finset.mem_filter] at hp ⊢
          cases hp.2 with
          | inl h0 => exact ⟨hp.1, produces_append_implies_produces U p x false h0⟩
          | inr h1 => exact ⟨hp.1, produces_append_implies_produces U p x true h1⟩
        · intro p _ _; exact zpow_nonneg (by norm_num) _
    _ = (programs.filter fun p => U.produces p (x ++ [false])).sum
          (fun p => (2 : ℝ) ^ (-(p.length : ℤ))) +
        (programs.filter fun p => U.produces p (x ++ [true])).sum
          (fun p => (2 : ℝ) ^ (-(p.length : ℤ))) := by
        rw [←Finset.sum_union disj]
        congr 1
        ext p
        simp only [Finset.mem_union, Finset.mem_filter]
        constructor
        · intro ⟨hmem, hor⟩
          cases hor with
          | inl h => exact Or.inl ⟨hmem, h⟩
          | inr h => exact Or.inr ⟨hmem, h⟩
        · intro h
          cases h with
          | inl ⟨hmem, h⟩ => exact ⟨hmem, Or.inl h⟩
          | inr ⟨hmem, h⟩ => exact ⟨hmem, Or.inr h⟩

/-- The main semimeasure theorem for infinite sequences -/
theorem universal_semimeasure (U : MonotoneMachine) (programs : Finset BinString)
    (hpf : PrefixFree (↑programs : Set BinString)) :
    ∃ sm : Semimeasure, ∀ x, sm.μ x = U.cylinderMeasure programs x := by
  refine ⟨⟨U.cylinderMeasure programs, ?nonneg, ?root, ?sub⟩, fun x => rfl⟩
  case nonneg =>
    intro x
    exact U.cylinderMeasure_nonneg programs x
  case root =>
    -- μ([]) ≤ 1 follows from Kraft inequality
    -- All programs produce [] (the empty prefix), so we sum over all programs
    unfold MonotoneMachine.cylinderMeasure
    have : programs.filter (fun p => U.produces p []) = programs := by
      ext p
      simp only [Finset.mem_filter, and_iff_left_iff_imp]
      intro _
      unfold MonotoneMachine.produces
      intro ⟨i, hi⟩
      simp at hi
    rw [this]
    -- Sum over all programs ≤ 1 by Kraft inequality
    have kraft := kraft_inequality programs hpf
    unfold kraftSum at kraft
    exact kraft
  case sub =>
    intro x
    exact cylinderMeasure_subadditive U programs x

/-! ### Connection Between Finite and Infinite Versions

The finite version (prefix-free machines on finite strings) and infinite version
(monotone machines on infinite sequences) are related:

1. **Restriction**: If U is monotone and we ask "does U(p) exactly equal x with no more output",
   we get a prefix-free machine.

2. **Extension**: Every prefix-free machine can be extended to a monotone machine by
   padding the output with zeros (or halting).

3. **Prediction requires infinite version**: Only the infinite version gives meaningful
   conditional probabilities for sequence prediction.

The infinite version is the "correct" foundation for Solomonoff induction and AIXI.
The finite version is a useful special case for studying computability.
-/

end Mettapedia.Logic.SolomonoffPrior
