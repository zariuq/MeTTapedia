import Mettapedia.UniversalAI.SolomonoffPrior.Basic
import Mettapedia.Computability.KolmogorovComplexity.ReferenceMachine

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

namespace Mettapedia.UniversalAI.SolomonoffPrior

open scoped Classical

/-! ## Part 6: Effective invariance -/

/-- Reference machines agree up to the length of an effective compiler prefix. -/
theorem invariance (U V : KolmogorovComplexity.ReferenceMachine) :
    ∃ c : ℕ, ∀ x : BinString,
      kolmogorovComplexity U x ≤ kolmogorovComplexity V x + c :=
  KolmogorovComplexity.ReferenceMachine.invariance_le U V

/-- Symmetric invariance for inhabited effective reference machines. -/
theorem invariance_symmetric (U V : KolmogorovComplexity.ReferenceMachine) :
    ∃ c : ℕ, ∀ x : BinString,
      |((kolmogorovComplexity U x : ℤ) - kolmogorovComplexity V x)| ≤ c := by
  obtain ⟨c1, h1⟩ := invariance U V
  obtain ⟨c2, h2⟩ := invariance V U
  refine ⟨max c1 c2, fun x => ?_⟩
  have h1' := h1 x
  have h2' := h2 x
  have hcast1 : (kolmogorovComplexity U x : ℤ) ≤ kolmogorovComplexity V x + c1 := by
    exact_mod_cast h1'
  have hcast2 : (kolmogorovComplexity V x : ℤ) ≤ kolmogorovComplexity U x + c2 := by
    exact_mod_cast h2'
  have hmax1 : (c1 : ℤ) ≤ max c1 c2 := by exact_mod_cast le_max_left c1 c2
  have hmax2 : (c2 : ℤ) ≤ max c1 c2 := by exact_mod_cast le_max_right c1 c2
  rw [abs_le]
  omega

/-! ## Part 7: Semimeasure Structure

Two formulations exist:
1. **Prefix-free machines on finite strings** (this file): Computable, sum ≤ 1 by Kraft
2. **Monotone machines on infinite strings** (classical Solomonoff): Natural semimeasure

Both are valuable: (1) for computational theory, (2) for prediction theory.
-/

/-- A semimeasure on binary strings (for INFINITE sequence interpretation).

    **IMPORTANT**: This structure is appropriate for MONOTONE machines producing
    infinite sequences, NOT prefix-free machines producing exact finite outputs!

    - The subadditivity property captures that cylinders partition:
      [x] = [x++0] ∪ [x++1], so μ([x]) ≥ μ([x++0]) + μ([x++1])
    - For finite outputs, this property doesn't make sense
    - See `universal_semimeasure` in Part 8 for the correct theorem
-/
structure Semimeasure where
  μ : BinString → ℝ
  nonneg : ∀ x, 0 ≤ μ x
  root_le_one : μ [] ≤ 1
  subadditive : ∀ x, μ x ≥ μ (x ++ [false]) + μ (x ++ [true])

/-! ### Why Prefix-Free Machines Don't Give Semimeasures

Prefix-free machines produce EXACT finite outputs.
A program that outputs "011" does NOT output "0110" or "0111" - these are
different, disjoint events. Therefore:

- μ(x) = Σ{p | output(p) = x} 2^{-|p|} (sum over programs outputting exactly x)
- μ(x++0) and μ(x++1) have NOTHING to do with μ(x)
- Subadditivity doesn't apply to this setting

**What the finite version DOES satisfy**:
- Non-negativity: μ(x) ≥ 0 ✅
- Kraft bound: Σ_x μ(x) ≤ 1 ✅ (for any finite set of outputs)

**For PLN prediction, use the infinite version** (`MonotoneMachine` + `universal_semimeasure`)!
-/

/-- Partial semimeasure properties for finite outputs.

    Prefix-free machines satisfy non-negativity and the Kraft bound,
    but NOT subadditivity (which requires the infinite interpretation).
-/
theorem algorithmicProbability_partial_properties (U : PrefixFreeMachine)
    (programs : Finset BinString)
    (hpf : PrefixFree (↑programs : Set BinString)) :
    (∀ x, 0 ≤ algorithmicProbability U programs x) ∧
    algorithmicProbability U programs [] ≤ 1 := by
  constructor
  · exact algorithmicProbability_nonneg U programs
  · -- μ([]) ≤ 1 follows from Kraft inequality on programs
    unfold algorithmicProbability
    have kraft := kraft_inequality programs hpf
    calc (programs.filter (fun p => U.compute p = some [])).sum (fun p => (2 : ℝ)^(-(p.length : ℤ)))
        ≤ programs.sum (fun p => (2 : ℝ)^(-(p.length : ℤ))) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact Finset.filter_subset _ _
          · intro p _ _; exact zpow_nonneg (by norm_num) _
      _ = kraftSum programs := rfl
      _ ≤ 1 := kraft

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

/-- Infinite binary sequences as functions ℕ → Bool

This is the standard representation in constructive mathematics:
- Each bit is computable given its index
- Finite prefixes can be observed
- Compatible with Bishop's constructive analysis
-/
abbrev InfBinString := ℕ → Bool

namespace InfBinString

/-- Extract the n-th bit (0-indexed) from an infinite sequence -/
def nth (ω : InfBinString) (n : ℕ) : Bool := ω n

/-- Check if a finite string is a prefix of an infinite sequence -/
def isPrefixOf (x : BinString) (ω : InfBinString) : Prop :=
  ∀ i : Fin x.length, x[i] = ω i

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
  have hi' : (i : ℕ) < (y ++ suffix).length := by simp; omega
  have step := hω (Fin.mk i hi')
  -- Convert using getElem_append_left directly in the goal
  convert step using 1
  exact (List.getElem_append_left i.isLt).symm

/-- Cylinders are disjoint if the strings differ at the last bit -/
theorem cylinder_disjoint_bit (x : BinString) :
    Disjoint (Cylinder (x ++ [false])) (Cylinder (x ++ [true])) := by
  rw [Set.disjoint_iff_inter_eq_empty, Set.eq_empty_iff_forall_notMem]
  intro ω ⟨h0, h1⟩
  unfold Cylinder isPrefixOf at h0 h1
  have hlen0 : x.length < (x ++ [false]).length := by simp
  have hlen1 : x.length < (x ++ [true]).length := by simp
  have eq0 := h0 (Fin.mk x.length hlen0)
  have eq1 := h1 (Fin.mk x.length hlen1)
  -- Prove that (x ++ [false])[x.length]'hlen0 = false
  have eq0_simp : (x ++ [false])[x.length]'hlen0 = false := by simp
  have eq0' : (x ++ [false])[Fin.mk x.length hlen0] = false := eq0_simp
  rw [eq0'] at eq0
  -- Prove that (x ++ [true])[x.length]'hlen1 = true
  have eq1_simp : (x ++ [true])[x.length]'hlen1 = true := by simp
  have eq1' : (x ++ [true])[Fin.mk x.length hlen1] = true := eq1_simp
  rw [eq1'] at eq1
  -- Now we have false = ω ↑⟨x.length, hlen0⟩ and true = ω ↑⟨x.length, hlen1⟩
  simp only at eq0 eq1
  -- Both are ω x.length, so we get false = true
  have : false = true := by rw [eq0, ←eq1]
  exact Bool.false_ne_true this

/-- The cylinders form a partition: [x] = [x++0] ∪ [x++1] -/
theorem cylinder_partition (x : BinString) :
    Cylinder x = Cylinder (x ++ [false]) ∪ Cylinder (x ++ [true]) := by
  ext ω
  constructor
  · intro h
    unfold Cylinder isPrefixOf at *
    by_cases hb : ω x.length = false
    · left
      intro i
      by_cases hi' : i.val < x.length
      · have eq := h (Fin.mk i.val hi')
        calc (x ++ [false])[i]
            = x[i.val]'hi' := List.getElem_append_left hi'
          _ = ω (i.val) := eq
      · have heq : i.val = x.length := by have := i.isLt; simp at this; omega
        have hlen : i.val < (x ++ [false]).length := i.isLt
        have aux : (x ++ [false])[i.val]'hlen = false := by simp [heq]
        have : (x ++ [false])[i] = false := by simpa using aux
        calc (x ++ [false])[i]
            = false := this
          _ = ω x.length := hb.symm
          _ = ω i.val := by rw [heq]
    · right
      push Not at hb
      have h' : ω x.length = true := Bool.eq_true_of_not_eq_false hb
      intro i
      by_cases hi' : i.val < x.length
      · have eq := h (Fin.mk i.val hi')
        calc (x ++ [true])[i]
            = x[i.val]'hi' := List.getElem_append_left hi'
          _ = ω (i.val) := eq
      · have heq : i.val = x.length := by have := i.isLt; simp at this; omega
        have hlen : i.val < (x ++ [true]).length := i.isLt
        have aux : (x ++ [true])[i.val]'hlen = true := by simp [heq]
        have : (x ++ [true])[i] = true := by simpa using aux
        calc (x ++ [true])[i]
            = true := this
          _ = ω x.length := h'.symm
          _ = ω i.val := by rw [heq]
  · intro h
    cases h with
    | inl h0 =>
      unfold Cylinder isPrefixOf at h0
      intro i
      have hi' : i.val < (x ++ [false]).length := by simp_all
      have step := h0 (Fin.mk i.val hi')
      calc x[i]
          = (x ++ [false])[i.val]'hi' := (List.getElem_append_left i.isLt).symm
        _ = ω (i.val) := step
    | inr h1 =>
      unfold Cylinder isPrefixOf at h1
      intro i
      have hi' : i.val < (x ++ [true]).length := by simp_all
      have step := h1 (Fin.mk i.val hi')
      calc x[i]
          = (x ++ [true])[i.val]'hi' := (List.getElem_append_left i.isLt).symm
        _ = ω (i.val) := step

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
  have hi' : i.val < (x ++ [b]).length := by simp_all
  have step := h (Fin.mk i.val hi')
  -- step : U.step p i.val = some (x ++ [b])[i.val]'hi'
  -- goal : U.step p i.val = some x[i]
  convert step using 2
  exact (List.getElem_append_left i.isLt).symm

/-- Programs producing x++0 and x++1 are disjoint -/
theorem produces_append_disjoint (U : MonotoneMachine) (p x : BinString) :
    ¬(U.produces p (x ++ [false]) ∧ U.produces p (x ++ [true])) := by
  intro ⟨h0, h1⟩
  unfold MonotoneMachine.produces at h0 h1
  have hlen0 : x.length < (x ++ [false]).length := by simp
  have hlen1 : x.length < (x ++ [true]).length := by simp
  have eq0 := h0 (Fin.mk x.length hlen0)
  have eq1 := h1 (Fin.mk x.length hlen1)
  -- Prove (x ++ [false])[x.length]'hlen0 = false
  have eq0_simp : (x ++ [false])[x.length]'hlen0 = false := by simp
  have eq0' : (x ++ [false])[Fin.mk x.length hlen0] = false := eq0_simp
  rw [eq0'] at eq0
  -- Prove (x ++ [true])[x.length]'hlen1 = true
  have eq1_simp : (x ++ [true])[x.length]'hlen1 = true := by simp
  have eq1' : (x ++ [true])[Fin.mk x.length hlen1] = true := eq1_simp
  rw [eq1'] at eq1
  -- Simplify Fin coercion
  simp only at eq0 eq1
  -- Now eq0 : U.step p x.length = some false, eq1 : U.step p x.length = some true
  rw [eq0] at eq1
  cases eq1

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
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.notMem_empty, iff_false]
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
          | inl h0 => exact ⟨h0.1, Or.inl h0.2⟩
          | inr h1 => exact ⟨h1.1, Or.inr h1.2⟩

/-- The cylinder measure for the empty string is bounded by 1.

    This follows from the Kraft inequality: all programs produce the empty prefix,
    so cylinderMeasure programs [] = ∑_{p ∈ programs} 2^(-|p|) ≤ 1.
-/
theorem cylinderMeasure_le_one (U : MonotoneMachine) (programs : Finset BinString)
    (hpf : PrefixFree (↑programs : Set BinString)) :
    U.cylinderMeasure programs [] ≤ 1 := by
  unfold MonotoneMachine.cylinderMeasure
  -- All programs produce the empty prefix
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

end Mettapedia.UniversalAI.SolomonoffPrior
