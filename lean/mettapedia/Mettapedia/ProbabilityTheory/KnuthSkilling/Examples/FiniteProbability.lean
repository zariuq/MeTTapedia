/-
# Finite Probability Spaces: Durrett Chapter 1 Examples

Demonstrates that K&S's `AdditiveValuation` captures standard finite probability theory.
These examples serve as validation that our bridge axioms are correct.

## Examples (from Durrett "Probability: Theory and Examples")

1. **Coin flip**: Ω = {H, T}, uniform measure P({H}) = P({T}) = 1/2
2. **Die roll**: Ω = {1,2,3,4,5,6}, uniform measure P({i}) = 1/6
3. **General uniform**: Ω = Fin n, P(A) = |A|/n
4. **Weighted**: Ω = Fin n with weights p₁,...,pₙ, P(A) = Σᵢ∈A pᵢ

## References

- Durrett, "Probability: Theory and Examples" (5th ed), Section 1.1
- Knuth & Skilling, "Foundations of Inference" (2012)
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic
import Mettapedia.ProbabilityTheory.KnuthSkilling.Bridge

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.Examples

open Classical Finset

/-! ## Set α as a PlausibilitySpace -/

/-- Sets form a PlausibilitySpace (distributive lattice with bounds) -/
instance (α : Type*) : PlausibilitySpace (Set α) := inferInstance

/-! ## Finite Uniform Measure -/

section FiniteUniform

variable {n : ℕ} [NeZero n]

/-- Cardinality of a finite set as a real number -/
noncomputable def setCard (s : Set (Fin n)) : ℝ :=
  (s.toFinset.card : ℝ)

/-- Uniform probability on Fin n: P(A) = |A|/n -/
noncomputable def uniformProb (s : Set (Fin n)) : ℝ :=
  setCard s / n

theorem uniformProb_empty : uniformProb (∅ : Set (Fin n)) = 0 := by
  simp [uniformProb, setCard]

theorem uniformProb_univ : uniformProb (Set.univ : Set (Fin n)) = 1 := by
  unfold uniformProb setCard
  simp only [Set.toFinset_univ, Finset.card_fin]
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  field_simp [hn]

theorem uniformProb_mono : Monotone (uniformProb : Set (Fin n) → ℝ) := by
  intro a b hab
  unfold uniformProb setCard
  have hsub : a.toFinset ⊆ b.toFinset := Set.toFinset_subset_toFinset.mpr hab
  have hcard : a.toFinset.card ≤ b.toFinset.card := Finset.card_le_card hsub
  gcongr

theorem uniformProb_nonneg (s : Set (Fin n)) : 0 ≤ uniformProb s := by
  unfold uniformProb setCard
  positivity

theorem uniformProb_additive {a b : Set (Fin n)} (h : Disjoint a b) :
    uniformProb (a ∪ b) = uniformProb a + uniformProb b := by
  unfold uniformProb setCard
  have hdisj : Disjoint a.toFinset b.toFinset := by
    rw [Set.disjoint_iff] at h
    simp only [Finset.disjoint_iff_ne, Set.mem_toFinset]
    intro x hxa y hyb hxy
    subst hxy
    exact h ⟨hxa, hyb⟩
  rw [Set.toFinset_union, Finset.card_union_of_disjoint hdisj]
  push_cast
  ring

/-- Uniform measure on Fin n is an AdditiveValuation -/
noncomputable def finUniformValuation : AdditiveValuation (Set (Fin n)) where
  val := uniformProb
  monotone := uniformProb_mono
  val_bot := uniformProb_empty
  val_top := uniformProb_univ
  additive_disjoint := uniformProb_additive

end FiniteUniform

/-! ## Coin Flip (Bool) -/

section CoinFlip

/-- Cardinality of a set of Bools -/
noncomputable def boolSetCard (s : Set Bool) : ℝ :=
  (s.toFinset.card : ℝ)

/-- Uniform probability on Bool (coin flip): P(A) = |A|/2 -/
noncomputable def coinProb (s : Set Bool) : ℝ :=
  boolSetCard s / 2

theorem coinProb_empty : coinProb (∅ : Set Bool) = 0 := by
  simp [coinProb, boolSetCard]

theorem coinProb_univ : coinProb (Set.univ : Set Bool) = 1 := by
  unfold coinProb boolSetCard
  simp only [Set.toFinset_univ]
  have h : (Finset.univ : Finset Bool).card = 2 := by decide
  simp only [h, Nat.cast_ofNat, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, div_self]

theorem coinProb_mono : Monotone (coinProb : Set Bool → ℝ) := by
  intro a b hab
  unfold coinProb boolSetCard
  have hsub : a.toFinset ⊆ b.toFinset := Set.toFinset_subset_toFinset.mpr hab
  have hcard : a.toFinset.card ≤ b.toFinset.card := Finset.card_le_card hsub
  gcongr

theorem coinProb_additive {a b : Set Bool} (h : Disjoint a b) :
    coinProb (a ∪ b) = coinProb a + coinProb b := by
  unfold coinProb boolSetCard
  have hdisj : Disjoint a.toFinset b.toFinset := by
    rw [Set.disjoint_iff] at h
    simp only [Finset.disjoint_iff_ne, Set.mem_toFinset]
    intro x hxa y hyb hxy
    subst hxy
    exact h ⟨hxa, hyb⟩
  rw [Set.toFinset_union, Finset.card_union_of_disjoint hdisj]
  push_cast
  ring

/-- Coin flip measure is an AdditiveValuation

Positive example: Fair coin, P({H}) = P({T}) = 1/2, P({H,T}) = 1
Negative example (NOT an AdditiveValuation): Biased "measure" where P({H}) = P({T}) = 1 -/
noncomputable def coinFlipValuation : AdditiveValuation (Set Bool) where
  val := coinProb
  monotone := coinProb_mono
  val_bot := coinProb_empty
  val_top := coinProb_univ
  additive_disjoint := coinProb_additive

/-- P({true}) = 1/2 for a fair coin -/
theorem coinFlip_heads : coinFlipValuation.v {true} = 1/2 := by
  unfold coinFlipValuation coinProb boolSetCard AdditiveValuation.v
  simp only [Set.toFinset_singleton, Finset.card_singleton, Nat.cast_one, one_div]

/-- P({false}) = 1/2 for a fair coin -/
theorem coinFlip_tails : coinFlipValuation.v {false} = 1/2 := by
  unfold coinFlipValuation coinProb boolSetCard AdditiveValuation.v
  simp only [Set.toFinset_singleton, Finset.card_singleton, Nat.cast_one, one_div]

end CoinFlip

/-! ## Die Roll (Fin 6) -/

section DieRoll

/-- Die roll uses the general finite uniform measure -/
noncomputable def dieRollValuation : AdditiveValuation (Set (Fin 6)) :=
  finUniformValuation

/-- P({i}) = 1/6 for a fair die -/
theorem dieRoll_single (i : Fin 6) : dieRollValuation.v {i} = 1/6 := by
  unfold dieRollValuation finUniformValuation uniformProb setCard AdditiveValuation.v
  simp only [Set.toFinset_singleton, Finset.card_singleton, Nat.cast_one]
  norm_num

end DieRoll

/-! ## Weighted Finite Measure -/

section WeightedFinite

variable {n : ℕ}

/-- Weighted probability: P(A) = Σᵢ∈A pᵢ where pᵢ are given weights -/
noncomputable def weightedProb (p : Fin n → ℝ) (s : Set (Fin n)) : ℝ :=
  ∑ i ∈ s.toFinset, p i

theorem weightedProb_empty (p : Fin n → ℝ) : weightedProb p ∅ = 0 := by
  simp [weightedProb]

theorem weightedProb_univ (p : Fin n → ℝ) (h_sum : ∑ i, p i = 1) :
    weightedProb p Set.univ = 1 := by
  simp [weightedProb, h_sum]

theorem weightedProb_mono (p : Fin n → ℝ) (h_nonneg : ∀ i, 0 ≤ p i) :
    Monotone (weightedProb p) := by
  intro a b hab
  unfold weightedProb
  apply Finset.sum_le_sum_of_subset_of_nonneg (Set.toFinset_subset_toFinset.mpr hab)
  intro i _ _
  exact h_nonneg i

theorem weightedProb_additive (p : Fin n → ℝ) {a b : Set (Fin n)} (h : Disjoint a b) :
    weightedProb p (a ∪ b) = weightedProb p a + weightedProb p b := by
  unfold weightedProb
  have hdisj : Disjoint a.toFinset b.toFinset := by
    rw [Set.disjoint_iff] at h
    simp only [Finset.disjoint_iff_ne, Set.mem_toFinset]
    intro x hxa y hyb hxy
    subst hxy
    exact h ⟨hxa, hyb⟩
  rw [Set.toFinset_union, Finset.sum_union hdisj]

/-- Weighted measure is an AdditiveValuation when weights are nonnegative and sum to 1 -/
noncomputable def weightedValuation (p : Fin n → ℝ)
    (h_nonneg : ∀ i, 0 ≤ p i) (h_sum : ∑ i, p i = 1) :
    AdditiveValuation (Set (Fin n)) where
  val := weightedProb p
  monotone := weightedProb_mono p h_nonneg
  val_bot := weightedProb_empty p
  val_top := weightedProb_univ p h_sum
  additive_disjoint := weightedProb_additive p

end WeightedFinite

/-! ## Summary: K&S Captures Classical Finite Probability -/

/--
These examples demonstrate that `AdditiveValuation` correctly captures
classical finite probability theory (Durrett Ch 1):

1. **Coin flip** (`coinFlipValuation`): P({H}) = P({T}) = 1/2
2. **Die roll** (`dieRollValuation`): P({i}) = 1/6 for each face
3. **Uniform finite** (`finUniformValuation`): P(A) = |A|/n
4. **Weighted finite** (`weightedValuation`): P(A) = Σᵢ∈A pᵢ

All satisfy the K&S bridge axioms:
- Monotone: A ⊆ B → P(A) ≤ P(B)
- P(∅) = 0
- P(Ω) = 1
- Additive: A ∩ B = ∅ → P(A ∪ B) = P(A) + P(B)

This validates that our `AdditiveValuation` is the correct bridge between
K&S's abstract framework and classical probability.
-/
theorem finite_probability_is_ks_model :
    (∃ _ : AdditiveValuation (Set Bool), True) ∧
    (∃ _ : AdditiveValuation (Set (Fin 6)), True) := by
  exact ⟨⟨coinFlipValuation, trivial⟩, ⟨dieRollValuation, trivial⟩⟩

end Mettapedia.ProbabilityTheory.KnuthSkilling.Examples
