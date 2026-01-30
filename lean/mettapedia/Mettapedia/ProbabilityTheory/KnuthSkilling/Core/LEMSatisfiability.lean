/-
# LEM Satisfiability in Heyting Algebras: The 2/3 Threshold

## Overview

This file formalizes results from arXiv:2110.11515 "Degree of Satisfiability
in Heyting Algebras" by Bumpus, Kocsis, and Master (2021).

The key result: In a finite non-Boolean Heyting algebra, the probability that
a uniformly random element satisfies x ∨ ¬x = ⊤ is at most 2/3.

Equivalently: If more than 2/3 of elements satisfy LEM, the algebra is Boolean.

## Connection to PLN

This provides a precise threshold for when Evidence "looks Boolean enough":
- If a high proportion of evidence states satisfy excluded middle, classical
  probability rules are approximately valid
- Below 2/3, we're genuinely in Heyting territory

## References

- Bumpus, Kocsis, Master, "Degree of Satisfiability in Heyting Algebras" (2021)
- John Carlos Baez, "The Probability of the Law of Excluded Middle" (2024)
-/

import Mathlib.Order.Heyting.Basic
import Mathlib.Order.Heyting.Regular
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic
import Hammer
import Mettapedia.ProbabilityTheory.KnuthSkilling.Core.RegularityLEMCounterexample

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.Heyting.LEMSatisfiability

/-! ## Basic Definitions -/

variable {α : Type*} [HeytingAlgebra α]

/-- An element satisfies the Law of Excluded Middle if a ⊔ aᶜ = ⊤ -/
def SatisfiesLEM (a : α) : Prop := a ⊔ aᶜ = ⊤

/-- The set of elements satisfying LEM -/
def LEMElements (α : Type*) [HeytingAlgebra α] : Set α :=
  {a | SatisfiesLEM a}

/-- Complemented elements: those with a true complement (not just pseudo-complement) -/
def IsComplemented (a : α) : Prop :=
  ∃ b : α, a ⊔ b = ⊤ ∧ a ⊓ b = ⊥

/-! ## Basic Properties -/

/-- ⊤ always satisfies LEM -/
theorem top_satisfiesLEM : SatisfiesLEM (⊤ : α) := by
  simp [SatisfiesLEM, compl_top]

/-- ⊥ always satisfies LEM -/
theorem bot_satisfiesLEM : SatisfiesLEM (⊥ : α) := by
  simp [SatisfiesLEM, compl_bot]

/-- In a Boolean algebra, ALL elements satisfy LEM -/
theorem boolean_all_satisfyLEM {β : Type*} [BooleanAlgebra β] (a : β) :
    SatisfiesLEM a := by
  simp [SatisfiesLEM, sup_compl_eq_top]

/-- If a satisfies LEM, then aᶜᶜ = a (double negation elimination for that element) -/
theorem compl_compl_of_satisfiesLEM (a : α) (h : SatisfiesLEM a) : aᶜᶜ = a := by
  apply le_antisymm
  · calc aᶜᶜ = aᶜᶜ ⊓ ⊤ := by simp
      _ = aᶜᶜ ⊓ (a ⊔ aᶜ) := by rw [h]
      _ = (aᶜᶜ ⊓ a) ⊔ (aᶜᶜ ⊓ aᶜ) := by rw [inf_sup_left]
      _ = (aᶜᶜ ⊓ a) ⊔ ⊥ := by simp only [inf_comm, inf_compl_eq_bot]
      _ = aᶜᶜ ⊓ a := by simp
      _ ≤ a := inf_le_right
  · exact le_compl_compl

/-! ## The 2/3 Threshold for Finite Heyting Algebras -/

section Finite

variable [Fintype α]

/-- The count of elements satisfying LEM -/
noncomputable def lemCount (α : Type*) [HeytingAlgebra α] [Fintype α] : ℕ :=
  Finset.card (@Finset.filter α (fun a => a ⊔ aᶜ = ⊤)
    (Classical.decPred (fun a : α => a ⊔ aᶜ = ⊤)) Finset.univ)

/-- The degree of LEM satisfiability (as a rational number) -/
noncomputable def lemDegree (α : Type*) [HeytingAlgebra α] [Fintype α] : ℚ :=
  (lemCount α : ℚ) / (Fintype.card α : ℚ)

/-- In a Boolean algebra, the LEM degree is 1 -/
theorem lemDegree_boolean {β : Type*} [BooleanAlgebra β] [Fintype β]
    (_hcard : 0 < Fintype.card β) : lemDegree β = 1 := by
  simp only [lemDegree, lemCount]
  have h : @Finset.filter β (fun a => a ⊔ aᶜ = ⊤) (Classical.decPred _) Finset.univ = Finset.univ := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, sup_compl_eq_top]
  rw [h, Finset.card_univ]
  field_simp

end Finite

/-! ## The 3-Element Chain: Simplest Non-Trivial Heyting Algebra

{⊥ < a < ⊤} is a chain, hence distributive, hence a Heyting algebra.
The middle element does NOT satisfy LEM, giving degree exactly 2/3.
-/

inductive Chain3 : Type
  | bot : Chain3
  | mid : Chain3
  | top : Chain3
  deriving DecidableEq, Fintype

namespace Chain3

open Chain3

/-- Order predicate for Chain3 -/
def le' (a b : Chain3) : Prop := match a, b with
  | bot, _ => True
  | mid, mid => True
  | mid, top => True
  | top, top => True
  | _, _ => False

instance : LE Chain3 := ⟨le'⟩

instance : LT Chain3 where
  lt a b := a ≤ b ∧ ¬b ≤ a

instance : DecidableRel (LE.le (α := Chain3)) := fun a b =>
  match a, b with
  | bot, _ => isTrue trivial
  | mid, mid => isTrue trivial
  | mid, top => isTrue trivial
  | top, top => isTrue trivial
  | mid, bot => isFalse (fun h => h)
  | top, bot => isFalse (fun h => h)
  | top, mid => isFalse (fun h => h)

private theorem le_refl' (a : Chain3) : a ≤ a := by cases a <;> trivial

private theorem le_trans' {a b c : Chain3} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  cases a <;> cases b <;> cases c <;> trivial

private theorem le_antisymm' {a b : Chain3} (hab : a ≤ b) (hba : b ≤ a) : a = b := by
  cases a <;> cases b <;> first | rfl | exact absurd hba (fun h => h) | exact absurd hab (fun h => h)

instance : Preorder Chain3 where
  le_refl := le_refl'
  le_trans := @le_trans'
  lt_iff_le_not_ge _ _ := Iff.rfl

instance : PartialOrder Chain3 where
  le_antisymm := @le_antisymm'

instance : BoundedOrder Chain3 where
  top := top
  le_top a := by cases a <;> trivial
  bot := bot
  bot_le a := trivial

/-- Meet on Chain3 -/
def inf' (a b : Chain3) : Chain3 := match a, b with
  | bot, _ => bot | _, bot => bot
  | mid, mid => mid | mid, top => mid | top, mid => mid
  | top, top => top

/-- Join on Chain3 -/
def sup' (a b : Chain3) : Chain3 := match a, b with
  | top, _ => top | _, top => top
  | mid, mid => mid | mid, bot => mid | bot, mid => mid
  | bot, bot => bot

instance : Lattice Chain3 where
  inf := inf'
  sup := sup'
  inf_le_left a b := by cases a <;> cases b <;> trivial
  inf_le_right a b := by cases a <;> cases b <;> trivial
  le_inf a b c _ _ := by cases a <;> cases b <;> cases c <;> trivial
  le_sup_left a b := by cases a <;> cases b <;> trivial
  le_sup_right a b := by cases a <;> cases b <;> trivial
  sup_le a b c _ _ := by cases a <;> cases b <;> cases c <;> trivial

instance : DistribLattice Chain3 where
  le_sup_inf a b c := by cases a <;> cases b <;> cases c <;> trivial

/-- Heyting implication: x ⇨ y = greatest z such that x ⊓ z ≤ y -/
def himp' (a b : Chain3) : Chain3 := match a, b with
  | _, top => top
  | bot, _ => top
  | mid, mid => top
  | mid, bot => bot
  | top, mid => mid
  | top, bot => bot

/-- Complement: a ⇨ ⊥ -/
def compl' (a : Chain3) : Chain3 := match a with
  | bot => top
  | mid => bot
  | top => bot

instance : HImp Chain3 := ⟨himp'⟩
instance : HasCompl Chain3 := ⟨compl'⟩

instance : HeytingAlgebra Chain3 where
  himp := himp'
  le_himp_iff a b c := by
    cases a <;> cases b <;> cases c <;> decide
  compl := compl'
  himp_bot a := by cases a <;> rfl

/-- The middle element does NOT satisfy LEM: mid ⊔ midᶜ = mid ⊔ ⊥ = mid ≠ ⊤ -/
theorem mid_not_satisfies_lem : ¬SatisfiesLEM (mid : Chain3) := by
  unfold SatisfiesLEM
  intro h
  cases h

/-- ⊥ satisfies LEM -/
theorem chain3_bot_satisfies_lem : SatisfiesLEM (bot : Chain3) := by
  unfold SatisfiesLEM
  rfl

/-- ⊤ satisfies LEM -/
theorem chain3_top_satisfies_lem : SatisfiesLEM (top : Chain3) := by
  unfold SatisfiesLEM
  rfl

/-- Helper: decide satisfiesLEM for Chain3 elements -/
private def chain3_satisfies_lem_dec (a : Chain3) : Decidable (a ⊔ aᶜ = ⊤) :=
  match a with
  | bot => isTrue rfl
  | mid => isFalse (fun h => by cases h)
  | top => isTrue rfl

/-- The LEM count for Chain3 is exactly 2 (only ⊥ and ⊤ satisfy LEM) -/
theorem chain3_lemCount : lemCount Chain3 = 2 := by
  simp only [lemCount]
  -- The filter contains exactly bot and top
  have h : @Finset.filter Chain3 (fun a => a ⊔ aᶜ = ⊤) (Classical.decPred _) Finset.univ =
           {bot, top} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
               Finset.mem_singleton]
    constructor
    · intro hx
      cases x
      · left; rfl
      · -- mid case: mid ⊔ midᶜ = mid ⊔ ⊥ = mid ≠ ⊤
        exfalso; cases hx
      · right; rfl
    · intro hx
      cases hx with
      | inl h => subst h; rfl
      | inr h => subst h; rfl
  rw [h]
  native_decide

/-- Chain3 has exactly 3 elements -/
theorem chain3_card : Fintype.card Chain3 = 3 := by native_decide

/-- **The 2/3 Threshold**: Chain3 achieves exactly 2/3 LEM degree -/
theorem chain3_lemDegree : lemDegree Chain3 = 2/3 := by
  simp only [lemDegree, chain3_lemCount, chain3_card]
  norm_num

/-- Chain3 is NOT Boolean (has non-complemented element) -/
theorem chain3_not_boolean : ∃ a : Chain3, a ⊔ aᶜ ≠ ⊤ := by
  use mid
  intro h
  cases h

end Chain3

/-! ## Structural Lemmas for the 2/3 Bound

Key lemmas about the complement operation in Heyting algebras:
1. Triple complement collapses: aᶜᶜᶜ = aᶜ (from mathlib: `compl_compl_compl`)
2. LEM is preserved by complement
3. Regular elements (a = aᶜᶜ) satisfy LEM
-/

/-- If a satisfies LEM, then aᶜ satisfies LEM -/
theorem satisfiesLEM_compl (a : α) (h : SatisfiesLEM a) : SatisfiesLEM aᶜ := by
  unfold SatisfiesLEM at *
  have hcc : aᶜᶜ = a := compl_compl_of_satisfiesLEM a h
  rw [hcc, sup_comm]
  exact h

/-- If a = aᶜᶜ (a is regular), then a satisfies LEM (in finite Heyting algebras).

    NOTE: This theorem requires finiteness. In infinite Heyting algebras there are
    counterexamples: in the opens of ℝ, (0,1) is regular but (0,1) ⊔ (0,1)ᶜ ≠ ℝ.

    For finite Heyting algebras (as in arXiv:2110.11515):
    - We can show (a ⊔ aᶜ)ᶜ = aᶜ ⊓ a = ⊥ (using de Morgan + regularity)
    - Hence (a ⊔ aᶜ)ᶜᶜ = ⊤
    - In the finite case, the structure ensures a ⊔ aᶜ = ⊤

    Reference: arXiv:2110.11515 Theorem 2.5 -/
theorem satisfiesLEM_of_regular [Fintype α] [DecidableEq α] (a : α) (ha : Heyting.IsRegular a) :
    SatisfiesLEM a := by
  unfold SatisfiesLEM
  -- CONTEXT: This theorem is ONLY for FINITE Heyting algebras.
  --
  -- INFINITE case: DISPROVEN in RegularityLEMCounterexample.lean
  --   - In Opens ℝ, the interval (0,1) is regular but fails LEM
  --   - Proof: (0,1) ∪ (0,1)ᶜ ≠ ℝ (point 0 is in neither)
  --
  -- FINITE case: STATUS UNKNOWN
  --   - Chain3 evidence: All regular elements (⊥, ⊤) DO satisfy LEM
  --   - But this doesn't prove the general finite case
  --
  -- NOTE: The original citation "arXiv:2110.11515 Theorem 2.5" was incorrect.
  -- That paper proves lem_degree ≤ 2/3 but does NOT discuss regular elements.
  --
  -- Partial progress:
  -- - For regular a: (a ⊔ aᶜ)ᶜ = ⊥ (proven)
  -- - Therefore: (a ⊔ aᶜ)ᶜᶜ = ⊤ (proven)
  -- - Cannot conclude a ⊔ aᶜ = ⊤ from this alone
  --
  -- TODO: Either:
  --   1. Find a finite Heyting algebra counterexample (would prove FALSE)
  --   2. Find a proof strategy using finiteness (would prove TRUE)
  --   3. Remove this theorem if unprovable
  sorry

/-- Non-LEM elements satisfy a ≠ aᶜᶜ (in finite Heyting algebras) -/
theorem ne_compl_compl_of_not_satisfiesLEM [Fintype α] [DecidableEq α] (a : α) (h : ¬SatisfiesLEM a) :
    a ≠ aᶜᶜ := by
  intro heq
  -- heq : a = aᶜᶜ means a is regular (Heyting.IsRegular a)
  -- Heyting.IsRegular is defined as aᶜᶜ = a
  exact h (satisfiesLEM_of_regular a heq.symm)

/-! ## Main Theorem: The 2/3 Upper Bound

For any finite non-Boolean Heyting algebra, lemDegree ≤ 2/3.

The proof strategy from the paper:
1. If α is non-Boolean, there exists a ∈ α with a ⊔ aᶜ ≠ ⊤
2. Consider the "LEM-failure" elements: {a | a ⊔ aᶜ ≠ ⊤}
3. Show this set has cardinality at least |α|/3
4. Hence LEM elements have cardinality at most 2|α|/3

This is non-trivial and requires careful analysis of the structure.
For now, we state it as a conjecture and prove the 2/3 is achievable (Chain3).
-/

section Finite
variable [Fintype α]

/-- The 2/3 threshold is achievable: Chain3 achieves exactly 2/3 -/
theorem two_thirds_achievable : ∃ (β : Type) (_ : HeytingAlgebra β) (_ : Fintype β),
    (∃ a : β, a ⊔ aᶜ ≠ ⊤) ∧ @lemDegree β _ _ = 2/3 := by
  exact ⟨Chain3, inferInstance, inferInstance, Chain3.chain3_not_boolean, Chain3.chain3_lemDegree⟩

/-- Conjecture: For any finite non-Boolean Heyting algebra, lemDegree ≤ 2/3
    (This is the main theorem of arXiv:2110.11515) -/
theorem lem_degree_le_two_thirds
    (hNotBoolean : ∃ a : α, a ⊔ aᶜ ≠ ⊤)
    (hCard : 0 < Fintype.card α) :
    lemDegree α ≤ 2/3 := by
  sorry -- Main theorem from the paper, requires significant proof

/-- Contrapositive: If lemDegree > 2/3, the algebra is Boolean -/
theorem boolean_of_lem_degree_gt_two_thirds
    (hCard : 0 < Fintype.card α)
    (hDegree : 2/3 < lemDegree α) :
    ∀ a : α, a ⊔ aᶜ = ⊤ := by
  by_contra h
  push_neg at h
  have := lem_degree_le_two_thirds h hCard
  linarith

end Finite

end Mettapedia.ProbabilityTheory.KnuthSkilling.Heyting.LEMSatisfiability
