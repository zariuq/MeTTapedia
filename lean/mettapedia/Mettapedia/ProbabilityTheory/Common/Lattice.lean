/-
# Common Lattice Operations

Shared lattice lemmas and operations used across probability theories.
This module provides ADDITIONAL lemmas beyond what mathlib provides,
specifically for probability theory applications.
-/

import Mathlib.Order.Lattice
import Mathlib.Order.BooleanAlgebra.Basic
import Mathlib.Order.Hom.Lattice
import Mathlib.Tactic

namespace Mettapedia.ProbabilityTheory.Common.LatticeOps

/-!
## §1: General Lattice Facts
-/

section GeneralLattice

variable {L : Type*} [Lattice L]

/-- The meet of elements bounded below by x is bounded below by x. -/
theorem inf_le_of_le_left {a b c : L} (h : a ≤ c) : a ⊓ b ≤ c :=
  le_trans inf_le_left h

/-- The meet of elements bounded below by x is bounded below by x. -/
theorem inf_le_of_le_right {a b c : L} (h : b ≤ c) : a ⊓ b ≤ c :=
  le_trans inf_le_right h

/-- Join is monotone in both arguments. -/
theorem sup_mono {a b c d : L} (hac : a ≤ c) (hbd : b ≤ d) : a ⊔ b ≤ c ⊔ d :=
  sup_le_sup hac hbd

/-- Meet is monotone in both arguments. -/
theorem inf_mono {a b c d : L} (hac : a ≤ c) (hbd : b ≤ d) : a ⊓ b ≤ c ⊓ d :=
  inf_le_inf hac hbd

end GeneralLattice

/-!
## §2: Bounded Lattice Facts
-/

section BoundedLattice

variable {L : Type*} [Lattice L] [BoundedOrder L]

/-- Everything is between ⊥ and ⊤. -/
theorem bounded (a : L) : ⊥ ≤ a ∧ a ≤ ⊤ := ⟨bot_le, le_top⟩

end BoundedLattice

/-!
## §3: Distributive Lattice Facts (for K&S)
-/

section DistributiveLattice

variable {L : Type*} [DistribLattice L]

/-- Modularity (consequence of distributivity): if a ≤ c then a ⊔ (b ⊓ c) = (a ⊔ b) ⊓ c. -/
theorem modular_law {a b c : L} (h : a ≤ c) : a ⊔ (b ⊓ c) = (a ⊔ b) ⊓ c := by
  apply le_antisymm
  · apply sup_le
    · exact le_inf le_sup_left h
    · exact inf_le_inf le_sup_right (le_refl c)
  · rw [inf_sup_right]
    apply sup_le
    · exact inf_le_of_le_left le_sup_left
    · exact le_sup_right

end DistributiveLattice

/-!
## §4: Boolean Algebra Facts (for Classical, Cox, D-S)
-/

section BooleanAlgebra

variable {L : Type*} [BooleanAlgebra L]

/-- a and b are disjoint iff a ≤ bᶜ. -/
theorem disjoint_iff_le_compl {a b : L} : a ⊓ b = ⊥ ↔ a ≤ bᶜ := by
  constructor
  · intro h
    calc a = a ⊓ ⊤ := by rw [inf_top_eq]
         _ = a ⊓ (b ⊔ bᶜ) := by rw [sup_compl_eq_top]
         _ = (a ⊓ b) ⊔ (a ⊓ bᶜ) := by rw [inf_sup_left]
         _ = ⊥ ⊔ (a ⊓ bᶜ) := by rw [h]
         _ = a ⊓ bᶜ := by rw [bot_sup_eq]
         _ ≤ bᶜ := _root_.inf_le_right
  · intro h
    apply le_bot_iff.mp
    calc a ⊓ b ≤ bᶜ ⊓ b := inf_le_inf_right b h
         _ = ⊥ := by rw [inf_comm, inf_compl_eq_bot]

end BooleanAlgebra

/-!
## §5: Disjoint Decompositions (for probability)
-/

section DisjointDecomposition

variable {L : Type*} [BooleanAlgebra L]

/-- Any element a can be written as (a ⊓ b) ⊔ (a ⊓ bᶜ). -/
theorem decompose_by (a b : L) : a = (a ⊓ b) ⊔ (a ⊓ bᶜ) := by
  calc a = a ⊓ ⊤ := by rw [inf_top_eq]
       _ = a ⊓ (b ⊔ bᶜ) := by rw [sup_compl_eq_top]
       _ = (a ⊓ b) ⊔ (a ⊓ bᶜ) := by rw [inf_sup_left]

/-- The two parts of the decomposition are disjoint. -/
theorem decompose_disjoint (a b : L) : (a ⊓ b) ⊓ (a ⊓ bᶜ) = ⊥ := by
  calc (a ⊓ b) ⊓ (a ⊓ bᶜ) = a ⊓ (b ⊓ (a ⊓ bᶜ)) := by rw [inf_assoc]
       _ = a ⊓ ((b ⊓ a) ⊓ bᶜ) := by rw [← inf_assoc b a bᶜ]
       _ = a ⊓ ((a ⊓ b) ⊓ bᶜ) := by rw [inf_comm b a]
       _ = a ⊓ (a ⊓ (b ⊓ bᶜ)) := by rw [inf_assoc]
       _ = a ⊓ (a ⊓ ⊥) := by rw [inf_compl_eq_bot]
       _ = a ⊓ ⊥ := by simp
       _ = ⊥ := by simp

/-- Law of total probability setup: a ⊔ b can be decomposed. -/
theorem sup_decompose (a b : L) : a ⊔ b = a ⊔ (b ⊓ aᶜ) := by
  apply le_antisymm
  · apply sup_le le_sup_left
    calc b = (b ⊓ a) ⊔ (b ⊓ aᶜ) := decompose_by b a
         _ ≤ a ⊔ (b ⊓ aᶜ) := sup_le_sup inf_le_right (le_refl _)
  · apply sup_le le_sup_left
    exact le_sup_of_le_right inf_le_left

/-- The new part is disjoint from a. -/
theorem sup_decompose_disjoint (a b : L) : a ⊓ (b ⊓ aᶜ) = ⊥ := by
  apply le_bot_iff.mp
  calc a ⊓ (b ⊓ aᶜ) = (a ⊓ b) ⊓ aᶜ := by rw [inf_assoc, inf_comm b aᶜ, ← inf_assoc]
       _ ≤ a ⊓ aᶜ := inf_le_inf_right aᶜ _root_.inf_le_left
       _ = ⊥ := inf_compl_eq_bot

end DisjointDecomposition

/-!
## §6: Linear Orders (for K&S)
-/

section LinearOrderLattice

variable {L : Type*} [LinearOrder L]

/-- In a linear order, any two elements are comparable. -/
theorem trichotomy (a b : L) : a < b ∨ a = b ∨ b < a := lt_trichotomy a b

/-- In a linear order, min is commutative. -/
theorem min_comm (a b : L) : min a b = min b a := _root_.min_comm a b

/-- In a linear order, max is commutative. -/
theorem max_comm (a b : L) : max a b = max b a := _root_.max_comm a b

end LinearOrderLattice

end Mettapedia.ProbabilityTheory.Common.LatticeOps
