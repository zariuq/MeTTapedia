import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

/-!
# Inclusion-Exclusion Identifiability Limits (Counterexample)

Chapter-9-style multideduction heuristics often use the first two inclusion-exclusion
terms plus a correction. This file proves a concrete finite counterexample:

- two event triples have identical first two terms,
- but different union cardinalities,

so the union cannot be determined from first-two-term statistics alone.
-/

namespace Mettapedia.Logic.PLNInclusionExclusionIdentifiability

/-! ## Two-term inclusion-exclusion statistics (cardinality form) -/

def ieTerm1 {α : Type*} [DecidableEq α] (A B C : Finset α) : Nat :=
  A.card + B.card + C.card

def ieTerm2 {α : Type*} [DecidableEq α] (A B C : Finset α) : Nat :=
  (A ∩ B).card + (A ∩ C).card + (B ∩ C).card

def ieTwoTermApprox {α : Type*} [DecidableEq α] (A B C : Finset α) : Nat :=
  ieTerm1 A B C - ieTerm2 A B C

def unionCard {α : Type*} [DecidableEq α] (A B C : Finset α) : Nat :=
  (A ∪ B ∪ C).card

/-! ## Concrete finite witness on a shared universe `Fin 4` -/

abbrev Omega := Fin 4

def A1 : Finset Omega := {0, 1}
def B1 : Finset Omega := {0, 2}
def C1 : Finset Omega := {0, 3}

def A2 : Finset Omega := {0, 1}
def B2 : Finset Omega := {1, 2}
def C2 : Finset Omega := {0, 2}

lemma first_model_values :
    ieTerm1 A1 B1 C1 = 6
      ∧ ieTerm2 A1 B1 C1 = 3
      ∧ ieTwoTermApprox A1 B1 C1 = 3
      ∧ unionCard A1 B1 C1 = 4 := by
  decide

lemma second_model_values :
    ieTerm1 A2 B2 C2 = 6
      ∧ ieTerm2 A2 B2 C2 = 3
      ∧ ieTwoTermApprox A2 B2 C2 = 3
      ∧ unionCard A2 B2 C2 = 3 := by
  decide

theorem same_first_two_terms_different_union :
    ieTerm1 A1 B1 C1 = ieTerm1 A2 B2 C2
      ∧ ieTerm2 A1 B1 C1 = ieTerm2 A2 B2 C2
      ∧ unionCard A1 B1 C1 ≠ unionCard A2 B2 C2 := by
  decide

/-! ## Counterexample: no universal predictor from first-two-term stats -/

theorem no_universal_union_predictor_from_first_two_terms :
    ¬ ∃ F : Nat → Nat → Nat,
        ∀ A B C : Finset Omega, unionCard A B C = F (ieTerm1 A B C) (ieTerm2 A B C) := by
  intro h
  rcases h with ⟨F, hF⟩
  have hA1 := hF A1 B1 C1
  have hA2 := hF A2 B2 C2
  have hT1 : ieTerm1 A1 B1 C1 = ieTerm1 A2 B2 C2 := by decide
  have hT2 : ieTerm2 A1 B1 C1 = ieTerm2 A2 B2 C2 := by decide
  have hUneq : unionCard A1 B1 C1 ≠ unionCard A2 B2 C2 := by decide
  have hUeq : unionCard A1 B1 C1 = unionCard A2 B2 C2 := by
    calc
      unionCard A1 B1 C1 = F (ieTerm1 A1 B1 C1) (ieTerm2 A1 B1 C1) := hA1
      _ = F (ieTerm1 A2 B2 C2) (ieTerm2 A2 B2 C2) := by simp [hT1, hT2]
      _ = unionCard A2 B2 C2 := hA2.symm
  exact hUneq hUeq

/-! ## Counterexample: no single additive correction for both models -/

theorem no_single_additive_correction_for_both_models :
    ¬ ∃ xi : Nat,
        unionCard A1 B1 C1 = ieTwoTermApprox A1 B1 C1 + xi
          ∧ unionCard A2 B2 C2 = ieTwoTermApprox A2 B2 C2 + xi := by
  rintro ⟨xi, h1, h2⟩
  have hU1 : unionCard A1 B1 C1 = 4 := by decide
  have hU2 : unionCard A2 B2 C2 = 3 := by decide
  have hI1 : ieTwoTermApprox A1 B1 C1 = 3 := by decide
  have hI2 : ieTwoTermApprox A2 B2 C2 = 3 := by decide
  have h1' : 4 = 3 + xi := by simpa [hU1, hI1] using h1
  have h2' : 3 = 3 + xi := by simpa [hU2, hI2] using h2
  have h2'' : 3 + xi = 3 + 0 := by simpa using h2'
  have hxi0 : xi = 0 := Nat.add_left_cancel h2''
  have h1'' : 4 = 3 + 0 := by
    rw [hxi0] at h1'
    exact h1'
  have h43 : (4 : Nat) = 3 := by
    calc
      (4 : Nat) = 3 + 0 := h1''
      _ = 3 := by simp
  exact (by decide : (4 : Nat) ≠ 3) h43

/-! ## Probability-form corollary on the shared denominator `|Omega| = 4` -/

def probCard (S : Finset Omega) : ℚ :=
  (S.card : ℚ) / 4

theorem same_first_two_terms_different_union_probabilities :
    ((ieTerm1 A1 B1 C1 : ℚ) / 4) = ((ieTerm1 A2 B2 C2 : ℚ) / 4)
      ∧ ((ieTerm2 A1 B1 C1 : ℚ) / 4) = ((ieTerm2 A2 B2 C2 : ℚ) / 4)
      ∧ probCard (A1 ∪ B1 ∪ C1) ≠ probCard (A2 ∪ B2 ∪ C2) := by
  have hT11 : ieTerm1 A1 B1 C1 = 6 := by decide
  have hT12 : ieTerm1 A2 B2 C2 = 6 := by decide
  have hT21 : ieTerm2 A1 B1 C1 = 3 := by decide
  have hT22 : ieTerm2 A2 B2 C2 = 3 := by decide
  have hU1 : unionCard A1 B1 C1 = 4 := by decide
  have hU2 : unionCard A2 B2 C2 = 3 := by decide
  refine ⟨?_, ?_, ?_⟩
  · calc
      ((ieTerm1 A1 B1 C1 : ℚ) / 4) = ((6 : ℚ) / 4) := by simp [hT11]
      _ = ((ieTerm1 A2 B2 C2 : ℚ) / 4) := by simp [hT12]
  · calc
      ((ieTerm2 A1 B1 C1 : ℚ) / 4) = ((3 : ℚ) / 4) := by simp [hT21]
      _ = ((ieTerm2 A2 B2 C2 : ℚ) / 4) := by simp [hT22]
  · intro hEq
    have hCard1 : (A1 ∪ B1 ∪ C1).card = 4 := by decide
    have hCard2 : (A2 ∪ B2 ∪ C2).card = 3 := by decide
    have hEq' :
        (((A1 ∪ B1 ∪ C1).card : ℚ) / 4) = (((A2 ∪ B2 ∪ C2).card : ℚ) / 4) := by
      simpa [probCard] using hEq
    rw [hCard1, hCard2] at hEq'
    norm_num at hEq'

end Mettapedia.Logic.PLNInclusionExclusionIdentifiability
