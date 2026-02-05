import Mettapedia.Logic.PLNJointEvidence
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators

/-!
# No-Go: Complete Deduction Cannot Be Based on Local (Per-Link) Evidence Alone

This file formalizes a key design fact for PLN:

*If you want a sound and complete inference rule for conditional links without extra assumptions,
you must carry a joint model (joint distribution / joint evidence), not only per-link truth values.*

Concretely, we build two different joint evidence states `E₁, E₂ : JointEvidence 3` which agree on:
- the proposition evidence for `A`, `B`, `C`
- the link evidence for `A ⟹ B` and `B ⟹ C`

but disagree on the link evidence for `A ⟹ C`.

Therefore, there is no function that can compute the *complete* evidence for `A ⟹ C` from only
these local premises.
-/

namespace Mettapedia.Logic.PLNJointEvidenceNoGo

open scoped BigOperators ENNReal

open Mettapedia.Logic.CompletePLN
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNJointEvidence
open Mettapedia.Logic.PLNJointEvidence.JointEvidence

/-! ## A concrete counterexample on 3 propositions -/

namespace Example3

abbrev A : Fin 3 := 0
abbrev B : Fin 3 := 1
abbrev C : Fin 3 := 2

/-- A 4-world support set inside `Fin 8`. -/
def S : Finset (Fin 8) :=
  {⟨1, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨6, by decide⟩}

/-- Uniform joint evidence: every world has count 1. -/
noncomputable def E₁ : JointEvidence 3 := fun _ => (1 : ℝ≥0∞)

/-- Supported joint evidence: worlds in `S` have count 2, others have 0. -/
noncomputable def E₂ : JointEvidence 3 := fun w => if w ∈ S then (2 : ℝ≥0∞) else 0

lemma countWorld_E₁ (P : Fin 8 → Bool) :
    countWorld (n := 3) (E := E₁) P =
      (({w : Fin 8 | P w = true} : Finset (Fin 8))).card := by
  classical
  unfold countWorld E₁
  simp

lemma countWorld_E₂ (P : Fin 8 → Bool) :
    countWorld (n := 3) (E := E₂) P =
      (({w : Fin 8 | P w = true ∧ w ∈ S} : Finset (Fin 8))).card * (2 : ℝ≥0∞) := by
  classical
  unfold countWorld E₂
  have h :
      (fun w : Fin 8 => if P w then (if w ∈ S then (2 : ℝ≥0∞) else 0) else 0) =
        (fun w : Fin 8 => if (P w = true ∧ w ∈ S) then (2 : ℝ≥0∞) else 0) := by
    funext w
    cases P w <;> simp
  -- Rewrite to a filtered sum, then simplify to card * const.
  simpa [h] using
    (Finset.sum_filter (s := (Finset.univ : Finset (Fin 8)))
      (p := fun w : Fin 8 => P w = true ∧ w ∈ S)
      (f := fun _ => (2 : ℝ≥0∞))).symm

/-! ### Card facts (computed) -/

lemma card_A_pos : (({w : Fin 8 | worldToAssignment 3 w A = true} : Finset (Fin 8))).card = 4 := by
  decide

lemma card_A_pos_S :
    (({w : Fin 8 | worldToAssignment 3 w A = true ∧ w ∈ S} : Finset (Fin 8))).card = 2 := by
  decide

lemma card_A_neg : (({w : Fin 8 | worldToAssignment 3 w A = false} : Finset (Fin 8))).card = 4 := by
  decide

lemma card_A_neg_S :
    (({w : Fin 8 | worldToAssignment 3 w A = false ∧ w ∈ S} : Finset (Fin 8))).card = 2 := by
  decide

lemma card_B_pos : (({w : Fin 8 | worldToAssignment 3 w B = true} : Finset (Fin 8))).card = 4 := by
  decide

lemma card_B_pos_S :
    (({w : Fin 8 | worldToAssignment 3 w B = true ∧ w ∈ S} : Finset (Fin 8))).card = 2 := by
  decide

lemma card_B_neg : (({w : Fin 8 | worldToAssignment 3 w B = false} : Finset (Fin 8))).card = 4 := by
  decide

lemma card_B_neg_S :
    (({w : Fin 8 | worldToAssignment 3 w B = false ∧ w ∈ S} : Finset (Fin 8))).card = 2 := by
  decide

lemma card_C_pos : (({w : Fin 8 | worldToAssignment 3 w C = true} : Finset (Fin 8))).card = 4 := by
  decide

lemma card_C_pos_S :
    (({w : Fin 8 | worldToAssignment 3 w C = true ∧ w ∈ S} : Finset (Fin 8))).card = 2 := by
  decide

lemma card_C_neg : (({w : Fin 8 | worldToAssignment 3 w C = false} : Finset (Fin 8))).card = 4 := by
  decide

lemma card_C_neg_S :
    (({w : Fin 8 | worldToAssignment 3 w C = false ∧ w ∈ S} : Finset (Fin 8))).card = 2 := by
  decide

lemma card_AB_pos :
    (({w : Fin 8 | worldToAssignment 3 w A = true ∧ worldToAssignment 3 w B = true} :
        Finset (Fin 8))).card = 2 := by
  decide

lemma card_AB_pos_S :
    (({w : Fin 8 |
          (worldToAssignment 3 w A = true ∧ worldToAssignment 3 w B = true) ∧ w ∈ S} :
        Finset (Fin 8))).card = 1 := by
  decide

lemma card_AB_neg :
    (({w : Fin 8 | worldToAssignment 3 w A = true ∧ worldToAssignment 3 w B = false} :
        Finset (Fin 8))).card = 2 := by
  decide

lemma card_AB_neg_S :
    (({w : Fin 8 |
          (worldToAssignment 3 w A = true ∧ worldToAssignment 3 w B = false) ∧ w ∈ S} :
        Finset (Fin 8))).card = 1 := by
  decide

lemma card_BC_pos :
    (({w : Fin 8 | worldToAssignment 3 w B = true ∧ worldToAssignment 3 w C = true} :
        Finset (Fin 8))).card = 2 := by
  decide

lemma card_BC_pos_S :
    (({w : Fin 8 |
          (worldToAssignment 3 w B = true ∧ worldToAssignment 3 w C = true) ∧ w ∈ S} :
        Finset (Fin 8))).card = 1 := by
  decide

lemma card_BC_neg :
    (({w : Fin 8 | worldToAssignment 3 w B = true ∧ worldToAssignment 3 w C = false} :
        Finset (Fin 8))).card = 2 := by
  decide

lemma card_BC_neg_S :
    (({w : Fin 8 |
          (worldToAssignment 3 w B = true ∧ worldToAssignment 3 w C = false) ∧ w ∈ S} :
        Finset (Fin 8))).card = 1 := by
  decide

lemma card_AC_pos :
    (({w : Fin 8 | worldToAssignment 3 w A = true ∧ worldToAssignment 3 w C = true} :
        Finset (Fin 8))).card = 2 := by
  decide

lemma card_AC_pos_S :
    (({w : Fin 8 |
          (worldToAssignment 3 w A = true ∧ worldToAssignment 3 w C = true) ∧ w ∈ S} :
        Finset (Fin 8))).card = 0 := by
  decide

/-! ### Premises agree, conclusion differs -/

theorem premises_agree :
    propEvidence (n := 3) (E := E₁) A = propEvidence (n := 3) (E := E₂) A ∧
    propEvidence (n := 3) (E := E₁) B = propEvidence (n := 3) (E := E₂) B ∧
    propEvidence (n := 3) (E := E₁) C = propEvidence (n := 3) (E := E₂) C ∧
    linkEvidence (n := 3) (E := E₁) A B = linkEvidence (n := 3) (E := E₂) A B ∧
    linkEvidence (n := 3) (E := E₁) B C = linkEvidence (n := 3) (E := E₂) B C := by
  classical
  refine ⟨?hA, ?hB, ?hC, ?hAB, ?hBC⟩
  · ext <;>
      simp [propEvidence, countWorld_E₁, countWorld_E₂, card_A_pos, card_A_pos_S, card_A_neg,
        card_A_neg_S] <;>
      norm_num
  · ext <;>
      simp [propEvidence, countWorld_E₁, countWorld_E₂, card_B_pos, card_B_pos_S, card_B_neg,
        card_B_neg_S] <;>
      norm_num
  · ext <;>
      simp [propEvidence, countWorld_E₁, countWorld_E₂, card_C_pos, card_C_pos_S, card_C_neg,
        card_C_neg_S] <;>
      norm_num
  · ext <;>
      simp [linkEvidence, countWorld_E₁, countWorld_E₂, card_AB_pos, card_AB_pos_S, card_AB_neg,
        card_AB_neg_S]
  · ext <;>
      simp [linkEvidence, countWorld_E₁, countWorld_E₂, card_BC_pos, card_BC_pos_S, card_BC_neg,
        card_BC_neg_S]

theorem conclusion_diff :
    linkEvidence (n := 3) (E := E₁) A C ≠ linkEvidence (n := 3) (E := E₂) A C := by
  classical
  intro hEq
  have hpos :
      (linkEvidence (n := 3) (E := E₁) A C).pos = (linkEvidence (n := 3) (E := E₂) A C).pos :=
    congrArg Evidence.pos hEq
  -- Compute the two positive counts: 2 vs 0.
  simp [linkEvidence, countWorld_E₁, countWorld_E₂, card_AC_pos, card_AC_pos_S] at hpos

/-! ### Corollary: No complete local deduction rule exists -/

/-- There is no "complete deduction" function which computes `A ⟹ C` evidence from only local
premises `A,B,C, A⟹B, B⟹C`, for all joint evidence models. -/
theorem no_local_complete_deduction
    (f : Evidence → Evidence → Evidence → Evidence → Evidence → Evidence) :
    ¬ (∀ E : JointEvidence 3,
        f (propEvidence (n := 3) (E := E) A)
          (propEvidence (n := 3) (E := E) B)
          (propEvidence (n := 3) (E := E) C)
          (linkEvidence (n := 3) (E := E) A B)
          (linkEvidence (n := 3) (E := E) B C)
        = linkEvidence (n := 3) (E := E) A C) := by
  intro h
  have h₁ := h E₁
  have h₂ := h E₂
  rcases premises_agree with ⟨hA, hB, hC, hAB, hBC⟩
  -- Rewrite `h₂` so it has the same left-hand side as `h₁`.
  have h₂' :
      f (propEvidence (n := 3) (E := E₁) A)
        (propEvidence (n := 3) (E := E₁) B)
        (propEvidence (n := 3) (E := E₁) C)
        (linkEvidence (n := 3) (E := E₁) A B)
        (linkEvidence (n := 3) (E := E₁) B C)
      = linkEvidence (n := 3) (E := E₂) A C := by
    simpa [hA, hB, hC, hAB, hBC] using h₂
  have : linkEvidence (n := 3) (E := E₁) A C = linkEvidence (n := 3) (E := E₂) A C := by
    exact Eq.trans h₁.symm h₂'
  exact conclusion_diff this

end Example3

end Mettapedia.Logic.PLNJointEvidenceNoGo
