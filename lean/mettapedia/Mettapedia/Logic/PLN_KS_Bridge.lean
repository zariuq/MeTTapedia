import Mettapedia.Logic.EvidenceQuantale
import Mettapedia.ProbabilityTheory.KnuthSkilling.Core.TotalityImprecision

/-!
# PLN BinaryEvidence vs Knuth-Skilling: the Totality Gate

This file records the clean meeting point between:

* Knuth–Skilling style representation theorems that produce **point-valued** maps `Θ : α → ℝ`, and
* PLN-style **evidence semantics** `BinaryEvidence := (n⁺, n⁻)`, which naturally admits incomparable values.

The key formal fact is simple:

> Any faithful point-valued order representation into `ℝ` forces the order to be **total**.

So, in domains where incomparable plausibility values are meaningful (e.g. "more positive evidence
but less negative evidence"), one should *not* expect a faithful point-valued probability calculus.
-/

namespace Mettapedia.Logic.PLN_KS_Bridge

open scoped ENNReal

open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.ProbabilityTheory.KnuthSkilling.TotalityImprecision

/-! ## BinaryEvidence has incomparable elements -/

theorem evidence_has_incomparables :
    ∃ x y : BinaryEvidence, ¬ (x ≤ y) ∧ ¬ (y ≤ x) := by
  refine ⟨⟨1, 0⟩, ⟨0, 1⟩, ?_, ?_⟩ <;>
    -- Coordinatewise order: need both components to be ≤, so (1,0) and (0,1) are incomparable.
    simp [BinaryEvidence.le_def]

/-! ## Therefore, no faithful point-valued `Θ : BinaryEvidence → ℝ` exists -/

/-- BinaryEvidence does not admit any faithful point-valued order representation into `ℝ`. -/
theorem evidence_no_faithfulPointRepresentation :
    ¬ FaithfulPointRepresentation BinaryEvidence := by
  apply no_faithfulPointRepresentation_of_incomparable (α := BinaryEvidence)
  exact evidence_has_incomparables

/-- Unfolded form of `evidence_no_faithfulPointRepresentation`. -/
theorem evidence_no_point_representation :
    ¬ ∃ Θ : BinaryEvidence → ℝ, ∀ a b : BinaryEvidence, a ≤ b ↔ Θ a ≤ Θ b := by
  exact evidence_no_faithfulPointRepresentation

/-! ## BinaryEvidence is not Boolean (Heyting negation does not satisfy LEM) -/

-- A small projection lemma so `simp` can compute the `pos` component of a join.
lemma pos_sup (x y : BinaryEvidence) : (x ⊔ y).pos = max x.pos y.pos := by
  rfl

/-- Law of excluded middle fails for the Heyting negation on `BinaryEvidence`. -/
theorem evidence_not_boolean :
    ∃ e : BinaryEvidence, e ⊔ e.compl ≠ (⊤ : BinaryEvidence) := by
  refine ⟨⟨1, 1⟩, ?_⟩
  intro h
  have hpos :
      ((⟨1, 1⟩ : BinaryEvidence) ⊔ (⟨1, 1⟩ : BinaryEvidence).compl).pos = (⊤ : BinaryEvidence).pos :=
    congrArg BinaryEvidence.pos h
  have hbotpos : (⊥ : BinaryEvidence).pos = 0 := by rfl
  have hbotneg : (⊥ : BinaryEvidence).neg = 0 := by rfl
  have htoppos : (⊤ : BinaryEvidence).pos = (⊤ : ENNReal) := by rfl
  have hpos_lhs :
      ((⟨1, 1⟩ : BinaryEvidence) ⊔ (⟨1, 1⟩ : BinaryEvidence).compl).pos = 1 := by
    simp [pos_sup, BinaryEvidence.compl, BinaryEvidence.himp, hbotpos, hbotneg]
  have : (1 : ENNReal) = (⊤ : ENNReal) := by
    calc
      (1 : ENNReal) = ((⟨1, 1⟩ : BinaryEvidence) ⊔ (⟨1, 1⟩ : BinaryEvidence).compl).pos :=
        hpos_lhs.symm
      _ = (⊤ : BinaryEvidence).pos := hpos
      _ = (⊤ : ENNReal) := htoppos
  exact ENNReal.one_ne_top this

end Mettapedia.Logic.PLN_KS_Bridge
