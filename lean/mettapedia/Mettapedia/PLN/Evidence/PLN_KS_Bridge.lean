import Mettapedia.PLN.Evidence.EvidenceQuantale
import KnuthSkilling.Core.TotalityImprecision

/-!
# PLN BinaryEvidence vs Scalar Order Reflection

This file records the clean meeting point between:

* scalar maps `Θ : α → ℝ` that are required to preserve and reflect order, and
* PLN-style **evidence semantics** `BinaryEvidence := (n⁺, n⁻)`, which naturally admits incomparable values.

The key formal fact is simple:

> Any order-reflecting point-valued representation into `ℝ` forces the order to be **total**.

This is deliberately stronger than Knuth–Skilling's one-way fidelity condition,
which permits scalar values to add comparisons not present in the lattice.  In
domains where incomparability itself is meaningful, an order-reflecting scalar
readout cannot retain it.
-/

namespace Mettapedia.PLN.Evidence.PLN_KS_Bridge

open scoped ENNReal

open Mettapedia.PLN.Evidence.EvidenceQuantale
open KnuthSkilling.TotalityImprecision

/-! ## BinaryEvidence has incomparable elements -/

theorem evidence_has_incomparables :
    ∃ x y : BinaryEvidence, ¬ (x ≤ y) ∧ ¬ (y ≤ x) := by
  refine ⟨⟨1, 0⟩, ⟨0, 1⟩, ?_, ?_⟩ <;>
    -- Coordinatewise order: need both components to be ≤, so (1,0) and (0,1) are incomparable.
    simp [BinaryEvidence.le_def]

/-! ## Therefore, no order-reflecting scalar readout exists -/

/-- BinaryEvidence has no point-valued representation into `ℝ` that preserves
and reflects its coordinatewise order. -/
theorem evidence_no_orderReflectingPointRepresentation :
    ¬ OrderReflectingPointRepresentation BinaryEvidence := by
  apply no_orderReflectingPointRepresentation_of_incomparable (α := BinaryEvidence)
  exact evidence_has_incomparables

/-- Unfolded form of `evidence_no_orderReflectingPointRepresentation`. -/
theorem evidence_no_orderEmbedding_into_real :
    ¬ ∃ Θ : BinaryEvidence → ℝ, ∀ a b : BinaryEvidence, a ≤ b ↔ Θ a ≤ Θ b := by
  exact evidence_no_orderReflectingPointRepresentation

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

end Mettapedia.PLN.Evidence.PLN_KS_Bridge
