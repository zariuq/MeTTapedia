import Mettapedia.Logic.EvidenceQuantale
import Mettapedia.ProbabilityTheory.KnuthSkilling.Core.TotalityImprecision

/-!
# PLN Evidence vs Knuth-Skilling: the Totality Gate

This file records the clean meeting point between:

* Knuth–Skilling style representation theorems that produce **point-valued** maps `Θ : α → ℝ`, and
* PLN-style **evidence semantics** `Evidence := (n⁺, n⁻)`, which naturally admits incomparable values.

The key formal fact is simple:

> Any faithful point-valued order representation into `ℝ` forces the order to be **total**.

So, in domains where incomparable plausibility values are meaningful (e.g. "more positive evidence
but less negative evidence"), one should *not* expect a faithful point-valued probability calculus.
-/

namespace Mettapedia.Logic.PLN_KS_Bridge

open scoped ENNReal

open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.ProbabilityTheory.KnuthSkilling.TotalityImprecision

/-! ## Evidence has incomparable elements -/

theorem evidence_has_incomparables :
    ∃ x y : Evidence, ¬ (x ≤ y) ∧ ¬ (y ≤ x) := by
  refine ⟨⟨1, 0⟩, ⟨0, 1⟩, ?_, ?_⟩ <;>
    -- Coordinatewise order: need both components to be ≤, so (1,0) and (0,1) are incomparable.
    simp [Evidence.le_def]

/-! ## Therefore, no faithful point-valued `Θ : Evidence → ℝ` exists -/

/-- Evidence does not admit any faithful point-valued order representation into `ℝ`. -/
theorem evidence_no_faithfulPointRepresentation :
    ¬ FaithfulPointRepresentation Evidence := by
  apply no_faithfulPointRepresentation_of_incomparable (α := Evidence)
  exact evidence_has_incomparables

/-- Unfolded form of `evidence_no_faithfulPointRepresentation`. -/
theorem evidence_no_point_representation :
    ¬ ∃ Θ : Evidence → ℝ, ∀ a b : Evidence, a ≤ b ↔ Θ a ≤ Θ b := by
  exact evidence_no_faithfulPointRepresentation

/-! ## Evidence is not Boolean (Heyting negation does not satisfy LEM) -/

-- A small projection lemma so `simp` can compute the `pos` component of a join.
lemma pos_sup (x y : Evidence) : (x ⊔ y).pos = max x.pos y.pos := by
  rfl

/-- Law of excluded middle fails for the Heyting negation on `Evidence`. -/
theorem evidence_not_boolean :
    ∃ e : Evidence, e ⊔ e.compl ≠ (⊤ : Evidence) := by
  refine ⟨⟨1, 1⟩, ?_⟩
  intro h
  have hpos :
      ((⟨1, 1⟩ : Evidence) ⊔ (⟨1, 1⟩ : Evidence).compl).pos = (⊤ : Evidence).pos :=
    congrArg Evidence.pos h
  have hbotpos : (⊥ : Evidence).pos = 0 := by rfl
  have hbotneg : (⊥ : Evidence).neg = 0 := by rfl
  have htoppos : (⊤ : Evidence).pos = (⊤ : ENNReal) := by rfl
  have hpos_lhs :
      ((⟨1, 1⟩ : Evidence) ⊔ (⟨1, 1⟩ : Evidence).compl).pos = 1 := by
    simp [pos_sup, Evidence.compl, Evidence.himp, hbotpos, hbotneg]
  have : (1 : ENNReal) = (⊤ : ENNReal) := by
    calc
      (1 : ENNReal) = ((⟨1, 1⟩ : Evidence) ⊔ (⟨1, 1⟩ : Evidence).compl).pos :=
        hpos_lhs.symm
      _ = (⊤ : Evidence).pos := hpos
      _ = (⊤ : ENNReal) := htoppos
  exact ENNReal.one_ne_top this

end Mettapedia.Logic.PLN_KS_Bridge
