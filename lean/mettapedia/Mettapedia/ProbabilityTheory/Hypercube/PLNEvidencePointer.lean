import Mettapedia.ProbabilityTheory.Hypercube.Basic
import Mettapedia.Logic.EvidenceQuantale
import Mettapedia.Logic.PLN_KS_Bridge

namespace Mettapedia.ProbabilityTheory.Hypercube.EvidenceQuantalePointer

open Mettapedia.Logic.EvidenceQuantale

/-!
# PLN BinaryEvidence vs KS (Hypercube Pointer)

This is a *small* bridge module for readers coming from the hypercube story.

Key point:
- The BinaryEvidence carrier `BinaryEvidence := (n⁺, n⁻)` used for PLN-style truth values is **not** a
  linearly ordered plausibility scale, so it cannot support a faithful point-valued
  `Θ : BinaryEvidence → ℝ` representation.

For the formal statements, see:
- `Mettapedia.Logic.PLN_KS_Bridge`
- `Mettapedia.Logic.EvidenceQuantale`
-/

/-! ## BinaryEvidence Sits on the “Drop Totality” Face -/

theorem evidence_has_incomparables :
    ∃ x y : BinaryEvidence, ¬(x ≤ y) ∧ ¬(y ≤ x) :=
  Mettapedia.Logic.PLN_KS_Bridge.evidence_has_incomparables

/-! ## BinaryEvidence Cannot Have a Faithful Point-Valued Representation -/

theorem evidence_no_point_representation :
    ¬ ∃ (Θ : BinaryEvidence → ℝ), ∀ a b : BinaryEvidence, a ≤ b ↔ Θ a ≤ Θ b :=
  Mettapedia.Logic.PLN_KS_Bridge.evidence_no_point_representation

/-! ## BinaryEvidence Is Heyting, Not Boolean -/

theorem evidence_not_boolean :
    ∃ e : BinaryEvidence, e ⊔ e.compl ≠ (⊤ : BinaryEvidence) :=
  Mettapedia.Logic.PLN_KS_Bridge.evidence_not_boolean

end Mettapedia.ProbabilityTheory.Hypercube.EvidenceQuantalePointer
