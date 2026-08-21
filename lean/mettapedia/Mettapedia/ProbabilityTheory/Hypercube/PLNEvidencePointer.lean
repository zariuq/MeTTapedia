import Mettapedia.ProbabilityTheory.Hypercube.Basic
import Mettapedia.PLN.Evidence.EvidenceQuantale
import Mettapedia.PLN.Evidence.PLN_KS_Bridge

namespace Mettapedia.ProbabilityTheory.Hypercube.EvidenceQuantalePointer

open Mettapedia.PLN.Evidence.EvidenceQuantale

/-!
# PLN BinaryEvidence vs KS (Hypercube Pointer)

This is a *small* bridge module for readers coming from the hypercube story.

Key point:
- The BinaryEvidence carrier `BinaryEvidence := (n⁺, n⁻)` used for PLN-style truth values is **not** a
  linearly ordered plausibility scale, so it cannot support an order-reflecting
  scalar representation `Θ : BinaryEvidence → ℝ`.

For the formal statements, see:
- `Mettapedia.PLN.Evidence.PLN_KS_Bridge`
- `Mettapedia.PLN.Evidence.EvidenceQuantale`
-/

/-! ## BinaryEvidence Has Genuine Incomparability -/

theorem evidence_has_incomparables :
    ∃ x y : BinaryEvidence, ¬(x ≤ y) ∧ ¬(y ≤ x) :=
  Mettapedia.PLN.Evidence.PLN_KS_Bridge.evidence_has_incomparables

/-! ## BinaryEvidence Cannot Embed Its Order into a Scalar -/

theorem evidence_no_orderEmbedding_into_real :
    ¬ ∃ (Θ : BinaryEvidence → ℝ), ∀ a b : BinaryEvidence, a ≤ b ↔ Θ a ≤ Θ b :=
  Mettapedia.PLN.Evidence.PLN_KS_Bridge.evidence_no_orderEmbedding_into_real

/-! ## BinaryEvidence Is Heyting, Not Boolean -/

theorem evidence_not_boolean :
    ∃ e : BinaryEvidence, e ⊔ e.compl ≠ (⊤ : BinaryEvidence) :=
  Mettapedia.PLN.Evidence.PLN_KS_Bridge.evidence_not_boolean

end Mettapedia.ProbabilityTheory.Hypercube.EvidenceQuantalePointer
