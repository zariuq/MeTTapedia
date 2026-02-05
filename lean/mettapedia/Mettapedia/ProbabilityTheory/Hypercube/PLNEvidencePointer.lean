import Mettapedia.ProbabilityTheory.Hypercube.Basic
import Mettapedia.Logic.EvidenceQuantale
import Mettapedia.Logic.PLN_KS_Bridge

namespace Mettapedia.ProbabilityTheory.Hypercube.EvidenceQuantalePointer

open Mettapedia.Logic.EvidenceQuantale

/-!
# PLN Evidence vs KS (Hypercube Pointer)

This is a *small* bridge module for readers coming from the hypercube story.

Key point:
- The Evidence carrier `Evidence := (n⁺, n⁻)` used for PLN-style truth values is **not** a
  linearly ordered plausibility scale, so it cannot support a faithful point-valued
  `Θ : Evidence → ℝ` representation.

For the formal statements, see:
- `Mettapedia.Logic.PLN_KS_Bridge`
- `Mettapedia.Logic.EvidenceQuantale`
-/

/-! ## Evidence Sits on the “Drop Totality” Face -/

theorem evidence_has_incomparables :
    ∃ x y : Evidence, ¬(x ≤ y) ∧ ¬(y ≤ x) :=
  Mettapedia.Logic.PLN_KS_Bridge.evidence_has_incomparables

/-! ## Evidence Cannot Have a Faithful Point-Valued Representation -/

theorem evidence_no_point_representation :
    ¬ ∃ (Θ : Evidence → ℝ), ∀ a b : Evidence, a ≤ b ↔ Θ a ≤ Θ b :=
  Mettapedia.Logic.PLN_KS_Bridge.evidence_no_point_representation

/-! ## Evidence Is Heyting, Not Boolean -/

theorem evidence_not_boolean :
    ∃ e : Evidence, e ⊔ e.compl ≠ (⊤ : Evidence) :=
  Mettapedia.Logic.PLN_KS_Bridge.evidence_not_boolean

end Mettapedia.ProbabilityTheory.Hypercube.EvidenceQuantalePointer
