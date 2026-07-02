import Mettapedia.Logic.HOL.Semantics.HeytingPushforward
import Mettapedia.PLN.Evidence.EvidenceQuantale

/-!
# Evidence-valued models and the Gödel–Dummett characterization

`BinaryEvidence` is a genuine frame (registered instance), so evidence-valued
Heyting models exist — but its frame is a product of two *linear* (Gödel)
frames, so it validates the Gödel–Dummett axiom `(a ⇨ b) ⊔ (b ⇨ a) = ⊤` while
refusing excluded middle.  Consequently every `BinaryEvidence`-valued model of
the EM-free calculus validates the LC axiom schema
`(φ → ψ) ∨ (ψ → φ)`, which is not an intuitionistic theorem: making the
evidence carrier the *truth algebra* strengthens the logic to Gödel–Dummett
logic.  This is the precise algebraic form of the support/evidence doctrine —
evidence values enter intuitionistic HOL as monotone *readouts* (`WMReadout`),
not as the primitive truth algebra; using them as truth values is legitimate
but changes the logic, and must be labeled as such.
-/

namespace Mettapedia.PLN.Bridges.HOL.EvidenceValued

open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.HeytingSem
open Mettapedia.PLN.Evidence.EvidenceQuantale
open scoped ENNReal

universe u v

variable {Base : Type u} {Const : Ty Base → Type v}

/-- **Gödel–Dummett law in `BinaryEvidence`**: its frame is a product of two
linear frames, so prelinearity holds. -/
theorem binaryEvidence_goedelDummett (a b : BinaryEvidence) :
    (a ⇨ b) ⊔ (b ⇨ a) = ⊤ := by
  refine le_antisymm le_top ?_
  change (⊤ : BinaryEvidence) ≤ _
  rw [BinaryEvidence.le_def]
  constructor
  · rcases le_total a.pos b.pos with h | h
    · calc (⊤ : BinaryEvidence).pos ≤ (a ⇨ b).pos := by
            show _ ≤ (BinaryEvidence.himp a b).pos
            simp [BinaryEvidence.himp, h]
        _ ≤ ((a ⇨ b) ⊔ (b ⇨ a)).pos := by
            exact (BinaryEvidence.le_def _ _).mp le_sup_left |>.1
    · calc (⊤ : BinaryEvidence).pos ≤ (b ⇨ a).pos := by
            show _ ≤ (BinaryEvidence.himp b a).pos
            simp [BinaryEvidence.himp, h]
        _ ≤ ((a ⇨ b) ⊔ (b ⇨ a)).pos := by
            exact (BinaryEvidence.le_def _ _).mp le_sup_right |>.1
  · rcases le_total a.neg b.neg with h | h
    · calc (⊤ : BinaryEvidence).neg ≤ (a ⇨ b).neg := by
            show _ ≤ (BinaryEvidence.himp a b).neg
            simp [BinaryEvidence.himp, h]
        _ ≤ ((a ⇨ b) ⊔ (b ⇨ a)).neg := by
            exact (BinaryEvidence.le_def _ _).mp le_sup_left |>.2
    · calc (⊤ : BinaryEvidence).neg ≤ (b ⇨ a).neg := by
            show _ ≤ (BinaryEvidence.himp b a).neg
            simp [BinaryEvidence.himp, h]
        _ ≤ ((a ⇨ b) ⊔ (b ⇨ a)).neg := by
            exact (BinaryEvidence.le_def _ _).mp le_sup_right |>.2

/-- Negative example: `BinaryEvidence` is not Boolean — the graded value
`(1, 1)` refutes excluded middle, so evidence-valued models remain genuinely
non-classical (they sit strictly between intuitionistic and classical:
Gödel–Dummett logic). -/
theorem binaryEvidence_not_boolean :
    ∃ a : BinaryEvidence, a ⊔ (a ⇨ ⊥) ≠ ⊤ := by
  refine ⟨⟨1, 1⟩, fun h => ?_⟩
  have hpos := congrArg BinaryEvidence.pos h
  have hred : ((⟨1, 1⟩ : BinaryEvidence) ⊔ ((⟨1, 1⟩ : BinaryEvidence) ⇨ ⊥)).pos
      = (1 : ℝ≥0∞) := by
    show ((BinaryEvidence.sup ⟨1, 1⟩ (BinaryEvidence.himp ⟨1, 1⟩ ⟨0, 0⟩))).pos = _
    simp [BinaryEvidence.sup, BinaryEvidence.himp]
  rw [hred] at hpos
  exact ENNReal.one_ne_top hpos

/-- Any Heyting-valued model whose value operations satisfy prelinearity
validates the LC axiom schema. -/
theorem HeytingGeneralModel.lc_valid_of_prelinear
    (M : HeytingGeneralModel Base Const)
    (hGD : ∀ a b : M.Ω, M.le M.top (M.sup (M.himp a b) (M.himp b a)))
    (φ ψ : ClosedFormula Const) :
    M.le M.top (M.val (.or (.imp φ ψ) (.imp ψ φ))) := by
  rw [M.val_or, M.val_imp, M.val_imp]
  exact hGD _ _

/-- **The doctrine theorem**: every pushforward of a Heyting-valued model onto
`BinaryEvidence` validates the Gödel–Dummett schema `(φ → ψ) ∨ (ψ → φ)` — an
axiom that is not derivable in the EM-free calculus.  Evidence-as-truth-algebra
is therefore a *stronger logic* (Gödel–Dummett), not plain intuitionistic HOL;
graded evidence enters the intuitionistic story as a monotone readout
(`WMReadout`), exactly as the crisp separating family already does. -/
theorem pushforward_binaryEvidence_validates_lc
    (M : HeytingGeneralModel.{u, v, max u v} Base Const)
    (D : ModelPushforwardData (Base := Base) M BinaryEvidence)
    (φ ψ : ClosedFormula Const) :
    (M.pushforward D).le (M.pushforward D).top
      ((M.pushforward D).val (.or (.imp φ ψ) (.imp ψ φ))) := by
  refine HeytingGeneralModel.lc_valid_of_prelinear _ (fun a b => ?_) φ ψ
  exact le_of_eq (binaryEvidence_goedelDummett a b).symm

end Mettapedia.PLN.Bridges.HOL.EvidenceValued
