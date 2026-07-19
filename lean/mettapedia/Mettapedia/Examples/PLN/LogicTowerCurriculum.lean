import Mathlib.Tactic
import Mettapedia.Logic.HOL.Semantics.GoedelDummettCountermodel
import Mettapedia.PLN.Bridges.Logic.PLNIntuitionisticBridge

/-!
# Logic-tower curriculum example

This file presents the proven tower facts used by the PLN bridge:
BinaryEvidence validates Dummett's axiom and refutes Boolean excluded middle;
HOL has strict intuitionistic < LC < classical examples; and the diagonal
embedding gives the exact BinaryEvidence/single-chain equivalence, not the
missing all-prelinear completeness bridge.
-/

namespace Mettapedia.Examples.PLN.LogicTowerCurriculum

open scoped ENNReal
open LO.Propositional
open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.WithParams
open Mettapedia.Logic.HOL.HeytingSem.GoedelDummett
open Mettapedia.PLN.Evidence.EvidenceQuantale
open Mettapedia.PLN.Bridges.Logic.PLNIntuitionisticBridge

abbrev ForkedBase := Mettapedia.Logic.HOL.KripkeHenkin.ForkedFrameBase
abbrev ForkedConst := Mettapedia.Logic.HOL.KripkeHenkin.ForkedFrameConst
abbrev EMBase := Mettapedia.Logic.HOL.KripkeHenkin.EMCanaryBase
abbrev EMConst := Mettapedia.Logic.HOL.KripkeHenkin.EMCanaryConst

/-! ## Positive case: BinaryEvidence validates Dummett/prelinearity -/

/-- BinaryEvidence validates the Dummett/prelinearity instance for every
valuation. -/
theorem binary_evidence_validates_dummett
    (v : PropVar → BinaryEvidence) (p q : PropVar) :
    valid v (((#p) ➝ (#q)) ⋎ ((#q) ➝ (#p))) :=
  evidence_valid_dummett v p q

/-- Concrete tower witness: BinaryEvidence validates something IPL cannot
derive. -/
theorem binary_evidence_strictly_above_ipl :
    ∃ φ : Formula PropVar,
      (∀ v : PropVar → BinaryEvidence, (PLNSemantics v) ⊧ φ) ∧
      ¬(Hilbert.Standard Int.axioms ⊢ φ) :=
  evidence_stronger_than_ipl

/-- LC derivations are valid under every BinaryEvidence valuation. -/
theorem binary_evidence_lc_sound {φ : Formula PropVar}
    (h : LO.Propositional.LC ⊢ φ) :
    universallyValid φ :=
  pln_lc_soundness h

/-! ## Negative case: BinaryEvidence is not classical -/

/-- BinaryEvidence is not Boolean: excluded middle fails at the evidence-algebra
level. -/
theorem binary_evidence_not_boolean :
    ¬∀ e : BinaryEvidence, e ⊔ eᶜ = ⊤ :=
  evidence_not_boolean

/-- Formula-level negative example: excluded middle is not universally valid in
BinaryEvidence. -/
theorem binary_evidence_does_not_validate_lem :
    ¬ universallyValid (((#0) ⋎ (∼(#0))) : Formula PropVar) :=
  lem_not_universallyValid

/-- Classical excluded middle is still visible through the proven
double-negation simulation. -/
theorem binary_evidence_validates_double_negated_lem
    (v : PropVar → BinaryEvidence) (p : PropVar) :
    (PLNSemantics v) ⊧ (∼∼((#p) ⋎ (∼(#p)))) :=
  lem_double_negation_valid v p

/-! ## Honest diagonal statement -/

/-- The diagonal embedding reflects non-top values; this is the proved
single-chain reflection fact, not an all-prelinear completeness theorem. -/
theorem diagonal_one_is_not_top :
    diagonal (1 : ℝ≥0∞) ≠ (⊤ : BinaryEvidence) :=
  diagonal_reflects_non_top ENNReal.one_ne_top

/-- Top reflection in its exact reusable form. -/
theorem diagonal_top_reflection {x : ℝ≥0∞} :
    diagonal x = (⊤ : BinaryEvidence) ↔ x = ⊤ :=
  diagonal_eq_top_iff

/-- BinaryEvidence universal validity is the same as validity in the single
`ℝ≥0∞` Gödel chain. -/
theorem binary_evidence_validity_is_single_chain
    (φ : Formula PropVar) :
    universallyValid φ ↔ ennrealGodelUniversallyValid φ :=
  universallyValid_iff_ennrealGodelUniversallyValid φ

/-! ## HOL tower strictness -/

/-- HOL strictness: intuitionistic derivability sits strictly below LC. -/
theorem hol_intuitionistic_strictly_below_lc :
    (¬ ClosedTheorySet.Provable (Const := ForkedConst)
        (∅ : ClosedTheorySet ForkedConst)
        Mettapedia.Logic.HOL.KripkeHenkin.forkedPrelinearity) ∧
      ProvableLC (Base := ForkedBase) (Const := ForkedConst)
        (∅ : ClosedTheorySet (WithParams ForkedConst))
        Mettapedia.Logic.HOL.KripkeHenkin.forkedPrelinearityLC :=
  Mettapedia.Logic.HOL.KripkeHenkin.intuitionistic_strictly_below_lc

/-- HOL strictness: LC sits strictly below classical HOL. -/
theorem hol_lc_strictly_below_classical :
    (¬ ProvableLC (Base := EMBase) (Const := EMConst)
        (∅ : ClosedTheorySet (WithParams EMConst))
        Mettapedia.Logic.HOL.KripkeHenkin.emCanaryExcludedMiddleLC) ∧
      ClosedTheorySet.Provable (Const := WithParams EMConst)
        (Mettapedia.Logic.HOL.EMSchema (Base := EMBase) EMConst)
        Mettapedia.Logic.HOL.KripkeHenkin.emCanaryExcludedMiddleLC :=
  Mettapedia.Logic.HOL.KripkeHenkin.lc_strictly_below_classical

end Mettapedia.Examples.PLN.LogicTowerCurriculum
