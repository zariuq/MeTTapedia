import Mettapedia.Logic.PLNDerivation
import Mettapedia.Logic.PLNWorldModelCalculus

/-!
# PLN Canonical API (Lean)

Small facade module that exposes the recommended, semantically grounded entry points:

- Correct strength formulas from `PLNDerivation`
- Categorical naming (`SourceRule` / `SinkRule`) as first-class aliases
- NB bridge theorem location: `PLNBayesNetInference`
- WM-calculus rewrite/query-equivalence types from `PLNWorldModelCalculus`

This file is intentionally lightweight: it is an index with stable names, not a new semantics layer.
-/

namespace Mettapedia.Logic.PLNCanonical

open Mettapedia.Logic

/-! ## Canonical rule-strength names -/

noncomputable abbrev deductionStrength := PLN.plnDeductionStrength
noncomputable abbrev inductionStrength := PLN.plnInductionStrength
noncomputable abbrev abductionStrength := PLN.plnAbductionStrength

noncomputable abbrev sourceRuleStrength := PLN.plnSourceRuleStrength
noncomputable abbrev sinkRuleStrength := PLN.plnSinkRuleStrength

theorem sourceRule_eq_induction (s_BA s_BC s_A s_B s_C : ℝ) :
    sourceRuleStrength s_BA s_BC s_A s_B s_C =
      inductionStrength s_BA s_BC s_A s_B s_C := rfl

theorem sinkRule_eq_abduction (s_AB s_CB s_A s_B s_C : ℝ) :
    sinkRuleStrength s_AB s_CB s_A s_B s_C =
      abductionStrength s_AB s_CB s_A s_B s_C := rfl

/-! ## WM-calculus canonical type aliases -/

abbrev WMQueryEq {State Query : Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModel State Query] :=
  PLNWorldModel.WMQueryEq (State := State) (Query := Query)

abbrev WMRewriteRule (State Query : Type*)
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModel State Query] :=
  PLNWorldModel.WMRewriteRule State Query

end Mettapedia.Logic.PLNCanonical
