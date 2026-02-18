import Mettapedia.Logic.PLNXiDerivedBNRules
import Mettapedia.Logic.PLNWorldModelCalculus

/-!
# PLN End-to-End (Stable Surface)

This module is intentionally thin: it exposes stable names for the proved
BN ↔ WM ↔ OSLF links without introducing heavyweight wrapper theorems that
trigger instance-resolution blowups.

Use this module as the canonical entry point for E2E references.
-/

namespace Mettapedia.Logic.PLNEndToEnd

open Mettapedia.Logic

/-! ## Chain (Deduction) -/

noncomputable abbrev chainFormulaExact :=
  @PLNXiDerivedBNRules.xi_deduction_queryStrength_eq_plnDeduction_of_chainBN

noncomputable abbrev chainAdmissible :=
  @PLNXiDerivedBNRules.xi_deduction_admissible_of_chainBN

noncomputable abbrev chainOSLFEvidence :=
  @PLNXiDerivedBNRules.xi_deduction_semE_atom_of_chainBN

noncomputable abbrev chainOSLFThreshold :=
  @PLNXiDerivedBNRules.xi_deduction_threshold_of_chainBN

/-! ## Fork (Source / Induction) -/

noncomputable abbrev forkFormulaExact :=
  @PLNXiDerivedBNRules.xi_source_queryStrength_eq_plnInduction_of_forkBN

noncomputable abbrev forkAdmissible :=
  @PLNXiDerivedBNRules.xi_sourceRule_admissible_of_forkBN

noncomputable abbrev forkOSLFEvidence :=
  @PLNXiDerivedBNRules.xi_sourceRule_semE_atom_of_forkBN

noncomputable abbrev forkOSLFThreshold :=
  @PLNXiDerivedBNRules.xi_sourceRule_threshold_of_forkBN

/-! ## Collider (Sink / Abduction) -/

noncomputable abbrev colliderStructural :=
  @PLNXiDerivedBNRules.xi_sinkRule_strength_eq_of_colliderBN

noncomputable abbrev colliderStructuralToReal :=
  @PLNXiDerivedBNRules.xi_sink_queryStrength_toReal_eq_of_colliderBN

noncomputable abbrev colliderAdmissible :=
  @PLNXiDerivedBNRules.xi_sinkRule_admissible_of_colliderBN

noncomputable abbrev colliderOSLFEvidence :=
  @PLNXiDerivedBNRules.xi_sinkRule_semE_atom_of_colliderBN

noncomputable abbrev colliderOSLFThreshold :=
  @PLNXiDerivedBNRules.xi_sinkRule_threshold_of_colliderBN

noncomputable abbrev colliderNotExact :=
  @PLNXiDerivedBNRules.plnAbductionStrength_not_exact_collider

noncomputable abbrev colliderExactWhenScreeningOff :=
  @PLNXiDerivedBNRules.plnAbductionStrength_exact_of_screeningOff

/-! ## Generic WM context lift -/

section Generic

variable {State Query : Type*}
variable [EvidenceClass.EvidenceType State] [PLNWorldModel.WorldModel State Query]

theorem wmRewriteRuleCtx
    {r : PLNWorldModel.WMRewriteRule State Query} {Γ : Set State} {W : State}
    (hSide : r.side) (hW : PLNWorldModel.WMJudgmentCtx Γ W) :
    PLNWorldModel.WMQueryJudgmentCtx Γ W r.conclusion (r.derive W) :=
  PLNWorldModel.WMRewriteRule.applyCtx hSide hW

end Generic

end Mettapedia.Logic.PLNEndToEnd
