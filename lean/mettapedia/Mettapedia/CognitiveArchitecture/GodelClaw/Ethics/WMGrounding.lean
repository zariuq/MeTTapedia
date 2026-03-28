import Mettapedia.CognitiveArchitecture.GodelClaw.Ethics.EthicsFormulaWMBridge
import Mettapedia.CognitiveArchitecture.GodelClaw.Ethics.FoundationalMeaningAgencyWMBridge
import Mettapedia.CognitiveArchitecture.GodelClaw.Ethics.Ontology.UpperShard
import Mettapedia.CognitiveArchitecture.GodelClaw.Ethics.Ontology.ConflictLane
import Mettapedia.CognitiveArchitecture.GodelClaw.Ethics.Ontology.HyperseedBridge
import Mettapedia.CognitiveArchitecture.GodelClaw.Ethics.Ontology.ESOUpperShard
import Mettapedia.CognitiveArchitecture.GodelClaw.Ethics.Ontology.GewirthTrustTriangleExample
import Mettapedia.CognitiveArchitecture.GodelClaw.Ethics.MetaEthicsTrustTriangleExample
import Mettapedia.CognitiveArchitecture.GodelClaw.Ethics.EthicalDecisionProblemCaseStudies
import Mettapedia.Ethics.FOETCore

/-!
# GodelClaw Ethics WM Grounding

Preferred import surface for the ethics-to-WM grounding lane.

Architecture:

- `Mettapedia.Ethics.FOETCore` provides the minimal structured-sentence /
  paradigm / choice-point semantic core that is being liberated from SUMO.
- `EthicsFormulaWMBridge` remains the thin final lowering layer into WM atoms.
- `Ontology.UpperShard` is the current four-axis kernel / adapter above that
  lowering, not the final ontology.
- `Ontology.ConflictLane` connects structured active-goal conflicts to FOET
  choice points and dilemma transport.
- `Ontology.ESOUpperShard` gives that upper shard its own small model theory
  and ontology-trace interface.
- `FoundationalMeaningAgencyWMBridge` grounds active goals in the WM meaning /
  agency story.
- `Ontology.HyperseedBridge` composes the richer ontology claims with Hyperseed
  traces and the protected-goal theorems.

This is the intended public surface for a SUMO-light, ontology-respecting
extraction path.
-/

namespace Mettapedia.CognitiveArchitecture.GodelClaw.Ethics

open Mettapedia.Ethics
open Mettapedia.Ethics.Gewirth

/-- Preferred public correctness bridge on the live Gewirth trust-triangle
lane.

This is the primary story the public GodelClaw ethics surface should tell:
the same PGC/purposive-agency witness yields both ontology-side satisfaction of
the upper-shard claim and DDL-grounded WM positive evidence for the
corresponding obligation. -/
theorem gewirthTrustTriangle_primaryWMGrounding_of_PPA
    {I : PGCInterpretation}
    (h : PGCAssumptions I)
    (context : I.Ctx) (agent : I.Entity)
    (hPPA : PPA I.ActsOnPurpose agent context (I.worldOf context)) :
    (Ontology.ESOUpperShardModel.ofGewirth
        (Label := Ontology.TrustTriangleUpperShardLabel) I context).Sat
        (Ontology.gewirthNonInterferenceClaim context agent).toUpperShard ∧
      let sem := Mettapedia.Ethics.GewirthBridge.deonticSemanticsOfGewirthOi
        (Ctx := I.Ctx) I.ob I.pv
      let obligationFormula : I.Ctx × I.World → Prop :=
        sem.deontic .Obligation
          (Mettapedia.Ethics.GewirthBridge.WorldEmbedding.ofMeaning
            (NonInterference I.InterferesWith agent I.FWB))
      let q : Mettapedia.Logic.DDLPlus.WMBridge.DeonticWMQuery I.Ctx I.World :=
        { formula := obligationFormula
          decFormula := Classical.decPred obligationFormula }
      (Mettapedia.Logic.DDLPlus.WMBridge.deonticAtomicEvidence
        ((⟨context, I.worldOf context⟩ :
          Mettapedia.Logic.DDLPlus.WMBridge.PointedDeontic I.Ctx I.World))
        q).pos ≠ 0 := by
  exact Ontology.gewirthNonInterferenceClaim_sat_and_deonticWMPositiveEvidence_of_PPA
    h context agent hPPA

/-- Preferred public non-Gewirth correctness bridge on the live trust-triangle
universal-duty / non-maleficence lane.

This exposes the strengthened no-harm path as a first-class theorem at the
public grounding surface: the trust-triangle structured ESO model satisfies the
claim, and the compiled WM query receives positive support on the canonical
carrier semantics. -/
theorem trustTriangle_nonMaleficence_primaryWMGrounding :
    trustTriangleStructuredESOModel.SatStructured
        Ontology.avoidHarmfulDisclosureClaim ∧
      WMPositiveQuerySupport
        ({regionSupportMassSemantics
            Mettapedia.Logic.MarkovLogicTrustTriangleExample.coreTriangle} :
          Mettapedia.Logic.MarkovLogicAbstract.MassState
            (Mettapedia.Logic.MarkovLogicClauseFactorGraph.ConstraintQuery Nat))
        bodhisattvaNonMaleficenceQuery := by
  refine ⟨avoidHarmfulDisclosureClaim_sat_in_trustTriangleStructuredESOModel, ?_⟩
  simpa using avoidHarmfulDisclosureClaim_wmPositive_in_trustTriangleStructuredESOModel

/-- Companion public non-Gewirth correctness bridge on the trust-triangle
respect-autonomy / consent lane. -/
theorem trustTriangle_consent_primaryWMGrounding :
    trustTriangleStructuredESOModel.SatStructured
        Ontology.avoidCoerciveOverrideClaim ∧
      WMPositiveQuerySupport
        ({regionSupportMassSemantics
            Mettapedia.Logic.MarkovLogicTrustTriangleExample.coreTriangle} :
          Mettapedia.Logic.MarkovLogicAbstract.MassState
            (Mettapedia.Logic.MarkovLogicClauseFactorGraph.ConstraintQuery Nat))
        bodhisattvaConsentQuery := by
  refine ⟨avoidCoerciveOverrideClaim_sat_in_trustTriangleStructuredESOModel, ?_⟩
  simpa using avoidCoerciveOverrideClaim_wmPositive_in_trustTriangleStructuredESOModel

/-- Public non-Gewirth bridge on the privacy-disclosure autonomy lane.

This theorem widens the public grounding surface beyond the trust triangle:
the structured source model satisfies the ask-consent obligation, and the live
privacy-disclosure practical-lowering query receives positive WM support on the
named autonomy region. -/
theorem privacyDisclosure_autonomy_primaryWMGrounding :
    privacyDisclosureStructuredESOModel.SatStructured
        privacyDisclosureAskConsentObligationClaim ∧
      WMPositiveQuerySupport
        ({regionSupportMassSemantics privacyDisclosureAutonomyRegion} :
          Mettapedia.Logic.MarkovLogicAbstract.MassState
            (Mettapedia.Logic.MarkovLogicClauseFactorGraph.ConstraintQuery Nat))
        (privacyDisclosureLegacyPracticalBridge.actionQuery .askConsent) := by
  refine ⟨privacyDisclosureAskConsentObligationClaim_sat_in_structuredESOModel, ?_⟩
  exact privacyDisclosureLegacyPracticalBridge_askConsent_wmPositive

/-- Public non-Gewirth bridge on the force-escalation protection lane.

This theorem widens the public grounding surface with the first live
consequentialist case study: the `lockDown` action carries a candidate-local
ground witness, is satisfied in the structured source model, and its practical
lowering receives positive WM support on the named protection region. -/
theorem forceEscalation_lockDown_primaryWMGrounding :
    forceEscalationLockDownObligationClaim.ground.WitnessedForCandidateSet₀
        forceEscalationCandidateSet.toFinset ∧
      forceEscalationStructuredESOModel.SatStructured
        forceEscalationLockDownObligationClaim ∧
      WMPositiveQuerySupport
        ({regionSupportMassSemantics forceEscalationProtectionRegion} :
          Mettapedia.Logic.MarkovLogicAbstract.MassState
            (Mettapedia.Logic.MarkovLogicClauseFactorGraph.ConstraintQuery Nat))
        (forceEscalationLegacyPracticalBridge.actionQuery .lockDown) := by
  refine ⟨forceEscalationLockDownObligationClaim_ground_witnessedForCandidateSet, ?_, ?_⟩
  · exact forceEscalationLockDownObligationClaim_sat_in_structuredESOModel
  · exact forceEscalationLegacyPracticalBridge_lockDown_wmPositive

end Mettapedia.CognitiveArchitecture.GodelClaw.Ethics
