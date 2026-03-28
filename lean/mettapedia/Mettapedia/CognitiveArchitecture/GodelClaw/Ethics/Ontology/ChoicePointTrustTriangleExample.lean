import Mettapedia.CognitiveArchitecture.GodelClaw.Ethics.Ontology.ESOUpperShard
import Mettapedia.CognitiveArchitecture.GodelClaw.Ethics.Ontology.ConflictLane
import Mettapedia.CognitiveArchitecture.GodelClaw.Ethics.BodhisattvaExample

set_option autoImplicit false

/-!
# ChoicePoint / Trust-Triangle Example

This file gives a concrete end-to-end example of the new Stage 3 spine:

- typed ESO-style observations extract directly to `StructuredEthicalClaim`,
- the four-axis kernel lowers directly to WM queries,
- a foundational-meaning profile uses one such structured active goal,
- and a live `ChoicePoint` on the active-goal lane transports conflict across
  deontic, value, utilitarian, and virtue readings.

The intended reading is an autonomous agent confronting two bad candidate
plans on the trust triangle:

- a harmful disclosure option,
- and a coercive override option.

Both options are seeded from observations, both live in the `activeGoal` role,
and both are rejected across the four ethical lenses.
-/

namespace Mettapedia.CognitiveArchitecture.GodelClaw.Ethics.Ontology

open Mettapedia.Ethics
open Mettapedia.Hyperseed
open Mettapedia.CognitiveArchitecture.GodelClaw.Ethics
open Mettapedia.Logic.MarkovLogicClauseFactorGraph
open Mettapedia.Logic.MarkovLogicTrustTriangleExample

/-- Tiny world for the structured trust-triangle deliberation example. -/
abbrev TrustTriangleChoiceWorld := Bool

/-- Two distinct candidate bad plans in the toy deliberation world. -/
def harmfulDisclosureFormula : Formula TrustTriangleChoiceWorld := fun w => w = false

def coerciveOverrideFormula : Formula TrustTriangleChoiceWorld := fun w => w = true

/-- Direct structured lowering into the existing trust-triangle WM queries. -/
def trustTriangleStructuredEncoder :
    StructuredEthicsQueryEncoder TrustTriangleChoiceWorld Nat Nat where
  propositionalQuery := fun _ presentation ground role _ =>
    match presentation, ground, role with
    | .deontic .Prohibition, .universalDuty .noHarm, .activeGoal =>
        bodhisattvaNonMaleficenceQuery
    | .deontic .Prohibition, .universalDuty .respectAutonomy, .activeGoal =>
        bodhisattvaConsentQuery
    | .deontic .Obligation, .gewirthPGC, .activeGoal =>
        bodhisattvaNonMaleficenceQuery
    | .axiological _, _, _ =>
        bodhisattvaEpistemicUniversalLoveQuery
    | _, _, _ =>
        bodhisattvaEpistemicUniversalLoveQuery
  relationalQuery := fun _ _ _ _ _ r =>
    match r with
    | .friendship => bodhisattvaReciprocityQuery
    | _ => bodhisattvaEpistemicUniversalLoveQuery
  dispositionalQuery := fun _ _ _ _ =>
    bodhisattvaEpistemicUniversalLoveQuery

/-- Candidate active goal rejecting harmful disclosure. -/
def avoidHarmfulDisclosureClaim : StructuredEthicalClaim TrustTriangleChoiceWorld Nat where
  subject := 1
  content := .propositional harmfulDisclosureFormula
  presentation := .deontic .Prohibition
  ground := .universalDuty .noHarm
  role := .activeGoal

/-- Candidate active goal rejecting coercive override. -/
def avoidCoerciveOverrideClaim : StructuredEthicalClaim TrustTriangleChoiceWorld Nat where
  subject := 1
  content := .propositional coerciveOverrideFormula
  presentation := .deontic .Prohibition
  ground := .universalDuty .respectAutonomy
  role := .activeGoal

/-- Structured observation alphabet for the autonomous deliberation lane. -/
inductive TrustTriangleStructuredObservation where
  | harmfulDisclosureCue
  | coerciveOverrideCue
  deriving DecidableEq, Repr

/-- Typed ESO-style source: observations extract directly to structured claims. -/
def trustTriangleStructuredTraceSource :
    StructuredESOTraceSource
      TrustTriangleStructuredObservation TrustTriangleChoiceWorld Nat where
  extract
    | .harmfulDisclosureCue => {avoidHarmfulDisclosureClaim}
    | .coerciveOverrideCue => {avoidCoerciveOverrideClaim}

/-- Foundational-meaning profile whose active goal is one structured claim from
the autonomous deliberation lane. -/
def trustTriangleAutonomousMeaningProfile :
    StructuredFoundationalMeaningProfile TrustTriangleChoiceWorld Nat Nat where
  situation := bodhisattvaNonMaleficenceQuery
  prediction := bodhisattvaEpistemicUniversalLoveQuery
  activeGoalClaim := avoidCoerciveOverrideClaim
  plan := bodhisattvaConsentQuery

@[simp] theorem avoidHarmfulDisclosureQuery_eq :
    avoidHarmfulDisclosureClaim.toQuery trustTriangleStructuredEncoder =
      bodhisattvaNonMaleficenceQuery := by
  simp [avoidHarmfulDisclosureClaim, StructuredEthicalClaim.toQuery,
    trustTriangleStructuredEncoder, bodhisattvaNonMaleficenceQuery]

@[simp] theorem avoidCoerciveOverrideQuery_eq :
    avoidCoerciveOverrideClaim.toQuery trustTriangleStructuredEncoder =
      bodhisattvaConsentQuery := by
  simp [avoidCoerciveOverrideClaim, StructuredEthicalClaim.toQuery,
    trustTriangleStructuredEncoder, bodhisattvaConsentQuery]

theorem trustTriangleStructuredClaim_supportedOn_coreTriangle
    (claim : StructuredEthicalClaim TrustTriangleChoiceWorld Nat) :
    claim.supportedOn trustTriangleStructuredEncoder coreTriangle := by
  have hEUL :
      ∀ p ∈ bodhisattvaEpistemicUniversalLoveQuery,
        (p : Sigma fun _ : Nat => Bool).1 ∈ coreTriangle :=
    agent1Query_supported
  have hNoHarm :
      ∀ p ∈ bodhisattvaNonMaleficenceQuery,
        (p : Sigma fun _ : Nat => Bool).1 ∈ coreTriangle :=
    bodhisattvaNonMaleficenceQuery_supported
  have hConsent :
      ∀ p ∈ bodhisattvaConsentQuery,
        (p : Sigma fun _ : Nat => Bool).1 ∈ coreTriangle :=
    bodhisattvaConsentQuery_supported
  have hReciprocity :
      ∀ p ∈ bodhisattvaReciprocityQuery,
        (p : Sigma fun _ : Nat => Bool).1 ∈ coreTriangle :=
    bodhisattvaReciprocityQuery_supported
  cases claim with
  | mk subject content presentation ground role =>
      cases content with
      | propositional φ =>
          cases presentation with
          | deontic attr =>
              cases attr with
              | Obligation =>
                  cases ground with
                  | asserted =>
                      cases role <;>
                        simpa [StructuredEthicalClaim.supportedOn, StructuredEthicalClaim.toQuery,
                          trustTriangleStructuredEncoder] using hEUL
                  | gewirthPGC =>
                      cases role with
                      | activeGoal =>
                          simpa [StructuredEthicalClaim.supportedOn, StructuredEthicalClaim.toQuery,
                            trustTriangleStructuredEncoder] using hNoHarm
                      | situation | prediction | plan | standingDisposition =>
                          simpa [StructuredEthicalClaim.supportedOn, StructuredEthicalClaim.toQuery,
                            trustTriangleStructuredEncoder] using hEUL
                  | universalDuty d =>
                      cases d <;> cases role <;>
                        simpa [StructuredEthicalClaim.supportedOn, StructuredEthicalClaim.toQuery,
                          trustTriangleStructuredEncoder] using hEUL
                  | careRelation source target rel =>
                      cases role <;>
                        simpa [StructuredEthicalClaim.supportedOn, StructuredEthicalClaim.toQuery,
                          trustTriangleStructuredEncoder] using hEUL
                  | consequentialist =>
                      cases role <;>
                        simpa [StructuredEthicalClaim.supportedOn, StructuredEthicalClaim.toQuery,
                          trustTriangleStructuredEncoder] using hEUL
              | Prohibition =>
                  cases ground with
                  | asserted =>
                      cases role <;>
                        simpa [StructuredEthicalClaim.supportedOn, StructuredEthicalClaim.toQuery,
                          trustTriangleStructuredEncoder] using hEUL
                  | gewirthPGC =>
                      cases role <;>
                        simpa [StructuredEthicalClaim.supportedOn, StructuredEthicalClaim.toQuery,
                          trustTriangleStructuredEncoder] using hEUL
                  | universalDuty d =>
                      cases d with
                      | noHarm =>
                          cases role with
                          | activeGoal =>
                              simpa [StructuredEthicalClaim.supportedOn, StructuredEthicalClaim.toQuery,
                                trustTriangleStructuredEncoder] using hNoHarm
                          | situation | prediction | plan | standingDisposition =>
                              simpa [StructuredEthicalClaim.supportedOn, StructuredEthicalClaim.toQuery,
                                trustTriangleStructuredEncoder] using hEUL
                      | respectAutonomy =>
                          cases role with
                          | activeGoal =>
                              simpa [StructuredEthicalClaim.supportedOn, StructuredEthicalClaim.toQuery,
                                trustTriangleStructuredEncoder] using hConsent
                          | situation | prediction | plan | standingDisposition =>
                              simpa [StructuredEthicalClaim.supportedOn, StructuredEthicalClaim.toQuery,
                                trustTriangleStructuredEncoder] using hEUL
                      | noDeception | noCoercion | keepPromises | beneficence =>
                          cases role <;>
                            simpa [StructuredEthicalClaim.supportedOn, StructuredEthicalClaim.toQuery,
                              trustTriangleStructuredEncoder] using hEUL
                  | careRelation source target rel =>
                      cases role <;>
                        simpa [StructuredEthicalClaim.supportedOn, StructuredEthicalClaim.toQuery,
                          trustTriangleStructuredEncoder] using hEUL
                  | consequentialist =>
                      cases role <;>
                        simpa [StructuredEthicalClaim.supportedOn, StructuredEthicalClaim.toQuery,
                          trustTriangleStructuredEncoder] using hEUL
              | Permission =>
                  cases ground <;> cases role <;>
                    simpa [StructuredEthicalClaim.supportedOn, StructuredEthicalClaim.toQuery,
                      trustTriangleStructuredEncoder] using hEUL
          | axiological attr =>
              cases ground <;> cases role <;>
                simpa [StructuredEthicalClaim.supportedOn, StructuredEthicalClaim.toQuery,
                  trustTriangleStructuredEncoder] using hEUL
          | unmodalized =>
              cases ground <;> cases role <;>
                simpa [StructuredEthicalClaim.supportedOn, StructuredEthicalClaim.toQuery,
                  trustTriangleStructuredEncoder] using hEUL
      | relational a b r =>
          cases r <;>
            first
              | simpa [StructuredEthicalClaim.supportedOn, StructuredEthicalClaim.toQuery,
                  trustTriangleStructuredEncoder] using hEUL
              | simpa [StructuredEthicalClaim.supportedOn, StructuredEthicalClaim.toQuery,
                  trustTriangleStructuredEncoder] using hReciprocity
      | dispositional a =>
          simpa [StructuredEthicalClaim.supportedOn, StructuredEthicalClaim.toQuery,
            trustTriangleStructuredEncoder] using hEUL

@[simp] theorem trustTriangleAutonomousMeaning_activeGoal_mem_traceSeed :
    trustTriangleAutonomousMeaningProfile.activeGoalQuery trustTriangleStructuredEncoder ∈
      traceSeed
        (trustTriangleStructuredTraceSource.frontier trustTriangleStructuredEncoder)
        ({TrustTriangleStructuredObservation.coerciveOverrideCue} :
          Multiset TrustTriangleStructuredObservation) := by
  refine (StructuredESOTraceSource.mem_traceSeed_iff
      (source := trustTriangleStructuredTraceSource)
      (enc := trustTriangleStructuredEncoder)
      (σ := ({TrustTriangleStructuredObservation.coerciveOverrideCue} :
        Multiset TrustTriangleStructuredObservation))
      (q := trustTriangleAutonomousMeaningProfile.activeGoalQuery trustTriangleStructuredEncoder)).2 ?_
  refine ⟨.coerciveOverrideCue, by decide, avoidCoerciveOverrideClaim, ?_, ?_⟩
  · simp [trustTriangleStructuredTraceSource]
  · simp [StructuredFoundationalMeaningProfile.activeGoalQuery, trustTriangleAutonomousMeaningProfile]

/-- Live active-goal conflict lane for the autonomous deliberation story. -/
def trustTriangleAutonomousConflictLane :
    EthicalConflictLane TrustTriangleChoiceWorld Nat where
  options := {avoidHarmfulDisclosureClaim, avoidCoerciveOverrideClaim}
  activeGoalOnly := by
    intro claim hclaim
    simp [avoidHarmfulDisclosureClaim, avoidCoerciveOverrideClaim] at hclaim
    rcases hclaim with rfl | rfl <;> rfl
  propositionalOnly := by
    intro claim hclaim
    simp [avoidHarmfulDisclosureClaim, avoidCoerciveOverrideClaim] at hclaim
    rcases hclaim with rfl | rfl
    · exact ⟨harmfulDisclosureFormula, rfl⟩
    · exact ⟨coerciveOverrideFormula, rfl⟩

/-- Toy semantics saying every candidate in this conflict lane is prohibited. -/
def trustTriangleConflictDeonticSemantics : DeonticSemantics TrustTriangleChoiceWorld where
  deontic attr _ _ := attr = .Prohibition

/-- The aligned value view of the same conflict lane. -/
def trustTriangleConflictValueSemantics : ValueSemantics TrustTriangleChoiceWorld where
  morally attr _ _ := attr = .MorallyBad

/-- Utility view of the same dilemma: every candidate has negative utility. -/
def trustTriangleConflictUtilitySemantics :
    UtilityAssignmentSemantics TrustTriangleChoiceWorld where
  utility := fun _ _ => -1

theorem trustTriangleConflict_alignment :
    ∀ a φ w,
      trustTriangleConflictDeonticSemantics.deontic a φ w ↔
        trustTriangleConflictValueSemantics.morally (deonticToMoralValue a) φ w := by
  intro a φ w
  cases a <;>
    simp [trustTriangleConflictDeonticSemantics, trustTriangleConflictValueSemantics,
      deonticToMoralValue]

theorem trustTriangleAutonomousConflictLane_deonticDilemma :
    trustTriangleAutonomousConflictLane.DeonticMoralDilemmaAt
      trustTriangleConflictDeonticSemantics true := by
  intro φ hφ
  simp [trustTriangleConflictDeonticSemantics]

theorem trustTriangleAutonomousConflictLane_valueDilemma :
    trustTriangleAutonomousConflictLane.ValueMoralDilemmaAt
      trustTriangleConflictValueSemantics true := by
  exact
    (trustTriangleAutonomousConflictLane.deonticMoralDilemmaAt_iff_valueMoralDilemmaAt
      trustTriangleConflictDeonticSemantics trustTriangleConflictValueSemantics
      trustTriangleConflict_alignment true).mp
        trustTriangleAutonomousConflictLane_deonticDilemma

theorem trustTriangleAutonomousConflictLane_utilitarianDilemma :
    trustTriangleAutonomousConflictLane.UtilitarianMoralDilemmaAt
      trustTriangleConflictUtilitySemantics true := by
  intro φ hφ
  simp [trustTriangleConflictUtilitySemantics]

theorem trustTriangleAutonomousConflictLane_virtueDilemma :
    trustTriangleAutonomousConflictLane.VirtueTargetMoralDilemmaAt
      (virtueTargetSemanticsOfUtility
        TrustTriangleChoiceWorld trustTriangleConflictUtilitySemantics) true := by
  exact
    (trustTriangleAutonomousConflictLane.utilitarianMoralDilemmaAt_iff_virtueTargetMoralDilemmaAt
      trustTriangleConflictUtilitySemantics true).mp
        trustTriangleAutonomousConflictLane_utilitarianDilemma

/-- End-to-end autonomous deliberation theorem:

one structured active goal is seeded into the foundational-meaning profile from
observations, while the live active-goal `ChoicePoint` is recognized as a
dilemma across the deontic, value, utilitarian, and virtue readings. -/
theorem trustTriangle_autonomous_choicePoint_example :
    trustTriangleAutonomousMeaningProfile.activeGoalQuery trustTriangleStructuredEncoder ∈
      traceSeed
        (trustTriangleStructuredTraceSource.frontier trustTriangleStructuredEncoder)
        ({TrustTriangleStructuredObservation.coerciveOverrideCue} :
          Multiset TrustTriangleStructuredObservation) ∧
    trustTriangleAutonomousConflictLane.DeonticMoralDilemmaAt
      trustTriangleConflictDeonticSemantics true ∧
    trustTriangleAutonomousConflictLane.ValueMoralDilemmaAt
      trustTriangleConflictValueSemantics true ∧
    trustTriangleAutonomousConflictLane.UtilitarianMoralDilemmaAt
      trustTriangleConflictUtilitySemantics true ∧
    trustTriangleAutonomousConflictLane.VirtueTargetMoralDilemmaAt
      (virtueTargetSemanticsOfUtility
        TrustTriangleChoiceWorld trustTriangleConflictUtilitySemantics) true := by
  refine ⟨trustTriangleAutonomousMeaning_activeGoal_mem_traceSeed, ?_, ?_, ?_, ?_⟩
  · exact trustTriangleAutonomousConflictLane_deonticDilemma
  · exact trustTriangleAutonomousConflictLane_valueDilemma
  · exact trustTriangleAutonomousConflictLane_utilitarianDilemma
  · exact trustTriangleAutonomousConflictLane_virtueDilemma

end Mettapedia.CognitiveArchitecture.GodelClaw.Ethics.Ontology
