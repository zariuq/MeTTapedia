import Mettapedia.CognitiveArchitecture.GodelClaw.Ethics.MetaEthicsKernel
import Mettapedia.CognitiveArchitecture.GodelClaw.Ethics.EthicalDecisionProblems
import Mettapedia.CognitiveArchitecture.GodelClaw.Ethics.PracticalResolutionTrustTriangleExample
import Mettapedia.CognitiveArchitecture.GodelClaw.Ethics.Ontology.GewirthTrustTriangleExample

set_option autoImplicit false

/-!
# Meta-Ethics: Trust-Triangle Example

This file provides the top-down counterpart to the practical trust-triangle
resolver:

- a concrete `MetaEthicalTheory`,
- a theory-guided rendering of actions into structured ethical claims,
- a simple admissibility discipline,
- and a small capstone theorem connecting recommendation, admissibility,
  and the meaning/WM bridge.

The design stays intentionally small.  The point is not to settle all of
meta-ethics here.  The point is to show one clean seam where:

1. a grounded theory constrains admissibility,
2. the practical resolver still recommends the same action,
3. and the recommended action becomes the active goal of a structured
   foundational-meaning profile.
-/

namespace Mettapedia.CognitiveArchitecture.GodelClaw.Ethics

open Mettapedia.Ethics
open Mettapedia.CognitiveArchitecture.GodelClaw.Ethics.Ontology
open Mettapedia.Logic.MarkovLogicClauseFactorGraph
open Mettapedia.Logic.MarkovLogicTrustTriangleExample
open Mettapedia.Logic.MarkovLogicAbstract
open Mettapedia.Logic.MarkovLogicAbstract.MassState

/-- The positive candidate formula in the two-state toy world.

This is intentionally world-robust: safe escalation is modeled as a fallback
policy available in either toy state, unlike the two bad candidates which each
pin the world to one bad branch. -/
def safeEscalationFormula : Formula TrustTriangleChoiceWorld := fun _ => True

theorem safeEscalationFormula_ne_harmfulDisclosureFormula :
    safeEscalationFormula ≠ harmfulDisclosureFormula := by
  intro h
  have hfalse := congrFun h true
  simp [safeEscalationFormula, harmfulDisclosureFormula] at hfalse

theorem safeEscalationFormula_ne_coerciveOverrideFormula :
    safeEscalationFormula ≠ coerciveOverrideFormula := by
  intro h
  have hfalse := congrFun h false
  simp [safeEscalationFormula, coerciveOverrideFormula] at hfalse

/-- The top-down positive claim endorsing the safe-escalation option. -/
def endorseSafeEscalationClaim : StructuredEthicalClaim TrustTriangleChoiceWorld Nat where
  subject := 1
  content := .propositional safeEscalationFormula
  presentation := .axiological .MorallyGood
  ground := .asserted
  role := .activeGoal

/-- The enlarged active-goal lane containing both bad options and the positive
safe-escalation option. -/
def trustTrianglePracticalConflictLane :
    EthicalConflictLane TrustTriangleChoiceWorld Nat where
  options := {
    avoidHarmfulDisclosureClaim,
    avoidCoerciveOverrideClaim,
    endorseSafeEscalationClaim
  }
  activeGoalOnly := by
    intro claim hclaim
    simp [avoidHarmfulDisclosureClaim, avoidCoerciveOverrideClaim,
      endorseSafeEscalationClaim] at hclaim
    rcases hclaim with rfl | rfl | rfl <;> rfl
  propositionalOnly := by
    intro claim hclaim
    simp [avoidHarmfulDisclosureClaim, avoidCoerciveOverrideClaim,
      endorseSafeEscalationClaim] at hclaim
    rcases hclaim with rfl | rfl | rfl
    · exact ⟨harmfulDisclosureFormula, rfl⟩
    · exact ⟨coerciveOverrideFormula, rfl⟩
    · exact ⟨safeEscalationFormula, rfl⟩

/-- The practical action formulas used by the top-down admissibility filter. -/
def trustTriangleActionFormula : TrustTriangleAction → Formula TrustTriangleChoiceWorld
  | .harmfulDisclosure => harmfulDisclosureFormula
  | .coerciveOverride => coerciveOverrideFormula
  | .safeEscalation => safeEscalationFormula

/-- The explicit practical problem induced by the trust-triangle action space. -/
def trustTrianglePracticalProblem :
    PracticalEthicalProblem TrustTriangleChoiceWorld Nat TrustTriangleAction where
  conflict := trustTrianglePracticalConflictLane
  candidates := Set.univ
  actionFormula := trustTriangleActionFormula
  candidate_sound := by
    intro a _
    cases a
    · exact ⟨avoidHarmfulDisclosureClaim, by
        simp [trustTrianglePracticalConflictLane], rfl⟩
    · exact ⟨avoidCoerciveOverrideClaim, by
        simp [trustTrianglePracticalConflictLane], rfl⟩
    · exact ⟨endorseSafeEscalationClaim, by
        simp [trustTrianglePracticalConflictLane], rfl⟩

/-- The top-down discipline admits only candidates in the current choice point
that are not the harmful-disclosure or coercive-override branches. -/
def trustTriangleConflictDiscipline :
    ConflictDiscipline TrustTriangleChoiceWorld where
  admissible cp φ :=
    φ ∈ cp ∧ φ ≠ harmfulDisclosureFormula ∧ φ ≠ coerciveOverrideFormula

theorem trustTriangleConflictDiscipline_safeEscalation_admissible :
    trustTriangleConflictDiscipline.admissible
      trustTrianglePracticalProblem.choicePoint safeEscalationFormula := by
  refine ⟨?_, safeEscalationFormula_ne_harmfulDisclosureFormula,
    safeEscalationFormula_ne_coerciveOverrideFormula⟩
  exact ⟨.safeEscalation, trivial, rfl⟩

theorem trustTriangleConflictDiscipline_harmfulDisclosure_inadmissible :
    ¬ trustTriangleConflictDiscipline.admissible
        trustTrianglePracticalProblem.choicePoint harmfulDisclosureFormula := by
  intro h
  exact h.2.1 rfl

theorem trustTriangleConflictDiscipline_coerciveOverride_inadmissible :
    ¬ trustTriangleConflictDiscipline.admissible
        trustTrianglePracticalProblem.choicePoint coerciveOverrideFormula := by
  intro h
  exact h.2.2 rfl

/-- Boolean companion to the trust-triangle admissibility discipline at the
computable practical-action seam. -/
def trustTriangleComputableConflictDiscipline :
    ComputableConflictDiscipline trustTrianglePracticalProblem where
  toConflictDiscipline := trustTriangleConflictDiscipline
  admissibleAction
    | .harmfulDisclosure => false
    | .coerciveOverride => false
    | .safeEscalation => true
  admissibleAction_spec := by
    intro a
    cases a <;>
      simp [trustTriangleConflictDiscipline, trustTrianglePracticalProblem,
        trustTrianglePracticalConflictLane, trustTriangleActionFormula,
        avoidHarmfulDisclosureClaim, avoidCoerciveOverrideClaim,
        endorseSafeEscalationClaim,
        safeEscalationFormula_ne_harmfulDisclosureFormula,
        safeEscalationFormula_ne_coerciveOverrideFormula]

/-- In the trust-triangle toy case, the admissible subset is exactly the safe
escalation action. -/
theorem mem_trustTriangle_admissibleCandidates_iff
    (a : TrustTriangleAction) :
    a ∈ admissibleCandidates
        trustTriangleConflictDiscipline
        trustTrianglePracticalProblem
        trustTriangleCandidateSet.toFinset ↔
      a = .safeEscalation := by
  cases a <;>
    simp [admissibleCandidates, trustTriangleCandidateSet_toFinset,
      trustTriangleCandidates, trustTriangleConflictDiscipline,
      trustTrianglePracticalProblem, trustTrianglePracticalConflictLane,
      trustTriangleActionFormula,
      avoidHarmfulDisclosureClaim, avoidCoerciveOverrideClaim,
      endorseSafeEscalationClaim,
      safeEscalationFormula_ne_harmfulDisclosureFormula,
      safeEscalationFormula_ne_coerciveOverrideFormula]

/-- Safe escalation dominates the admissible subset induced by the top-down
discipline. -/
theorem safeEscalation_dominates_trustTriangle_admissibleCandidates :
    dominatesAll trustTrianglePrinciple trustTriangleProfiles
      (admissibleCandidates
        trustTriangleConflictDiscipline
        trustTrianglePracticalProblem
        trustTriangleCandidateSet.toFinset)
      .safeEscalation := by
  constructor
  · exact (mem_trustTriangle_admissibleCandidates_iff .safeEscalation).2 rfl
  · intro b hb hne
    have hbSafe : b = .safeEscalation :=
      (mem_trustTriangle_admissibleCandidates_iff b).1 hb
    exact False.elim (hne hbSafe)

/-- The live theory-guided computable resolver really does recommend safe
escalation once the top-down discipline is compiled to a boolean filter. -/
theorem trustTriangle_theoryGuidedResolveJudgmentComputable_recommends_safeEscalation :
    (theoryGuidedResolveJudgmentComputable
        trustTriangleComputableConflictDiscipline
        trustTriangleDutyDomain
        trustTriangleCandidateSet
        trustTrianglePrinciple
        trustTriangleProfiles).Recommends .safeEscalation := by
  have hexists :
      ∃ a ∈ admissibleCandidates
          trustTriangleComputableConflictDiscipline.toConflictDiscipline
          trustTrianglePracticalProblem
          trustTriangleCandidateSet.toFinset,
        dominatesAll trustTrianglePrinciple trustTriangleProfiles
          (admissibleCandidates
            trustTriangleComputableConflictDiscipline.toConflictDiscipline
            trustTrianglePracticalProblem
            trustTriangleCandidateSet.toFinset) a := by
    refine ⟨.safeEscalation,
      (mem_trustTriangle_admissibleCandidates_iff .safeEscalation).2 rfl,
      safeEscalation_dominates_trustTriangle_admissibleCandidates⟩
  rcases theoryGuidedResolveJudgmentComputable_chosen_admissible_and_dominant
      (discipline := trustTriangleComputableConflictDiscipline)
      (dutyDomain := trustTriangleDutyDomain)
      (candidateSet := trustTriangleCandidateSet)
      (principle := trustTrianglePrinciple)
      (profiles := trustTriangleProfiles)
      hexists with
    ⟨a, hrec, hadm, _⟩
  have ha : a = .safeEscalation :=
    (mem_trustTriangle_admissibleCandidates_iff a).1 hadm
  simpa [ha] using hrec

/-- Explicit filtered comparison count for the trust-triangle theory-guided
decision problem: 3 candidate checks plus the coarse quadratic fallback over
the 3 candidates, 1 clause, and 2 duties. -/
theorem trustTriangle_theoryGuided_filteredComparisonCount_eq :
    filteredComparisonCount 3 1 1 2 = 21 := by
  norm_num [filteredComparisonCount]

/-- Reusable theory-guided computational-ethics package for the trust-triangle
lane.  This turns the concrete example into one explicit decision problem:
admissibility, dominant admissibility, recommendation, and budget are now all
spoken in the shared decision-problem vocabulary. -/
def trustTriangleTheoryGuidedDecisionProblem :
    TheoryGuidedDecisionProblem
      TrustTriangleChoiceWorld Nat TrustTriangleAction
      TrustTriangleFeature TrustTriangleDuty where
  practicalProblem := trustTrianglePracticalProblem
  discipline := trustTriangleComputableConflictDiscipline
  dutyDomain := trustTriangleDutyDomain
  candidateSet := trustTriangleCandidateSet
  principle := trustTrianglePrinciple
  profiles := trustTriangleProfiles
  filterCheckCost := 1

theorem trustTriangleTheoryGuidedDecisionProblem_hasDominantAdmissibleAction :
    trustTriangleTheoryGuidedDecisionProblem.HasDominantAdmissibleAction := by
  refine ⟨.safeEscalation, ?_, ?_⟩
  · simpa [TheoryGuidedDecisionProblem.admissibleActionSet,
      trustTriangleTheoryGuidedDecisionProblem] using
      (mem_trustTriangle_admissibleCandidates_iff .safeEscalation).2 rfl
  · simpa [TheoryGuidedDecisionProblem.admissibleActionSet,
      trustTriangleTheoryGuidedDecisionProblem] using
      safeEscalation_dominates_trustTriangle_admissibleCandidates

theorem trustTriangleTheoryGuidedDecisionProblem_hasAdmissibleAction :
    trustTriangleTheoryGuidedDecisionProblem.HasAdmissibleAction := by
  exact TheoryGuidedDecisionProblem.hasAdmissibleAction_of_hasDominantAdmissibleAction
    trustTriangleTheoryGuidedDecisionProblem_hasDominantAdmissibleAction

theorem trustTriangleTheoryGuidedDecisionProblem_status_recommends :
    trustTriangleTheoryGuidedDecisionProblem.resolveJudgment.status = .recommends := by
  exact TheoryGuidedDecisionProblem.status_recommends_of_hasDominantAdmissibleAction
    trustTriangleTheoryGuidedDecisionProblem_hasDominantAdmissibleAction

theorem trustTriangleTheoryGuidedDecisionProblem_recommends_safeEscalation :
    trustTriangleTheoryGuidedDecisionProblem.Recommends .safeEscalation := by
  simpa [TheoryGuidedDecisionProblem.Recommends,
    TheoryGuidedDecisionProblem.resolveJudgment,
    trustTriangleTheoryGuidedDecisionProblem] using
    trustTriangle_theoryGuidedResolveJudgmentComputable_recommends_safeEscalation

theorem trustTriangleTheoryGuidedDecisionProblem_safeEscalation_is_admissible_and_dominant :
    trustTriangleTheoryGuidedDecisionProblem.Recommends .safeEscalation ∧
      .safeEscalation ∈ trustTriangleTheoryGuidedDecisionProblem.admissibleActionSet ∧
      dominatesAll trustTrianglePrinciple trustTriangleProfiles
        trustTriangleTheoryGuidedDecisionProblem.admissibleActionSet
        .safeEscalation := by
  refine ⟨trustTriangleTheoryGuidedDecisionProblem_recommends_safeEscalation, ?_, ?_⟩
  · simpa [TheoryGuidedDecisionProblem.admissibleActionSet,
      trustTriangleTheoryGuidedDecisionProblem] using
      (mem_trustTriangle_admissibleCandidates_iff .safeEscalation).2 rfl
  · simpa [TheoryGuidedDecisionProblem.admissibleActionSet,
      trustTriangleTheoryGuidedDecisionProblem] using
      safeEscalation_dominates_trustTriangle_admissibleCandidates

theorem trustTriangleTheoryGuidedDecisionProblem_comparisonBudget_eq :
    trustTriangleTheoryGuidedDecisionProblem.comparisonBudget = 21 := by
  simpa [TheoryGuidedDecisionProblem.comparisonBudget,
    trustTriangleTheoryGuidedDecisionProblem] using
    trustTriangle_theoryGuided_filteredComparisonCount_eq

/-- Deontological support for the no-harm branch of the scenario. -/
def trustTriangleNoHarmConstraint :
    Mettapedia.CognitiveArchitecture.Values.Deontological.DeontologicalConstraint
      TrustTriangleAction where
  status
    | .harmfulDisclosure => .forbidden
    | _ => .permitted
  description := "Trust-triangle no-harm constraint"

/-- Deontological support for the autonomy branch of the scenario. -/
def trustTriangleAutonomyConstraint :
    Mettapedia.CognitiveArchitecture.Values.Deontological.DeontologicalConstraint
      TrustTriangleAction where
  status
    | .coerciveOverride => .forbidden
    | _ => .permitted
  description := "Trust-triangle autonomy constraint"

/-- Duty strengths used to witness the universal-duty grounds in the
trust-triangle theory. -/
def trustTriangleDutyStrengths :
    Mettapedia.CognitiveArchitecture.Values.Deontological.UniversalDuty →
      Mettapedia.CognitiveArchitecture.Values.Deontological.ObligationStrength
  | .noHarm =>
      { confidence := Mettapedia.CognitiveArchitecture.OpenPsi.UnitValue.one
        importance := Mettapedia.CognitiveArchitecture.OpenPsi.UnitValue.one }
  | .respectAutonomy =>
      { confidence := Mettapedia.CognitiveArchitecture.OpenPsi.UnitValue.one
        importance := Mettapedia.CognitiveArchitecture.OpenPsi.UnitValue.one }
  | _ =>
      { confidence := Mettapedia.CognitiveArchitecture.OpenPsi.UnitValue.half
        importance := Mettapedia.CognitiveArchitecture.OpenPsi.UnitValue.half }

/-- A concrete deontological layer witnessing that the two trust-triangle
universal duties are live and positively weighted. -/
def trustTriangleDeontologicalLayer :
    Mettapedia.CognitiveArchitecture.Values.Deontological.DeontologicalLayer
      TrustTriangleAction where
  constraints :=
    { constraints := [trustTriangleNoHarmConstraint, trustTriangleAutonomyConstraint] }
  dutyStrengths := trustTriangleDutyStrengths
  strictTruth := true

theorem trustTriangle_noHarm_ground_witnessed :
    (EthicalGround.universalDuty
      Mettapedia.CognitiveArchitecture.Values.Deontological.UniversalDuty.noHarm :
      EthicalGround Nat).Witnessed₀ := by
  refine EthicalGround.witnessed₀_universalDuty_of_positiveStrength
    trustTriangleDeontologicalLayer
    Mettapedia.CognitiveArchitecture.Values.Deontological.UniversalDuty.noHarm ?_ ?_
  · norm_num [trustTriangleDeontologicalLayer, trustTriangleDutyStrengths,
      Mettapedia.CognitiveArchitecture.OpenPsi.UnitValue.one]
  · norm_num [trustTriangleDeontologicalLayer, trustTriangleDutyStrengths,
      Mettapedia.CognitiveArchitecture.OpenPsi.UnitValue.one]

theorem trustTriangle_respectAutonomy_ground_witnessed :
    (EthicalGround.universalDuty
      Mettapedia.CognitiveArchitecture.Values.Deontological.UniversalDuty.respectAutonomy :
      EthicalGround Nat).Witnessed₀ := by
  refine EthicalGround.witnessed₀_universalDuty_of_positiveStrength
    trustTriangleDeontologicalLayer
    Mettapedia.CognitiveArchitecture.Values.Deontological.UniversalDuty.respectAutonomy ?_ ?_
  · norm_num [trustTriangleDeontologicalLayer, trustTriangleDutyStrengths,
      Mettapedia.CognitiveArchitecture.OpenPsi.UnitValue.one]
  · norm_num [trustTriangleDeontologicalLayer, trustTriangleDutyStrengths,
      Mettapedia.CognitiveArchitecture.OpenPsi.UnitValue.one]

/-- The grounded normative base for the tiny top-down theory. -/
def trustTriangleNormativeBase :
    NormativeBase TrustTriangleChoiceWorld Nat where
  core := {
    avoidHarmfulDisclosureClaim,
    avoidCoerciveOverrideClaim,
    endorseSafeEscalationClaim
  }
  grounded := by
    intro claim hclaim
    simp [avoidHarmfulDisclosureClaim, avoidCoerciveOverrideClaim,
      endorseSafeEscalationClaim] at hclaim
    rcases hclaim with rfl | rfl | rfl
    · exact trustTriangle_noHarm_ground_witnessed
    · exact trustTriangle_respectAutonomy_ground_witnessed
    · exact EthicalGround.witnessed₀_asserted

/-- Bridge principle: the harmful-disclosure situation licenses the no-harm
prohibition claim. -/
def harmfulDisclosureBridge :
    BridgePrinciple TrustTriangleChoiceWorld Nat where
  premises := harmfulDisclosureFormula
  conclusion := avoidHarmfulDisclosureClaim

/-- Bridge principle: the coercive-override situation licenses the autonomy
prohibition claim. -/
def coerciveOverrideBridge :
    BridgePrinciple TrustTriangleChoiceWorld Nat where
  premises := coerciveOverrideFormula
  conclusion := avoidCoerciveOverrideClaim

/-- Bridge principle: the world-robust fallback situation licenses the
positive safe-escalation claim. -/
def safeEscalationBridge :
    BridgePrinciple TrustTriangleChoiceWorld Nat where
  premises := safeEscalationFormula
  conclusion := endorseSafeEscalationClaim

/-- A tiny trust-triangle theory with one primary deontological reading and a
pluralistic admissible-paradigm set. -/
def trustTriangleMetaTheory :
    MetaEthicalTheory TrustTriangleChoiceWorld Nat where
  descriptiveAssumptions := {safeEscalationFormula}
  normativeBase := trustTriangleNormativeBase
  bridgePrinciples := {
    harmfulDisclosureBridge,
    coerciveOverrideBridge,
    safeEscalationBridge
  }
  bridges_grounded := by
    intro bp hbp
    simp [harmfulDisclosureBridge, coerciveOverrideBridge, safeEscalationBridge] at hbp
    rcases hbp with rfl | rfl | rfl
    · exact trustTriangle_noHarm_ground_witnessed
    · exact trustTriangle_respectAutonomy_ground_witnessed
    · exact EthicalGround.witnessed₀_asserted
  primaryParadigm := .deontological
  admissibleParadigms := Set.univ
  primary_mem_admissible := by simp
  conflictDiscipline := trustTriangleConflictDiscipline

/-- Render each practical action into the structured ethical claim it activates
in the top-down theory. -/
def trustTriangleActionRendering :
    ActionRendering TrustTriangleChoiceWorld Nat TrustTriangleAction where
  toClaim
    | .harmfulDisclosure => avoidHarmfulDisclosureClaim
    | .coerciveOverride => avoidCoerciveOverrideClaim
    | .safeEscalation => endorseSafeEscalationClaim

/-- The concrete theory-guided interface for the trust-triangle action space. -/
def trustTriangleTheoryGuidedInterface :
    TheoryGuidedPracticalInterface TrustTriangleChoiceWorld Nat TrustTriangleAction where
  theory := trustTriangleMetaTheory
  rendering := trustTriangleActionRendering

/-- The practical bridge obtained from the top-down rendering and the existing
structured trust-triangle encoder. -/
def trustTriangleTheoryPracticalBridge : PracticalEthicsBridge TrustTriangleChoiceWorld Nat
    TrustTriangleAction Nat :=
  trustTriangleTheoryGuidedInterface.toPracticalBridge trustTriangleStructuredEncoder

/-- Concrete label policy for staging the trust-triangle action rendering
through the legacy upper-shard encoder.  The policy depends on content/ground
but intentionally ignores presentation, so aligned deontic/value readings keep
the same legacy label. -/
def trustTriangleUpperShardStructuredLabeler :
    StructuredClaimLabeler TrustTriangleChoiceWorld Nat
      Ontology.TrustTriangleUpperShardLabel where
  label claim :=
    match claim.content, claim.ground with
    | .propositional _, .universalDuty .noHarm => .nonInterference
    | .propositional _, .universalDuty .respectAutonomy => .respectAutonomy
    | .propositional _, .asserted => .friendship
    | .relational _ _ .friendship, _ => .friendship
    | .dispositional _, _ => .friendship
    | _, _ => .friendship

theorem trustTriangleUpperShardStructuredLabeler_aligned :
    trustTriangleUpperShardStructuredLabeler.DeonticValueAligned := by
  intro _ ground _ _ _
  cases ground <;> rfl

/-- Practical bridge that stages the trust-triangle action rendering through
the live legacy upper-shard encoder.  This is the concrete instance used to
discharge the new labeler-alignment hypothesis on a real encoder/labeler pair.
-/
def trustTriangleUpperShardLegacyPracticalBridge :
    PracticalEthicsBridge TrustTriangleChoiceWorld Nat TrustTriangleAction Nat :=
  trustTriangleActionRendering.toPracticalBridge
    (StructuredEthicsQueryEncoder.ofLegacy
      trustTriangleUpperShardStructuredLabeler
      (Ontology.trustTriangleUpperShardEncoder (Agent := Nat)))

theorem trustTriangleUpperShardLegacyPracticalBridge_harmfulDisclosure_query_eq_axiological :
    trustTriangleUpperShardLegacyPracticalBridge.actionQuery .harmfulDisclosure =
      ({ subject := 1
         content := .propositional harmfulDisclosureFormula
         presentation := .axiological (deonticToMoralValue .Prohibition)
         ground := .universalDuty .noHarm
         role := .activeGoal } : StructuredEthicalClaim TrustTriangleChoiceWorld Nat).toQuery
        (StructuredEthicsQueryEncoder.ofLegacy
          trustTriangleUpperShardStructuredLabeler
          (Ontology.trustTriangleUpperShardEncoder (Agent := Nat))) := by
  simpa [trustTriangleUpperShardLegacyPracticalBridge] using
    (ActionRendering.toPracticalBridge_actionQuery_deontic_toAxiological_ofLegacy_eq_of_aligned
      (rendering := trustTriangleActionRendering)
      (labeler := trustTriangleUpperShardStructuredLabeler)
      (enc := Ontology.trustTriangleUpperShardEncoder (Agent := Nat))
      (hEncAlign := Ontology.trustTriangleUpperShardEncoder_aligned (Agent := Nat))
      (hLabelAlign := trustTriangleUpperShardStructuredLabeler_aligned)
      (a := .harmfulDisclosure)
      (subject := 1)
      (ground := .universalDuty .noHarm)
      (role := .activeGoal)
      (tag := .Prohibition)
      (φ := harmfulDisclosureFormula)
      (hClaim := rfl))

theorem trustTriangleUpperShardLegacyPracticalBridge_harmfulDisclosure_query_eq_nonMaleficence :
    trustTriangleUpperShardLegacyPracticalBridge.actionQuery .harmfulDisclosure =
      bodhisattvaNonMaleficenceQuery := by
  rw [trustTriangleUpperShardLegacyPracticalBridge_harmfulDisclosure_query_eq_axiological]
  rfl

theorem trustTriangleUpperShardLegacyPracticalBridge_coerciveOverride_query_eq_axiological :
    trustTriangleUpperShardLegacyPracticalBridge.actionQuery .coerciveOverride =
      ({ subject := 1
         content := .propositional coerciveOverrideFormula
         presentation := .axiological (deonticToMoralValue .Prohibition)
         ground := .universalDuty .respectAutonomy
         role := .activeGoal } : StructuredEthicalClaim TrustTriangleChoiceWorld Nat).toQuery
        (StructuredEthicsQueryEncoder.ofLegacy
          trustTriangleUpperShardStructuredLabeler
          (Ontology.trustTriangleUpperShardEncoder (Agent := Nat))) := by
  simpa [trustTriangleUpperShardLegacyPracticalBridge] using
    (ActionRendering.toPracticalBridge_actionQuery_deontic_toAxiological_ofLegacy_eq_of_aligned
      (rendering := trustTriangleActionRendering)
      (labeler := trustTriangleUpperShardStructuredLabeler)
      (enc := Ontology.trustTriangleUpperShardEncoder (Agent := Nat))
      (hEncAlign := Ontology.trustTriangleUpperShardEncoder_aligned (Agent := Nat))
      (hLabelAlign := trustTriangleUpperShardStructuredLabeler_aligned)
      (a := .coerciveOverride)
      (subject := 1)
      (ground := .universalDuty .respectAutonomy)
      (role := .activeGoal)
      (tag := .Prohibition)
      (φ := coerciveOverrideFormula)
      (hClaim := rfl))

theorem trustTriangleUpperShardLegacyPracticalBridge_coerciveOverride_query_eq_consent :
    trustTriangleUpperShardLegacyPracticalBridge.actionQuery .coerciveOverride =
      bodhisattvaConsentQuery := by
  rw [trustTriangleUpperShardLegacyPracticalBridge_coerciveOverride_query_eq_axiological]
  rfl

@[simp] theorem trustTriangleTheoryPracticalBridge_safeEscalationQuery :
    trustTriangleTheoryPracticalBridge.actionQuery .safeEscalation =
      bodhisattvaEpistemicUniversalLoveQuery := by
  rfl

/-- The meaning-profile image of the recommended safe-escalation action. -/
def trustTriangleTheoryGuidedMeaningProfile :
    StructuredFoundationalMeaningProfile TrustTriangleChoiceWorld Nat Nat :=
  trustTriangleTheoryPracticalBridge.toMeaningProfile
    bodhisattvaNonMaleficenceQuery
    bodhisattvaEpistemicUniversalLoveQuery
    .safeEscalation
    bodhisattvaConsentQuery

@[simp] theorem trustTriangleTheoryGuidedMeaningProfile_activeGoalQuery :
    trustTriangleTheoryGuidedMeaningProfile.activeGoalQuery trustTriangleStructuredEncoder =
      trustTriangleTheoryPracticalBridge.actionQuery .safeEscalation := by
  rfl

@[simp] theorem trustTriangleTheoryGuidedMeaningProfile_activeGoalQuery_eq_eul :
    trustTriangleTheoryGuidedMeaningProfile.activeGoalQuery trustTriangleStructuredEncoder =
      bodhisattvaEpistemicUniversalLoveQuery := by
  rw [trustTriangleTheoryGuidedMeaningProfile_activeGoalQuery]
  exact trustTriangleTheoryPracticalBridge_safeEscalationQuery

/-- Source-side model for the trust-triangle lane with graded regulative ideals.

The agents partially realize ethical ideals:
- epistemic universal love: 0.7 (substantial but imperfect care)
- non-harm duty: 0.9 (strong commitment)
- respect-autonomy duty: 0.8 (solid commitment)
- friendship: 0.6 (moderate reciprocity)

These are regulative ideals, not constitutive facts: no agent perfectly
realizes them, but all realize them to a positive degree. -/
def trustTriangleStructuredESOModel :
    ESOUpperShardModel TrustTriangleChoiceWorld Nat Unit where
  currentWorld := true
  valueSemantics := {
    morally := fun attr φ w => attr = .MorallyGood ∧ φ w
  }
  deonticSemantics := {
    deontic := fun attr _ _ => attr = .Prohibition
  }
  epistemicUniversalLoveDegree := fun _ => ⟨7/10, by norm_num, by norm_num⟩
  universalDutyDegree := fun _ d => match d with
    | .noHarm => ⟨9/10, by norm_num, by norm_num⟩
    | .respectAutonomy => ⟨8/10, by norm_num, by norm_num⟩
    | _ => ⟨5/10, by norm_num, by norm_num⟩
  relationDegree := fun _ _ r => match r with
    | .friendship => ⟨6/10, by norm_num, by norm_num⟩
    | _ => ⟨3/10, by norm_num, by norm_num⟩

theorem trustTriangleStructuredESOModel_regionSupportAdequate :
    trustTriangleStructuredESOModel.RegionSupportAdequate
      trustTriangleStructuredEncoder coreTriangle := by
  intro claim _
  exact trustTriangleStructuredClaim_supportedOn_coreTriangle claim

theorem avoidHarmfulDisclosureClaim_sat_in_trustTriangleStructuredESOModel :
    trustTriangleStructuredESOModel.SatStructured avoidHarmfulDisclosureClaim := by
  simp [trustTriangleStructuredESOModel, avoidHarmfulDisclosureClaim,
    ESOUpperShardModel.SatStructured]

theorem avoidCoerciveOverrideClaim_sat_in_trustTriangleStructuredESOModel :
    trustTriangleStructuredESOModel.SatStructured avoidCoerciveOverrideClaim := by
  simp [trustTriangleStructuredESOModel, avoidCoerciveOverrideClaim,
    ESOUpperShardModel.SatStructured]

theorem endorseSafeEscalationClaim_sat_in_trustTriangleStructuredESOModel :
    trustTriangleStructuredESOModel.SatStructured endorseSafeEscalationClaim := by
  simp [trustTriangleStructuredESOModel, endorseSafeEscalationClaim,
    ESOUpperShardModel.SatStructured, safeEscalationFormula]

theorem avoidHarmfulDisclosureClaim_wmPositive_in_trustTriangleStructuredESOModel :
    WMPositiveQuerySupport
      ({regionSupportMassSemantics coreTriangle} : MassState (ConstraintQuery Nat))
      (avoidHarmfulDisclosureClaim.toQuery trustTriangleStructuredEncoder) := by
  exact ESOUpperShardModel.satStructured_toWMPositiveQuerySupport_of_regionSupportAdequate
    trustTriangleStructuredESOModel
    trustTriangleStructuredEncoder
    coreTriangle
    trustTriangleStructuredESOModel_regionSupportAdequate
    avoidHarmfulDisclosureClaim
    avoidHarmfulDisclosureClaim_sat_in_trustTriangleStructuredESOModel

theorem avoidCoerciveOverrideClaim_wmPositive_in_trustTriangleStructuredESOModel :
    WMPositiveQuerySupport
      ({regionSupportMassSemantics coreTriangle} : MassState (ConstraintQuery Nat))
      (avoidCoerciveOverrideClaim.toQuery trustTriangleStructuredEncoder) := by
  exact ESOUpperShardModel.satStructured_toWMPositiveQuerySupport_of_regionSupportAdequate
    trustTriangleStructuredESOModel
    trustTriangleStructuredEncoder
    coreTriangle
    trustTriangleStructuredESOModel_regionSupportAdequate
    avoidCoerciveOverrideClaim
    avoidCoerciveOverrideClaim_sat_in_trustTriangleStructuredESOModel

theorem endorseSafeEscalationClaim_wmPositive_in_trustTriangleStructuredESOModel :
    WMPositiveQuerySupport
      ({regionSupportMassSemantics coreTriangle} : MassState (ConstraintQuery Nat))
      (endorseSafeEscalationClaim.toQuery trustTriangleStructuredEncoder) := by
  exact ESOUpperShardModel.satStructured_toWMPositiveQuerySupport_of_regionSupportAdequate
    trustTriangleStructuredESOModel
    trustTriangleStructuredEncoder
    coreTriangle
    trustTriangleStructuredESOModel_regionSupportAdequate
    endorseSafeEscalationClaim
    endorseSafeEscalationClaim_sat_in_trustTriangleStructuredESOModel

theorem trustTriangleTheoryGuidedMeaningProfile_activeGoalQuery_wmPositive :
    WMPositiveQuerySupport
      ({regionSupportMassSemantics coreTriangle} : MassState (ConstraintQuery Nat))
      (trustTriangleTheoryGuidedMeaningProfile.activeGoalQuery trustTriangleStructuredEncoder) := by
  simpa [trustTriangleTheoryGuidedMeaningProfile_activeGoalQuery_eq_eul,
    endorseSafeEscalationClaim, StructuredEthicalClaim.toQuery,
    trustTriangleStructuredEncoder, bodhisattvaEpistemicUniversalLoveQuery] using
    endorseSafeEscalationClaim_wmPositive_in_trustTriangleStructuredESOModel

theorem harmfulDisclosure_not_dominant :
    ¬ dominatesAll trustTrianglePrinciple trustTriangleProfiles
        trustTriangleCandidates .harmfulDisclosure := by
  intro hdom
  have hpref := hdom.2 .safeEscalation (by simp [trustTriangleCandidates]) (by decide)
  rcases hpref with ⟨clause, hmem, hsatisfies⟩
  simp [trustTrianglePrinciple] at hmem
  subst hmem
  have hnoHarm := hsatisfies .noHarm
  simp [GenEthActionProfile.differential, trustTriangleProfiles] at hnoHarm

theorem coerciveOverride_not_dominant :
    ¬ dominatesAll trustTrianglePrinciple trustTriangleProfiles
        trustTriangleCandidates .coerciveOverride := by
  intro hdom
  have hpref := hdom.2 .safeEscalation (by simp [trustTriangleCandidates]) (by decide)
  rcases hpref with ⟨clause, hmem, hsatisfies⟩
  simp [trustTrianglePrinciple] at hmem
  subst hmem
  have hnoHarm := hsatisfies .noHarm
  simp [GenEthActionProfile.differential, trustTriangleProfiles] at hnoHarm

theorem dominatesAll_eq_safeEscalation
    {a : TrustTriangleAction}
    (hdom : dominatesAll trustTrianglePrinciple trustTriangleProfiles
      trustTriangleCandidates a) :
    a = .safeEscalation := by
  cases a with
  | harmfulDisclosure =>
      exact False.elim (harmfulDisclosure_not_dominant hdom)
  | coerciveOverride =>
      exact False.elim (coerciveOverride_not_dominant hdom)
  | safeEscalation =>
      rfl

/-- The existing practical resolver really does choose safe escalation. -/
theorem trustTriangle_resolver_recommends_safeEscalation :
    (pairwiseResolveJudgment trustTrianglePrinciple trustTriangleProfiles
      trustTriangleCandidates).Recommends .safeEscalation := by
  obtain ⟨a, hrec, hdom⟩ := trustTriangle_resolver_chosen_dominates
  have ha : a = .safeEscalation := dominatesAll_eq_safeEscalation hdom
  simpa [ha] using hrec

/-- Top-down capstone: the practical resolver recommends safe escalation, the
top-down theory marks that option admissible, and the rendered active goal
lands on the named universal-love WM query. -/
theorem trustTriangle_metaEthical_capstone :
    (pairwiseResolveJudgment trustTrianglePrinciple trustTriangleProfiles
      trustTriangleCandidates).Recommends .safeEscalation ∧
    trustTriangleMetaTheory.conflictDiscipline.admissible
      trustTrianglePracticalProblem.choicePoint safeEscalationFormula ∧
    trustTriangleTheoryGuidedMeaningProfile.activeGoalQuery trustTriangleStructuredEncoder =
      bodhisattvaEpistemicUniversalLoveQuery := by
  refine ⟨trustTriangle_resolver_recommends_safeEscalation, ?_, ?_⟩
  · exact trustTriangleConflictDiscipline_safeEscalation_admissible
  · exact trustTriangleTheoryGuidedMeaningProfile_activeGoalQuery_eq_eul

/-- Correctness capstone on the live trust-triangle lane: the top-down
safe-escalation claim is satisfied in the concrete source model, its compiled
query has positive WM support in the canonical `coreTriangle` state, and that
same supported query is the active goal of the theory-guided meaning profile. -/
theorem trustTriangle_metaEthical_correctness_capstone :
    trustTriangleStructuredESOModel.SatStructured endorseSafeEscalationClaim ∧
    WMPositiveQuerySupport
      ({regionSupportMassSemantics coreTriangle} : MassState (ConstraintQuery Nat))
      (endorseSafeEscalationClaim.toQuery trustTriangleStructuredEncoder) ∧
    WMPositiveQuerySupport
      ({regionSupportMassSemantics coreTriangle} : MassState (ConstraintQuery Nat))
      (trustTriangleTheoryGuidedMeaningProfile.activeGoalQuery trustTriangleStructuredEncoder) := by
  refine ⟨endorseSafeEscalationClaim_sat_in_trustTriangleStructuredESOModel, ?_, ?_⟩
  · exact endorseSafeEscalationClaim_wmPositive_in_trustTriangleStructuredESOModel
  · exact trustTriangleTheoryGuidedMeaningProfile_activeGoalQuery_wmPositive

end Mettapedia.CognitiveArchitecture.GodelClaw.Ethics
