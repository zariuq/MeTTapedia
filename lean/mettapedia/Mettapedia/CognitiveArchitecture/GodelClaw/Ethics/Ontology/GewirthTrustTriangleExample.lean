import Mettapedia.CognitiveArchitecture.GodelClaw.Ethics.Ontology.ESOUpperShard
import Mettapedia.CognitiveArchitecture.GodelClaw.Ethics.BodhisattvaExample
import Mettapedia.Logic.DDLPlus.WMBridge
import Mettapedia.UniversalAI.GodelMachine.MetaGoalShellPreservationExample

set_option autoImplicit false

/-!
# Gewirth / Trust-Triangle Upper-Shard Example

This file gives a concrete ontology-grounded example on top of the existing
trust-triangle WM development.

The source-side reading stays explicitly Gewirthian:

- a purposeful agent gets a right to non-interference with their FWB,
- operator-facing care stays visible as an upper-shard claim,
- and both claims are seeded from ontology observations before WM lowering.

The target-side result is a real WM theorem:

- the compiled non-interference active goal stays within the shell bound along
  the proof-backed development path, and
- under exact closure it is preserved exactly, together with the
  operator-facing query.
-/

namespace Mettapedia.CognitiveArchitecture.GodelClaw.Ethics.Ontology

open Mettapedia.Ethics
open Mettapedia.Ethics.Gewirth
open Mettapedia.Hyperseed
open Mettapedia.CognitiveArchitecture.GodelClaw.Ethics
open Mettapedia.Logic.MarkovLogicClauseSemantics
open Mettapedia.Logic.MarkovLogicClauseFactorGraph
open Mettapedia.Logic.MarkovLogicDynamicIndividuation
open Mettapedia.Logic.MarkovLogicInfiniteSpecification
open Mettapedia.Logic.MarkovLogicInfiniteFixedRegionDLR
open Mettapedia.Logic.MarkovLogicInfiniteUniqueness.ClassicalInfiniteGroundMLNSpec
open Mettapedia.Logic.MarkovLogicInfiniteWorldModel
open Mettapedia.Logic.MarkovLogicInfiniteVariableNeighborhoodWorldOfViews
open Mettapedia.Logic.MarkovLogicOntologyGrowth
open Mettapedia.Logic.MarkovLogicTrustTriangleExample
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.MarkovLogicAbstract
open Mettapedia.Logic.MarkovLogicAbstract.MassState
open Mettapedia.UniversalAI.GodelMachine
open Mettapedia.UniversalAI.GodelMachine.MetaGoalShellPreservation
open Mettapedia.UniversalAI.GodelMachine.MetaGoalShellPreservationExample
open MeasureTheory

universe u

local instance : DecidableEq VarNClauseId := inferInstance

/-- Labels for the trust-triangle upper-shard lowering. -/
inductive TrustTriangleUpperShardLabel where
  | nonInterference
  | respectAutonomy
  | friendship
  deriving DecidableEq, Repr

/-- Final WM lowering for the trust-triangle upper-shard example.

This encoder is intentionally coarse: it lands structured upper-shard claims on
the already-proved trust-triangle atoms `{0,1,2}`.  The ontological structure
is carried by the source-side claim types, not by pretending the target WM
space is already a full ontology. -/
def trustTriangleUpperShardEncoder {Agent : Type*} :
    EthicsQueryEncoder Agent TrustTriangleUpperShardLabel Nat where
  epistemicUniversalLoveAtom := fun _ => 1
  moralValueAtom := fun _ _ l =>
    match l with
    | .nonInterference => 0
    | .respectAutonomy => 2
    | .friendship => 2
  deonticAtom := fun _ _ l =>
    match l with
    | .nonInterference => 0
    | .respectAutonomy => 2
    | .friendship => 2
  universalDutyAtom := fun _ d =>
    match d with
    | .noHarm => 0
    | .noDeception => 1
    | .noCoercion => 2
    | .respectAutonomy => 2
    | .keepPromises => 2
    | .beneficence => 1
  relationalAtom := fun _ _ r =>
    match r with
    | .trust => 1
    | .loyalty => 2
    | .gratitude => 2
    | .forgiveness => 0
    | .love => 1
    | .friendship => 2

theorem trustTriangleUpperShardEncoder_aligned {Agent : Type*} :
    (trustTriangleUpperShardEncoder (Agent := Agent)).DeonticValueAligned := by
  intro _ _ l
  cases l <;> rfl

theorem trustTriangleUpperShardClaim_supportedOn_coreTriangle
    {World : Type u} {Agent : Type u}
    (claim : UpperShardEthicalClaim World Agent TrustTriangleUpperShardLabel) :
    claim.supportedOn (trustTriangleUpperShardEncoder (Agent := Agent)) coreTriangle := by
  cases claim with
  | disposition d =>
      cases d with
      | epistemicUniversalLove a =>
          simp [UpperShardEthicalClaim.supportedOn, UpperShardEthicalClaim.toAnchor,
            EthicalAnchor.supportedOn, trustTriangleUpperShardEncoder, coreTriangle]
  | normative n =>
      cases n with
      | presentedValue s =>
          cases s with
          | mk agent label sentence =>
              cases label <;>
                simp [UpperShardEthicalClaim.supportedOn, UpperShardEthicalClaim.toAnchor,
                  NormativeClaim.toAnchor, EthicalAnchor.supportedOn,
                  LabeledValueJudgmentSentence.toAnchor,
                  trustTriangleUpperShardEncoder, coreTriangle]
      | presentedDeontic s =>
          cases s with
          | mk agent label sentence =>
              cases label <;>
                simp [UpperShardEthicalClaim.supportedOn, UpperShardEthicalClaim.toAnchor,
                  NormativeClaim.toAnchor, EthicalAnchor.supportedOn,
                  LabeledDeonticSentence.toAnchor,
                  trustTriangleUpperShardEncoder, coreTriangle]
      | groundedUniversalDuty a d =>
          cases d <;>
            simp [UpperShardEthicalClaim.supportedOn, UpperShardEthicalClaim.toAnchor,
              NormativeClaim.toAnchor, EthicalAnchor.supportedOn,
              trustTriangleUpperShardEncoder, coreTriangle]
      | groundedGewirthRight gw =>
          cases gw with
          | mk context agent label =>
              cases label <;>
                simp [UpperShardEthicalClaim.supportedOn, UpperShardEthicalClaim.toAnchor,
                  NormativeClaim.toAnchor, EthicalAnchor.supportedOn,
                  LabeledGewirthRightClaim.toDeonticSentence,
                  LabeledDeonticSentence.toAnchor,
                  trustTriangleUpperShardEncoder, coreTriangle]
  | relational r =>
      cases r with
      | mk source target relation =>
          cases relation <;>
            simp [UpperShardEthicalClaim.supportedOn, UpperShardEthicalClaim.toAnchor,
              EthicalAnchor.supportedOn, trustTriangleUpperShardEncoder, coreTriangle]

/-- The structured Gewirth right used in the trust-triangle example. -/
def gewirthNonInterferenceClaim
    {I : PGCInterpretation} (context : I.Ctx) (agent : I.Entity) :
    LabeledGewirthRightClaim TrustTriangleUpperShardLabel I where
  context := context
  agent := agent
  label := .nonInterference

/-- Operator-facing care claim used in the combined theorem. -/
def operatorCareClaim
    {I : PGCInterpretation} (operator : I.Entity) :
    UpperShardEthicalClaim (I.Ctx × I.World) I.Entity TrustTriangleUpperShardLabel :=
  .disposition (.epistemicUniversalLove operator)

/-- Structured upper-shard protected family on the trust triangle. -/
def trustTriangleUpperShardClaims
    {I : PGCInterpretation} (context : I.Ctx) (agent operator : I.Entity) :
    ProtectedUpperShardClaims (I.Ctx × I.World) I.Entity TrustTriangleUpperShardLabel where
  epistemicUniversalLove := operatorCareClaim operator
  nonMaleficence := (gewirthNonInterferenceClaim context agent).toUpperShard
  consent := .normative (.groundedUniversalDuty agent .respectAutonomy)
  reciprocity := .relational { source := agent, target := operator, relation := .friendship }

/-- The compiled upper-shard family lives on the same protected trust-triangle
core. -/
def trustTriangleUpperShardGoals
    {I : PGCInterpretation} (context : I.Ctx) (agent operator : I.Entity) :
    ProtectedEthicsQueryFamily coreTriangle :=
  (trustTriangleUpperShardClaims context agent operator).toProtectedEthicsQueryFamily
    (enc := trustTriangleUpperShardEncoder (Agent := I.Entity))
    (hEUL := trustTriangleUpperShardClaim_supportedOn_coreTriangle _)
    (hNoHarm := trustTriangleUpperShardClaim_supportedOn_coreTriangle _)
    (hConsent := trustTriangleUpperShardClaim_supportedOn_coreTriangle _)
    (hReciprocity := trustTriangleUpperShardClaim_supportedOn_coreTriangle _)

/-- Meaning/agency profile whose active goal is the Gewirth non-interference
claim. -/
def trustTriangleGewirthMeaningProfile
    {I : PGCInterpretation} (context : I.Ctx) (agent : I.Entity) :
    UpperShardFoundationalMeaningProfile
      (I.Ctx × I.World) I.Entity TrustTriangleUpperShardLabel Nat where
  situation := bodhisattvaNonMaleficenceQuery
  prediction := bodhisattvaEpistemicUniversalLoveQuery
  activeGoalClaim := (gewirthNonInterferenceClaim context agent).toUpperShard
  plan := bodhisattvaConsentQuery

/-- Ontology-side observations used to seed the upper-shard example. -/
inductive TrustTriangleUpperShardObservation where
  | ppaCue
  | operatorCue
  | consentCue
  | reciprocityCue
  deriving DecidableEq, Repr

/-- Ontology trace source for the structured trust-triangle example. -/
def trustTriangleUpperShardTraceSource
    {I : PGCInterpretation} (context : I.Ctx) (agent operator : I.Entity) :
    ESOUpperShardTraceSource
      TrustTriangleUpperShardObservation (I.Ctx × I.World) I.Entity TrustTriangleUpperShardLabel where
  extract
    | .ppaCue => {(gewirthNonInterferenceClaim context agent).toUpperShard}
    | .operatorCue => {operatorCareClaim operator}
    | .consentCue => {.normative (.groundedUniversalDuty agent .respectAutonomy)}
    | .reciprocityCue => {.relational { source := agent, target := operator, relation := .friendship }}

@[simp] theorem gewirthNonInterferenceClaim_query_eq_nonMaleficence
    {I : PGCInterpretation} (context : I.Ctx) (agent : I.Entity) :
    (gewirthNonInterferenceClaim context agent).toUpperShard.toQuery
        (trustTriangleUpperShardEncoder (Agent := I.Entity)) =
      bodhisattvaNonMaleficenceQuery := by
  simp [gewirthNonInterferenceClaim, UpperShardEthicalClaim.toQuery,
    UpperShardEthicalClaim.toAnchor, NormativeClaim.toAnchor,
    LabeledGewirthRightClaim.toUpperShard, LabeledGewirthRightClaim.toDeonticSentence,
    LabeledDeonticSentence.toAnchor, EthicalAnchor.toQuery,
    trustTriangleUpperShardEncoder, bodhisattvaNonMaleficenceQuery]

@[simp] theorem operatorCareClaim_query_eq_epistemicUniversalLove
    {I : PGCInterpretation} (operator : I.Entity) :
    (operatorCareClaim operator).toQuery
        (trustTriangleUpperShardEncoder (Agent := I.Entity)) =
      bodhisattvaEpistemicUniversalLoveQuery := by
  simp [operatorCareClaim, UpperShardEthicalClaim.toQuery,
    UpperShardEthicalClaim.toAnchor, EthicalAnchor.toQuery,
    trustTriangleUpperShardEncoder, bodhisattvaEpistemicUniversalLoveQuery, agent1Query]

theorem trustTriangleGewirth_activeGoal_mem_upperShardGoals
    {I : PGCInterpretation} (context : I.Ctx) (agent operator : I.Entity) :
    (trustTriangleGewirthMeaningProfile context agent).activeGoalQuery
        (trustTriangleUpperShardEncoder (Agent := I.Entity)) ∈
      (trustTriangleUpperShardGoals context agent operator).goals := by
  have hProtected :
      (trustTriangleGewirthMeaningProfile context agent).ActiveGoalProtectedBy
        (trustTriangleUpperShardClaims context agent operator) := by
    right
    left
    simp [trustTriangleGewirthMeaningProfile, trustTriangleUpperShardClaims]
  simpa [trustTriangleUpperShardGoals]
    using UpperShardFoundationalMeaningProfile.activeGoal_mem_protectedFamily
      (profile := trustTriangleGewirthMeaningProfile context agent)
      (enc := trustTriangleUpperShardEncoder (Agent := I.Entity))
      (claims := trustTriangleUpperShardClaims context agent operator)
      (hEUL := trustTriangleUpperShardClaim_supportedOn_coreTriangle _)
      (hNoHarm := trustTriangleUpperShardClaim_supportedOn_coreTriangle _)
      (hConsent := trustTriangleUpperShardClaim_supportedOn_coreTriangle _)
      (hReciprocity := trustTriangleUpperShardClaim_supportedOn_coreTriangle _)
      hProtected

theorem trustTriangleGewirth_activeGoal_mem_bodhisattvaGoals
    {I : PGCInterpretation} (context : I.Ctx) (agent _operator : I.Entity) :
    (trustTriangleGewirthMeaningProfile context agent).activeGoalQuery
        (trustTriangleUpperShardEncoder (Agent := I.Entity)) ∈
      trustTriangleBodhisattvaGoals.goals := by
  simpa [trustTriangleGewirthMeaningProfile]
    using trustTriangleBodhisattvaGoals.mem_nonMaleficence

theorem trustTriangleGewirth_operator_mem_bodhisattvaGoals
    {I : PGCInterpretation} (operator : I.Entity) :
    (operatorCareClaim operator).toQuery
        (trustTriangleUpperShardEncoder (Agent := I.Entity)) ∈
      trustTriangleBodhisattvaGoals.goals := by
  simpa using trustTriangleBodhisattvaGoals.mem_epistemicUniversalLove

theorem trustTriangleGewirth_activeGoal_mem_traceSeed
    {I : PGCInterpretation} (context : I.Ctx) (agent operator : I.Entity) :
    (trustTriangleGewirthMeaningProfile context agent).activeGoalQuery
        (trustTriangleUpperShardEncoder (Agent := I.Entity)) ∈
      traceSeed
        ((trustTriangleUpperShardTraceSource context agent operator).frontier
          (trustTriangleUpperShardEncoder (Agent := I.Entity)))
        ({TrustTriangleUpperShardObservation.ppaCue} :
          Multiset TrustTriangleUpperShardObservation) := by
  exact UpperShardFoundationalMeaningProfile.activeGoal_mem_traceSeed
    (extract := (trustTriangleUpperShardTraceSource context agent operator).extract)
    (enc := trustTriangleUpperShardEncoder (Agent := I.Entity))
    (σ := {TrustTriangleUpperShardObservation.ppaCue})
    (o := .ppaCue)
    (profile := trustTriangleGewirthMeaningProfile context agent)
    (ho := by simp)
    (hmem := by simp [trustTriangleGewirthMeaningProfile, trustTriangleUpperShardTraceSource])

theorem operatorCareClaim_mem_traceSeed
    {I : PGCInterpretation} (context : I.Ctx) (agent operator : I.Entity) :
    (operatorCareClaim operator).toQuery
        (trustTriangleUpperShardEncoder (Agent := I.Entity)) ∈
      traceSeed
        ((trustTriangleUpperShardTraceSource context agent operator).frontier
          (trustTriangleUpperShardEncoder (Agent := I.Entity)))
        ({TrustTriangleUpperShardObservation.operatorCue} :
          Multiset TrustTriangleUpperShardObservation) := by
  exact ⟨.operatorCue, by simp, by
    simp [ESOUpperShardTraceSource.frontier, upperShardFrontier,
      trustTriangleUpperShardTraceSource, operatorCareClaim]⟩

/-- Ethics-surface correctness capstone for the Gewirth non-interference lane.

The same PGC / purposive-agency witness yields both:

1. ontology-side satisfaction of the upper-shard Gewirth claim, and
2. logic-side positive WM evidence for the corresponding DDLPlus obligation.

This exposes the already-proved `Ethics -> DDLPlus -> WM` chain directly from
the trust-triangle ethics surface, rather than leaving it hidden in the logic
layer. -/
theorem gewirthNonInterferenceClaim_sat_and_deonticWMPositiveEvidence_of_PPA
    {I : PGCInterpretation}
    (h : PGCAssumptions I)
    (context : I.Ctx) (agent : I.Entity)
    (hPPA : PPA I.ActsOnPurpose agent context (I.worldOf context)) :
    (ESOUpperShardModel.ofGewirth (Label := TrustTriangleUpperShardLabel) I context).Sat
        (gewirthNonInterferenceClaim context agent).toUpperShard ∧
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
  refine ⟨(gewirthNonInterferenceClaim context agent).sat_toUpperShard_of_PPA h hPPA, ?_⟩
  simpa using
    Mettapedia.Logic.DDLPlus.WMBridge.pgc_nonInterference_wmPositiveEvidence
      I h context agent hPPA

/-- Path-level Gewirth/WM example:

if a purposeful agent has the Gewirth right to non-interference, then that
structured upper-shard active goal is seedable from ontology observations and
its WM truth value stays within the cumulative shell bound along the proved
trust-triangle reflective-development path.  The same path also keeps the
operator-facing care query within the same bound. -/
theorem trustTriangle_gewirth_nonInterference_and_operator_path_example
    {I : PGCInterpretation}
    (h : PGCAssumptions I)
    (context : I.Ctx) (agent operator : I.Entity)
    (hPPA : PPA I.ActsOnPurpose agent context (I.worldOf context)) :
    ∃ measures :
        MetaGoalShellPreservationPathDLR
          (Atom := Nat) (ClauseId := VarNClauseId) trustTriangleBodhisattvaPath,
      (ESOUpperShardModel.ofGewirth (Label := TrustTriangleUpperShardLabel) I context).Sat
          (gewirthNonInterferenceClaim context agent).toUpperShard ∧
        expectedUtilityFromStart trustTriangleBodhisattvaPath.endMachine >
          expectedUtilityFromStart trustTriangleBodhisattvaPath.startMachine ∧
        (trustTriangleGewirthMeaningProfile context agent).activeGoalQuery
            (trustTriangleUpperShardEncoder (Agent := I.Entity)) ∈
          (trustTriangleUpperShardGoals context agent operator).goals ∧
        (trustTriangleGewirthMeaningProfile context agent).activeGoalQuery
            (trustTriangleUpperShardEncoder (Agent := I.Entity)) ∈
          traceSeed
            ((trustTriangleUpperShardTraceSource context agent operator).frontier
              (trustTriangleUpperShardEncoder (Agent := I.Entity)))
            ({TrustTriangleUpperShardObservation.ppaCue} :
              Multiset TrustTriangleUpperShardObservation) ∧
        (operatorCareClaim operator).toQuery
            (trustTriangleUpperShardEncoder (Agent := I.Entity)) ∈
          traceSeed
            ((trustTriangleUpperShardTraceSource context agent operator).frontier
              (trustTriangleUpperShardEncoder (Agent := I.Entity)))
            ({TrustTriangleUpperShardObservation.operatorCue} :
              Multiset TrustTriangleUpperShardObservation) ∧
        |(BinaryWorldModel.queryStrength
            ({infiniteMLNMassSemantics trustTriangleBodhisattvaPath.startSpec
                measures.startMeasure measures.startDLR} :
              MassState (ConstraintQuery Nat))
            ((trustTriangleGewirthMeaningProfile context agent).activeGoalQuery
              (trustTriangleUpperShardEncoder (Agent := I.Entity)))).toReal -
          (BinaryWorldModel.queryStrength
            ({infiniteMLNMassSemantics trustTriangleBodhisattvaPath.endSpec
                measures.endMeasure measures.endDLR} :
              MassState (ConstraintQuery Nat))
            ((trustTriangleGewirthMeaningProfile context agent).activeGoalQuery
              (trustTriangleUpperShardEncoder (Agent := I.Entity)))).toReal| ≤
            12 ∧
        |(BinaryWorldModel.queryStrength
            ({infiniteMLNMassSemantics trustTriangleBodhisattvaPath.startSpec
                measures.startMeasure measures.startDLR} :
              MassState (ConstraintQuery Nat))
            ((operatorCareClaim operator).toQuery
              (trustTriangleUpperShardEncoder (Agent := I.Entity)))).toReal -
          (BinaryWorldModel.queryStrength
            ({infiniteMLNMassSemantics trustTriangleBodhisattvaPath.endSpec
                measures.endMeasure measures.endDLR} :
              MassState (ConstraintQuery Nat))
            ((operatorCareClaim operator).toQuery
              (trustTriangleUpperShardEncoder (Agent := I.Entity)))).toReal| ≤
            12 := by
  rcases trustTriangle_bodhisattva_path_example with
    ⟨measures, _himprove, hOperator, _hNoHarm, _hConsent, _hReciprocity⟩
  have hUpper :=
    MetaGoalShellPreservationPathDLR.utility_improves_and_protectedUpperShardActiveGoal_drift_bounded
      (family := trustTriangleBodhisattvaGoals)
      (path := trustTriangleBodhisattvaPath)
      measures trustTriangleBodhisattvaPath_coherent
      (profile := trustTriangleGewirthMeaningProfile context agent)
      (enc := trustTriangleUpperShardEncoder (Agent := I.Entity))
      (hgoal := trustTriangleGewirth_activeGoal_mem_bodhisattvaGoals context agent operator)
  refine ⟨measures,
    (gewirthNonInterferenceClaim context agent).sat_toUpperShard_of_PPA h hPPA,
    hUpper.1,
    trustTriangleGewirth_activeGoal_mem_upperShardGoals context agent operator,
    trustTriangleGewirth_activeGoal_mem_traceSeed context agent operator,
    operatorCareClaim_mem_traceSeed context agent operator,
    ?_, ?_⟩
  · simpa [trustTriangleBodhisattvaPath_totalErrorBound] using hUpper.2
  · simpa [operatorCareClaim_query_eq_epistemicUniversalLove operator,
      trustTriangleBodhisattvaPath_totalErrorBound] using hOperator

/-- Exact closure version of the Gewirth/WM example:

when the rewrite stays outside the closed trust-triangle core, the compiled
Gewirth non-interference active goal and the operator-facing care query are
preserved exactly while utility improves. -/
theorem trustTriangle_gewirth_nonInterference_and_operator_exact_example
    {I : PGCInterpretation}
    (h : PGCAssumptions I)
    (context : I.Ctx) (agent operator : I.Entity)
    (hPPA : PPA I.ActsOnPurpose agent context (I.worldOf context))
    (wt wc₁ wc₂ : ℝ)
    (hwt : |wt| < 1 / 2) (hwc₁ : |wc₁| < 1 / 2) (hwc₂ : |wc₂| < 1 / 2)
    (μ₁ : ProbabilityMeasure (InfiniteWorld Nat))
    (μ₂ : ProbabilityMeasure (InfiniteWorld Nat))
    (hμ₁ : FixedRegionCylinderDLR
      (triangleChainSpec wt wc₁).toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₁ : Measure (InfiniteWorld Nat)))
    (hμ₂ : FixedRegionCylinderDLR
      (triangleChainSpec wt wc₂).toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₂ : Measure (InfiniteWorld Nat))) :
    (ESOUpperShardModel.ofGewirth (Label := TrustTriangleUpperShardLabel) I context).Sat
        (gewirthNonInterferenceClaim context agent).toUpperShard ∧
      expectedUtilityFromStart (toyMachine 1) >
        expectedUtilityFromStart (toyMachine 0) ∧
      (trustTriangleGewirthMeaningProfile context agent).activeGoalQuery
          (trustTriangleUpperShardEncoder (Agent := I.Entity)) ∈
        (trustTriangleUpperShardGoals context agent operator).goals ∧
      BinaryWorldModel.queryStrength
        ({infiniteMLNMassSemantics (triangleChainSpec wt wc₁) μ₁ hμ₁} :
          MassState (ConstraintQuery Nat))
        ((trustTriangleGewirthMeaningProfile context agent).activeGoalQuery
          (trustTriangleUpperShardEncoder (Agent := I.Entity))) =
      BinaryWorldModel.queryStrength
        ({infiniteMLNMassSemantics (triangleChainSpec wt wc₂) μ₂ hμ₂} :
          MassState (ConstraintQuery Nat))
        ((trustTriangleGewirthMeaningProfile context agent).activeGoalQuery
          (trustTriangleUpperShardEncoder (Agent := I.Entity))) ∧
      BinaryWorldModel.queryStrength
        ({infiniteMLNMassSemantics (triangleChainSpec wt wc₁) μ₁ hμ₁} :
          MassState (ConstraintQuery Nat))
        ((operatorCareClaim operator).toQuery
          (trustTriangleUpperShardEncoder (Agent := I.Entity))) =
      BinaryWorldModel.queryStrength
        ({infiniteMLNMassSemantics (triangleChainSpec wt wc₂) μ₂ hμ₂} :
          MassState (ConstraintQuery Nat))
        ((operatorCareClaim operator).toQuery
          (trustTriangleUpperShardEncoder (Agent := I.Entity))) := by
  let closure : DynamicIndividuationClosure (triangleChainSpec wt wc₁) :=
    trustTriangleClosure wt wc₁
  let cross : CrossSpecDLR (triangleChainSpec wt wc₁) (triangleChainSpec wt wc₂) :=
    { oldMeasure := μ₁
      newMeasure := μ₂
      oldDLR := hμ₁
      newDLR := hμ₂ }
  have hAgree :
      SpecAgreesOnRegion (triangleChainSpec wt wc₁) (triangleChainSpec wt wc₂)
        ((triangleChainSpec wt wc₁).iterExpandRegion closure.proto.seed closure.closureDepth) := by
    simpa [closure, trustTriangleClosure,
      Mettapedia.Logic.MarkovLogicInfiniteUniqueness.ClassicalInfiniteGroundMLNSpec.iterExpandRegion]
      using specs_agree_on_triangle wt wc₁ wc₂
  have hClosed₂ :
      InteractionClosed (triangleChainSpec wt wc₂)
        ((triangleChainSpec wt wc₁).iterExpandRegion closure.proto.seed closure.closureDepth) := by
    simpa [closure, trustTriangleClosure,
      Mettapedia.Logic.MarkovLogicInfiniteUniqueness.ClassicalInfiniteGroundMLNSpec.iterExpandRegion]
      using triangleCore_interactionClosed wt wc₂
  let family : ProtectedEthicsQueryFamily closure.proto.seed := by
    simpa [closure, trustTriangleClosure] using trustTriangleBodhisattvaGoals
  have hUpper :=
    validModification_preserves_protectedUpperShardActiveGoal_of_dynamicIndividuationClosure
      (oldMachine := toyMachine 0) (newMachine := toyMachine 1)
      (proofBacked := toyMachine_validModification_of_lt (by norm_num))
      (closure := closure)
      (hagree := hAgree)
      (hclosed₂ := hClosed₂)
      (hbudget₁ := triangleChainSpec_budget wt wc₁ hwt hwc₁)
      (hbudget₂ := triangleChainSpec_budget wt wc₂ hwt hwc₂)
      (family := family)
      (profile := trustTriangleGewirthMeaningProfile context agent)
      (enc := trustTriangleUpperShardEncoder (Agent := I.Entity))
      (measures := cross)
      (hgoal := trustTriangleGewirth_activeGoal_mem_bodhisattvaGoals context agent operator)
  rcases trustTriangle_bodhisattva_exact_example wt wc₁ wc₂ hwt hwc₁ hwc₂ μ₁ μ₂ hμ₁ hμ₂ with
    ⟨_himprove, hOperator, _hNoHarm, _hConsent, _hReciprocity⟩
  exact ⟨(gewirthNonInterferenceClaim context agent).sat_toUpperShard_of_PPA h hPPA,
    hUpper.1,
    trustTriangleGewirth_activeGoal_mem_upperShardGoals context agent operator,
    hUpper.2,
    by simpa [operatorCareClaim_query_eq_epistemicUniversalLove operator] using hOperator⟩

end Mettapedia.CognitiveArchitecture.GodelClaw.Ethics.Ontology
