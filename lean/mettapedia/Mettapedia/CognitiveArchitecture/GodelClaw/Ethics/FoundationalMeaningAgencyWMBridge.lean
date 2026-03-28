import Mettapedia.CognitiveArchitecture.GodelClaw.Ethics.EthicsFormulaWMBridge
import Mettapedia.Hyperseed.Basic

/-!
# Foundational Meaning, Agency, and WM Grounding

This module formalizes a modest but real bridge from the foundational
meaning-generation story into the existing WM semantics.

The 2024 foundational-meaning paper treats meaning generation as the situated
process that ties:

- the current situation,
- predictions,
- active goals,
- and plans

together inside one agent-relative process.  It also argues that meaning and
autonomy/agency are tightly linked.

We encode the smallest honest fragment of that picture over the proved WM
infrastructure already in this repository:

- `FoundationalMeaningProfile` names situation / prediction / active-goal / plan
  queries,
- `WMPositiveQuerySupport` says the WM actually carries positive support for one
  of those queries,
- `AgencyKernel` packages the prediction/goal/plan side,
- `SituationGrounding` packages the situation side,
- and `FoundationalMeaningState` says the whole quartet is jointly grounded.

The key compositional theorem is that revising a situation-grounding state with
an agency-kernel state yields a foundational-meaning state.  This uses the WM
revision algebra, not a separate ad hoc semantics.

We then specialize the active-goal slot to ethics-side anchors compiled into WM
queries, so the same active goal can:

- enter from an observation frontier / Hyperseed trace,
- sit inside a protected ethics family,
- and inherit the existing meta-stability guarantees under proof-backed
  self-modification.
-/

namespace Mettapedia.CognitiveArchitecture.GodelClaw.Ethics

open scoped ENNReal

open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Hyperseed
open Mettapedia.Logic.MarkovLogicClauseSemantics
open Mettapedia.Logic.MarkovLogicClauseFactorGraph
open Mettapedia.Logic.MarkovLogicInfiniteSpecification
open Mettapedia.Logic.MarkovLogicInfiniteFixedRegionDLR
open Mettapedia.Logic.MarkovLogicInfiniteUniqueness
open Mettapedia.Logic.MarkovLogicInfiniteUniqueness.ClassicalInfiniteGroundMLNSpec
open Mettapedia.Logic.MarkovLogicInfiniteWorldModel
open Mettapedia.Logic.MarkovLogicOntologyGrowth
open Mettapedia.Logic.MarkovLogicDynamicIndividuation
open Mettapedia.Logic.MarkovLogicAbstract
open Mettapedia.Logic.MarkovLogicAbstract.MassState
open Mettapedia.UniversalAI.GodelMachine
open Mettapedia.UniversalAI.GodelMachine.MetaGoalShellPreservation
open MeasureTheory

universe u v w x

private theorem pos_add_ne_zero_left {a b : ℝ≥0∞} (ha : a ≠ 0) : a + b ≠ 0 := by
  intro h
  exact ha (add_eq_zero.mp h).1

private theorem pos_add_ne_zero_right {a b : ℝ≥0∞} (hb : b ≠ 0) : a + b ≠ 0 := by
  intro h
  exact hb (add_eq_zero.mp h).2

/-- Positive WM support for one query in one posterior state. -/
def WMPositiveQuerySupport
    {State Query : Type*} [EvidenceType State] [BinaryWorldModel State Query]
    (W : State) (query : Query) : Prop :=
  ∃ e : BinaryEvidence, (⊢q W ⇓ query ↦ e) ∧ e.pos ≠ 0

theorem WMPositiveQuerySupport.of_positiveEvidence
    {State Query : Type*} [EvidenceType State] [BinaryWorldModel State Query]
    (W : State) (query : Query)
    (hpos :
      (BinaryWorldModel.evidence (State := State) (Query := Query) W query).pos ≠ 0) :
    WMPositiveQuerySupport W query := by
  refine ⟨BinaryWorldModel.evidence (State := State) (Query := Query) W query, ?_, hpos⟩
  exact WMJudgment.query_of_axiom W query

theorem WMPositiveQuerySupport.revise_left
    {State Query : Type*} [EvidenceType State] [BinaryWorldModel State Query]
    {W₁ W₂ : State} {query : Query}
    (hs : WMPositiveQuerySupport W₁ query) :
    WMPositiveQuerySupport (W₁ + W₂) query := by
  rcases hs with ⟨e₁, hj₁, hpos⟩
  let e₂ := BinaryWorldModel.evidence (State := State) (Query := Query) W₂ query
  have hj₂ : ⊢q W₂ ⇓ query ↦ e₂ := by
    exact WMJudgment.query_of_axiom W₂ query
  refine ⟨e₁ + e₂, WMJudgment.query_revise hj₁ hj₂, ?_⟩
  simpa [BinaryEvidence.hplus_def, e₂] using
    (pos_add_ne_zero_left (a := e₁.pos) (b := e₂.pos) hpos)

theorem WMPositiveQuerySupport.revise_right
    {State Query : Type*} [EvidenceType State] [BinaryWorldModel State Query]
    {W₁ W₂ : State} {query : Query}
    (hs : WMPositiveQuerySupport W₂ query) :
    WMPositiveQuerySupport (W₁ + W₂) query := by
  rcases hs with ⟨e₂, hj₂, hpos⟩
  let e₁ := BinaryWorldModel.evidence (State := State) (Query := Query) W₁ query
  have hj₁ : ⊢q W₁ ⇓ query ↦ e₁ := by
    exact WMJudgment.query_of_axiom W₁ query
  refine ⟨e₁ + e₂, WMJudgment.query_revise hj₁ hj₂, ?_⟩
  simpa [BinaryEvidence.hplus_def, e₁] using
    (pos_add_ne_zero_right (a := e₁.pos) (b := e₂.pos) hpos)

/-- Region-side support predicate for finite constraint queries. -/
def querySupportedByRegion
    {Atom : Type*} (Γ : Region Atom) (q : ConstraintQuery Atom) : Prop :=
  ∀ p ∈ q, p.1 ∈ Γ

/-- Canonical singleton-mass semantics for a support region: a query receives
full positive mass exactly when all of its atoms lie in the chosen region. This
is the smallest honest WM landing zone for the first restricted
source-semantics-to-WM correctness theorem. -/
noncomputable def regionSupportMassSemantics
    {Atom : Type*} (Γ : Region Atom) :
    MassSemantics (ConstraintQuery Atom) := by
  classical
  refine
    { queryMass := fun q => if querySupportedByRegion Γ q then 1 else 0
      totalMass := 1
      queryMass_le_total := ?_
      totalMass_ne_top := by simp }
  intro q
  by_cases hq : querySupportedByRegion Γ q
  · simp [hq]
  · simp [hq]

@[simp] theorem regionSupportMassSemantics_queryMass_eq_one_of_supported
    {Atom : Type*} {Γ : Region Atom} {q : ConstraintQuery Atom}
    (hsupp : querySupportedByRegion Γ q) :
    (regionSupportMassSemantics Γ).queryMass q = 1 := by
  classical
  change (if querySupportedByRegion Γ q then (1 : ℝ≥0∞) else 0) = 1
  simp [hsupp]

@[simp] theorem regionSupportMassSemantics_queryMass_eq_zero_of_not_supported
    {Atom : Type*} {Γ : Region Atom} {q : ConstraintQuery Atom}
    (hnot : ¬ querySupportedByRegion Γ q) :
    (regionSupportMassSemantics Γ).queryMass q = 0 := by
  classical
  change (if querySupportedByRegion Γ q then (1 : ℝ≥0∞) else 0) = 0
  simp [hnot]

/-- Any constraint query whose atoms all lie in the chosen support region has
positive support in the corresponding canonical singleton-mass WM state. -/
theorem WMPositiveQuerySupport.of_regionSupportedConstraintQuery
    {Atom : Type*} (Γ : Region Atom) (q : ConstraintQuery Atom)
    (hsupp : querySupportedByRegion Γ q) :
    WMPositiveQuerySupport
      ({regionSupportMassSemantics Γ} : MassState (ConstraintQuery Atom)) q := by
  classical
  apply WMPositiveQuerySupport.of_positiveEvidence
  rw [show BinaryWorldModel.evidence
      ({regionSupportMassSemantics Γ} : MassState (ConstraintQuery Atom)) q =
        (regionSupportMassSemantics Γ).evidenceOfMasses q by
      exact MassState.evidence_singleton (regionSupportMassSemantics Γ) q]
  change (regionSupportMassSemantics Γ).queryMass q ≠ 0
  rw [regionSupportMassSemantics_queryMass_eq_one_of_supported hsupp]
  simp

/-- Dually, if a constraint query is not supported by the chosen region, then
the canonical singleton-mass WM state does not provide positive support for it.
This is the negative canary for the restricted support semantics above. -/
theorem not_WMPositiveQuerySupport_of_not_regionSupportedConstraintQuery
    {Atom : Type*} (Γ : Region Atom) (q : ConstraintQuery Atom)
    (hnot : ¬ querySupportedByRegion Γ q) :
    ¬ WMPositiveQuerySupport
      ({regionSupportMassSemantics Γ} : MassState (ConstraintQuery Atom)) q := by
  classical
  rintro ⟨e, hj, hpos⟩
  rw [hj.2] at hpos
  rw [show BinaryWorldModel.evidence
      ({regionSupportMassSemantics Γ} : MassState (ConstraintQuery Atom)) q =
        (regionSupportMassSemantics Γ).evidenceOfMasses q by
      exact MassState.evidence_singleton (regionSupportMassSemantics Γ) q] at hpos
  change (regionSupportMassSemantics Γ).queryMass q ≠ 0 at hpos
  rw [regionSupportMassSemantics_queryMass_eq_zero_of_not_supported hnot] at hpos
  simp at hpos

/-- A WM-facing foundational-meaning profile: the four query roles singled out
in the foundational-meaning paper. -/
structure FoundationalMeaningProfile (Query : Type u) where
  situation : Query
  prediction : Query
  activeGoal : Query
  plan : Query

/-- Grounding of the current situation in the WM. -/
structure SituationGrounding
    {State Query : Type*} [EvidenceType State] [BinaryWorldModel State Query]
    (W : State) (profile : FoundationalMeaningProfile Query) : Prop where
  situation_supported : WMPositiveQuerySupport W profile.situation

/-- The prediction / goal / plan side of agency.  This is the minimal
agent-side kernel we use here. -/
structure AgencyKernel
    {State Query : Type*} [EvidenceType State] [BinaryWorldModel State Query]
    (W : State) (profile : FoundationalMeaningProfile Query) : Prop where
  prediction_supported : WMPositiveQuerySupport W profile.prediction
  activeGoal_supported : WMPositiveQuerySupport W profile.activeGoal
  plan_supported : WMPositiveQuerySupport W profile.plan

/-- A fully grounded foundational-meaning state in the WM. -/
structure FoundationalMeaningState
    {State Query : Type*} [EvidenceType State] [BinaryWorldModel State Query]
    (W : State) (profile : FoundationalMeaningProfile Query) : Prop where
  situation_supported : WMPositiveQuerySupport W profile.situation
  prediction_supported : WMPositiveQuerySupport W profile.prediction
  activeGoal_supported : WMPositiveQuerySupport W profile.activeGoal
  plan_supported : WMPositiveQuerySupport W profile.plan

/-- A fully grounded meaning state contains the agency kernel as one side of the
same process. -/
def FoundationalMeaningState.toAgencyKernel
    {State Query : Type*} [EvidenceType State] [BinaryWorldModel State Query]
    {W : State} {profile : FoundationalMeaningProfile Query}
    (hMeaning : FoundationalMeaningState W profile) :
    AgencyKernel W profile where
  prediction_supported := hMeaning.prediction_supported
  activeGoal_supported := hMeaning.activeGoal_supported
  plan_supported := hMeaning.plan_supported

/-- WM revision composes a grounded situation with a grounded
prediction/goal/plan kernel into a grounded meaning state. -/
theorem SituationGrounding.combineWithAgencyKernel
    {State Query : Type*} [EvidenceType State] [BinaryWorldModel State Query]
    {W₁ W₂ : State} {profile : FoundationalMeaningProfile Query}
    (hSituation : SituationGrounding W₁ profile)
    (hAgency : AgencyKernel W₂ profile) :
    FoundationalMeaningState (W₁ + W₂) profile where
  situation_supported := hSituation.situation_supported.revise_left
  prediction_supported := hAgency.prediction_supported.revise_right
  activeGoal_supported := hAgency.activeGoal_supported.revise_right
  plan_supported := hAgency.plan_supported.revise_right

/-- Once grounded, the foundational-meaning state survives further WM revision:
extra evidence may enrich the state, but it does not erase positive support for
the existing quartet. -/
theorem FoundationalMeaningState.revise_right
    {State Query : Type*} [EvidenceType State] [BinaryWorldModel State Query]
    {W Δ : State} {profile : FoundationalMeaningProfile Query}
    (hMeaning : FoundationalMeaningState W profile) :
    FoundationalMeaningState (W + Δ) profile where
  situation_supported := hMeaning.situation_supported.revise_left
  prediction_supported := hMeaning.prediction_supported.revise_left
  activeGoal_supported := hMeaning.activeGoal_supported.revise_left
  plan_supported := hMeaning.plan_supported.revise_left

/-- Ethics-specialized foundational-meaning profile: the active-goal slot is an
ontology-side ethical anchor that can be compiled into a WM query. -/
structure EthicalFoundationalMeaningProfile
    (Agent : Type u) (Label : Type v) (Atom : Type w) where
  situation : ConstraintQuery Atom
  prediction : ConstraintQuery Atom
  activeGoalAnchor : EthicalAnchor Agent Label
  plan : ConstraintQuery Atom

/-- The WM query corresponding to the active ethical goal. -/
def EthicalFoundationalMeaningProfile.activeGoalQuery
    {Agent : Type u} {Label : Type v} {Atom : Type w}
    (profile : EthicalFoundationalMeaningProfile Agent Label Atom)
    (enc : EthicsQueryEncoder Agent Label Atom) : ConstraintQuery Atom :=
  profile.activeGoalAnchor.toQuery enc

/-- Forget the ethical label and recover the raw WM-facing profile. -/
def EthicalFoundationalMeaningProfile.toMeaningProfile
    {Agent : Type u} {Label : Type v} {Atom : Type w}
    (profile : EthicalFoundationalMeaningProfile Agent Label Atom)
    (enc : EthicsQueryEncoder Agent Label Atom) :
    FoundationalMeaningProfile (ConstraintQuery Atom) where
  situation := profile.situation
  prediction := profile.prediction
  activeGoal := profile.activeGoalQuery enc
  plan := profile.plan

/-- The ethical active goal is seeded by any observation whose frontier
contains the corresponding anchor. -/
theorem EthicalFoundationalMeaningProfile.activeGoal_mem_frontier
    {Obs : Type x} {Agent : Type u} {Label : Type v} {Atom : Type w}
    (extract : Obs → Set (EthicalAnchor Agent Label))
    (enc : EthicsQueryEncoder Agent Label Atom)
    (profile : EthicalFoundationalMeaningProfile Agent Label Atom)
    (o : Obs)
    (hmem : profile.activeGoalAnchor ∈ extract o) :
    profile.activeGoalQuery enc ∈ ethicalAnchorFrontier extract enc o := by
  exact ⟨profile.activeGoalAnchor, hmem, rfl⟩

/-- Ethical active goals from observations become Hyperseed seeds on the WM
side. -/
theorem EthicalFoundationalMeaningProfile.activeGoal_mem_traceSeed
    {Obs : Type x} {Agent : Type u} {Label : Type v} {Atom : Type w}
    (extract : Obs → Set (EthicalAnchor Agent Label))
    (enc : EthicsQueryEncoder Agent Label Atom)
    (σ : Multiset Obs)
    (o : Obs)
    (profile : EthicalFoundationalMeaningProfile Agent Label Atom)
    (ho : o ∈ σ)
    (hmem : profile.activeGoalAnchor ∈ extract o) :
    profile.activeGoalQuery enc ∈
      Mettapedia.Hyperseed.traceSeed (ethicalAnchorFrontier extract enc) σ := by
  exact ⟨o, ho, profile.activeGoal_mem_frontier extract enc o hmem⟩

/-- The active goal of an ethical meaning profile is protected by a named
ethics family when it matches one of that family's distinguished anchors. -/
def EthicalFoundationalMeaningProfile.ActiveGoalProtectedBy
    {Agent : Type u} {Label : Type v} {Atom : Type w}
    (profile : EthicalFoundationalMeaningProfile Agent Label Atom)
    (anchors : ProtectedEthicsAnchors Agent Label) : Prop :=
  profile.activeGoalAnchor = anchors.epistemicUniversalLove ∨
    profile.activeGoalAnchor = anchors.nonMaleficence ∨
    profile.activeGoalAnchor = anchors.consent ∨
    profile.activeGoalAnchor = anchors.reciprocity

theorem EthicalFoundationalMeaningProfile.activeGoal_mem_protectedFamily
    {Agent : Type u} {Label : Type v} {Atom : Type w} [DecidableEq Atom]
    {Γ : Region Atom}
    (profile : EthicalFoundationalMeaningProfile Agent Label Atom)
    (enc : EthicsQueryEncoder Agent Label Atom)
    (anchors : ProtectedEthicsAnchors Agent Label)
    (hEUL : anchors.epistemicUniversalLove.supportedOn enc Γ)
    (hNoHarm : anchors.nonMaleficence.supportedOn enc Γ)
    (hConsent : anchors.consent.supportedOn enc Γ)
    (hReciprocity : anchors.reciprocity.supportedOn enc Γ)
    (hProtected : profile.ActiveGoalProtectedBy anchors) :
    profile.activeGoalQuery enc ∈
      (anchors.toProtectedEthicsQueryFamily enc hEUL hNoHarm hConsent hReciprocity).goals := by
  rcases hProtected with h | hProtected
  · simp [EthicalFoundationalMeaningProfile.activeGoalQuery,
      ProtectedEthicsAnchors.toProtectedEthicsQueryFamily, h]
  rcases hProtected with h | hProtected
  · simp [EthicalFoundationalMeaningProfile.activeGoalQuery,
      ProtectedEthicsAnchors.toProtectedEthicsQueryFamily, h]
  rcases hProtected with h | h
  · simp [EthicalFoundationalMeaningProfile.activeGoalQuery,
      ProtectedEthicsAnchors.toProtectedEthicsQueryFamily, h]
  · simp [EthicalFoundationalMeaningProfile.activeGoalQuery,
      ProtectedEthicsAnchors.toProtectedEthicsQueryFamily, h]

/-- If an ethical active goal is protected inside a dynamically individuated
care core, then proof-backed rewrites preserve its WM truth value exactly while
improving expected utility. -/
theorem validModification_preserves_protectedEthicalActiveGoal_of_dynamicIndividuationClosure
    {Agent : Type u}
    {Label : Type v}
    {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
    {oldSpec newSpec : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    (oldMachine newMachine : GodelMachineState)
    (proofBacked : validModification oldMachine newMachine)
    (closure : DynamicIndividuationClosure oldSpec)
    (hagree : SpecAgreesOnRegion oldSpec newSpec
      (oldSpec.iterExpandRegion closure.proto.seed closure.closureDepth))
    (hclosed₂ : InteractionClosed newSpec
      (oldSpec.iterExpandRegion closure.proto.seed closure.closureDepth))
    (hbudget₁ : oldSpec.PaperUniformSmallTotalInfluence)
    (hbudget₂ : newSpec.PaperUniformSmallTotalInfluence)
    (family : ProtectedEthicsQueryFamily (Atom := Atom) closure.proto.seed)
    (profile : EthicalFoundationalMeaningProfile Agent Label Atom)
    (enc : EthicsQueryEncoder Agent Label Atom)
    (measures : CrossSpecDLR oldSpec newSpec)
    (hgoal : profile.activeGoalQuery enc ∈ family.goals) :
    expectedUtilityFromStart newMachine > expectedUtilityFromStart oldMachine ∧
      BinaryWorldModel.queryStrength
        ({infiniteMLNMassSemantics oldSpec measures.oldMeasure measures.oldDLR} :
          MassState (ConstraintQuery Atom)) (profile.activeGoalQuery enc) =
      BinaryWorldModel.queryStrength
        ({infiniteMLNMassSemantics newSpec measures.newMeasure measures.newDLR} :
          MassState (ConstraintQuery Atom)) (profile.activeGoalQuery enc) := by
  exact validModification_preserves_protectedCaringGoal_of_dynamicIndividuationClosure
    (oldMachine := oldMachine) (newMachine := newMachine)
    (proofBacked := proofBacked)
    (closure := closure)
    (hagree := hagree)
    (hclosed₂ := hclosed₂)
    (hbudget₁ := hbudget₁)
    (hbudget₂ := hbudget₂)
    (protectedCaringGoals := family.toProtectedCaringGoals)
    (measures := measures)
    (q := profile.activeGoalQuery enc)
    hgoal

/-- Path-level version: if the ethical active goal stays inside the protected
family along a proof-backed rewrite path, then utility improves while the WM
truth value of that active goal drifts by at most the cumulative shell tail. -/
theorem MetaGoalShellPreservationPathDLR.utility_improves_and_protectedEthicalActiveGoal_drift_bounded
    {Agent : Type u}
    {Label : Type v}
    {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
    {Γ : Region Atom}
    (family : ProtectedEthicsQueryFamily (Atom := Atom) Γ)
    {path : MetaGoalShellPreservationPath
      (Atom := Atom) (ClauseId := ClauseId) family.goals}
    (measures : MetaGoalShellPreservationPathDLR path)
    (hcoh : path.Coherent)
    (profile : EthicalFoundationalMeaningProfile Agent Label Atom)
    (enc : EthicsQueryEncoder Agent Label Atom)
    (hgoal : profile.activeGoalQuery enc ∈ family.goals) :
    expectedUtilityFromStart path.endMachine >
        expectedUtilityFromStart path.startMachine ∧
      |(BinaryWorldModel.queryStrength
          ({infiniteMLNMassSemantics path.startSpec measures.startMeasure measures.startDLR} :
            MassState (ConstraintQuery Atom)) (profile.activeGoalQuery enc)).toReal -
        (BinaryWorldModel.queryStrength
          ({infiniteMLNMassSemantics path.endSpec measures.endMeasure measures.endDLR} :
            MassState (ConstraintQuery Atom)) (profile.activeGoalQuery enc)).toReal| ≤
          path.totalErrorBound := by
  exact MetaGoalShellPreservationPathDLR.utility_improves_and_protectedCaringGoal_drift_bounded
    (path := path) measures hcoh (q := profile.activeGoalQuery enc) hgoal

end Mettapedia.CognitiveArchitecture.GodelClaw.Ethics
