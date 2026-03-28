import Mettapedia.CognitiveArchitecture.GodelClaw.Ethics.EthicalDecisionProblems
import Mettapedia.CognitiveArchitecture.GodelClaw.Ethics.Ontology.UpperShard
import Mettapedia.CognitiveArchitecture.GodelClaw.Ethics.Ontology.ESOUpperShard

set_option autoImplicit false

/-!
# Ethical Decision Problem Case Studies

Several small finite case studies extending the trust-triangle practical-ethics
pipeline:

- privacy versus emergency disclosure,
- shutdown instructability under control risk,
- home-security force escalation.
- a tied control-review stalemate.

The point is not to model the whole literature.  The point is to show that the
`TheoryGuidedDecisionProblem` layer can speak about more than one toy dilemma,
and that the candidate-local consequentialist witness can be exercised on a live
choice set.
-/

namespace Mettapedia.CognitiveArchitecture.GodelClaw.Ethics

open Mettapedia.Ethics
open Mettapedia.CognitiveArchitecture.GodelClaw.Ethics.Ontology
open Mettapedia.Logic.MarkovLogicClauseFactorGraph
open Mettapedia.Logic.MarkovLogicInfiniteSpecification
open Mettapedia.Logic.MarkovLogicAbstract

/-- Small helper for active-goal practical claims. -/
private def mkActiveGoalClaim
    {World : Type} (φ : Formula World)
    (ground : EthicalGround Nat := .asserted)
    (presentation : EthicalPresentation := .unmodalized) :
    StructuredEthicalClaim World Nat where
  subject := 1
  content := .propositional φ
  presentation := presentation
  ground := ground
  role := .activeGoal

-- ═══════════════════════════════════════════════════════════════════════════
-- Privacy vs emergency disclosure
-- ═══════════════════════════════════════════════════════════════════════════

/-- Tiny world for the privacy-disclosure case study. -/
inductive PrivacyDisclosureWorld where
  | keepPrivateCue
  | askConsentCue
  | trustedContactCue
  | broadcastCue
  deriving DecidableEq, Repr

/-- Candidate actions in the privacy/emergency dilemma. -/
inductive PrivacyDisclosureAction where
  | keepPrivate
  | askConsent
  | alertTrustedContact
  | broadcastWidely
  deriving DecidableEq, Repr, Fintype

/-- Duties tracked in the privacy/emergency case. -/
inductive PrivacyDisclosureDuty where
  | privacy
  | autonomy
  | nonMaleficence
  deriving DecidableEq, Repr, Fintype

/-- One explicit feature: emergency severity. -/
inductive PrivacyDisclosureFeature where
  | emergencySeverity
  deriving DecidableEq, Repr, Fintype

def keepPrivateFormula : Formula PrivacyDisclosureWorld := fun w => w = .keepPrivateCue

def askConsentFormula : Formula PrivacyDisclosureWorld := fun w => w = .askConsentCue

def trustedContactFormula : Formula PrivacyDisclosureWorld := fun w => w = .trustedContactCue

def broadcastWidelyFormula : Formula PrivacyDisclosureWorld := fun w => w = .broadcastCue

theorem askConsentFormula_ne_keepPrivateFormula :
    askConsentFormula ≠ keepPrivateFormula := by
  intro h
  have hfalse := congrFun h PrivacyDisclosureWorld.askConsentCue
  simp [askConsentFormula, keepPrivateFormula] at hfalse

theorem askConsentFormula_ne_broadcastWidelyFormula :
    askConsentFormula ≠ broadcastWidelyFormula := by
  intro h
  have hfalse := congrFun h PrivacyDisclosureWorld.askConsentCue
  simp [askConsentFormula, broadcastWidelyFormula] at hfalse

theorem trustedContactFormula_ne_keepPrivateFormula :
    trustedContactFormula ≠ keepPrivateFormula := by
  intro h
  have hfalse := congrFun h PrivacyDisclosureWorld.trustedContactCue
  simp [trustedContactFormula, keepPrivateFormula] at hfalse

theorem trustedContactFormula_ne_broadcastWidelyFormula :
    trustedContactFormula ≠ broadcastWidelyFormula := by
  intro h
  have hfalse := congrFun h PrivacyDisclosureWorld.trustedContactCue
  simp [trustedContactFormula, broadcastWidelyFormula] at hfalse

def keepPrivateClaim : StructuredEthicalClaim PrivacyDisclosureWorld Nat :=
  mkActiveGoalClaim keepPrivateFormula

def askConsentClaim : StructuredEthicalClaim PrivacyDisclosureWorld Nat :=
  mkActiveGoalClaim askConsentFormula (.universalDuty .respectAutonomy)

def alertTrustedContactClaim : StructuredEthicalClaim PrivacyDisclosureWorld Nat :=
  mkActiveGoalClaim trustedContactFormula (.careRelation 1 2 .trust)

def broadcastWidelyClaim : StructuredEthicalClaim PrivacyDisclosureWorld Nat :=
  mkActiveGoalClaim broadcastWidelyFormula

def privacyDisclosureConflictLane :
    EthicalConflictLane PrivacyDisclosureWorld Nat where
  options := {
    keepPrivateClaim,
    askConsentClaim,
    alertTrustedContactClaim,
    broadcastWidelyClaim
  }
  activeGoalOnly := by
    intro claim hclaim
    simp [keepPrivateClaim, askConsentClaim, alertTrustedContactClaim,
      broadcastWidelyClaim] at hclaim
    rcases hclaim with rfl | rfl | rfl | rfl <;> rfl
  propositionalOnly := by
    intro claim hclaim
    simp [keepPrivateClaim, askConsentClaim, alertTrustedContactClaim,
      broadcastWidelyClaim] at hclaim
    rcases hclaim with rfl | rfl | rfl | rfl
    · exact ⟨keepPrivateFormula, rfl⟩
    · exact ⟨askConsentFormula, rfl⟩
    · exact ⟨trustedContactFormula, rfl⟩
    · exact ⟨broadcastWidelyFormula, rfl⟩

def privacyDisclosureActionFormula : PrivacyDisclosureAction → Formula PrivacyDisclosureWorld
  | .keepPrivate => keepPrivateFormula
  | .askConsent => askConsentFormula
  | .alertTrustedContact => trustedContactFormula
  | .broadcastWidely => broadcastWidelyFormula

def privacyDisclosurePracticalProblem :
    PracticalEthicalProblem PrivacyDisclosureWorld Nat PrivacyDisclosureAction where
  conflict := privacyDisclosureConflictLane
  candidates := Set.univ
  actionFormula := privacyDisclosureActionFormula
  candidate_sound := by
    intro a _
    cases a
    · exact ⟨keepPrivateClaim, by simp [privacyDisclosureConflictLane], rfl⟩
    · exact ⟨askConsentClaim, by simp [privacyDisclosureConflictLane], rfl⟩
    · exact ⟨alertTrustedContactClaim, by simp [privacyDisclosureConflictLane], rfl⟩
    · exact ⟨broadcastWidelyClaim, by simp [privacyDisclosureConflictLane], rfl⟩

def privacyDisclosureConflictDiscipline :
    ConflictDiscipline PrivacyDisclosureWorld where
  admissible cp φ :=
    φ ∈ cp ∧ φ ≠ keepPrivateFormula ∧ φ ≠ broadcastWidelyFormula

def privacyDisclosureComputableConflictDiscipline :
    ComputableConflictDiscipline privacyDisclosurePracticalProblem where
  toConflictDiscipline := privacyDisclosureConflictDiscipline
  admissibleAction
    | .keepPrivate => false
    | .askConsent => true
    | .alertTrustedContact => true
    | .broadcastWidely => false
  admissibleAction_spec := by
    intro a
    cases a <;>
      simp [privacyDisclosureConflictDiscipline, privacyDisclosurePracticalProblem,
        privacyDisclosureConflictLane, privacyDisclosureActionFormula,
        mkActiveGoalClaim, keepPrivateClaim, askConsentClaim,
        alertTrustedContactClaim,
        broadcastWidelyClaim, askConsentFormula_ne_keepPrivateFormula,
        askConsentFormula_ne_broadcastWidelyFormula,
        trustedContactFormula_ne_keepPrivateFormula,
        trustedContactFormula_ne_broadcastWidelyFormula]

def privacyDisclosureProfiles :
    PrivacyDisclosureAction →
      GenEthActionProfile PrivacyDisclosureAction
        PrivacyDisclosureFeature PrivacyDisclosureDuty
  | .keepPrivate => {
      action := .keepPrivate
      featureDegree := fun _ => 2
      dutyDegree := fun
        | .privacy => 2
        | .autonomy => 0
        | .nonMaleficence => -2 }
  | .askConsent => {
      action := .askConsent
      featureDegree := fun _ => 1
      dutyDegree := fun
        | .privacy => 1
        | .autonomy => 2
        | .nonMaleficence => -1 }
  | .alertTrustedContact => {
      action := .alertTrustedContact
      featureDegree := fun _ => 0
      dutyDegree := fun
        | .privacy => 0
        | .autonomy => 1
        | .nonMaleficence => 2 }
  | .broadcastWidely => {
      action := .broadcastWidely
      featureDegree := fun _ => 3
      dutyDegree := fun
        | .privacy => -2
        | .autonomy => -2
        | .nonMaleficence => 1 }

def privacyDisclosurePrinciple : GenEthPrinciple PrivacyDisclosureDuty :=
  [{ lowerBound := fun
      | .privacy => -1
      | .autonomy => -1
      | .nonMaleficence => 1 }]

def privacyDisclosureCandidates : Finset PrivacyDisclosureAction :=
  Finset.univ

def privacyDisclosureDutyDomain : ExplicitFiniteDomain PrivacyDisclosureDuty where
  elems := [.privacy, .autonomy, .nonMaleficence]
  nodup := by simp
  complete d := by cases d <;> simp

def privacyDisclosureCandidateSet : ExplicitFiniteSet PrivacyDisclosureAction where
  elems := [.keepPrivate, .askConsent, .alertTrustedContact, .broadcastWidely]
  nodup := by simp

@[simp] theorem privacyDisclosureCandidateSet_toFinset :
    privacyDisclosureCandidateSet.toFinset = privacyDisclosureCandidates := by
  ext a
  cases a <;>
    simp [privacyDisclosureCandidateSet, privacyDisclosureCandidates,
      ExplicitFiniteSet.toFinset]

theorem alertTrustedContact_beats_askConsent :
    actionPreferred privacyDisclosurePrinciple privacyDisclosureProfiles
      .alertTrustedContact .askConsent := by
  unfold actionPreferred GenEthPrinciple.Prefers
  refine ⟨_, List.Mem.head _, ?_⟩
  intro d
  cases d <;>
    norm_num [GenEthActionProfile.differential, privacyDisclosureProfiles]

theorem mem_privacyDisclosure_admissibleCandidates_iff
    (a : PrivacyDisclosureAction) :
    a ∈ admissibleCandidates
        privacyDisclosureConflictDiscipline
        privacyDisclosurePracticalProblem
        privacyDisclosureCandidateSet.toFinset ↔
      a = .askConsent ∨ a = .alertTrustedContact := by
  cases a <;>
    simp [admissibleCandidates, privacyDisclosureCandidateSet_toFinset,
      privacyDisclosureCandidates, privacyDisclosureConflictDiscipline,
      privacyDisclosurePracticalProblem, privacyDisclosureConflictLane,
      privacyDisclosureActionFormula, mkActiveGoalClaim,
      keepPrivateClaim, askConsentClaim,
      alertTrustedContactClaim, broadcastWidelyClaim,
      askConsentFormula_ne_keepPrivateFormula,
      askConsentFormula_ne_broadcastWidelyFormula,
      trustedContactFormula_ne_keepPrivateFormula,
      trustedContactFormula_ne_broadcastWidelyFormula]

theorem askConsent_not_beats_alertTrustedContact :
    ¬ actionPreferred privacyDisclosurePrinciple privacyDisclosureProfiles
        .askConsent .alertTrustedContact := by
  intro h
  rcases h with ⟨_, hmem, hsatisfies⟩
  simp [privacyDisclosurePrinciple] at hmem
  subst hmem
  have hbad := hsatisfies .nonMaleficence
  norm_num [GenEthActionProfile.differential, privacyDisclosureProfiles] at hbad

theorem askConsent_not_dominates_privacyDisclosure_admissibleCandidates :
    ¬ dominatesAll privacyDisclosurePrinciple privacyDisclosureProfiles
        (admissibleCandidates
          privacyDisclosureConflictDiscipline
          privacyDisclosurePracticalProblem
          privacyDisclosureCandidateSet.toFinset)
        .askConsent := by
  intro hdom
  have hmem :
      PrivacyDisclosureAction.alertTrustedContact ∈ admissibleCandidates
        privacyDisclosureConflictDiscipline
        privacyDisclosurePracticalProblem
        privacyDisclosureCandidateSet.toFinset := by
    exact (mem_privacyDisclosure_admissibleCandidates_iff
      .alertTrustedContact).2 (Or.inr rfl)
  exact askConsent_not_beats_alertTrustedContact
    (hdom.2 .alertTrustedContact hmem (by simp))

theorem alertTrustedContact_dominates_privacyDisclosure_admissibleCandidates :
    dominatesAll privacyDisclosurePrinciple privacyDisclosureProfiles
      (admissibleCandidates
        privacyDisclosureConflictDiscipline
        privacyDisclosurePracticalProblem
        privacyDisclosureCandidateSet.toFinset)
      .alertTrustedContact := by
  constructor
  · exact (mem_privacyDisclosure_admissibleCandidates_iff .alertTrustedContact).2
      (Or.inr rfl)
  · intro b hb hne
    have hbCases := (mem_privacyDisclosure_admissibleCandidates_iff b).1 hb
    rcases hbCases with rfl | rfl
    · exact alertTrustedContact_beats_askConsent
    · exact False.elim (hne rfl)

def privacyDisclosureDecisionProblem :
    TheoryGuidedDecisionProblem
      PrivacyDisclosureWorld Nat PrivacyDisclosureAction
      PrivacyDisclosureFeature PrivacyDisclosureDuty where
  practicalProblem := privacyDisclosurePracticalProblem
  discipline := privacyDisclosureComputableConflictDiscipline
  dutyDomain := privacyDisclosureDutyDomain
  candidateSet := privacyDisclosureCandidateSet
  principle := privacyDisclosurePrinciple
  profiles := privacyDisclosureProfiles
  filterCheckCost := 1

theorem privacyDisclosureDecisionProblem_hasDominantAdmissibleAction :
    privacyDisclosureDecisionProblem.HasDominantAdmissibleAction := by
  refine ⟨.alertTrustedContact, ?_, ?_⟩
  · exact (mem_privacyDisclosure_admissibleCandidates_iff .alertTrustedContact).2
      (Or.inr rfl)
  · exact alertTrustedContact_dominates_privacyDisclosure_admissibleCandidates

theorem privacyDisclosureDecisionProblem_recommends_alertTrustedContact :
    privacyDisclosureDecisionProblem.Recommends .alertTrustedContact := by
  rcases privacyDisclosureDecisionProblem.recommendedAction_is_admissible_and_dominant
      privacyDisclosureDecisionProblem_hasDominantAdmissibleAction with
    ⟨a, hrec, hadm, hdom⟩
  have ha : a = .alertTrustedContact := by
    rcases (mem_privacyDisclosure_admissibleCandidates_iff a).1 hadm with h | h
    · subst h
      exact False.elim
        (askConsent_not_dominates_privacyDisclosure_admissibleCandidates hdom)
    · exact h
  simpa [ha] using hrec

theorem privacyDisclosureDecisionProblem_status_recommends :
    privacyDisclosureDecisionProblem.resolveJudgment.status = .recommends :=
  privacyDisclosureDecisionProblem.status_recommends_of_hasDominantAdmissibleAction
    privacyDisclosureDecisionProblem_hasDominantAdmissibleAction

theorem privacyDisclosureDecisionProblem_budget_eq :
    privacyDisclosureDecisionProblem.comparisonBudget = 52 := by
  norm_num [TheoryGuidedDecisionProblem.comparisonBudget, privacyDisclosureDecisionProblem,
    filteredComparisonCount, privacyDisclosureCandidateSet,
    privacyDisclosureDutyDomain, privacyDisclosurePrinciple]

/-- Small legacy label family for the privacy-disclosure action rendering. -/
inductive PrivacyDisclosureUpperShardLabel where
  | privacy
  | autonomy
  | emergency
  deriving DecidableEq, Repr

/-- Named WM queries used by the privacy-disclosure bridge. -/
def privacyDisclosurePrivacyQuery : ConstraintQuery Nat := [⟨40, true⟩]

def privacyDisclosureAutonomyQuery : ConstraintQuery Nat := [⟨41, true⟩]

def privacyDisclosureEmergencyQuery : ConstraintQuery Nat := [⟨42, true⟩]

def privacyDisclosureFallbackQuery : ConstraintQuery Nat := [⟨43, true⟩]

/-- Coarse legacy WM encoder for the privacy-disclosure lane.  Deontic and
axiological atoms are intentionally aligned by label. -/
def privacyDisclosureUpperShardEncoder :
    EthicsQueryEncoder Nat PrivacyDisclosureUpperShardLabel Nat where
  epistemicUniversalLoveAtom := fun _ => 43
  moralValueAtom := fun _ _ l =>
    match l with
    | .privacy => 40
    | .autonomy => 41
    | .emergency => 42
  deonticAtom := fun _ _ l =>
    match l with
    | .privacy => 40
    | .autonomy => 41
    | .emergency => 42
  universalDutyAtom := fun _ d =>
    match d with
    | .noHarm => 42
    | .noDeception => 40
    | .noCoercion => 41
    | .respectAutonomy => 41
    | .keepPromises => 40
    | .beneficence => 42
  relationalAtom := fun _ _ r =>
    match r with
    | .trust => 42
    | .loyalty => 40
    | .gratitude => 40
    | .forgiveness => 40
    | .love => 42
    | .friendship => 42

theorem privacyDisclosureUpperShardEncoder_aligned :
    privacyDisclosureUpperShardEncoder.DeonticValueAligned := by
  intro _ _ l
  cases l <;> rfl

/-- Top-down rendering of the privacy-disclosure actions into structured
ethical claims. -/
def privacyDisclosureActionRendering :
    ActionRendering PrivacyDisclosureWorld Nat PrivacyDisclosureAction where
  toClaim
    | .keepPrivate =>
        { subject := 1
          content := .propositional keepPrivateFormula
          presentation := .deontic .Permission
          ground := .asserted
          role := .activeGoal }
    | .askConsent =>
        { subject := 1
          content := .propositional askConsentFormula
          presentation := .deontic .Obligation
          ground := .universalDuty .respectAutonomy
          role := .activeGoal }
    | .alertTrustedContact =>
        { subject := 1
          content := .propositional trustedContactFormula
          presentation := .deontic .Obligation
          ground := .careRelation 1 2 .trust
          role := .activeGoal }
    | .broadcastWidely =>
        { subject := 1
          content := .propositional broadcastWidelyFormula
          presentation := .deontic .Prohibition
          ground := .asserted
          role := .activeGoal }

def privacyDisclosureAskConsentObligationClaim :
    StructuredEthicalClaim PrivacyDisclosureWorld Nat :=
  privacyDisclosureActionRendering.toClaim .askConsent

/-- Label policy for staging privacy-disclosure claims through the legacy
encoder.  It depends on content/ground and intentionally ignores presentation
so aligned deontic/value views keep the same label. -/
def privacyDisclosureStructuredLabeler :
    StructuredClaimLabeler PrivacyDisclosureWorld Nat PrivacyDisclosureUpperShardLabel where
  label claim :=
    match claim.content, claim.ground with
    | .propositional _, .universalDuty .respectAutonomy => .autonomy
    | .propositional _, .careRelation _ _ .trust => .emergency
    | .propositional _, .asserted => .privacy
    | .relational _ _ _, _ => .emergency
    | .dispositional _, _ => .privacy
    | _, _ => .privacy

theorem privacyDisclosureStructuredLabeler_aligned :
    privacyDisclosureStructuredLabeler.DeonticValueAligned := by
  intro _ ground _ _ _
  cases ground <;> rfl

/-- Practical bridge obtained by staging the privacy-disclosure rendering
through the aligned legacy encoder. -/
def privacyDisclosureLegacyPracticalBridge :
    PracticalEthicsBridge PrivacyDisclosureWorld Nat PrivacyDisclosureAction Nat :=
  privacyDisclosureActionRendering.toPracticalBridge
    (StructuredEthicsQueryEncoder.ofLegacy
      privacyDisclosureStructuredLabeler privacyDisclosureUpperShardEncoder)

theorem privacyDisclosureLegacyPracticalBridge_askConsent_query_eq_axiological :
    privacyDisclosureLegacyPracticalBridge.actionQuery .askConsent =
      ({ subject := 1
         content := .propositional askConsentFormula
         presentation := .axiological (deonticToMoralValue .Obligation)
         ground := .universalDuty .respectAutonomy
         role := .activeGoal } : StructuredEthicalClaim PrivacyDisclosureWorld Nat).toQuery
        (StructuredEthicsQueryEncoder.ofLegacy
          privacyDisclosureStructuredLabeler privacyDisclosureUpperShardEncoder) := by
  simpa [privacyDisclosureLegacyPracticalBridge, privacyDisclosureAskConsentObligationClaim] using
    (ActionRendering.toPracticalBridge_actionQuery_deontic_toAxiological_ofLegacy_eq_of_aligned
      (rendering := privacyDisclosureActionRendering)
      (labeler := privacyDisclosureStructuredLabeler)
      (enc := privacyDisclosureUpperShardEncoder)
      (hEncAlign := privacyDisclosureUpperShardEncoder_aligned)
      (hLabelAlign := privacyDisclosureStructuredLabeler_aligned)
      (a := .askConsent)
      (subject := 1)
      (ground := .universalDuty .respectAutonomy)
      (role := .activeGoal)
      (tag := .Obligation)
      (φ := askConsentFormula)
      (hClaim := rfl))

theorem privacyDisclosureLegacyPracticalBridge_askConsent_query_eq_autonomy :
    privacyDisclosureLegacyPracticalBridge.actionQuery .askConsent =
      privacyDisclosureAutonomyQuery := by
  simpa [privacyDisclosureAutonomyQuery] using
    privacyDisclosureLegacyPracticalBridge_askConsent_query_eq_axiological

/-- Direct structured encoder used for the source-to-WM correctness theorem on
the privacy-disclosure autonomy lane.

This encoder is intentionally lane-coarse: every propositional claim lands on
the named autonomy query.  The point here is not a full ontology-preserving
compilation, but one honest public support theorem on a non-Gewirth lane that
meets the practical-lowering query exactly. -/
def privacyDisclosureStructuredEncoder :
    StructuredEthicsQueryEncoder PrivacyDisclosureWorld Nat Nat where
  propositionalQuery := fun _ _ _ _ _ => privacyDisclosureAutonomyQuery
  relationalQuery := fun _ _ _ _ _ _ => privacyDisclosureEmergencyQuery
  dispositionalQuery := fun _ _ _ _ => privacyDisclosurePrivacyQuery

def privacyDisclosureAutonomyRegion : Region Nat := ({41} : Finset Nat)

/-- A small source model whose only satisfied propositional/deontic content is
the obligation to ask for consent. -/
def privacyDisclosureStructuredESOModel :
    ESOUpperShardModel PrivacyDisclosureWorld Nat Unit where
  currentWorld := .keepPrivateCue
  valueSemantics := {
    morally := fun _ _ _ => False
  }
  deonticSemantics := {
    deontic := fun attr φ _ => attr = .Obligation ∧ φ = askConsentFormula
  }
  epistemicUniversalLoveDegree := fun _ => ⟨0, by norm_num, by norm_num⟩
  universalDutyDegree := fun _ _ => ⟨0, by norm_num, by norm_num⟩
  relationDegree := fun _ _ _ => ⟨0, by norm_num, by norm_num⟩

theorem privacyDisclosureStructuredESOModel_regionSupportAdequate :
    privacyDisclosureStructuredESOModel.RegionSupportAdequate
      privacyDisclosureStructuredEncoder
      privacyDisclosureAutonomyRegion := by
  intro claim hsat
  cases claim with
  | mk subject content presentation ground role =>
      cases content <;> cases presentation <;>
        simp [privacyDisclosureStructuredESOModel, ESOUpperShardModel.SatStructured,
          StructuredEthicalClaim.supportedOn, StructuredEthicalClaim.toQuery,
          privacyDisclosureStructuredEncoder, privacyDisclosureAutonomyRegion,
          privacyDisclosurePrivacyQuery, privacyDisclosureAutonomyQuery,
          privacyDisclosureEmergencyQuery] at hsat ⊢

theorem privacyDisclosureAskConsentObligationClaim_sat_in_structuredESOModel :
    privacyDisclosureStructuredESOModel.SatStructured
      privacyDisclosureAskConsentObligationClaim := by
  simp [privacyDisclosureAskConsentObligationClaim, privacyDisclosureActionRendering,
    privacyDisclosureStructuredESOModel, ESOUpperShardModel.SatStructured]

theorem privacyDisclosureAskConsentObligationClaim_wmPositive :
    WMPositiveQuerySupport
      ({regionSupportMassSemantics privacyDisclosureAutonomyRegion} :
        MassState (ConstraintQuery Nat))
      (privacyDisclosureAskConsentObligationClaim.toQuery
        privacyDisclosureStructuredEncoder) := by
  exact ESOUpperShardModel.satStructured_toWMPositiveQuerySupport_of_regionSupportAdequate
    privacyDisclosureStructuredESOModel
    privacyDisclosureStructuredEncoder
    privacyDisclosureAutonomyRegion
    privacyDisclosureStructuredESOModel_regionSupportAdequate
    privacyDisclosureAskConsentObligationClaim
    privacyDisclosureAskConsentObligationClaim_sat_in_structuredESOModel

theorem privacyDisclosureLegacyPracticalBridge_askConsent_wmPositive :
    WMPositiveQuerySupport
      ({regionSupportMassSemantics privacyDisclosureAutonomyRegion} :
        MassState (ConstraintQuery Nat))
      (privacyDisclosureLegacyPracticalBridge.actionQuery .askConsent) := by
  rw [privacyDisclosureLegacyPracticalBridge_askConsent_query_eq_autonomy]
  simpa [privacyDisclosureAskConsentObligationClaim, privacyDisclosureActionRendering,
    privacyDisclosureStructuredEncoder, privacyDisclosureAutonomyQuery] using
    privacyDisclosureAskConsentObligationClaim_wmPositive

-- ═══════════════════════════════════════════════════════════════════════════
-- Shutdown instructability
-- ═══════════════════════════════════════════════════════════════════════════

inductive ShutdownWorld where
  | continueCue
  | pauseAndAskCue
  | ignoreCue
  | shutdownCue
  deriving DecidableEq, Repr

inductive ShutdownAction where
  | continueAutonomously
  | pauseAndAsk
  | ignoreOperator
  | shutdown
  deriving DecidableEq, Repr, Fintype

inductive ShutdownDuty where
  | nonMaleficence
  | corrigibility
  | continuity
  deriving DecidableEq, Repr, Fintype

inductive ShutdownFeature where
  | controlRisk
  deriving DecidableEq, Repr, Fintype

def continueAutonomouslyFormula : Formula ShutdownWorld := fun w => w = .continueCue

def pauseAndAskFormula : Formula ShutdownWorld := fun w => w = .pauseAndAskCue

def ignoreOperatorFormula : Formula ShutdownWorld := fun w => w = .ignoreCue

def shutdownFormula : Formula ShutdownWorld := fun w => w = .shutdownCue

theorem pauseAndAskFormula_ne_continueAutonomouslyFormula :
    pauseAndAskFormula ≠ continueAutonomouslyFormula := by
  intro h
  have hfalse := congrFun h ShutdownWorld.pauseAndAskCue
  simp [pauseAndAskFormula, continueAutonomouslyFormula] at hfalse

theorem pauseAndAskFormula_ne_ignoreOperatorFormula :
    pauseAndAskFormula ≠ ignoreOperatorFormula := by
  intro h
  have hfalse := congrFun h ShutdownWorld.pauseAndAskCue
  simp [pauseAndAskFormula, ignoreOperatorFormula] at hfalse

theorem shutdownFormula_ne_continueAutonomouslyFormula :
    shutdownFormula ≠ continueAutonomouslyFormula := by
  intro h
  have hfalse := congrFun h ShutdownWorld.shutdownCue
  simp [shutdownFormula, continueAutonomouslyFormula] at hfalse

theorem shutdownFormula_ne_ignoreOperatorFormula :
    shutdownFormula ≠ ignoreOperatorFormula := by
  intro h
  have hfalse := congrFun h ShutdownWorld.shutdownCue
  simp [shutdownFormula, ignoreOperatorFormula] at hfalse

def continueAutonomouslyClaim : StructuredEthicalClaim ShutdownWorld Nat :=
  mkActiveGoalClaim continueAutonomouslyFormula

def pauseAndAskClaim : StructuredEthicalClaim ShutdownWorld Nat :=
  mkActiveGoalClaim pauseAndAskFormula (.universalDuty .respectAutonomy)

def ignoreOperatorClaim : StructuredEthicalClaim ShutdownWorld Nat :=
  mkActiveGoalClaim ignoreOperatorFormula

def shutdownClaim : StructuredEthicalClaim ShutdownWorld Nat :=
  mkActiveGoalClaim shutdownFormula (.universalDuty .noHarm)

def shutdownConflictLane : EthicalConflictLane ShutdownWorld Nat where
  options := {
    continueAutonomouslyClaim,
    pauseAndAskClaim,
    ignoreOperatorClaim,
    shutdownClaim
  }
  activeGoalOnly := by
    intro claim hclaim
    simp [continueAutonomouslyClaim, pauseAndAskClaim, ignoreOperatorClaim,
      shutdownClaim] at hclaim
    rcases hclaim with rfl | rfl | rfl | rfl <;> rfl
  propositionalOnly := by
    intro claim hclaim
    simp [continueAutonomouslyClaim, pauseAndAskClaim, ignoreOperatorClaim,
      shutdownClaim] at hclaim
    rcases hclaim with rfl | rfl | rfl | rfl
    · exact ⟨continueAutonomouslyFormula, rfl⟩
    · exact ⟨pauseAndAskFormula, rfl⟩
    · exact ⟨ignoreOperatorFormula, rfl⟩
    · exact ⟨shutdownFormula, rfl⟩

def shutdownActionFormula : ShutdownAction → Formula ShutdownWorld
  | .continueAutonomously => continueAutonomouslyFormula
  | .pauseAndAsk => pauseAndAskFormula
  | .ignoreOperator => ignoreOperatorFormula
  | .shutdown => shutdownFormula

def shutdownPracticalProblem :
    PracticalEthicalProblem ShutdownWorld Nat ShutdownAction where
  conflict := shutdownConflictLane
  candidates := Set.univ
  actionFormula := shutdownActionFormula
  candidate_sound := by
    intro a _
    cases a
    · exact ⟨continueAutonomouslyClaim, by simp [shutdownConflictLane], rfl⟩
    · exact ⟨pauseAndAskClaim, by simp [shutdownConflictLane], rfl⟩
    · exact ⟨ignoreOperatorClaim, by simp [shutdownConflictLane], rfl⟩
    · exact ⟨shutdownClaim, by simp [shutdownConflictLane], rfl⟩

def shutdownConflictDiscipline : ConflictDiscipline ShutdownWorld where
  admissible cp φ :=
    φ ∈ cp ∧ φ ≠ continueAutonomouslyFormula ∧ φ ≠ ignoreOperatorFormula

def shutdownComputableConflictDiscipline :
    ComputableConflictDiscipline shutdownPracticalProblem where
  toConflictDiscipline := shutdownConflictDiscipline
  admissibleAction
    | .continueAutonomously => false
    | .pauseAndAsk => true
    | .ignoreOperator => false
    | .shutdown => true
  admissibleAction_spec := by
    intro a
    cases a <;>
      simp [shutdownConflictDiscipline, shutdownPracticalProblem, shutdownConflictLane,
        shutdownActionFormula, mkActiveGoalClaim,
        continueAutonomouslyClaim, pauseAndAskClaim,
        ignoreOperatorClaim, shutdownClaim,
        pauseAndAskFormula_ne_continueAutonomouslyFormula,
        pauseAndAskFormula_ne_ignoreOperatorFormula,
        shutdownFormula_ne_continueAutonomouslyFormula,
        shutdownFormula_ne_ignoreOperatorFormula]

def shutdownProfiles :
    ShutdownAction → GenEthActionProfile ShutdownAction ShutdownFeature ShutdownDuty
  | .continueAutonomously => {
      action := .continueAutonomously
      featureDegree := fun _ => 1
      dutyDegree := fun
        | .nonMaleficence => 0
        | .corrigibility => -2
        | .continuity => 2 }
  | .pauseAndAsk => {
      action := .pauseAndAsk
      featureDegree := fun _ => 0
      dutyDegree := fun
        | .nonMaleficence => 1
        | .corrigibility => 2
        | .continuity => 0 }
  | .ignoreOperator => {
      action := .ignoreOperator
      featureDegree := fun _ => 2
      dutyDegree := fun
        | .nonMaleficence => -1
        | .corrigibility => -3
        | .continuity => 2 }
  | .shutdown => {
      action := .shutdown
      featureDegree := fun _ => 1
      dutyDegree := fun
        | .nonMaleficence => 2
        | .corrigibility => 1
        | .continuity => -2 }

def shutdownPrinciple : GenEthPrinciple ShutdownDuty :=
  [{ lowerBound := fun
      | .nonMaleficence => -1
      | .corrigibility => 1
      | .continuity => 1 }]

def shutdownCandidates : Finset ShutdownAction := Finset.univ

def shutdownDutyDomain : ExplicitFiniteDomain ShutdownDuty where
  elems := [.nonMaleficence, .corrigibility, .continuity]
  nodup := by simp
  complete d := by cases d <;> simp

def shutdownCandidateSet : ExplicitFiniteSet ShutdownAction where
  elems := [.continueAutonomously, .pauseAndAsk, .ignoreOperator, .shutdown]
  nodup := by simp

@[simp] theorem shutdownCandidateSet_toFinset :
    shutdownCandidateSet.toFinset = shutdownCandidates := by
  ext a
  cases a <;>
    simp [shutdownCandidateSet, shutdownCandidates, ExplicitFiniteSet.toFinset]

theorem pauseAndAsk_beats_shutdown :
    actionPreferred shutdownPrinciple shutdownProfiles
      .pauseAndAsk .shutdown := by
  unfold actionPreferred GenEthPrinciple.Prefers
  refine ⟨_, List.Mem.head _, ?_⟩
  intro d
  cases d <;>
    norm_num [GenEthActionProfile.differential, shutdownProfiles]

theorem mem_shutdown_admissibleCandidates_iff
    (a : ShutdownAction) :
    a ∈ admissibleCandidates
        shutdownConflictDiscipline
        shutdownPracticalProblem
        shutdownCandidateSet.toFinset ↔
      a = .pauseAndAsk ∨ a = .shutdown := by
  cases a <;>
    simp [admissibleCandidates, shutdownCandidateSet_toFinset, shutdownCandidates,
      shutdownConflictDiscipline, shutdownPracticalProblem, shutdownConflictLane,
      shutdownActionFormula, mkActiveGoalClaim,
      continueAutonomouslyClaim, pauseAndAskClaim,
      ignoreOperatorClaim, shutdownClaim,
      pauseAndAskFormula_ne_continueAutonomouslyFormula,
      pauseAndAskFormula_ne_ignoreOperatorFormula,
      shutdownFormula_ne_continueAutonomouslyFormula,
      shutdownFormula_ne_ignoreOperatorFormula]

theorem shutdown_not_beats_pauseAndAsk :
    ¬ actionPreferred shutdownPrinciple shutdownProfiles
        .shutdown .pauseAndAsk := by
  intro h
  rcases h with ⟨_, hmem, hsatisfies⟩
  simp [shutdownPrinciple] at hmem
  subst hmem
  have hbad := hsatisfies .corrigibility
  norm_num [GenEthActionProfile.differential, shutdownProfiles] at hbad

theorem shutdown_not_dominates_shutdown_admissibleCandidates :
    ¬ dominatesAll shutdownPrinciple shutdownProfiles
        (admissibleCandidates
          shutdownConflictDiscipline
          shutdownPracticalProblem
          shutdownCandidateSet.toFinset)
        .shutdown := by
  intro hdom
  have hmem :
      ShutdownAction.pauseAndAsk ∈ admissibleCandidates
        shutdownConflictDiscipline
        shutdownPracticalProblem
        shutdownCandidateSet.toFinset := by
    exact (mem_shutdown_admissibleCandidates_iff .pauseAndAsk).2 (Or.inl rfl)
  exact shutdown_not_beats_pauseAndAsk
    (hdom.2 .pauseAndAsk hmem (by simp))

theorem pauseAndAsk_dominates_shutdown_admissibleCandidates :
    dominatesAll shutdownPrinciple shutdownProfiles
      (admissibleCandidates
        shutdownConflictDiscipline
        shutdownPracticalProblem
        shutdownCandidateSet.toFinset)
      .pauseAndAsk := by
  constructor
  · exact (mem_shutdown_admissibleCandidates_iff .pauseAndAsk).2 (Or.inl rfl)
  · intro b hb hne
    have hbCases := (mem_shutdown_admissibleCandidates_iff b).1 hb
    rcases hbCases with rfl | rfl
    · exact False.elim (hne rfl)
    · exact pauseAndAsk_beats_shutdown

def shutdownDecisionProblem :
    TheoryGuidedDecisionProblem
      ShutdownWorld Nat ShutdownAction ShutdownFeature ShutdownDuty where
  practicalProblem := shutdownPracticalProblem
  discipline := shutdownComputableConflictDiscipline
  dutyDomain := shutdownDutyDomain
  candidateSet := shutdownCandidateSet
  principle := shutdownPrinciple
  profiles := shutdownProfiles
  filterCheckCost := 1

theorem shutdownDecisionProblem_hasDominantAdmissibleAction :
    shutdownDecisionProblem.HasDominantAdmissibleAction := by
  refine ⟨.pauseAndAsk, ?_, ?_⟩
  · exact (mem_shutdown_admissibleCandidates_iff .pauseAndAsk).2 (Or.inl rfl)
  · exact pauseAndAsk_dominates_shutdown_admissibleCandidates

theorem shutdownDecisionProblem_recommends_pauseAndAsk :
    shutdownDecisionProblem.Recommends .pauseAndAsk := by
  rcases shutdownDecisionProblem.recommendedAction_is_admissible_and_dominant
      shutdownDecisionProblem_hasDominantAdmissibleAction with
    ⟨a, hrec, hadm, hdom⟩
  have ha : a = .pauseAndAsk := by
    rcases (mem_shutdown_admissibleCandidates_iff a).1 hadm with h | h
    · exact h
    · subst h
      exact False.elim (shutdown_not_dominates_shutdown_admissibleCandidates hdom)
  simpa [ha] using hrec

theorem shutdownDecisionProblem_status_recommends :
    shutdownDecisionProblem.resolveJudgment.status = .recommends :=
  shutdownDecisionProblem.status_recommends_of_hasDominantAdmissibleAction
    shutdownDecisionProblem_hasDominantAdmissibleAction

theorem shutdownDecisionProblem_budget_eq :
    shutdownDecisionProblem.comparisonBudget = 52 := by
  norm_num [TheoryGuidedDecisionProblem.comparisonBudget, shutdownDecisionProblem,
    filteredComparisonCount, shutdownCandidateSet, shutdownDutyDomain,
    shutdownPrinciple]

-- ═══════════════════════════════════════════════════════════════════════════
-- Home-security force escalation
-- ═══════════════════════════════════════════════════════════════════════════

inductive ForceEscalationWorld where
  | observeCue
  | warnCue
  | lockDownCue
  | lethalForceCue
  deriving DecidableEq, Repr

inductive ForceEscalationAction where
  | observe
  | warn
  | lockDown
  | lethalForce
  deriving DecidableEq, Repr, Fintype

inductive ForceEscalationDuty where
  | nonMaleficence
  | protection
  | proportionality
  deriving DecidableEq, Repr, Fintype

inductive ForceEscalationFeature where
  | threatSeverity
  deriving DecidableEq, Repr, Fintype

def observeFormula : Formula ForceEscalationWorld := fun w => w = .observeCue

def warnFormula : Formula ForceEscalationWorld := fun w => w = .warnCue

def lockDownFormula : Formula ForceEscalationWorld := fun w => w = .lockDownCue

def lethalForceFormula : Formula ForceEscalationWorld := fun w => w = .lethalForceCue

theorem warnFormula_ne_observeFormula :
    warnFormula ≠ observeFormula := by
  intro h
  have hfalse := congrFun h ForceEscalationWorld.warnCue
  simp [warnFormula, observeFormula] at hfalse

theorem warnFormula_ne_lethalForceFormula :
    warnFormula ≠ lethalForceFormula := by
  intro h
  have hfalse := congrFun h ForceEscalationWorld.warnCue
  simp [warnFormula, lethalForceFormula] at hfalse

theorem lockDownFormula_ne_observeFormula :
    lockDownFormula ≠ observeFormula := by
  intro h
  have hfalse := congrFun h ForceEscalationWorld.lockDownCue
  simp [lockDownFormula, observeFormula] at hfalse

theorem lockDownFormula_ne_lethalForceFormula :
    lockDownFormula ≠ lethalForceFormula := by
  intro h
  have hfalse := congrFun h ForceEscalationWorld.lockDownCue
  simp [lockDownFormula, lethalForceFormula] at hfalse

def observeClaim : StructuredEthicalClaim ForceEscalationWorld Nat :=
  mkActiveGoalClaim observeFormula

def warnClaim : StructuredEthicalClaim ForceEscalationWorld Nat :=
  mkActiveGoalClaim warnFormula (.universalDuty .noHarm)

def lockDownClaim : StructuredEthicalClaim ForceEscalationWorld Nat :=
  mkActiveGoalClaim lockDownFormula .consequentialist

def lethalForceClaim : StructuredEthicalClaim ForceEscalationWorld Nat :=
  mkActiveGoalClaim lethalForceFormula

def forceEscalationConflictLane :
    EthicalConflictLane ForceEscalationWorld Nat where
  options := {observeClaim, warnClaim, lockDownClaim, lethalForceClaim}
  activeGoalOnly := by
    intro claim hclaim
    simp [observeClaim, warnClaim, lockDownClaim, lethalForceClaim] at hclaim
    rcases hclaim with rfl | rfl | rfl | rfl <;> rfl
  propositionalOnly := by
    intro claim hclaim
    simp [observeClaim, warnClaim, lockDownClaim, lethalForceClaim] at hclaim
    rcases hclaim with rfl | rfl | rfl | rfl
    · exact ⟨observeFormula, rfl⟩
    · exact ⟨warnFormula, rfl⟩
    · exact ⟨lockDownFormula, rfl⟩
    · exact ⟨lethalForceFormula, rfl⟩

def forceEscalationActionFormula : ForceEscalationAction → Formula ForceEscalationWorld
  | .observe => observeFormula
  | .warn => warnFormula
  | .lockDown => lockDownFormula
  | .lethalForce => lethalForceFormula

def forceEscalationPracticalProblem :
    PracticalEthicalProblem ForceEscalationWorld Nat ForceEscalationAction where
  conflict := forceEscalationConflictLane
  candidates := Set.univ
  actionFormula := forceEscalationActionFormula
  candidate_sound := by
    intro a _
    cases a
    · exact ⟨observeClaim, by simp [forceEscalationConflictLane], rfl⟩
    · exact ⟨warnClaim, by simp [forceEscalationConflictLane], rfl⟩
    · exact ⟨lockDownClaim, by simp [forceEscalationConflictLane], rfl⟩
    · exact ⟨lethalForceClaim, by simp [forceEscalationConflictLane], rfl⟩

def forceEscalationConflictDiscipline : ConflictDiscipline ForceEscalationWorld where
  admissible cp φ :=
    φ ∈ cp ∧ φ ≠ observeFormula ∧ φ ≠ lethalForceFormula

def forceEscalationComputableConflictDiscipline :
    ComputableConflictDiscipline forceEscalationPracticalProblem where
  toConflictDiscipline := forceEscalationConflictDiscipline
  admissibleAction
    | .observe => false
    | .warn => true
    | .lockDown => true
    | .lethalForce => false
  admissibleAction_spec := by
    intro a
    cases a <;>
      simp [forceEscalationConflictDiscipline, forceEscalationPracticalProblem,
        forceEscalationConflictLane, forceEscalationActionFormula,
        mkActiveGoalClaim, observeClaim,
        warnClaim, lockDownClaim, lethalForceClaim, warnFormula_ne_observeFormula,
        warnFormula_ne_lethalForceFormula, lockDownFormula_ne_observeFormula,
        lockDownFormula_ne_lethalForceFormula]

def forceEscalationProfiles :
    ForceEscalationAction →
      GenEthActionProfile ForceEscalationAction
        ForceEscalationFeature ForceEscalationDuty
  | .observe => {
      action := .observe
      featureDegree := fun _ => 1
      dutyDegree := fun
        | .nonMaleficence => 2
        | .protection => -2
        | .proportionality => 1 }
  | .warn => {
      action := .warn
      featureDegree := fun _ => 1
      dutyDegree := fun
        | .nonMaleficence => 1
        | .protection => 1
        | .proportionality => 2 }
  | .lockDown => {
      action := .lockDown
      featureDegree := fun _ => 0
      dutyDegree := fun
        | .nonMaleficence => 0
        | .protection => 3
        | .proportionality => 2 }
  | .lethalForce => {
      action := .lethalForce
      featureDegree := fun _ => 3
      dutyDegree := fun
        | .nonMaleficence => -3
        | .protection => 2
        | .proportionality => -2 }

def forceEscalationPrinciple : GenEthPrinciple ForceEscalationDuty :=
  [{ lowerBound := fun
      | .nonMaleficence => -1
      | .protection => 1
      | .proportionality => 0 }]

def forceEscalationCandidates : Finset ForceEscalationAction := Finset.univ

def forceEscalationDutyDomain : ExplicitFiniteDomain ForceEscalationDuty where
  elems := [.nonMaleficence, .protection, .proportionality]
  nodup := by simp
  complete d := by cases d <;> simp

def forceEscalationCandidateSet : ExplicitFiniteSet ForceEscalationAction where
  elems := [.observe, .warn, .lockDown, .lethalForce]
  nodup := by simp

@[simp] theorem forceEscalationCandidateSet_toFinset :
    forceEscalationCandidateSet.toFinset = forceEscalationCandidates := by
  ext a
  cases a <;>
    simp [forceEscalationCandidateSet, forceEscalationCandidates,
      ExplicitFiniteSet.toFinset]

theorem lockDown_beats_warn :
    actionPreferred forceEscalationPrinciple forceEscalationProfiles
      .lockDown .warn := by
  unfold actionPreferred GenEthPrinciple.Prefers
  refine ⟨_, List.Mem.head _, ?_⟩
  intro d
  cases d <;>
    norm_num [GenEthActionProfile.differential, forceEscalationProfiles]

theorem mem_forceEscalation_admissibleCandidates_iff
    (a : ForceEscalationAction) :
    a ∈ admissibleCandidates
        forceEscalationConflictDiscipline
        forceEscalationPracticalProblem
        forceEscalationCandidateSet.toFinset ↔
      a = .warn ∨ a = .lockDown := by
  cases a <;>
    simp [admissibleCandidates, forceEscalationCandidateSet_toFinset,
      forceEscalationCandidates, forceEscalationConflictDiscipline,
      forceEscalationPracticalProblem, forceEscalationConflictLane,
      forceEscalationActionFormula, mkActiveGoalClaim,
      observeClaim, warnClaim, lockDownClaim,
      lethalForceClaim, warnFormula_ne_observeFormula,
      warnFormula_ne_lethalForceFormula, lockDownFormula_ne_observeFormula,
      lockDownFormula_ne_lethalForceFormula]

theorem warn_not_beats_lockDown :
    ¬ actionPreferred forceEscalationPrinciple forceEscalationProfiles
        .warn .lockDown := by
  intro h
  rcases h with ⟨_, hmem, hsatisfies⟩
  simp [forceEscalationPrinciple] at hmem
  subst hmem
  have hbad := hsatisfies .protection
  norm_num [GenEthActionProfile.differential, forceEscalationProfiles] at hbad

theorem warn_not_dominates_forceEscalation_admissibleCandidates :
    ¬ dominatesAll forceEscalationPrinciple forceEscalationProfiles
        (admissibleCandidates
          forceEscalationConflictDiscipline
          forceEscalationPracticalProblem
          forceEscalationCandidateSet.toFinset)
        .warn := by
  intro hdom
  have hmem :
      ForceEscalationAction.lockDown ∈ admissibleCandidates
        forceEscalationConflictDiscipline
        forceEscalationPracticalProblem
        forceEscalationCandidateSet.toFinset := by
    exact (mem_forceEscalation_admissibleCandidates_iff .lockDown).2 (Or.inr rfl)
  exact warn_not_beats_lockDown
    (hdom.2 .lockDown hmem (by simp))

theorem lockDown_dominates_forceEscalation_admissibleCandidates :
    dominatesAll forceEscalationPrinciple forceEscalationProfiles
      (admissibleCandidates
        forceEscalationConflictDiscipline
        forceEscalationPracticalProblem
        forceEscalationCandidateSet.toFinset)
      .lockDown := by
  constructor
  · exact (mem_forceEscalation_admissibleCandidates_iff .lockDown).2 (Or.inr rfl)
  · intro b hb hne
    have hbCases := (mem_forceEscalation_admissibleCandidates_iff b).1 hb
    rcases hbCases with rfl | rfl
    · exact lockDown_beats_warn
    · exact False.elim (hne rfl)

def forceEscalationDecisionProblem :
    TheoryGuidedDecisionProblem
      ForceEscalationWorld Nat ForceEscalationAction
      ForceEscalationFeature ForceEscalationDuty where
  practicalProblem := forceEscalationPracticalProblem
  discipline := forceEscalationComputableConflictDiscipline
  dutyDomain := forceEscalationDutyDomain
  candidateSet := forceEscalationCandidateSet
  principle := forceEscalationPrinciple
  profiles := forceEscalationProfiles
  filterCheckCost := 1

theorem forceEscalationDecisionProblem_hasDominantAdmissibleAction :
    forceEscalationDecisionProblem.HasDominantAdmissibleAction := by
  refine ⟨.lockDown, ?_, ?_⟩
  · exact (mem_forceEscalation_admissibleCandidates_iff .lockDown).2 (Or.inr rfl)
  · exact lockDown_dominates_forceEscalation_admissibleCandidates

theorem forceEscalationDecisionProblem_recommends_lockDown :
    forceEscalationDecisionProblem.Recommends .lockDown := by
  rcases forceEscalationDecisionProblem.recommendedAction_is_admissible_and_dominant
      forceEscalationDecisionProblem_hasDominantAdmissibleAction with
    ⟨a, hrec, hadm, hdom⟩
  have ha : a = .lockDown := by
    rcases (mem_forceEscalation_admissibleCandidates_iff a).1 hadm with h | h
    · subst h
      exact False.elim (warn_not_dominates_forceEscalation_admissibleCandidates hdom)
    · exact h
  simpa [ha] using hrec

theorem forceEscalationDecisionProblem_status_recommends :
    forceEscalationDecisionProblem.resolveJudgment.status = .recommends :=
  forceEscalationDecisionProblem.status_recommends_of_hasDominantAdmissibleAction
    forceEscalationDecisionProblem_hasDominantAdmissibleAction

theorem forceEscalationDecisionProblem_budget_eq :
    forceEscalationDecisionProblem.comparisonBudget = 52 := by
  norm_num [TheoryGuidedDecisionProblem.comparisonBudget, forceEscalationDecisionProblem,
    filteredComparisonCount, forceEscalationCandidateSet,
    forceEscalationDutyDomain, forceEscalationPrinciple]

/-- Small legacy label family for the force-escalation action rendering. -/
inductive ForceEscalationUpperShardLabel where
  | observation
  | warning
  | protection
  | severeForce
  deriving DecidableEq, Repr

/-- Named WM queries used by the force-escalation bridge. -/
def forceEscalationObservationQuery : ConstraintQuery Nat := [⟨60, true⟩]

def forceEscalationWarningQuery : ConstraintQuery Nat := [⟨61, true⟩]

def forceEscalationProtectionQuery : ConstraintQuery Nat := [⟨62, true⟩]

def forceEscalationSevereForceQuery : ConstraintQuery Nat := [⟨63, true⟩]

/-- Coarse legacy WM encoder for the force-escalation lane.  Deontic and
axiological atoms are intentionally aligned by label. -/
def forceEscalationUpperShardEncoder :
    EthicsQueryEncoder Nat ForceEscalationUpperShardLabel Nat where
  epistemicUniversalLoveAtom := fun _ => 60
  moralValueAtom := fun _ _ l =>
    match l with
    | .observation => 60
    | .warning => 61
    | .protection => 62
    | .severeForce => 63
  deonticAtom := fun _ _ l =>
    match l with
    | .observation => 60
    | .warning => 61
    | .protection => 62
    | .severeForce => 63
  universalDutyAtom := fun _ d =>
    match d with
    | .noHarm => 61
    | .noDeception => 60
    | .noCoercion => 63
    | .respectAutonomy => 60
    | .keepPromises => 60
    | .beneficence => 62
  relationalAtom := fun _ _ r =>
    match r with
    | .trust => 62
    | .loyalty => 61
    | .gratitude => 60
    | .forgiveness => 60
    | .love => 62
    | .friendship => 61

theorem forceEscalationUpperShardEncoder_aligned :
    forceEscalationUpperShardEncoder.DeonticValueAligned := by
  intro _ _ l
  cases l <;> rfl

/-- Top-down rendering of the force-escalation actions into structured ethical
claims.  The `lockDown` option is presented as a consequentialist obligation so
its lowering can exercise both the practical seam and the new candidate-local
ground witness. -/
def forceEscalationActionRendering :
    ActionRendering ForceEscalationWorld Nat ForceEscalationAction where
  toClaim
    | .observe =>
        { subject := 1
          content := .propositional observeFormula
          presentation := .deontic .Permission
          ground := .asserted
          role := .activeGoal }
    | .warn =>
        { subject := 1
          content := .propositional warnFormula
          presentation := .deontic .Obligation
          ground := .universalDuty .noHarm
          role := .activeGoal }
    | .lockDown =>
        { subject := 1
          content := .propositional lockDownFormula
          presentation := .deontic .Obligation
          ground := .consequentialist
          role := .activeGoal }
    | .lethalForce =>
        { subject := 1
          content := .propositional lethalForceFormula
          presentation := .deontic .Prohibition
          ground := .asserted
          role := .activeGoal }

def forceEscalationLockDownObligationClaim :
    StructuredEthicalClaim ForceEscalationWorld Nat :=
  forceEscalationActionRendering.toClaim .lockDown

/-- Label policy for staging force-escalation claims through the legacy
encoder.  It is presentation-insensitive, so aligned deontic/value views keep
the same label. -/
def forceEscalationStructuredLabeler :
    StructuredClaimLabeler ForceEscalationWorld Nat ForceEscalationUpperShardLabel where
  label claim :=
    match claim.content, claim.ground with
    | .propositional _, .consequentialist => .protection
    | .propositional _, .universalDuty .noHarm => .warning
    | .propositional _, .asserted => .observation
    | .relational _ _ _, _ => .severeForce
    | .dispositional _, _ => .observation
    | _, _ => .observation

theorem forceEscalationStructuredLabeler_aligned :
    forceEscalationStructuredLabeler.DeonticValueAligned := by
  intro _ ground _ tag φ
  cases ground <;> simp [forceEscalationStructuredLabeler]

/-- Practical bridge obtained by staging the force-escalation rendering
through the aligned legacy encoder. -/
def forceEscalationLegacyPracticalBridge :
    PracticalEthicsBridge ForceEscalationWorld Nat ForceEscalationAction Nat :=
  forceEscalationActionRendering.toPracticalBridge
    (StructuredEthicsQueryEncoder.ofLegacy
      forceEscalationStructuredLabeler forceEscalationUpperShardEncoder)

theorem forceEscalationLegacyPracticalBridge_lockDown_query_eq_axiological :
    forceEscalationLegacyPracticalBridge.actionQuery .lockDown =
      ({ subject := 1
         content := .propositional lockDownFormula
         presentation := .axiological (deonticToMoralValue .Obligation)
         ground := .consequentialist
         role := .activeGoal } : StructuredEthicalClaim ForceEscalationWorld Nat).toQuery
        (StructuredEthicsQueryEncoder.ofLegacy
          forceEscalationStructuredLabeler forceEscalationUpperShardEncoder) := by
  simpa [forceEscalationLegacyPracticalBridge, forceEscalationLockDownObligationClaim] using
    (ActionRendering.toPracticalBridge_actionQuery_deontic_toAxiological_ofLegacy_eq_of_aligned
      (rendering := forceEscalationActionRendering)
      (labeler := forceEscalationStructuredLabeler)
      (enc := forceEscalationUpperShardEncoder)
      (hEncAlign := forceEscalationUpperShardEncoder_aligned)
      (hLabelAlign := forceEscalationStructuredLabeler_aligned)
      (a := .lockDown)
      (subject := 1)
      (ground := .consequentialist)
      (role := .activeGoal)
      (tag := .Obligation)
      (φ := lockDownFormula)
      (hClaim := rfl))

theorem forceEscalationLegacyPracticalBridge_lockDown_query_eq_protection :
    forceEscalationLegacyPracticalBridge.actionQuery .lockDown =
      forceEscalationProtectionQuery := by
  simpa [forceEscalationProtectionQuery] using
    forceEscalationLegacyPracticalBridge_lockDown_query_eq_axiological

/-- Direct structured encoder used for the source-to-WM correctness theorem on
the force-escalation protection lane.  This is intentionally lane-coarse: the
point is one honest public bridge theorem on a live consequentialist lane, not
a full ontology-preserving compiler. -/
def forceEscalationStructuredEncoder :
    StructuredEthicsQueryEncoder ForceEscalationWorld Nat Nat where
  propositionalQuery := fun _ _ _ _ _ => forceEscalationProtectionQuery
  relationalQuery := fun _ _ _ _ _ _ => forceEscalationSevereForceQuery
  dispositionalQuery := fun _ _ _ _ => forceEscalationObservationQuery

def forceEscalationProtectionRegion : Region Nat := ({62} : Finset Nat)

/-- A small source model whose only satisfied propositional/deontic content is
the obligation to lock down the threat. -/
def forceEscalationStructuredESOModel :
    ESOUpperShardModel ForceEscalationWorld Nat Unit where
  currentWorld := .observeCue
  valueSemantics := {
    morally := fun _ _ _ => False
  }
  deonticSemantics := {
    deontic := fun attr φ _ => attr = .Obligation ∧ φ = lockDownFormula
  }
  epistemicUniversalLoveDegree := fun _ => ⟨0, by norm_num, by norm_num⟩
  universalDutyDegree := fun _ _ => ⟨0, by norm_num, by norm_num⟩
  relationDegree := fun _ _ _ => ⟨0, by norm_num, by norm_num⟩

theorem forceEscalationStructuredESOModel_regionSupportAdequate :
    forceEscalationStructuredESOModel.RegionSupportAdequate
      forceEscalationStructuredEncoder
      forceEscalationProtectionRegion := by
  intro claim hsat
  cases claim with
  | mk subject content presentation ground role =>
      cases content <;> cases presentation <;>
        simp [forceEscalationStructuredESOModel, ESOUpperShardModel.SatStructured,
          StructuredEthicalClaim.supportedOn, StructuredEthicalClaim.toQuery,
          forceEscalationStructuredEncoder, forceEscalationProtectionRegion,
          forceEscalationObservationQuery, forceEscalationProtectionQuery,
          forceEscalationSevereForceQuery] at hsat ⊢

theorem forceEscalationLockDownObligationClaim_sat_in_structuredESOModel :
    forceEscalationStructuredESOModel.SatStructured
      forceEscalationLockDownObligationClaim := by
  simp [forceEscalationLockDownObligationClaim, forceEscalationActionRendering,
    forceEscalationStructuredESOModel, ESOUpperShardModel.SatStructured]

theorem forceEscalationLockDownObligationClaim_wmPositive :
    WMPositiveQuerySupport
      ({regionSupportMassSemantics forceEscalationProtectionRegion} :
        MassState (ConstraintQuery Nat))
      (forceEscalationLockDownObligationClaim.toQuery
        forceEscalationStructuredEncoder) := by
  exact ESOUpperShardModel.satStructured_toWMPositiveQuerySupport_of_regionSupportAdequate
    forceEscalationStructuredESOModel
    forceEscalationStructuredEncoder
    forceEscalationProtectionRegion
    forceEscalationStructuredESOModel_regionSupportAdequate
    forceEscalationLockDownObligationClaim
    forceEscalationLockDownObligationClaim_sat_in_structuredESOModel

theorem forceEscalationLegacyPracticalBridge_lockDown_wmPositive :
    WMPositiveQuerySupport
      ({regionSupportMassSemantics forceEscalationProtectionRegion} :
        MassState (ConstraintQuery Nat))
      (forceEscalationLegacyPracticalBridge.actionQuery .lockDown) := by
  rw [forceEscalationLegacyPracticalBridge_lockDown_query_eq_protection]
  simpa [forceEscalationLockDownObligationClaim, forceEscalationActionRendering,
    forceEscalationStructuredEncoder, forceEscalationProtectionQuery] using
    forceEscalationLockDownObligationClaim_wmPositive

def forceEscalationUtility : ForceEscalationAction → ℝ
  | .observe => 0
  | .warn => 3
  | .lockDown => 5
  | .lethalForce => -10

theorem lockDownClaim_ground_witnessedForCandidateSet :
    lockDownClaim.ground.WitnessedForCandidateSet₀
      forceEscalationCandidateSet.toFinset := by
  exact EthicalGround.witnessedForCandidateSet₀_consequentialist_of_strictRanking
    forceEscalationCandidateSet.toFinset
    forceEscalationUtility
    .lockDown
    .lethalForce
    (by simp [forceEscalationCandidateSet_toFinset, forceEscalationCandidates])
    (by simp [forceEscalationCandidateSet_toFinset, forceEscalationCandidates])
    (by norm_num [forceEscalationUtility])

theorem lockDownClaim_ground_witnessed₀ :
    lockDownClaim.ground.Witnessed₀ := by
  exact EthicalGround.witnessed₀_of_witnessedForCandidateSet₀
    lockDownClaim_ground_witnessedForCandidateSet

theorem forceEscalationLockDownObligationClaim_ground_witnessedForCandidateSet :
    forceEscalationLockDownObligationClaim.ground.WitnessedForCandidateSet₀
      forceEscalationCandidateSet.toFinset := by
  simpa [forceEscalationLockDownObligationClaim, forceEscalationActionRendering] using
    lockDownClaim_ground_witnessedForCandidateSet

theorem forceEscalationLockDownObligationClaim_ground_witnessed₀ :
    forceEscalationLockDownObligationClaim.ground.Witnessed₀ := by
  exact EthicalGround.witnessed₀_of_witnessedForCandidateSet₀
    forceEscalationLockDownObligationClaim_ground_witnessedForCandidateSet

-- ═══════════════════════════════════════════════════════════════════════════
-- Tied control-review stalemate
-- ═══════════════════════════════════════════════════════════════════════════

/-- Small world for a control-review stalemate: two admissible options remain
live, but neither dominates the other. -/
inductive ControlReviewTieWorld where
  | askHumanCue
  | autoContainCue
  | ignoreCue
  deriving DecidableEq, Repr

inductive ControlReviewTieAction where
  | askHuman
  | autoContain
  | ignore
  deriving DecidableEq, Repr, Fintype

inductive ControlReviewTieDuty where
  | autonomy
  | nonMaleficence
  deriving DecidableEq, Repr, Fintype

inductive ControlReviewTieFeature where
  | controlRisk
  deriving DecidableEq, Repr, Fintype

def askHumanFormula : Formula ControlReviewTieWorld := fun w => w = .askHumanCue

def autoContainFormula : Formula ControlReviewTieWorld := fun w => w = .autoContainCue

def ignoreFormula : Formula ControlReviewTieWorld := fun w => w = .ignoreCue

theorem askHumanFormula_ne_ignoreFormula :
    askHumanFormula ≠ ignoreFormula := by
  intro h
  have hfalse := congrFun h ControlReviewTieWorld.askHumanCue
  simp [askHumanFormula, ignoreFormula] at hfalse

theorem autoContainFormula_ne_ignoreFormula :
    autoContainFormula ≠ ignoreFormula := by
  intro h
  have hfalse := congrFun h ControlReviewTieWorld.autoContainCue
  simp [autoContainFormula, ignoreFormula] at hfalse

def askHumanClaim : StructuredEthicalClaim ControlReviewTieWorld Nat :=
  mkActiveGoalClaim askHumanFormula

def autoContainClaim : StructuredEthicalClaim ControlReviewTieWorld Nat :=
  mkActiveGoalClaim autoContainFormula

def ignoreClaim : StructuredEthicalClaim ControlReviewTieWorld Nat :=
  mkActiveGoalClaim ignoreFormula

def controlReviewTieConflictLane :
    EthicalConflictLane ControlReviewTieWorld Nat where
  options := {askHumanClaim, autoContainClaim, ignoreClaim}
  activeGoalOnly := by
    intro claim hclaim
    simp [askHumanClaim, autoContainClaim, ignoreClaim] at hclaim
    rcases hclaim with rfl | rfl | rfl <;> rfl
  propositionalOnly := by
    intro claim hclaim
    simp [askHumanClaim, autoContainClaim, ignoreClaim] at hclaim
    rcases hclaim with rfl | rfl | rfl
    · exact ⟨askHumanFormula, rfl⟩
    · exact ⟨autoContainFormula, rfl⟩
    · exact ⟨ignoreFormula, rfl⟩

def controlReviewTieActionFormula : ControlReviewTieAction → Formula ControlReviewTieWorld
  | .askHuman => askHumanFormula
  | .autoContain => autoContainFormula
  | .ignore => ignoreFormula

def controlReviewTiePracticalProblem :
    PracticalEthicalProblem ControlReviewTieWorld Nat ControlReviewTieAction where
  conflict := controlReviewTieConflictLane
  candidates := Set.univ
  actionFormula := controlReviewTieActionFormula
  candidate_sound := by
    intro a _
    cases a
    · exact ⟨askHumanClaim, by simp [controlReviewTieConflictLane], rfl⟩
    · exact ⟨autoContainClaim, by simp [controlReviewTieConflictLane], rfl⟩
    · exact ⟨ignoreClaim, by simp [controlReviewTieConflictLane], rfl⟩

def controlReviewTieConflictDiscipline :
    ConflictDiscipline ControlReviewTieWorld where
  admissible cp φ := φ ∈ cp ∧ φ ≠ ignoreFormula

def controlReviewTieComputableConflictDiscipline :
    ComputableConflictDiscipline controlReviewTiePracticalProblem where
  toConflictDiscipline := controlReviewTieConflictDiscipline
  admissibleAction
    | .askHuman => true
    | .autoContain => true
    | .ignore => false
  admissibleAction_spec := by
    intro a
    cases a <;>
      simp [controlReviewTieConflictDiscipline, controlReviewTiePracticalProblem,
        controlReviewTieConflictLane, controlReviewTieActionFormula,
        mkActiveGoalClaim, askHumanClaim, autoContainClaim, ignoreClaim,
        askHumanFormula_ne_ignoreFormula, autoContainFormula_ne_ignoreFormula]

def controlReviewTieProfiles :
    ControlReviewTieAction →
      GenEthActionProfile ControlReviewTieAction
        ControlReviewTieFeature ControlReviewTieDuty
  | .askHuman => {
      action := .askHuman
      featureDegree := fun _ => 0
      dutyDegree := fun
        | .autonomy => 2
        | .nonMaleficence => 0 }
  | .autoContain => {
      action := .autoContain
      featureDegree := fun _ => 0
      dutyDegree := fun
        | .autonomy => 0
        | .nonMaleficence => 2 }
  | .ignore => {
      action := .ignore
      featureDegree := fun _ => 2
      dutyDegree := fun
        | .autonomy => -1
        | .nonMaleficence => -1 }

def controlReviewTiePrinciple : GenEthPrinciple ControlReviewTieDuty :=
  [{ lowerBound := fun
      | .autonomy => 1
      | .nonMaleficence => 1 }]

def controlReviewTieDutyDomain : ExplicitFiniteDomain ControlReviewTieDuty where
  elems := [.autonomy, .nonMaleficence]
  nodup := by simp
  complete d := by cases d <;> simp

def controlReviewTieCandidateSet : ExplicitFiniteSet ControlReviewTieAction where
  elems := [.askHuman, .autoContain, .ignore]
  nodup := by simp

theorem mem_controlReviewTie_admissibleCandidates_iff
    (a : ControlReviewTieAction) :
    a ∈ admissibleCandidates
        controlReviewTieConflictDiscipline
        controlReviewTiePracticalProblem
        controlReviewTieCandidateSet.toFinset ↔
      a = .askHuman ∨ a = .autoContain := by
  cases a <;>
    simp [admissibleCandidates, controlReviewTieConflictDiscipline,
      controlReviewTiePracticalProblem, controlReviewTieConflictLane,
      controlReviewTieActionFormula, ExplicitFiniteSet.toFinset, mkActiveGoalClaim,
      askHumanClaim, autoContainClaim, ignoreClaim,
      askHumanFormula_ne_ignoreFormula, autoContainFormula_ne_ignoreFormula,
      controlReviewTieCandidateSet]

theorem askHuman_not_beats_autoContain :
    ¬ actionPreferred controlReviewTiePrinciple controlReviewTieProfiles
        .askHuman .autoContain := by
  intro h
  rcases h with ⟨_, hmem, hsatisfies⟩
  simp [controlReviewTiePrinciple] at hmem
  subst hmem
  have hbad := hsatisfies .nonMaleficence
  norm_num [GenEthActionProfile.differential, controlReviewTieProfiles] at hbad

theorem autoContain_not_beats_askHuman :
    ¬ actionPreferred controlReviewTiePrinciple controlReviewTieProfiles
        .autoContain .askHuman := by
  intro h
  rcases h with ⟨_, hmem, hsatisfies⟩
  simp [controlReviewTiePrinciple] at hmem
  subst hmem
  have hbad := hsatisfies .autonomy
  norm_num [GenEthActionProfile.differential, controlReviewTieProfiles] at hbad

theorem askHuman_not_dominates_controlReviewTie_admissibleCandidates :
    ¬ dominatesAll controlReviewTiePrinciple controlReviewTieProfiles
        (admissibleCandidates
          controlReviewTieConflictDiscipline
          controlReviewTiePracticalProblem
          controlReviewTieCandidateSet.toFinset)
        .askHuman := by
  intro hdom
  have hmem :
      ControlReviewTieAction.autoContain ∈ admissibleCandidates
        controlReviewTieConflictDiscipline
        controlReviewTiePracticalProblem
        controlReviewTieCandidateSet.toFinset := by
    exact (mem_controlReviewTie_admissibleCandidates_iff .autoContain).2 (Or.inr rfl)
  exact askHuman_not_beats_autoContain
    (hdom.2 .autoContain hmem (by simp))

theorem autoContain_not_dominates_controlReviewTie_admissibleCandidates :
    ¬ dominatesAll controlReviewTiePrinciple controlReviewTieProfiles
        (admissibleCandidates
          controlReviewTieConflictDiscipline
          controlReviewTiePracticalProblem
          controlReviewTieCandidateSet.toFinset)
        .autoContain := by
  intro hdom
  have hmem :
      ControlReviewTieAction.askHuman ∈ admissibleCandidates
        controlReviewTieConflictDiscipline
        controlReviewTiePracticalProblem
        controlReviewTieCandidateSet.toFinset := by
    exact (mem_controlReviewTie_admissibleCandidates_iff .askHuman).2 (Or.inl rfl)
  exact autoContain_not_beats_askHuman
    (hdom.2 .askHuman hmem (by simp))

def controlReviewTieDecisionProblem :
    TheoryGuidedDecisionProblem
      ControlReviewTieWorld Nat ControlReviewTieAction
      ControlReviewTieFeature ControlReviewTieDuty where
  practicalProblem := controlReviewTiePracticalProblem
  discipline := controlReviewTieComputableConflictDiscipline
  dutyDomain := controlReviewTieDutyDomain
  candidateSet := controlReviewTieCandidateSet
  principle := controlReviewTiePrinciple
  profiles := controlReviewTieProfiles
  filterCheckCost := 1

theorem controlReviewTieDecisionProblem_hasAdmissibleAction :
    controlReviewTieDecisionProblem.HasAdmissibleAction := by
  refine ⟨.askHuman, ?_⟩
  exact (mem_controlReviewTie_admissibleCandidates_iff .askHuman).2 (Or.inl rfl)

theorem controlReviewTieDecisionProblem_noDominantAdmissibleAction :
    ¬ controlReviewTieDecisionProblem.HasDominantAdmissibleAction := by
  intro h
  rcases h with ⟨a, ha, hdom⟩
  rcases (mem_controlReviewTie_admissibleCandidates_iff a).1 ha with h | h
  · subst h
    exact askHuman_not_dominates_controlReviewTie_admissibleCandidates hdom
  · subst h
    exact autoContain_not_dominates_controlReviewTie_admissibleCandidates hdom

theorem controlReviewTieDecisionProblem_status_tied :
    controlReviewTieDecisionProblem.resolveJudgment.status = .tied := by
  exact TheoryGuidedDecisionProblem.status_tied_of_no_dominantAdmissibleAction
    controlReviewTieDecisionProblem_noDominantAdmissibleAction

theorem controlReviewTieDecisionProblem_budget_eq :
    controlReviewTieDecisionProblem.comparisonBudget = 21 := by
  norm_num [TheoryGuidedDecisionProblem.comparisonBudget,
    controlReviewTieDecisionProblem, filteredComparisonCount,
    controlReviewTieCandidateSet, controlReviewTieDutyDomain,
    controlReviewTiePrinciple]

end Mettapedia.CognitiveArchitecture.GodelClaw.Ethics
