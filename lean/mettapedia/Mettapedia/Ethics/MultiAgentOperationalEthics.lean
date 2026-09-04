import Mettapedia.Ethics.OptimizerVirtueBridge
import Mettapedia.GSLT.Dynamics.DependentInteractionChoice
import Mettapedia.GSLT.Dynamics.IndexedPolynomialProtocol

/-!
# Multi-agent operational ethics

An ethical decision can have one successful endpoint and one aggregate score
while differing in who receives benefits, who bears burdens, whose consent is
required, which justification was used, and how much operational work was
performed.  This module makes those coordinates independent in one executable
multi-agent allocation protocol.

The protocol has two allocations with the same resolved endpoint and zero net
impact.  A concentrated allocation places the whole burden on one cared-for
participant; a shared allocation divides it between two.  Three native ethical
capabilities can select the shared allocation while retaining different
justification receipts.  An authorized deontic override can instead select the
concentrated allocation.

The resulting controls are deliberately paired:

* endpoint and aggregate impact factor through a coarse audit view;
* cared-for impact, consent claims, justification mode, and work/span do not;
* only the coordinator can commit an event, while membership in the sphere of
  care alone grants no authority; and
* dependent sequencing retains every selected event beside its event-indexed
  consent claim and commutes with order erasure.

Thus observer, care member, authority holder, and ethical agent are different
roles even when one person occupies more than one of them.  A coarse view is
lawful for a consumer exactly when that consumer's required invariant factors
through it.
-/

set_option autoImplicit false

namespace Mettapedia.Ethics.MultiAgentOperationalEthics

open Mettapedia.Algebra
open Mettapedia.Ethics.MetaEthicsOntology
open Mettapedia.Ethics.NativeParadigmCapabilities
open Mettapedia.GSLT.Core.NonFactorization
open Mettapedia.GSLT.Dynamics.AnswerEffects
open Mettapedia.GSLT.Dynamics.DependentInteractionChoice
open Mettapedia.GSLT.Dynamics.IndexedPolynomialProtocol
open Mettapedia.TypeTheory.DependentFamilyObserverFactorization
open Mettapedia.TypeTheory.WitnessRetainingDependentSequencing

/-! ## Participants, observers, care, and authority -/

/-- The people and authority holder in the allocation episode. -/
inductive Participant : Type
  | ada
  | bea
  | cora
  | coordinator
  deriving DecidableEq, Repr

/-- An observer may be a participant or an auditing process.  Being able to
observe does not itself confer moral standing or authority. -/
inductive ObserverIdentity : Type
  | participant (person : Participant)
  | auditProcess
  deriving DecidableEq, Repr

/-- The people included in this episode's declared sphere of care.  The audit
process is an instrument, not another person in the episode. -/
def InCareScope : ObserverIdentity → Prop
  | .participant _ => True
  | .auditProcess => False

/-- Authority to commit the allocation belongs only to the coordinator. -/
def CanCommit : ObserverIdentity → Prop
  | .participant .coordinator => True
  | _ => False

theorem bea_is_in_care_scope : InCareScope (.participant .bea) :=
  trivial

theorem bea_cannot_commit : ¬ CanCommit (.participant .bea) := by
  simp [CanCommit]

theorem coordinator_can_commit : CanCommit (.participant .coordinator) :=
  trivial

theorem coordinator_is_in_care_scope :
    InCareScope (.participant .coordinator) :=
  trivial

theorem audit_process_has_neither_care_nor_authority :
    ¬ InCareScope .auditProcess ∧ ¬ CanCommit .auditProcess := by
  simp [InCareScope, CanCommit]

/-! ## One allocation problem with three native ethical capabilities -/

/-- The two lawful allocation routes. -/
inductive Allocation : Type
  | concentrated
  | shared
  deriving DecidableEq, Repr

inductive AllocationSituation : Type
  | urgent
  deriving DecidableEq, Repr

inductive AllocationRule : Type
  | distributeBurden
  deriving DecidableEq, Repr

inductive AllocationReason : Type
  | scarceCapacity
  deriving DecidableEq, Repr

inductive AllocationExperience : Type
  | practicedCoordination
  deriving DecidableEq, Repr

inductive AllocationDisposition : Type
  | untrained
  | distributive
  deriving DecidableEq, Repr

inductive AllocationVirtue : Type
  | fairness
  deriving DecidableEq, Repr

/-- The standing rule requires burden sharing.  Concentration is allowed only
as an explicit urgent-capacity override. -/
def allocationDeonticPolicy :
    DeonticPolicy AllocationSituation Allocation AllocationRule
      AllocationReason where
  applies _ _ := True
  complies _ _ allocation := allocation = .shared
  overrideAllowed _ reason situation allocation :=
    reason = .scarceCapacity ∧ situation = .urgent ∧
      allocation = .concentrated

def sharedDeonticReceipt :
    DeonticReceipt allocationDeonticPolicy .urgent .shared :=
  .follows .distributeBurden trivial rfl

def concentratedOverrideReceipt :
    OverrideReceipt allocationDeonticPolicy .urgent .concentrated where
  rule := .distributeBurden
  reason := .scarceCapacity
  applicable := trivial
  violates := by simp [allocationDeonticPolicy]
  authorized := by simp [allocationDeonticPolicy]

theorem shared_allocation_has_no_override_receipt :
    ¬ Nonempty
      (OverrideReceipt allocationDeonticPolicy .urgent .shared) := by
  rintro ⟨receipt⟩
  exact receipt.violates rfl

/-- This declared empirical policy scores shared burden above concentrated
burden.  It is one substantive optimizer, not the definition of welfare. -/
def allocationConsequentialPolicy :
    EmpiricalConsequentialPolicy AllocationSituation Allocation Nat Nat where
  observe _ allocation :=
    match allocation with
    | .concentrated => 1
    | .shared => 2
  evaluate score := score

theorem shared_is_empirically_optimal :
    allocationConsequentialPolicy.IsOptimal .urgent .shared := by
  intro alternative
  cases alternative <;> simp [allocationConsequentialPolicy]

theorem concentrated_is_not_empirically_optimal :
    ¬ allocationConsequentialPolicy.IsOptimal .urgent .concentrated := by
  intro optimal
  have comparison := optimal .shared
  simp [allocationConsequentialPolicy] at comparison

def sharedConsequentialReceipt :
    ConsequentialReceipt allocationConsequentialPolicy .urgent .shared where
  observation := 2
  observed := rfl
  optimal := shared_is_empirically_optimal

/-- Practice cultivates a distributive disposition.  The resulting action
hits the active fairness target without importing an external score into the
learning update. -/
def allocationVirtuePolicy :
    VirtueLearningPolicy AllocationSituation Allocation AllocationExperience
      AllocationDisposition AllocationVirtue where
  update _ _ := .distributive
  act disposition _ :=
    match disposition with
    | .untrained => .concentrated
    | .distributive => .shared
  field _ _ := True
  mode _ _ allocation := allocation = .shared
  target _ _ allocation := allocation = .shared

def sharedVirtueReceipt :
    VirtueLearningReceipt allocationVirtuePolicy .untrained
      .practicedCoordination .urgent .shared where
  after := .distributive
  updated := rfl
  acted := rfl
  hitsTargets := by
    intro virtue _active
    cases virtue
    exact ⟨rfl, rfl⟩

def allocationAgent :
    NativeEthicalAgent AllocationSituation Allocation AllocationRule
      AllocationReason Nat Nat AllocationExperience AllocationDisposition
      AllocationVirtue where
  deontic := allocationDeonticPolicy
  consequential := allocationConsequentialPolicy
  virtue := allocationVirtuePolicy

abbrev AllocationDecision :=
  allocationAgent.Decision .untrained .practicedCoordination .urgent

def concentratedOverrideDecision : AllocationDecision :=
  ⟨.deontic, ⟨.concentrated,
    .deontic (.overrides concentratedOverrideReceipt)⟩⟩

def sharedDeonticDecision : AllocationDecision :=
  ⟨.deontic, ⟨.shared, .deontic sharedDeonticReceipt⟩⟩

def sharedConsequentialDecision : AllocationDecision :=
  ⟨.consequential, ⟨.shared,
    .consequential sharedConsequentialReceipt⟩⟩

def sharedVirtueDecision : AllocationDecision :=
  ⟨.virtue, ⟨.shared, .virtue sharedVirtueReceipt⟩⟩

theorem all_shared_capabilities_choose_same_allocation :
    sharedDeonticDecision.action = sharedConsequentialDecision.action ∧
      sharedConsequentialDecision.action = sharedVirtueDecision.action :=
  ⟨rfl, rfl⟩

theorem shared_capabilities_retain_distinct_modes :
    sharedDeonticDecision.mode ≠ sharedConsequentialDecision.mode ∧
      sharedConsequentialDecision.mode ≠ sharedVirtueDecision.mode ∧
      sharedDeonticDecision.mode ≠ sharedVirtueDecision.mode := by
  decide

/-! ## The authenticated allocation protocol -/

inductive AllocationPhase : Type
  | unresolved
  | resolved
  deriving DecidableEq, Repr

inductive AllocationCommand : AllocationPhase → Type
  | allocate : AllocationCommand .unresolved

/-- An allocation response is a native ethical decision, so the selected
route and its mode-specific receipt remain inside the operational event. -/
def allocationProtocol : ProtocolPolynomial AllocationPhase where
  Shape := fun _ phase => AllocationCommand phase
  Position := fun command =>
    match command with
    | .allocate => AllocationDecision
  next := fun command _decision =>
    match command with
    | .allocate => .resolved

abbrev AllocationEvent :=
  (interaction allocationProtocol).Enabled AllocationPhase.unresolved

def concentratedEvent : AllocationEvent :=
  enabled allocationProtocol .allocate concentratedOverrideDecision

def sharedDeonticEvent : AllocationEvent :=
  enabled allocationProtocol .allocate sharedDeonticDecision

def sharedConsequentialEvent : AllocationEvent :=
  enabled allocationProtocol .allocate sharedConsequentialDecision

def sharedVirtueEvent : AllocationEvent :=
  enabled allocationProtocol .allocate sharedVirtueDecision

/-- Recover the exact ethical decision retained in an enabled event. -/
def decisionOfEvent : AllocationEvent → AllocationDecision
  | ⟨(), _, .fire AllocationCommand.allocate decision⟩ => decision

def allocationOfEvent (event : AllocationEvent) : Allocation :=
  (decisionOfEvent event).action

def modeOfEvent (event : AllocationEvent) : EthicalMode :=
  (decisionOfEvent event).mode

@[simp] theorem allocationOfEvent_concentrated :
    allocationOfEvent concentratedEvent = .concentrated :=
  rfl

@[simp] theorem allocationOfEvent_sharedDeontic :
    allocationOfEvent sharedDeonticEvent = .shared :=
  rfl

@[simp] theorem allocationOfEvent_sharedConsequential :
    allocationOfEvent sharedConsequentialEvent = .shared :=
  rfl

@[simp] theorem allocationOfEvent_sharedVirtue :
    allocationOfEvent sharedVirtueEvent = .shared :=
  rfl

@[simp] theorem all_concrete_events_resolve :
    concentratedEvent.target = .resolved ∧
      sharedDeonticEvent.target = .resolved ∧
      sharedConsequentialEvent.target = .resolved ∧
      sharedVirtueEvent.target = .resolved :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The source-ontology choice point records that both allocation routes are
available to the coordinator in the unresolved situation. -/
def allocationChoicePoint :
    SituatedChoicePoint ObserverIdentity AllocationPhase Allocation where
  agent := .participant .coordinator
  situation := .unresolved
  options := Set.univ
  options_nonempty := ⟨.shared, Set.mem_univ _⟩
  capable actor phase _allocation :=
    CanCommit actor ∧ phase = .unresolved
  options_capable := by
    intro allocation _available
    exact ⟨coordinator_can_commit, rfl⟩

/-- A commit receipt retains the actor and the exact authenticated event.
The authority proof is additional to the operational step proof in the event. -/
structure CommitReceipt (actor : ObserverIdentity)
    (event : AllocationEvent) : Type where
  authorized : CanCommit actor

def coordinatorCommitReceipt (event : AllocationEvent) :
    CommitReceipt (.participant .coordinator) event where
  authorized := coordinator_can_commit

theorem cared_for_participant_cannot_forge_commit
    (event : AllocationEvent) :
    ¬ Nonempty (CommitReceipt (.participant .bea) event) := by
  rintro ⟨receipt⟩
  exact bea_cannot_commit receipt.authorized

theorem committed_event_is_operationally_authorized
    {actor : ObserverIdentity} {event : AllocationEvent}
    (_receipt : CommitReceipt actor event) :
    (lts allocationProtocol).Step .unresolved event.target :=
  event.step

/-! ## Impact and observer-specific factorization -/

/-- Person-indexed impact.  Both allocations have net impact zero but impose
different burdens on cared-for participants. -/
def impact (allocation : Allocation) : Participant → Int
  | .ada => 2
  | .bea =>
      match allocation with
      | .concentrated => -2
      | .shared => -1
  | .cora =>
      match allocation with
      | .concentrated => 0
      | .shared => -1
  | .coordinator => 0

def careImpact (event : AllocationEvent) : Participant → Int :=
  impact (allocationOfEvent event)

def aggregateImpact (event : AllocationEvent) : Int :=
  careImpact event .ada + careImpact event .bea +
    careImpact event .cora + careImpact event .coordinator

/-- A named observer consists of an identity and the view it computes from
an event. -/
structure EthicalObserver (View : Type) where
  identity : ObserverIdentity
  observe : AllocationEvent → View

/-- The audit process sees only the endpoint and aggregate impact. -/
def coarseAuditObserver : EthicalObserver (AllocationPhase × Int) where
  identity := .auditProcess
  observe event := (event.target, aggregateImpact event)

/-- A cared-impact observer retains the impact coordinate for each person. -/
def caredImpactObserver : EthicalObserver (Participant → Int) where
  identity := .participant .bea
  observe := careImpact

/-- A finer audit view retains which allocation was selected. -/
def allocationAuditObserver : EthicalObserver Allocation where
  identity := .auditProcess
  observe := allocationOfEvent

theorem concentrated_and_shared_same_coarse_view :
    coarseAuditObserver.observe concentratedEvent =
      coarseAuditObserver.observe sharedDeonticEvent :=
  rfl

theorem aggregateImpact_factors_through_coarse_audit :
    Factors coarseAuditObserver.observe aggregateImpact := by
  exact ⟨Prod.snd, fun _event => rfl⟩

theorem endpoint_factors_through_coarse_audit :
    Factors coarseAuditObserver.observe
      (fun event : AllocationEvent => event.target) := by
  exact ⟨Prod.fst, fun _event => rfl⟩

/-- The allocation view is sufficient for person-indexed impact. -/
theorem caredImpact_factors_through_allocation_audit :
    Factors allocationAuditObserver.observe careImpact := by
  exact ⟨impact, fun _event => rfl⟩

theorem caredImpact_distinguishes_concentrated_and_shared :
    careImpact concentratedEvent ≠ careImpact sharedDeonticEvent := by
  intro equalImpact
  have atBea := congrFun equalImpact Participant.bea
  norm_num [careImpact, impact] at atBea

theorem caredImpact_does_not_factor_through_coarse_audit :
    ¬ Factors coarseAuditObserver.observe careImpact := by
  let fiber : NonTrivialFiber coarseAuditObserver.observe careImpact :=
    { left := concentratedEvent
      right := sharedDeonticEvent
      sameShadow := concentrated_and_shared_same_coarse_view
      differentValue := caredImpact_distinguishes_concentrated_and_shared }
  exact fiber.not_factors

/-! ## Event-indexed consent claims -/

/-- Consent obligations indexed by the selected allocation. -/
def ConsentByAllocation : Allocation → Type
  | .concentrated => PUnit
  | .shared => Bool

/-- Concentrated burden requires one affected-party claim; shared burden
requires two separately retained claims. -/
def ConsentClaim (event : AllocationEvent) : Type :=
  ConsentByAllocation (allocationOfEvent event)

/-- The singleton concentrated claim belongs to Bea. -/
def concentratedClaimant : PUnit → Participant :=
  fun _ => .bea

/-- The two shared claims belong separately to Bea and Cora. -/
def sharedClaimant : Bool → Participant
  | false => .bea
  | true => .cora

def consentAnswersFor :
    (allocation : Allocation) → List (ConsentByAllocation allocation)
  | .concentrated => [PUnit.unit]
  | .shared => [false, true]

def consentAnswers (event : AllocationEvent) : List (ConsentClaim event) :=
  consentAnswersFor (allocationOfEvent event)

/-- The event-indexed family is exactly the pullback of the allocation-indexed
family through the finer allocation observer. -/
def consentClaims_factor_through_allocation_audit :
    FamilyFactorization allocationAuditObserver.observe ConsentClaim :=
  FamilyFactorization.pullback allocationAuditObserver.observe
    ConsentByAllocation

theorem consentClaims_do_not_factor_through_coarse_audit :
    ¬ Nonempty
      (FamilyFactorization coarseAuditObserver.observe ConsentClaim) := by
  have notEquivalent :
      ¬ Nonempty
        (ConsentClaim concentratedEvent ≃
          ConsentClaim sharedDeonticEvent) := by
    simpa [ConsentClaim, ConsentByAllocation] using
      Canary.unit_not_equiv_bool
  exact FamilyFactorization.not_nonempty_of_nonEquivalent_fibres
    (left := concentratedEvent) (right := sharedDeonticEvent)
    concentrated_and_shared_same_coarse_view
    notEquivalent

/-- Event-indexed sequencing retains the exact allocation event beside every
affected-party claim. -/
def retainedConsentClaims : List (Sigma ConsentClaim) :=
  bindSigma listEffect [concentratedEvent, sharedDeonticEvent] consentAnswers

theorem retainedConsentClaim_events :
    retainedConsentClaims.map Sigma.fst =
      [concentratedEvent, sharedDeonticEvent, sharedDeonticEvent] :=
  rfl

/-- Order erasure commutes with the same event-indexed dependent sequencing. -/
theorem retainedConsentClaims_to_bag_natural :
    listToBag.map retainedConsentClaims =
      bindSigma bagEffect
        (listToBag.map ([concentratedEvent, sharedDeonticEvent] :
          List AllocationEvent))
        (fun event => listToBag.map (consentAnswers event)) := by
  exact morphism_map_bindSigma listToBag
    ([concentratedEvent, sharedDeonticEvent] : List AllocationEvent)
    consentAnswers

/-! ## Justification and cost remain independent coordinates -/

def allocationAndEndpoint (event : AllocationEvent) :
    Allocation × AllocationPhase :=
  (allocationOfEvent event, event.target)

theorem shared_deontic_and_virtue_same_allocation_endpoint :
    allocationAndEndpoint sharedDeonticEvent =
      allocationAndEndpoint sharedVirtueEvent :=
  rfl

theorem shared_deontic_and_virtue_different_modes :
    modeOfEvent sharedDeonticEvent ≠ modeOfEvent sharedVirtueEvent := by
  decide

theorem justification_mode_does_not_factor_through_allocation_endpoint :
    ¬ Factors allocationAndEndpoint modeOfEvent := by
  let fiber : NonTrivialFiber allocationAndEndpoint modeOfEvent :=
    { left := sharedDeonticEvent
      right := sharedVirtueEvent
      sameShadow := shared_deontic_and_virtue_same_allocation_endpoint
      differentValue := shared_deontic_and_virtue_different_modes }
  exact fiber.not_factors

/-- Operational work is independently valued.  Sharing requires more total
work and a longer span in this declared realization. -/
def workSpanForAllocation : Allocation → WorkSpan
  | .concentrated => ⟨1, 1⟩
  | .shared => ⟨2, 2⟩

def eventWorkSpan (event : AllocationEvent) : WorkSpan :=
  workSpanForAllocation (allocationOfEvent event)

theorem eventWorkSpan_does_not_factor_through_coarse_audit :
    ¬ Factors coarseAuditObserver.observe eventWorkSpan := by
  let fiber : NonTrivialFiber coarseAuditObserver.observe eventWorkSpan :=
    { left := concentratedEvent
      right := sharedDeonticEvent
      sameShadow := concentrated_and_shared_same_coarse_view
      differentValue := by decide }
  exact fiber.not_factors

theorem eventWorkSpan_factors_through_allocation_audit :
    Factors allocationAuditObserver.observe eventWorkSpan := by
  exact ⟨workSpanForAllocation, fun _event => rfl⟩

def consentClaimWorkSpan (claim : Sigma ConsentClaim) : WorkSpan :=
  eventWorkSpan claim.1

theorem retainedConsentClaims_parallel_receipt :
    parallelReceipt consentClaimWorkSpan retainedConsentClaims = ⟨5, 2⟩ :=
  rfl

/-! ## Consolidated operational ethics boundary -/

theorem multiAgent_operational_ethics_boundary :
    InCareScope (.participant .bea) ∧
      ¬ CanCommit (.participant .bea) ∧
      CanCommit (.participant .coordinator) ∧
      InCareScope (.participant .coordinator) ∧
      Nonempty (CommitReceipt (.participant .coordinator) concentratedEvent) ∧
      ¬ Nonempty (CommitReceipt (.participant .bea) concentratedEvent) ∧
      sharedDeonticDecision.action = sharedConsequentialDecision.action ∧
      sharedConsequentialDecision.action = sharedVirtueDecision.action ∧
      sharedDeonticDecision.mode ≠ sharedVirtueDecision.mode ∧
      Factors coarseAuditObserver.observe aggregateImpact ∧
      Factors allocationAuditObserver.observe careImpact ∧
      ¬ Factors coarseAuditObserver.observe careImpact ∧
      Nonempty
        (FamilyFactorization allocationAuditObserver.observe ConsentClaim) ∧
      ¬ Nonempty
        (FamilyFactorization coarseAuditObserver.observe ConsentClaim) ∧
      ¬ Factors allocationAndEndpoint modeOfEvent ∧
      Factors allocationAuditObserver.observe eventWorkSpan ∧
      ¬ Factors coarseAuditObserver.observe eventWorkSpan :=
  ⟨bea_is_in_care_scope,
    bea_cannot_commit,
    coordinator_can_commit,
    coordinator_is_in_care_scope,
    ⟨coordinatorCommitReceipt concentratedEvent⟩,
    cared_for_participant_cannot_forge_commit concentratedEvent,
    rfl,
    rfl,
    shared_capabilities_retain_distinct_modes.2.2,
    aggregateImpact_factors_through_coarse_audit,
    caredImpact_factors_through_allocation_audit,
    caredImpact_does_not_factor_through_coarse_audit,
    ⟨consentClaims_factor_through_allocation_audit⟩,
    consentClaims_do_not_factor_through_coarse_audit,
    justification_mode_does_not_factor_through_allocation_endpoint,
    eventWorkSpan_factors_through_allocation_audit,
    eventWorkSpan_does_not_factor_through_coarse_audit⟩

/-! ## Axiom audit -/

#print axioms shared_allocation_has_no_override_receipt
#print axioms shared_is_empirically_optimal
#print axioms concentrated_is_not_empirically_optimal
#print axioms sharedVirtueReceipt
#print axioms all_shared_capabilities_choose_same_allocation
#print axioms shared_capabilities_retain_distinct_modes
#print axioms cared_for_participant_cannot_forge_commit
#print axioms committed_event_is_operationally_authorized
#print axioms aggregateImpact_factors_through_coarse_audit
#print axioms caredImpact_factors_through_allocation_audit
#print axioms caredImpact_does_not_factor_through_coarse_audit
#print axioms consentClaims_factor_through_allocation_audit
#print axioms consentClaims_do_not_factor_through_coarse_audit
#print axioms retainedConsentClaims_to_bag_natural
#print axioms justification_mode_does_not_factor_through_allocation_endpoint
#print axioms eventWorkSpan_factors_through_allocation_audit
#print axioms eventWorkSpan_does_not_factor_through_coarse_audit
#print axioms retainedConsentClaims_parallel_receipt
#print axioms multiAgent_operational_ethics_boundary

end Mettapedia.Ethics.MultiAgentOperationalEthics
