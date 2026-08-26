import Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.ActionMemoryEdgeConservedRouteCredit

/-!
# Authenticated direct route credit and quarantined hindsight evidence

This module is the exact semantic repair for the action-memory credit ledger.
Direct addressability evidence and collateral hindsight evidence inhabit
different account constructors.  A collateral success therefore cannot change
the primary route readout unless an explicitly named, separately certified
transport is introduced later.

Receipt identity and checker artifact are distinct types.  Redemption is
single-use by receipt identity; checker artifacts certify adjudication but are
not used as linear-resource keys.  The runtime binding is deliberately outside
this file.
-/

namespace Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery

noncomputable section

attribute [local instance] Classical.propDecidable

universe uQ uP uT uI uK uA uR uV

/-! ## Exact account and receipt types -/

/-- Direct route evidence and hindsight competence are disjoint accounts. -/
inductive RouteEvidenceAccount
    (Query : Type uQ) (Target : Type uT) (Root : Type uR) where
  | direct (query : Query) (root : Root)
  | hindsight (generatingQuery : Query) (solvedTarget : Target) (root : Root)
deriving DecidableEq, Fintype

/-- A complete authenticated receipt.  No injectivity assumption relates the
opaque `receiptId` to the independently supplied checker artifact. -/
structure AuthenticatedEdgeReceipt
    (Query : Type uQ) (Program : Type uP) (Target : Type uT)
    (ReceiptId : Type uI) (CheckerArtifact : Type uK)
    (Action : Type uA) (Root : Type uR) (Provenance : Type uV) where
  receiptId : ReceiptId
  checkerArtifact : CheckerArtifact
  generatingQuery : Query
  queriedTarget : Target
  solvedTarget : Target
  program : Program
  provenance : Provenance
  selectedActions : List Action
  usedRoots : Finset Root
  checkerAccepted : Bool

/-- Authority predicates are explicit inputs to the theory.  In particular,
source validity is not inferred from a hash-shaped value. -/
structure EdgeCreditAuthority
    (Query : Type uQ) (Program : Type uP) (Target : Type uT)
    (CheckerArtifact : Type uK) (Action : Type uA)
    (Root : Type uR) (Provenance : Type uV) where
  queryTarget : Query → Target
  payloadValid : Program → Provenance → List Action → Prop
  /-- The checker artifact authenticates this exact generated fact.  A unary
  "artifact is accepted" predicate would permit transplanting a real receipt
  to an unrelated query, program, or target. -/
  checkerArtifactAccepted :
    CheckerArtifact → Query → Target → Program → Target → Prop
  sourceReceiptValid : Root → Prop

def AuthenticatedEdgeReceipt.SourceValid
    {Query : Type uQ} {Program : Type uP} {Target : Type uT}
    {ReceiptId : Type uI} {CheckerArtifact : Type uK}
    {Action : Type uA} {Root : Type uR} {Provenance : Type uV}
    (authority : EdgeCreditAuthority Query Program Target CheckerArtifact
      Action Root Provenance)
    (receipt : AuthenticatedEdgeReceipt Query Program Target ReceiptId
      CheckerArtifact Action Root Provenance) : Prop :=
  authority.payloadValid receipt.program receipt.provenance
      receipt.selectedActions ∧
    authority.checkerArtifactAccepted receipt.checkerArtifact
      receipt.generatingQuery receipt.queriedTarget receipt.program
      receipt.solvedTarget ∧
    receipt.queriedTarget = authority.queryTarget receipt.generatingQuery ∧
    ∀ root ∈ receipt.usedRoots, authority.sourceReceiptValid root

/-- The exact state retains the registration boundary and declared conserved
total alongside the linear account state. -/
structure AuthenticatedEdgeCreditState
    (Query : Type uQ) (Target : Type uT) (Root : Type uR)
    (ReceiptId : Type uI) [DecidableEq ReceiptId] where
  creditState : RouteCreditState (RouteEvidenceAccount Query Target Root) ReceiptId
  registeredEdges : Finset (RouteEdge Query Root)
  declaredTotal : ℕ

def AuthenticatedEdgeCreditState.reserve
    {Query : Type uQ} {Target : Type uT} {Root : Type uR}
    {ReceiptId : Type uI} [DecidableEq ReceiptId]
    (state : AuthenticatedEdgeCreditState Query Target Root ReceiptId) : ℕ :=
  state.creditState.ledger.reserve

def AuthenticatedEdgeCreditState.directCredit
    {Query : Type uQ} {Target : Type uT} {Root : Type uR}
    {ReceiptId : Type uI} [DecidableEq ReceiptId]
    (state : AuthenticatedEdgeCreditState Query Target Root ReceiptId)
    (query : Query) (root : Root) : ℕ :=
  state.creditState.ledger.credit (.direct query root)

def AuthenticatedEdgeCreditState.hindsightCredit
    {Query : Type uQ} {Target : Type uT} {Root : Type uR}
    {ReceiptId : Type uI} [DecidableEq ReceiptId]
    (state : AuthenticatedEdgeCreditState Query Target Root ReceiptId)
    (query : Query) (target : Target) (root : Root) : ℕ :=
  state.creditState.ledger.credit (.hindsight query target root)

def AuthenticatedEdgeCreditState.redeemedReceiptIds
    {Query : Type uQ} {Target : Type uT} {Root : Type uR}
    {ReceiptId : Type uI} [DecidableEq ReceiptId]
    (state : AuthenticatedEdgeCreditState Query Target Root ReceiptId) :
    Finset ReceiptId :=
  state.creditState.redeemedReceipts

def AuthenticatedEdgeCreditState.total
    {Query : Type uQ} {Target : Type uT} {Root : Type uR}
    {ReceiptId : Type uI}
    [Fintype Query] [Fintype Target] [Fintype Root]
    [DecidableEq ReceiptId]
    (state : AuthenticatedEdgeCreditState Query Target Root ReceiptId) : ℕ :=
  state.creditState.total

def AuthenticatedEdgeCreditState.ValidTotal
    {Query : Type uQ} {Target : Type uT} {Root : Type uR}
    {ReceiptId : Type uI}
    [Fintype Query] [Fintype Target] [Fintype Root]
    [DecidableEq ReceiptId]
    (state : AuthenticatedEdgeCreditState Query Target Root ReceiptId) : Prop :=
  state.total = state.declaredTotal

/-! ## Supports, authorization, and packet movement -/

def directAccountSupport
    {Query : Type uQ} {Program : Type uP} {Target : Type uT}
    {ReceiptId : Type uI} {CheckerArtifact : Type uK}
    {Action : Type uA} {Root : Type uR} {Provenance : Type uV}
    [DecidableEq Query] [DecidableEq Target] [DecidableEq Root]
    (receipt : AuthenticatedEdgeReceipt Query Program Target ReceiptId
      CheckerArtifact Action Root Provenance) :
    Finset (RouteEvidenceAccount Query Target Root) :=
  receipt.usedRoots.image fun root =>
    .direct receipt.generatingQuery root

def hindsightAccountSupport
    {Query : Type uQ} {Program : Type uP} {Target : Type uT}
    {ReceiptId : Type uI} {CheckerArtifact : Type uK}
    {Action : Type uA} {Root : Type uR} {Provenance : Type uV}
    [DecidableEq Query] [DecidableEq Target] [DecidableEq Root]
    (receipt : AuthenticatedEdgeReceipt Query Program Target ReceiptId
      CheckerArtifact Action Root Provenance) :
    Finset (RouteEvidenceAccount Query Target Root) :=
  receipt.usedRoots.image fun root =>
    .hindsight receipt.generatingQuery receipt.solvedTarget root

@[simp] theorem directAccountSupport_card
    {Query : Type uQ} {Program : Type uP} {Target : Type uT}
    {ReceiptId : Type uI} {CheckerArtifact : Type uK}
    {Action : Type uA} {Root : Type uR} {Provenance : Type uV}
    [DecidableEq Query] [DecidableEq Target] [DecidableEq Root]
    (receipt : AuthenticatedEdgeReceipt Query Program Target ReceiptId
      CheckerArtifact Action Root Provenance) :
    (directAccountSupport receipt).card = receipt.usedRoots.card := by
  exact Finset.card_image_of_injective _ fun _ _ equality => by
    injection equality

@[simp] theorem hindsightAccountSupport_card
    {Query : Type uQ} {Program : Type uP} {Target : Type uT}
    {ReceiptId : Type uI} {CheckerArtifact : Type uK}
    {Action : Type uA} {Root : Type uR} {Provenance : Type uV}
    [DecidableEq Query] [DecidableEq Target] [DecidableEq Root]
    (receipt : AuthenticatedEdgeReceipt Query Program Target ReceiptId
      CheckerArtifact Action Root Provenance) :
    (hindsightAccountSupport receipt).card = receipt.usedRoots.card := by
  exact Finset.card_image_of_injective _ fun _ _ equality => by
    injection equality

theorem authenticatedAccountSupport_exact_split
    {count : ℕ} (supported : SupportedRouteCount count) :
    count * routeCreditShare count = routeCreditPacket := by
  exact supportedRouteCount_exact_split supported

theorem authenticatedAccountSupport_rejected_outside_registered_range
    {count : ℕ} (unsupported : ¬ SupportedRouteCount count) :
    exactEdgeCreditShare? count = none :=
  exactEdgeCreditShare?_eq_none unsupported

structure DirectCreditAuthorization
    {Query : Type uQ} {Program : Type uP} {Target : Type uT}
    {ReceiptId : Type uI} {CheckerArtifact : Type uK}
    {Action : Type uA} {Root : Type uR} {Provenance : Type uV}
    [DecidableEq ReceiptId]
    (authority : EdgeCreditAuthority Query Program Target CheckerArtifact
      Action Root Provenance)
    (receipt : AuthenticatedEdgeReceipt Query Program Target ReceiptId
      CheckerArtifact Action Root Provenance)
    (state : AuthenticatedEdgeCreditState Query Target Root ReceiptId) : Prop where
  checkerAccepted : receipt.checkerAccepted = true
  sourceValid : receipt.SourceValid authority
  directPolarity : receipt.solvedTarget = receipt.queriedTarget
  supportNonempty : receipt.usedRoots.Nonempty
  supportAtMostEight : receipt.usedRoots.card ≤ 8
  registered : ∀ root ∈ receipt.usedRoots,
    (receipt.generatingQuery, root) ∈ state.registeredEdges
  reserveEnough : routeCreditPacket ≤ state.reserve
  fresh : receipt.receiptId ∉ state.redeemedReceiptIds

structure HindsightCreditAuthorization
    {Query : Type uQ} {Program : Type uP} {Target : Type uT}
    {ReceiptId : Type uI} {CheckerArtifact : Type uK}
    {Action : Type uA} {Root : Type uR} {Provenance : Type uV}
    [DecidableEq ReceiptId]
    (authority : EdgeCreditAuthority Query Program Target CheckerArtifact
      Action Root Provenance)
    (receipt : AuthenticatedEdgeReceipt Query Program Target ReceiptId
      CheckerArtifact Action Root Provenance)
    (state : AuthenticatedEdgeCreditState Query Target Root ReceiptId) : Prop where
  checkerAccepted : receipt.checkerAccepted = true
  sourceValid : receipt.SourceValid authority
  hindsightPolarity : receipt.solvedTarget ≠ receipt.queriedTarget
  supportNonempty : receipt.usedRoots.Nonempty
  supportAtMostEight : receipt.usedRoots.card ≤ 8
  registered : ∀ root ∈ receipt.usedRoots,
    (receipt.generatingQuery, root) ∈ state.registeredEdges
  reserveEnough : routeCreditPacket ≤ state.reserve
  fresh : receipt.receiptId ∉ state.redeemedReceiptIds

def spendAccountPacket
    {Query : Type uQ} {Target : Type uT} {Root : Type uR}
    {ReceiptId : Type uI}
    [DecidableEq Query] [DecidableEq Target] [DecidableEq Root]
    [DecidableEq ReceiptId]
    (receiptId : ReceiptId)
    (accounts : Finset (RouteEvidenceAccount Query Target Root))
    (state : AuthenticatedEdgeCreditState Query Target Root ReceiptId) :
    AuthenticatedEdgeCreditState Query Target Root ReceiptId :=
  { state with
    creditState :=
      { ledger := allocateRouteCredit state.creditState.ledger accounts
        redeemedReceipts := insert receiptId state.creditState.redeemedReceipts } }

theorem spendAccountPacket_conserves_total
    {Query : Type uQ} {Target : Type uT} {Root : Type uR}
    {ReceiptId : Type uI}
    [Fintype Query] [Fintype Target] [Fintype Root]
    [DecidableEq Query] [DecidableEq Target] [DecidableEq Root]
    [DecidableEq ReceiptId]
    (receiptId : ReceiptId)
    (accounts : Finset (RouteEvidenceAccount Query Target Root))
    (state : AuthenticatedEdgeCreditState Query Target Root ReceiptId)
    (supported : SupportedRouteCount accounts.card)
    (reserveEnough : routeCreditPacket ≤ state.reserve) :
    (spendAccountPacket receiptId accounts state).total = state.total := by
  exact allocateRouteCredit_conserves_total state.creditState.ledger accounts
    supported reserveEnough

@[simp] theorem spendAccountPacket_marks_receipt
    {Query : Type uQ} {Target : Type uT} {Root : Type uR}
    {ReceiptId : Type uI}
    [DecidableEq Query] [DecidableEq Target] [DecidableEq Root]
    [DecidableEq ReceiptId]
    (receiptId : ReceiptId)
    (accounts : Finset (RouteEvidenceAccount Query Target Root))
    (state : AuthenticatedEdgeCreditState Query Target Root ReceiptId) :
    receiptId ∈ (spendAccountPacket receiptId accounts state).redeemedReceiptIds := by
  simp [spendAccountPacket, AuthenticatedEdgeCreditState.redeemedReceiptIds]

def redeemAuthenticatedDirectCredit
    {Query : Type uQ} {Program : Type uP} {Target : Type uT}
    {ReceiptId : Type uI} {CheckerArtifact : Type uK}
    {Action : Type uA} {Root : Type uR} {Provenance : Type uV}
    [DecidableEq Query] [DecidableEq Target] [DecidableEq Root]
    [DecidableEq ReceiptId]
    (authority : EdgeCreditAuthority Query Program Target CheckerArtifact
      Action Root Provenance)
    (receipt : AuthenticatedEdgeReceipt Query Program Target ReceiptId
      CheckerArtifact Action Root Provenance)
    (state : AuthenticatedEdgeCreditState Query Target Root ReceiptId) :
    AuthenticatedEdgeCreditState Query Target Root ReceiptId :=
  if DirectCreditAuthorization authority receipt state then
    spendAccountPacket receipt.receiptId (directAccountSupport receipt) state
  else state

def redeemAuthenticatedHindsightCredit
    {Query : Type uQ} {Program : Type uP} {Target : Type uT}
    {ReceiptId : Type uI} {CheckerArtifact : Type uK}
    {Action : Type uA} {Root : Type uR} {Provenance : Type uV}
    [DecidableEq Query] [DecidableEq Target] [DecidableEq Root]
    [DecidableEq ReceiptId]
    (authority : EdgeCreditAuthority Query Program Target CheckerArtifact
      Action Root Provenance)
    (receipt : AuthenticatedEdgeReceipt Query Program Target ReceiptId
      CheckerArtifact Action Root Provenance)
    (state : AuthenticatedEdgeCreditState Query Target Root ReceiptId) :
    AuthenticatedEdgeCreditState Query Target Root ReceiptId :=
  if HindsightCreditAuthorization authority receipt state then
    spendAccountPacket receipt.receiptId (hindsightAccountSupport receipt) state
  else state

/-! ## Conservation and exact rejection behavior -/

theorem redeemAuthenticatedDirectCredit_conserves_total
    {Query : Type uQ} {Program : Type uP} {Target : Type uT}
    {ReceiptId : Type uI} {CheckerArtifact : Type uK}
    {Action : Type uA} {Root : Type uR} {Provenance : Type uV}
    [Fintype Query] [Fintype Target] [Fintype Root]
    [DecidableEq Query] [DecidableEq Target] [DecidableEq Root]
    [DecidableEq ReceiptId]
    (authority : EdgeCreditAuthority Query Program Target CheckerArtifact
      Action Root Provenance)
    (receipt : AuthenticatedEdgeReceipt Query Program Target ReceiptId
      CheckerArtifact Action Root Provenance)
    (state : AuthenticatedEdgeCreditState Query Target Root ReceiptId) :
    (redeemAuthenticatedDirectCredit authority receipt state).total = state.total := by
  unfold redeemAuthenticatedDirectCredit
  split
  next authorization =>
    apply spendAccountPacket_conserves_total
    · rw [directAccountSupport_card]
      exact ⟨Finset.one_le_card.mpr authorization.supportNonempty,
        authorization.supportAtMostEight⟩
    · exact authorization.reserveEnough
  next => rfl

theorem redeemAuthenticatedHindsightCredit_conserves_total
    {Query : Type uQ} {Program : Type uP} {Target : Type uT}
    {ReceiptId : Type uI} {CheckerArtifact : Type uK}
    {Action : Type uA} {Root : Type uR} {Provenance : Type uV}
    [Fintype Query] [Fintype Target] [Fintype Root]
    [DecidableEq Query] [DecidableEq Target] [DecidableEq Root]
    [DecidableEq ReceiptId]
    (authority : EdgeCreditAuthority Query Program Target CheckerArtifact
      Action Root Provenance)
    (receipt : AuthenticatedEdgeReceipt Query Program Target ReceiptId
      CheckerArtifact Action Root Provenance)
    (state : AuthenticatedEdgeCreditState Query Target Root ReceiptId) :
    (redeemAuthenticatedHindsightCredit authority receipt state).total = state.total := by
  unfold redeemAuthenticatedHindsightCredit
  split
  next authorization =>
    apply spendAccountPacket_conserves_total
    · rw [hindsightAccountSupport_card]
      exact ⟨Finset.one_le_card.mpr authorization.supportNonempty,
        authorization.supportAtMostEight⟩
    · exact authorization.reserveEnough
  next => rfl

@[simp] theorem redeemAuthenticatedDirectCredit_declaredTotal
    {Query : Type uQ} {Program : Type uP} {Target : Type uT}
    {ReceiptId : Type uI} {CheckerArtifact : Type uK}
    {Action : Type uA} {Root : Type uR} {Provenance : Type uV}
    [DecidableEq Query] [DecidableEq Target] [DecidableEq Root]
    [DecidableEq ReceiptId]
    (authority : EdgeCreditAuthority Query Program Target CheckerArtifact
      Action Root Provenance)
    (receipt : AuthenticatedEdgeReceipt Query Program Target ReceiptId
      CheckerArtifact Action Root Provenance)
    (state : AuthenticatedEdgeCreditState Query Target Root ReceiptId) :
    (redeemAuthenticatedDirectCredit authority receipt state).declaredTotal =
      state.declaredTotal := by
  unfold redeemAuthenticatedDirectCredit
  by_cases authorization : DirectCreditAuthorization authority receipt state
  · rw [if_pos authorization]
    unfold spendAccountPacket
    rfl
  · rw [if_neg authorization]

@[simp] theorem redeemAuthenticatedHindsightCredit_declaredTotal
    {Query : Type uQ} {Program : Type uP} {Target : Type uT}
    {ReceiptId : Type uI} {CheckerArtifact : Type uK}
    {Action : Type uA} {Root : Type uR} {Provenance : Type uV}
    [DecidableEq Query] [DecidableEq Target] [DecidableEq Root]
    [DecidableEq ReceiptId]
    (authority : EdgeCreditAuthority Query Program Target CheckerArtifact
      Action Root Provenance)
    (receipt : AuthenticatedEdgeReceipt Query Program Target ReceiptId
      CheckerArtifact Action Root Provenance)
    (state : AuthenticatedEdgeCreditState Query Target Root ReceiptId) :
    (redeemAuthenticatedHindsightCredit authority receipt state).declaredTotal =
      state.declaredTotal := by
  unfold redeemAuthenticatedHindsightCredit
  by_cases authorization : HindsightCreditAuthorization authority receipt state
  · rw [if_pos authorization]
    unfold spendAccountPacket
    rfl
  · rw [if_neg authorization]

theorem redeemAuthenticatedDirectCredit_preserves_validTotal
    {Query : Type uQ} {Program : Type uP} {Target : Type uT}
    {ReceiptId : Type uI} {CheckerArtifact : Type uK}
    {Action : Type uA} {Root : Type uR} {Provenance : Type uV}
    [Fintype Query] [Fintype Target] [Fintype Root]
    [DecidableEq Query] [DecidableEq Target] [DecidableEq Root]
    [DecidableEq ReceiptId]
    (authority : EdgeCreditAuthority Query Program Target CheckerArtifact
      Action Root Provenance)
    (receipt : AuthenticatedEdgeReceipt Query Program Target ReceiptId
      CheckerArtifact Action Root Provenance)
    (state : AuthenticatedEdgeCreditState Query Target Root ReceiptId)
    (valid : state.ValidTotal) :
    (redeemAuthenticatedDirectCredit authority receipt state).ValidTotal := by
  unfold AuthenticatedEdgeCreditState.ValidTotal at valid ⊢
  calc
    (redeemAuthenticatedDirectCredit authority receipt state).total = state.total :=
      redeemAuthenticatedDirectCredit_conserves_total authority receipt state
    _ = state.declaredTotal := valid
    _ = (redeemAuthenticatedDirectCredit authority receipt state).declaredTotal := by
      symm
      exact redeemAuthenticatedDirectCredit_declaredTotal authority receipt state

theorem redeemAuthenticatedHindsightCredit_preserves_validTotal
    {Query : Type uQ} {Program : Type uP} {Target : Type uT}
    {ReceiptId : Type uI} {CheckerArtifact : Type uK}
    {Action : Type uA} {Root : Type uR} {Provenance : Type uV}
    [Fintype Query] [Fintype Target] [Fintype Root]
    [DecidableEq Query] [DecidableEq Target] [DecidableEq Root]
    [DecidableEq ReceiptId]
    (authority : EdgeCreditAuthority Query Program Target CheckerArtifact
      Action Root Provenance)
    (receipt : AuthenticatedEdgeReceipt Query Program Target ReceiptId
      CheckerArtifact Action Root Provenance)
    (state : AuthenticatedEdgeCreditState Query Target Root ReceiptId)
    (valid : state.ValidTotal) :
    (redeemAuthenticatedHindsightCredit authority receipt state).ValidTotal := by
  unfold AuthenticatedEdgeCreditState.ValidTotal at valid ⊢
  calc
    (redeemAuthenticatedHindsightCredit authority receipt state).total = state.total :=
      redeemAuthenticatedHindsightCredit_conserves_total authority receipt state
    _ = state.declaredTotal := valid
    _ = (redeemAuthenticatedHindsightCredit authority receipt state).declaredTotal := by
      symm
      exact redeemAuthenticatedHindsightCredit_declaredTotal authority receipt state

theorem redeemAuthenticatedDirectCredit_identity_of_not_authorized
    {Query : Type uQ} {Program : Type uP} {Target : Type uT}
    {ReceiptId : Type uI} {CheckerArtifact : Type uK}
    {Action : Type uA} {Root : Type uR} {Provenance : Type uV}
    [DecidableEq Query] [DecidableEq Target] [DecidableEq Root]
    [DecidableEq ReceiptId]
    (authority : EdgeCreditAuthority Query Program Target CheckerArtifact
      Action Root Provenance)
    (receipt : AuthenticatedEdgeReceipt Query Program Target ReceiptId
      CheckerArtifact Action Root Provenance)
    (state : AuthenticatedEdgeCreditState Query Target Root ReceiptId)
    (denied : ¬ DirectCreditAuthorization authority receipt state) :
    redeemAuthenticatedDirectCredit authority receipt state = state := by
  simp [redeemAuthenticatedDirectCredit, denied]

theorem redeemAuthenticatedHindsightCredit_identity_of_not_authorized
    {Query : Type uQ} {Program : Type uP} {Target : Type uT}
    {ReceiptId : Type uI} {CheckerArtifact : Type uK}
    {Action : Type uA} {Root : Type uR} {Provenance : Type uV}
    [DecidableEq Query] [DecidableEq Target] [DecidableEq Root]
    [DecidableEq ReceiptId]
    (authority : EdgeCreditAuthority Query Program Target CheckerArtifact
      Action Root Provenance)
    (receipt : AuthenticatedEdgeReceipt Query Program Target ReceiptId
      CheckerArtifact Action Root Provenance)
    (state : AuthenticatedEdgeCreditState Query Target Root ReceiptId)
    (denied : ¬ HindsightCreditAuthorization authority receipt state) :
    redeemAuthenticatedHindsightCredit authority receipt state = state := by
  simp [redeemAuthenticatedHindsightCredit, denied]

theorem direct_checker_rejection_identity
    {Query Program Target ReceiptId CheckerArtifact Action Root Provenance : Type*}
    [DecidableEq Query] [DecidableEq Target] [DecidableEq Root]
    [DecidableEq ReceiptId]
    (authority : EdgeCreditAuthority Query Program Target CheckerArtifact
      Action Root Provenance)
    (receipt : AuthenticatedEdgeReceipt Query Program Target ReceiptId
      CheckerArtifact Action Root Provenance)
    (state : AuthenticatedEdgeCreditState Query Target Root ReceiptId)
    (rejected : receipt.checkerAccepted = false) :
    redeemAuthenticatedDirectCredit authority receipt state = state := by
  apply redeemAuthenticatedDirectCredit_identity_of_not_authorized
  intro admitted
  have accepted := admitted.checkerAccepted
  simp [rejected] at accepted

theorem hindsight_checker_rejection_identity
    {Query Program Target ReceiptId CheckerArtifact Action Root Provenance : Type*}
    [DecidableEq Query] [DecidableEq Target] [DecidableEq Root]
    [DecidableEq ReceiptId]
    (authority : EdgeCreditAuthority Query Program Target CheckerArtifact
      Action Root Provenance)
    (receipt : AuthenticatedEdgeReceipt Query Program Target ReceiptId
      CheckerArtifact Action Root Provenance)
    (state : AuthenticatedEdgeCreditState Query Target Root ReceiptId)
    (rejected : receipt.checkerAccepted = false) :
    redeemAuthenticatedHindsightCredit authority receipt state = state := by
  apply redeemAuthenticatedHindsightCredit_identity_of_not_authorized
  intro admitted
  have accepted := admitted.checkerAccepted
  simp [rejected] at accepted

theorem direct_malformed_payload_identity
    {Query Program Target ReceiptId CheckerArtifact Action Root Provenance : Type*}
    [DecidableEq Query] [DecidableEq Target] [DecidableEq Root]
    [DecidableEq ReceiptId]
    (authority : EdgeCreditAuthority Query Program Target CheckerArtifact
      Action Root Provenance)
    (receipt : AuthenticatedEdgeReceipt Query Program Target ReceiptId
      CheckerArtifact Action Root Provenance)
    (state : AuthenticatedEdgeCreditState Query Target Root ReceiptId)
    (malformed : ¬ authority.payloadValid receipt.program receipt.provenance
      receipt.selectedActions) :
    redeemAuthenticatedDirectCredit authority receipt state = state := by
  apply redeemAuthenticatedDirectCredit_identity_of_not_authorized
  intro admitted
  exact malformed admitted.sourceValid.1

theorem hindsight_malformed_payload_identity
    {Query Program Target ReceiptId CheckerArtifact Action Root Provenance : Type*}
    [DecidableEq Query] [DecidableEq Target] [DecidableEq Root]
    [DecidableEq ReceiptId]
    (authority : EdgeCreditAuthority Query Program Target CheckerArtifact
      Action Root Provenance)
    (receipt : AuthenticatedEdgeReceipt Query Program Target ReceiptId
      CheckerArtifact Action Root Provenance)
    (state : AuthenticatedEdgeCreditState Query Target Root ReceiptId)
    (malformed : ¬ authority.payloadValid receipt.program receipt.provenance
      receipt.selectedActions) :
    redeemAuthenticatedHindsightCredit authority receipt state = state := by
  apply redeemAuthenticatedHindsightCredit_identity_of_not_authorized
  intro admitted
  exact malformed admitted.sourceValid.1

theorem direct_checkerArtifact_invalid_identity
    {Query Program Target ReceiptId CheckerArtifact Action Root Provenance : Type*}
    [DecidableEq Query] [DecidableEq Target] [DecidableEq Root]
    [DecidableEq ReceiptId]
    (authority : EdgeCreditAuthority Query Program Target CheckerArtifact
      Action Root Provenance)
    (receipt : AuthenticatedEdgeReceipt Query Program Target ReceiptId
      CheckerArtifact Action Root Provenance)
    (state : AuthenticatedEdgeCreditState Query Target Root ReceiptId)
    (invalid : ¬ authority.checkerArtifactAccepted receipt.checkerArtifact
      receipt.generatingQuery receipt.queriedTarget receipt.program
      receipt.solvedTarget) :
    redeemAuthenticatedDirectCredit authority receipt state = state := by
  apply redeemAuthenticatedDirectCredit_identity_of_not_authorized
  intro admitted
  exact invalid admitted.sourceValid.2.1

theorem hindsight_checkerArtifact_invalid_identity
    {Query Program Target ReceiptId CheckerArtifact Action Root Provenance : Type*}
    [DecidableEq Query] [DecidableEq Target] [DecidableEq Root]
    [DecidableEq ReceiptId]
    (authority : EdgeCreditAuthority Query Program Target CheckerArtifact
      Action Root Provenance)
    (receipt : AuthenticatedEdgeReceipt Query Program Target ReceiptId
      CheckerArtifact Action Root Provenance)
    (state : AuthenticatedEdgeCreditState Query Target Root ReceiptId)
    (invalid : ¬ authority.checkerArtifactAccepted receipt.checkerArtifact
      receipt.generatingQuery receipt.queriedTarget receipt.program
      receipt.solvedTarget) :
    redeemAuthenticatedHindsightCredit authority receipt state = state := by
  apply redeemAuthenticatedHindsightCredit_identity_of_not_authorized
  intro admitted
  exact invalid admitted.sourceValid.2.1

theorem direct_sourceReceipt_invalid_identity
    {Query Program Target ReceiptId CheckerArtifact Action Root Provenance : Type*}
    [DecidableEq Query] [DecidableEq Target] [DecidableEq Root]
    [DecidableEq ReceiptId]
    (authority : EdgeCreditAuthority Query Program Target CheckerArtifact
      Action Root Provenance)
    (receipt : AuthenticatedEdgeReceipt Query Program Target ReceiptId
      CheckerArtifact Action Root Provenance)
    (state : AuthenticatedEdgeCreditState Query Target Root ReceiptId)
    (root : Root) (used : root ∈ receipt.usedRoots)
    (invalid : ¬ authority.sourceReceiptValid root) :
    redeemAuthenticatedDirectCredit authority receipt state = state := by
  apply redeemAuthenticatedDirectCredit_identity_of_not_authorized
  intro admitted
  exact invalid (admitted.sourceValid.2.2.2 root used)

theorem hindsight_sourceReceipt_invalid_identity
    {Query Program Target ReceiptId CheckerArtifact Action Root Provenance : Type*}
    [DecidableEq Query] [DecidableEq Target] [DecidableEq Root]
    [DecidableEq ReceiptId]
    (authority : EdgeCreditAuthority Query Program Target CheckerArtifact
      Action Root Provenance)
    (receipt : AuthenticatedEdgeReceipt Query Program Target ReceiptId
      CheckerArtifact Action Root Provenance)
    (state : AuthenticatedEdgeCreditState Query Target Root ReceiptId)
    (root : Root) (used : root ∈ receipt.usedRoots)
    (invalid : ¬ authority.sourceReceiptValid root) :
    redeemAuthenticatedHindsightCredit authority receipt state = state := by
  apply redeemAuthenticatedHindsightCredit_identity_of_not_authorized
  intro admitted
  exact invalid (admitted.sourceValid.2.2.2 root used)

theorem direct_queriedTarget_mismatch_identity
    {Query Program Target ReceiptId CheckerArtifact Action Root Provenance : Type*}
    [DecidableEq Query] [DecidableEq Target] [DecidableEq Root]
    [DecidableEq ReceiptId]
    (authority : EdgeCreditAuthority Query Program Target CheckerArtifact
      Action Root Provenance)
    (receipt : AuthenticatedEdgeReceipt Query Program Target ReceiptId
      CheckerArtifact Action Root Provenance)
    (state : AuthenticatedEdgeCreditState Query Target Root ReceiptId)
    (mismatch : receipt.queriedTarget ≠
      authority.queryTarget receipt.generatingQuery) :
    redeemAuthenticatedDirectCredit authority receipt state = state := by
  apply redeemAuthenticatedDirectCredit_identity_of_not_authorized
  intro admitted
  exact mismatch admitted.sourceValid.2.2.1

theorem hindsight_queriedTarget_mismatch_identity
    {Query Program Target ReceiptId CheckerArtifact Action Root Provenance : Type*}
    [DecidableEq Query] [DecidableEq Target] [DecidableEq Root]
    [DecidableEq ReceiptId]
    (authority : EdgeCreditAuthority Query Program Target CheckerArtifact
      Action Root Provenance)
    (receipt : AuthenticatedEdgeReceipt Query Program Target ReceiptId
      CheckerArtifact Action Root Provenance)
    (state : AuthenticatedEdgeCreditState Query Target Root ReceiptId)
    (mismatch : receipt.queriedTarget ≠
      authority.queryTarget receipt.generatingQuery) :
    redeemAuthenticatedHindsightCredit authority receipt state = state := by
  apply redeemAuthenticatedHindsightCredit_identity_of_not_authorized
  intro admitted
  exact mismatch admitted.sourceValid.2.2.1

theorem direct_wrong_polarity_identity
    {Query Program Target ReceiptId CheckerArtifact Action Root Provenance : Type*}
    [DecidableEq Query] [DecidableEq Target] [DecidableEq Root]
    [DecidableEq ReceiptId]
    (authority : EdgeCreditAuthority Query Program Target CheckerArtifact
      Action Root Provenance)
    (receipt : AuthenticatedEdgeReceipt Query Program Target ReceiptId
      CheckerArtifact Action Root Provenance)
    (state : AuthenticatedEdgeCreditState Query Target Root ReceiptId)
    (collateral : receipt.solvedTarget ≠ receipt.queriedTarget) :
    redeemAuthenticatedDirectCredit authority receipt state = state := by
  apply redeemAuthenticatedDirectCredit_identity_of_not_authorized
  intro admitted
  exact collateral admitted.directPolarity

theorem hindsight_wrong_polarity_identity
    {Query Program Target ReceiptId CheckerArtifact Action Root Provenance : Type*}
    [DecidableEq Query] [DecidableEq Target] [DecidableEq Root]
    [DecidableEq ReceiptId]
    (authority : EdgeCreditAuthority Query Program Target CheckerArtifact
      Action Root Provenance)
    (receipt : AuthenticatedEdgeReceipt Query Program Target ReceiptId
      CheckerArtifact Action Root Provenance)
    (state : AuthenticatedEdgeCreditState Query Target Root ReceiptId)
    (direct : receipt.solvedTarget = receipt.queriedTarget) :
    redeemAuthenticatedHindsightCredit authority receipt state = state := by
  apply redeemAuthenticatedHindsightCredit_identity_of_not_authorized
  intro admitted
  exact admitted.hindsightPolarity direct

theorem direct_empty_support_identity
    {Query Program Target ReceiptId CheckerArtifact Action Root Provenance : Type*}
    [DecidableEq Query] [DecidableEq Target] [DecidableEq Root]
    [DecidableEq ReceiptId]
    (authority : EdgeCreditAuthority Query Program Target CheckerArtifact
      Action Root Provenance)
    (receipt : AuthenticatedEdgeReceipt Query Program Target ReceiptId
      CheckerArtifact Action Root Provenance)
    (state : AuthenticatedEdgeCreditState Query Target Root ReceiptId)
    (empty : receipt.usedRoots = ∅) :
    redeemAuthenticatedDirectCredit authority receipt state = state := by
  apply redeemAuthenticatedDirectCredit_identity_of_not_authorized
  intro admitted
  have nonempty := admitted.supportNonempty
  rw [empty] at nonempty
  exact Finset.not_nonempty_empty nonempty

theorem hindsight_empty_support_identity
    {Query Program Target ReceiptId CheckerArtifact Action Root Provenance : Type*}
    [DecidableEq Query] [DecidableEq Target] [DecidableEq Root]
    [DecidableEq ReceiptId]
    (authority : EdgeCreditAuthority Query Program Target CheckerArtifact
      Action Root Provenance)
    (receipt : AuthenticatedEdgeReceipt Query Program Target ReceiptId
      CheckerArtifact Action Root Provenance)
    (state : AuthenticatedEdgeCreditState Query Target Root ReceiptId)
    (empty : receipt.usedRoots = ∅) :
    redeemAuthenticatedHindsightCredit authority receipt state = state := by
  apply redeemAuthenticatedHindsightCredit_identity_of_not_authorized
  intro admitted
  have nonempty := admitted.supportNonempty
  rw [empty] at nonempty
  exact Finset.not_nonempty_empty nonempty

theorem direct_unsupported_support_identity
    {Query Program Target ReceiptId CheckerArtifact Action Root Provenance : Type*}
    [DecidableEq Query] [DecidableEq Target] [DecidableEq Root]
    [DecidableEq ReceiptId]
    (authority : EdgeCreditAuthority Query Program Target CheckerArtifact
      Action Root Provenance)
    (receipt : AuthenticatedEdgeReceipt Query Program Target ReceiptId
      CheckerArtifact Action Root Provenance)
    (state : AuthenticatedEdgeCreditState Query Target Root ReceiptId)
    (tooMany : 8 < receipt.usedRoots.card) :
    redeemAuthenticatedDirectCredit authority receipt state = state := by
  apply redeemAuthenticatedDirectCredit_identity_of_not_authorized
  intro admitted
  exact (Nat.not_le_of_lt tooMany) admitted.supportAtMostEight

theorem hindsight_unsupported_support_identity
    {Query Program Target ReceiptId CheckerArtifact Action Root Provenance : Type*}
    [DecidableEq Query] [DecidableEq Target] [DecidableEq Root]
    [DecidableEq ReceiptId]
    (authority : EdgeCreditAuthority Query Program Target CheckerArtifact
      Action Root Provenance)
    (receipt : AuthenticatedEdgeReceipt Query Program Target ReceiptId
      CheckerArtifact Action Root Provenance)
    (state : AuthenticatedEdgeCreditState Query Target Root ReceiptId)
    (tooMany : 8 < receipt.usedRoots.card) :
    redeemAuthenticatedHindsightCredit authority receipt state = state := by
  apply redeemAuthenticatedHindsightCredit_identity_of_not_authorized
  intro admitted
  exact (Nat.not_le_of_lt tooMany) admitted.supportAtMostEight

theorem direct_unknown_edge_identity
    {Query Program Target ReceiptId CheckerArtifact Action Root Provenance : Type*}
    [DecidableEq Query] [DecidableEq Target] [DecidableEq Root]
    [DecidableEq ReceiptId]
    (authority : EdgeCreditAuthority Query Program Target CheckerArtifact
      Action Root Provenance)
    (receipt : AuthenticatedEdgeReceipt Query Program Target ReceiptId
      CheckerArtifact Action Root Provenance)
    (state : AuthenticatedEdgeCreditState Query Target Root ReceiptId)
    {root : Root} (used : root ∈ receipt.usedRoots)
    (unknown : (receipt.generatingQuery, root) ∉ state.registeredEdges) :
    redeemAuthenticatedDirectCredit authority receipt state = state := by
  apply redeemAuthenticatedDirectCredit_identity_of_not_authorized
  intro admitted
  exact unknown (admitted.registered root used)

theorem hindsight_unknown_edge_identity
    {Query Program Target ReceiptId CheckerArtifact Action Root Provenance : Type*}
    [DecidableEq Query] [DecidableEq Target] [DecidableEq Root]
    [DecidableEq ReceiptId]
    (authority : EdgeCreditAuthority Query Program Target CheckerArtifact
      Action Root Provenance)
    (receipt : AuthenticatedEdgeReceipt Query Program Target ReceiptId
      CheckerArtifact Action Root Provenance)
    (state : AuthenticatedEdgeCreditState Query Target Root ReceiptId)
    {root : Root} (used : root ∈ receipt.usedRoots)
    (unknown : (receipt.generatingQuery, root) ∉ state.registeredEdges) :
    redeemAuthenticatedHindsightCredit authority receipt state = state := by
  apply redeemAuthenticatedHindsightCredit_identity_of_not_authorized
  intro admitted
  exact unknown (admitted.registered root used)

theorem direct_insufficient_reserve_identity
    {Query Program Target ReceiptId CheckerArtifact Action Root Provenance : Type*}
    [DecidableEq Query] [DecidableEq Target] [DecidableEq Root]
    [DecidableEq ReceiptId]
    (authority : EdgeCreditAuthority Query Program Target CheckerArtifact
      Action Root Provenance)
    (receipt : AuthenticatedEdgeReceipt Query Program Target ReceiptId
      CheckerArtifact Action Root Provenance)
    (state : AuthenticatedEdgeCreditState Query Target Root ReceiptId)
    (insufficient : state.reserve < routeCreditPacket) :
    redeemAuthenticatedDirectCredit authority receipt state = state := by
  apply redeemAuthenticatedDirectCredit_identity_of_not_authorized
  intro admitted
  exact (Nat.not_le_of_lt insufficient) admitted.reserveEnough

theorem hindsight_insufficient_reserve_identity
    {Query Program Target ReceiptId CheckerArtifact Action Root Provenance : Type*}
    [DecidableEq Query] [DecidableEq Target] [DecidableEq Root]
    [DecidableEq ReceiptId]
    (authority : EdgeCreditAuthority Query Program Target CheckerArtifact
      Action Root Provenance)
    (receipt : AuthenticatedEdgeReceipt Query Program Target ReceiptId
      CheckerArtifact Action Root Provenance)
    (state : AuthenticatedEdgeCreditState Query Target Root ReceiptId)
    (insufficient : state.reserve < routeCreditPacket) :
    redeemAuthenticatedHindsightCredit authority receipt state = state := by
  apply redeemAuthenticatedHindsightCredit_identity_of_not_authorized
  intro admitted
  exact (Nat.not_le_of_lt insufficient) admitted.reserveEnough

theorem direct_spent_receipt_identity
    {Query Program Target ReceiptId CheckerArtifact Action Root Provenance : Type*}
    [DecidableEq Query] [DecidableEq Target] [DecidableEq Root]
    [DecidableEq ReceiptId]
    (authority : EdgeCreditAuthority Query Program Target CheckerArtifact
      Action Root Provenance)
    (receipt : AuthenticatedEdgeReceipt Query Program Target ReceiptId
      CheckerArtifact Action Root Provenance)
    (state : AuthenticatedEdgeCreditState Query Target Root ReceiptId)
    (spent : receipt.receiptId ∈ state.redeemedReceiptIds) :
    redeemAuthenticatedDirectCredit authority receipt state = state := by
  apply redeemAuthenticatedDirectCredit_identity_of_not_authorized
  intro admitted
  exact admitted.fresh spent

theorem hindsight_spent_receipt_identity
    {Query Program Target ReceiptId CheckerArtifact Action Root Provenance : Type*}
    [DecidableEq Query] [DecidableEq Target] [DecidableEq Root]
    [DecidableEq ReceiptId]
    (authority : EdgeCreditAuthority Query Program Target CheckerArtifact
      Action Root Provenance)
    (receipt : AuthenticatedEdgeReceipt Query Program Target ReceiptId
      CheckerArtifact Action Root Provenance)
    (state : AuthenticatedEdgeCreditState Query Target Root ReceiptId)
    (spent : receipt.receiptId ∈ state.redeemedReceiptIds) :
    redeemAuthenticatedHindsightCredit authority receipt state = state := by
  apply redeemAuthenticatedHindsightCredit_identity_of_not_authorized
  intro admitted
  exact admitted.fresh spent

/-! ## Single use, clone safety, and arbitrary interleavings -/

theorem direct_redemption_is_single_use
    {Query Program Target ReceiptId CheckerArtifact Action Root Provenance : Type*}
    [DecidableEq Query] [DecidableEq Target] [DecidableEq Root]
    [DecidableEq ReceiptId]
    (authority : EdgeCreditAuthority Query Program Target CheckerArtifact
      Action Root Provenance)
    (receipt : AuthenticatedEdgeReceipt Query Program Target ReceiptId
      CheckerArtifact Action Root Provenance)
    (state : AuthenticatedEdgeCreditState Query Target Root ReceiptId)
    (authorized : DirectCreditAuthorization authority receipt state) :
    redeemAuthenticatedDirectCredit authority receipt
      (redeemAuthenticatedDirectCredit authority receipt state) =
        redeemAuthenticatedDirectCredit authority receipt state := by
  have first : redeemAuthenticatedDirectCredit authority receipt state =
      spendAccountPacket receipt.receiptId (directAccountSupport receipt) state := by
    simp [redeemAuthenticatedDirectCredit, authorized]
  rw [first]
  exact direct_spent_receipt_identity authority receipt _
    (spendAccountPacket_marks_receipt _ _ _)

theorem hindsight_redemption_is_single_use
    {Query Program Target ReceiptId CheckerArtifact Action Root Provenance : Type*}
    [DecidableEq Query] [DecidableEq Target] [DecidableEq Root]
    [DecidableEq ReceiptId]
    (authority : EdgeCreditAuthority Query Program Target CheckerArtifact
      Action Root Provenance)
    (receipt : AuthenticatedEdgeReceipt Query Program Target ReceiptId
      CheckerArtifact Action Root Provenance)
    (state : AuthenticatedEdgeCreditState Query Target Root ReceiptId)
    (authorized : HindsightCreditAuthorization authority receipt state) :
    redeemAuthenticatedHindsightCredit authority receipt
      (redeemAuthenticatedHindsightCredit authority receipt state) =
        redeemAuthenticatedHindsightCredit authority receipt state := by
  have first : redeemAuthenticatedHindsightCredit authority receipt state =
      spendAccountPacket receipt.receiptId (hindsightAccountSupport receipt) state := by
    simp [redeemAuthenticatedHindsightCredit, authorized]
  rw [first]
  exact hindsight_spent_receipt_identity authority receipt _
    (spendAccountPacket_marks_receipt _ _ _)

def directAccountSupportFromList
    {Query : Type uQ} {Target : Type uT} {Root : Type uR}
    [DecidableEq Query] [DecidableEq Target] [DecidableEq Root]
    (query : Query) (roots : List Root) :
    Finset (RouteEvidenceAccount Query Target Root) :=
  roots.toFinset.image fun root => .direct query root

theorem duplicate_root_occurrence_does_not_change_direct_support
    {Query : Type uQ} {Target : Type uT} {Root : Type uR}
    [DecidableEq Query] [DecidableEq Target] [DecidableEq Root]
    (query : Query) (root : Root) (rest : List Root) :
    directAccountSupportFromList (Target := Target) query (root :: root :: rest) =
      directAccountSupportFromList (Target := Target) query (root :: rest) := by
  simp [directAccountSupportFromList]

theorem duplicate_root_occurrence_does_not_multiply_packet
    {Query : Type uQ} {Target : Type uT} {Root : Type uR}
    {ReceiptId : Type uI}
    [DecidableEq Query] [DecidableEq Target] [DecidableEq Root]
    [DecidableEq ReceiptId]
    (receiptId : ReceiptId) (query : Query) (root : Root) (rest : List Root)
    (state : AuthenticatedEdgeCreditState Query Target Root ReceiptId) :
    spendAccountPacket receiptId
        (directAccountSupportFromList (Target := Target) query
          (root :: root :: rest)) state =
      spendAccountPacket receiptId
        (directAccountSupportFromList (Target := Target) query
          (root :: rest)) state := by
  rw [duplicate_root_occurrence_does_not_change_direct_support]

inductive AuthenticatedCreditEvent
    (Query : Type uQ) (Program : Type uP) (Target : Type uT)
    (ReceiptId : Type uI) (CheckerArtifact : Type uK)
    (Action : Type uA) (Root : Type uR) (Provenance : Type uV) where
  | direct (receipt : AuthenticatedEdgeReceipt Query Program Target ReceiptId
      CheckerArtifact Action Root Provenance)
  | hindsight (receipt : AuthenticatedEdgeReceipt Query Program Target ReceiptId
      CheckerArtifact Action Root Provenance)

def redeemAuthenticatedCreditEvent
    {Query Program Target ReceiptId CheckerArtifact Action Root Provenance : Type*}
    [DecidableEq Query] [DecidableEq Target] [DecidableEq Root]
    [DecidableEq ReceiptId]
    (authority : EdgeCreditAuthority Query Program Target CheckerArtifact
      Action Root Provenance)
    (event : AuthenticatedCreditEvent Query Program Target ReceiptId
      CheckerArtifact Action Root Provenance)
    (state : AuthenticatedEdgeCreditState Query Target Root ReceiptId) :
    AuthenticatedEdgeCreditState Query Target Root ReceiptId :=
  match event with
  | .direct receipt => redeemAuthenticatedDirectCredit authority receipt state
  | .hindsight receipt => redeemAuthenticatedHindsightCredit authority receipt state

def redeemAuthenticatedCreditEvents
    {Query Program Target ReceiptId CheckerArtifact Action Root Provenance : Type*}
    [DecidableEq Query] [DecidableEq Target] [DecidableEq Root]
    [DecidableEq ReceiptId]
    (authority : EdgeCreditAuthority Query Program Target CheckerArtifact
      Action Root Provenance) :
    List (AuthenticatedCreditEvent Query Program Target ReceiptId CheckerArtifact
      Action Root Provenance) →
      AuthenticatedEdgeCreditState Query Target Root ReceiptId →
      AuthenticatedEdgeCreditState Query Target Root ReceiptId
  | [], state => state
  | event :: events, state =>
      redeemAuthenticatedCreditEvents authority events
        (redeemAuthenticatedCreditEvent authority event state)

theorem redeemAuthenticatedCreditEvents_conserves_total
    {Query Program Target ReceiptId CheckerArtifact Action Root Provenance : Type*}
    [Fintype Query] [Fintype Target] [Fintype Root]
    [DecidableEq Query] [DecidableEq Target] [DecidableEq Root]
    [DecidableEq ReceiptId]
    (authority : EdgeCreditAuthority Query Program Target CheckerArtifact
      Action Root Provenance)
    (events : List (AuthenticatedCreditEvent Query Program Target ReceiptId
      CheckerArtifact Action Root Provenance))
    (state : AuthenticatedEdgeCreditState Query Target Root ReceiptId) :
    (redeemAuthenticatedCreditEvents authority events state).total = state.total := by
  induction events generalizing state with
  | nil => rfl
  | cons event events inductionHypothesis =>
      cases event with
      | direct receipt =>
          rw [redeemAuthenticatedCreditEvents, inductionHypothesis]
          exact redeemAuthenticatedDirectCredit_conserves_total
            authority receipt state
      | hindsight receipt =>
          rw [redeemAuthenticatedCreditEvents, inductionHypothesis]
          exact redeemAuthenticatedHindsightCredit_conserves_total
            authority receipt state

/-! ## Query locality and the experiment-facing readout -/

theorem spendDirect_other_query_unchanged
    {Query : Type uQ} {Program : Type uP} {Target : Type uT}
    {ReceiptId : Type uI} {CheckerArtifact : Type uK}
    {Action : Type uA} {Root : Type uR} {Provenance : Type uV}
    [DecidableEq Query] [DecidableEq Target] [DecidableEq Root]
    [DecidableEq ReceiptId]
    (receipt : AuthenticatedEdgeReceipt Query Program Target ReceiptId
      CheckerArtifact Action Root Provenance)
    (state : AuthenticatedEdgeCreditState Query Target Root ReceiptId)
    (otherQuery : Query) (root : Root)
    (different : otherQuery ≠ receipt.generatingQuery) :
    (spendAccountPacket receipt.receiptId (directAccountSupport receipt) state).directCredit
        otherQuery root = state.directCredit otherQuery root := by
  apply allocateRouteCredit_ineligible_root
  simp only [directAccountSupport, Finset.mem_image]
  rintro ⟨usedRoot, _used, accountEquality⟩
  injection accountEquality with queryEquality _rootEquality
  exact different queryEquality.symm

theorem spendHindsight_directCredit_unchanged
    {Query : Type uQ} {Program : Type uP} {Target : Type uT}
    {ReceiptId : Type uI} {CheckerArtifact : Type uK}
    {Action : Type uA} {Root : Type uR} {Provenance : Type uV}
    [DecidableEq Query] [DecidableEq Target] [DecidableEq Root]
    [DecidableEq ReceiptId]
    (receipt : AuthenticatedEdgeReceipt Query Program Target ReceiptId
      CheckerArtifact Action Root Provenance)
    (state : AuthenticatedEdgeCreditState Query Target Root ReceiptId)
    (query : Query) (root : Root) :
    (spendAccountPacket receipt.receiptId (hindsightAccountSupport receipt) state).directCredit
        query root = state.directCredit query root := by
  apply allocateRouteCredit_ineligible_root
  simp [hindsightAccountSupport]

theorem redeemDirect_other_query_unchanged
    {Query Program Target ReceiptId CheckerArtifact Action Root Provenance : Type*}
    [DecidableEq Query] [DecidableEq Target] [DecidableEq Root]
    [DecidableEq ReceiptId]
    (authority : EdgeCreditAuthority Query Program Target CheckerArtifact
      Action Root Provenance)
    (receipt : AuthenticatedEdgeReceipt Query Program Target ReceiptId
      CheckerArtifact Action Root Provenance)
    (state : AuthenticatedEdgeCreditState Query Target Root ReceiptId)
    (otherQuery : Query) (root : Root)
    (different : otherQuery ≠ receipt.generatingQuery) :
    (redeemAuthenticatedDirectCredit authority receipt state).directCredit
        otherQuery root = state.directCredit otherQuery root := by
  unfold redeemAuthenticatedDirectCredit
  split
  · exact spendDirect_other_query_unchanged receipt state otherQuery root different
  · rfl

theorem redeemHindsight_directCredit_unchanged
    {Query Program Target ReceiptId CheckerArtifact Action Root Provenance : Type*}
    [DecidableEq Query] [DecidableEq Target] [DecidableEq Root]
    [DecidableEq ReceiptId]
    (authority : EdgeCreditAuthority Query Program Target CheckerArtifact
      Action Root Provenance)
    (receipt : AuthenticatedEdgeReceipt Query Program Target ReceiptId
      CheckerArtifact Action Root Provenance)
    (state : AuthenticatedEdgeCreditState Query Target Root ReceiptId)
    (query : Query) (root : Root) :
    (redeemAuthenticatedHindsightCredit authority receipt state).directCredit
        query root = state.directCredit query root := by
  unfold redeemAuthenticatedHindsightCredit
  split
  · exact spendHindsight_directCredit_unchanged receipt state query root
  · rfl

/-- Primary route weights read direct addressability only. -/
def primaryRouteWeight
    {Query : Type uQ} {Target : Type uT} {Root : Type uR}
    {ReceiptId : Type uI} [DecidableEq ReceiptId]
    (baseWeight : Query → Root → ℝ) (quantum : ℝ)
    (state : AuthenticatedEdgeCreditState Query Target Root ReceiptId)
    (query : Query) (root : Root) : ℝ :=
  baseWeight query root + quantum * state.directCredit query root

theorem primaryRouteWeight_reads_directCredit_only
    {Query : Type uQ} {Target : Type uT} {Root : Type uR}
    {ReceiptId : Type uI} [DecidableEq ReceiptId]
    (baseWeight : Query → Root → ℝ) (quantum : ℝ)
    (state : AuthenticatedEdgeCreditState Query Target Root ReceiptId)
    (query : Query) (root : Root) :
    primaryRouteWeight baseWeight quantum state query root =
      baseWeight query root + quantum * state.directCredit query root := rfl

theorem redeemHindsight_primaryRouteWeight_unchanged
    {Query Program Target ReceiptId CheckerArtifact Action Root Provenance : Type*}
    [DecidableEq Query] [DecidableEq Target] [DecidableEq Root]
    [DecidableEq ReceiptId]
    (authority : EdgeCreditAuthority Query Program Target CheckerArtifact
      Action Root Provenance)
    (receipt : AuthenticatedEdgeReceipt Query Program Target ReceiptId
      CheckerArtifact Action Root Provenance)
    (state : AuthenticatedEdgeCreditState Query Target Root ReceiptId)
    (baseWeight : Query → Root → ℝ) (quantum : ℝ)
    (query : Query) (root : Root) :
    primaryRouteWeight baseWeight quantum
        (redeemAuthenticatedHindsightCredit authority receipt state) query root =
      primaryRouteWeight baseWeight quantum state query root := by
  simp only [primaryRouteWeight]
  rw [redeemHindsight_directCredit_unchanged]

def directLedgerOfAuthenticatedState
    {Query : Type uQ} {Target : Type uT} {Root : Type uR}
    {ReceiptId : Type uI} [DecidableEq ReceiptId]
    (state : AuthenticatedEdgeCreditState Query Target Root ReceiptId) :
    EdgeRouteCreditLedger Query Root where
  reserve := state.reserve
  credit := fun edge => state.directCredit edge.1 edge.2

/-! ## Receipt identity is not checker-artifact identity -/

abbrev ReceiptFixture := AuthenticatedEdgeReceipt Bool Unit Bool Bool Unit Unit Unit Unit

def receiptFixtureAuthority : EdgeCreditAuthority Bool Unit Bool Unit Unit Unit Unit where
  queryTarget := id
  payloadValid := fun program provenance actions =>
    program = () ∧ provenance = () ∧ actions = [()]
  checkerArtifactAccepted := fun artifact _query _queriedTarget _program _solvedTarget =>
    artifact = ()
  sourceReceiptValid := fun root => root = ()

def firstSameArtifactReceipt : ReceiptFixture where
  receiptId := false
  checkerArtifact := ()
  generatingQuery := false
  queriedTarget := false
  solvedTarget := false
  program := ()
  provenance := ()
  selectedActions := [()]
  usedRoots := {()}
  checkerAccepted := true

def secondSameArtifactReceipt : ReceiptFixture where
  receiptId := true
  checkerArtifact := ()
  generatingQuery := false
  queriedTarget := false
  solvedTarget := false
  program := ()
  provenance := ()
  selectedActions := [()]
  usedRoots := {()}
  checkerAccepted := true

def twoReceiptFixtureState : AuthenticatedEdgeCreditState Bool Bool Unit Bool where
  creditState :=
    { ledger := { reserve := 2 * routeCreditPacket, credit := fun _ => 0 }
      redeemedReceipts := ∅ }
  registeredEdges := {(false, ())}
  declaredTotal := 2 * routeCreditPacket

theorem distinct_receiptIds_share_checkerArtifact :
    firstSameArtifactReceipt.receiptId ≠ secondSameArtifactReceipt.receiptId ∧
      firstSameArtifactReceipt.checkerArtifact =
        secondSameArtifactReceipt.checkerArtifact := by
  decide

theorem firstSameArtifactReceipt_authorized :
    DirectCreditAuthorization receiptFixtureAuthority firstSameArtifactReceipt
      twoReceiptFixtureState := by
  constructor <;>
    simp [AuthenticatedEdgeReceipt.SourceValid, receiptFixtureAuthority,
      firstSameArtifactReceipt, twoReceiptFixtureState,
      AuthenticatedEdgeCreditState.reserve,
      AuthenticatedEdgeCreditState.redeemedReceiptIds, routeCreditPacket]

def afterFirstSameArtifactReceipt :
    AuthenticatedEdgeCreditState Bool Bool Unit Bool :=
  spendAccountPacket firstSameArtifactReceipt.receiptId
    (directAccountSupport firstSameArtifactReceipt) twoReceiptFixtureState

theorem redeem_firstSameArtifactReceipt :
    redeemAuthenticatedDirectCredit receiptFixtureAuthority
        firstSameArtifactReceipt twoReceiptFixtureState =
      afterFirstSameArtifactReceipt := by
  simp [redeemAuthenticatedDirectCredit, firstSameArtifactReceipt_authorized,
    afterFirstSameArtifactReceipt]

theorem secondSameArtifactReceipt_authorized :
    DirectCreditAuthorization receiptFixtureAuthority secondSameArtifactReceipt
      afterFirstSameArtifactReceipt := by
  constructor <;>
    simp [AuthenticatedEdgeReceipt.SourceValid, receiptFixtureAuthority,
      secondSameArtifactReceipt, afterFirstSameArtifactReceipt,
      twoReceiptFixtureState, spendAccountPacket, directAccountSupport,
      AuthenticatedEdgeCreditState.reserve,
      AuthenticatedEdgeCreditState.redeemedReceiptIds, allocateRouteCredit,
      routeCreditShare, routeCreditPacket]
  norm_num [firstSameArtifactReceipt, secondSameArtifactReceipt]

def afterSecondSameArtifactReceipt :
    AuthenticatedEdgeCreditState Bool Bool Unit Bool :=
  spendAccountPacket secondSameArtifactReceipt.receiptId
    (directAccountSupport secondSameArtifactReceipt) afterFirstSameArtifactReceipt

theorem redeem_secondSameArtifactReceipt :
    redeemAuthenticatedDirectCredit receiptFixtureAuthority
        secondSameArtifactReceipt afterFirstSameArtifactReceipt =
      afterSecondSameArtifactReceipt := by
  simp [redeemAuthenticatedDirectCredit, secondSameArtifactReceipt_authorized,
    afterSecondSameArtifactReceipt]

theorem distinct_receiptIds_same_artifact_both_redeem :
    let afterFirst := redeemAuthenticatedDirectCredit receiptFixtureAuthority
      firstSameArtifactReceipt twoReceiptFixtureState
    let afterSecond := redeemAuthenticatedDirectCredit receiptFixtureAuthority
      secondSameArtifactReceipt afterFirst
    afterSecond.directCredit false () = 2 * routeCreditPacket ∧
      false ∈ afterSecond.redeemedReceiptIds ∧
      true ∈ afterSecond.redeemedReceiptIds := by
  simp only [redeem_firstSameArtifactReceipt, redeem_secondSameArtifactReceipt]
  norm_num [afterSecondSameArtifactReceipt, afterFirstSameArtifactReceipt,
    firstSameArtifactReceipt, secondSameArtifactReceipt, twoReceiptFixtureState,
    spendAccountPacket, directAccountSupport,
    AuthenticatedEdgeCreditState.directCredit,
    AuthenticatedEdgeCreditState.redeemedReceiptIds,
    AuthenticatedEdgeCreditState.reserve,
    allocateRouteCredit, routeCreditShare, routeCreditPacket]

/-! The checker boundary is fact-indexed, not merely artifact-indexed. -/

def factBoundFixtureAuthority :
    EdgeCreditAuthority Bool Unit Bool Unit Unit Unit Unit where
  queryTarget := id
  payloadValid := fun program provenance actions =>
    program = () ∧ provenance = () ∧ actions = [()]
  checkerArtifactAccepted :=
    fun artifact generatingQuery queriedTarget program solvedTarget =>
      artifact = () ∧ generatingQuery = false ∧ queriedTarget = false ∧
        program = () ∧ solvedTarget = false
  sourceReceiptValid := fun root => root = ()

/-- The artifact is genuine for the first fact, but has been transplanted to
the claim that the same program solved a different target. -/
def transplantedArtifactReceipt : ReceiptFixture where
  receiptId := true
  checkerArtifact := ()
  generatingQuery := false
  queriedTarget := false
  solvedTarget := true
  program := ()
  provenance := ()
  selectedActions := [()]
  usedRoots := {()}
  checkerAccepted := true

theorem fact_bound_artifact_accepts_original_receipt :
    firstSameArtifactReceipt.SourceValid factBoundFixtureAuthority := by
  simp [AuthenticatedEdgeReceipt.SourceValid, firstSameArtifactReceipt,
    factBoundFixtureAuthority]

theorem accepted_artifact_cannot_be_transplanted_to_another_fact :
    ¬ transplantedArtifactReceipt.SourceValid factBoundFixtureAuthority := by
  simp [AuthenticatedEdgeReceipt.SourceValid, transplantedArtifactReceipt,
    factBoundFixtureAuthority]

/-- Deliberately wrong linearization: checker artifacts, rather than compound
receipt identities, are treated as spent keys. -/
def faultyArtifactKeyedDirectRedemption
    (receipt : ReceiptFixture)
    (state : AuthenticatedEdgeCreditState Bool Bool Unit Unit) :
    AuthenticatedEdgeCreditState Bool Bool Unit Unit :=
  if receipt.checkerArtifact ∈ state.redeemedReceiptIds then state
  else spendAccountPacket receipt.checkerArtifact
    (directAccountSupport receipt) state

def artifactKeyedFixtureState : AuthenticatedEdgeCreditState Bool Bool Unit Unit where
  creditState :=
    { ledger := { reserve := 2 * routeCreditPacket, credit := fun _ => 0 }
      redeemedReceipts := ∅ }
  registeredEdges := {(false, ())}
  declaredTotal := 2 * routeCreditPacket

def afterFirstArtifactKeyedRedemption :
    AuthenticatedEdgeCreditState Bool Bool Unit Unit :=
  spendAccountPacket firstSameArtifactReceipt.checkerArtifact
    (directAccountSupport firstSameArtifactReceipt) artifactKeyedFixtureState

theorem faulty_first_artifact_redemption :
    faultyArtifactKeyedDirectRedemption firstSameArtifactReceipt
        artifactKeyedFixtureState = afterFirstArtifactKeyedRedemption := by
  unfold faultyArtifactKeyedDirectRedemption
  rw [if_neg]
  · rfl
  · simp [artifactKeyedFixtureState,
      AuthenticatedEdgeCreditState.redeemedReceiptIds]

theorem artifact_marked_after_first :
    secondSameArtifactReceipt.checkerArtifact ∈
      afterFirstArtifactKeyedRedemption.redeemedReceiptIds := by
  simp [afterFirstArtifactKeyedRedemption, secondSameArtifactReceipt,
    firstSameArtifactReceipt, spendAccountPacket,
    AuthenticatedEdgeCreditState.redeemedReceiptIds]

theorem artifact_as_spent_key_wrongly_suppresses_second_receipt :
    let afterFirst := faultyArtifactKeyedDirectRedemption
      firstSameArtifactReceipt artifactKeyedFixtureState
    faultyArtifactKeyedDirectRedemption secondSameArtifactReceipt afterFirst =
      afterFirst := by
  rw [faulty_first_artifact_redemption]
  exact if_pos artifact_marked_after_first

/-! ## Quarantine and an explicit unsound merge -/

/-- This operator is intentionally named unsound.  It moves a selected
hindsight account into the generating query's direct account without a
destination-query support certificate. -/
def unsoundMergeHindsightIntoDirect
    {Query : Type uQ} {Target : Type uT} {Root : Type uR}
    {ReceiptId : Type uI}
    [DecidableEq Query] [DecidableEq Target] [DecidableEq Root]
    [DecidableEq ReceiptId]
    (query : Query) (target : Target)
    (state : AuthenticatedEdgeCreditState Query Target Root ReceiptId) :
    AuthenticatedEdgeCreditState Query Target Root ReceiptId :=
  { state with creditState :=
      { state.creditState with ledger :=
          { reserve := state.reserve
            credit := fun account =>
              match account with
              | .direct observedQuery root =>
                  state.directCredit observedQuery root +
                    if observedQuery = query then
                      state.hindsightCredit query target root
                    else 0
              | .hindsight observedQuery observedTarget root =>
                  if observedQuery = query ∧ observedTarget = target then 0
                  else state.hindsightCredit observedQuery observedTarget root } } }

def collateralReceipt : ReceiptFixture where
  receiptId := false
  checkerArtifact := ()
  generatingQuery := true
  queriedTarget := true
  solvedTarget := false
  program := ()
  provenance := ()
  selectedActions := [()]
  usedRoots := {()}
  checkerAccepted := true

def collateralFixtureState : AuthenticatedEdgeCreditState Bool Bool Unit Bool where
  creditState :=
    { ledger := { reserve := routeCreditPacket, credit := fun _ => 0 }
      redeemedReceipts := ∅ }
  registeredEdges := {(true, ())}
  declaredTotal := routeCreditPacket

theorem collateralReceipt_authorized :
    HindsightCreditAuthorization receiptFixtureAuthority collateralReceipt
      collateralFixtureState := by
  constructor <;>
    simp [AuthenticatedEdgeReceipt.SourceValid, receiptFixtureAuthority,
      collateralReceipt, collateralFixtureState,
      AuthenticatedEdgeCreditState.reserve,
      AuthenticatedEdgeCreditState.redeemedReceiptIds, routeCreditPacket]

def quarantinedCollateralState :
    AuthenticatedEdgeCreditState Bool Bool Unit Bool :=
  spendAccountPacket collateralReceipt.receiptId
    (hindsightAccountSupport collateralReceipt) collateralFixtureState

theorem redeem_collateralReceipt :
    redeemAuthenticatedHindsightCredit receiptFixtureAuthority collateralReceipt
        collateralFixtureState = quarantinedCollateralState := by
  simp [redeemAuthenticatedHindsightCredit, collateralReceipt_authorized,
    quarantinedCollateralState]

theorem collateral_quarantine_and_unsound_merge_change_routing_fixture :
    let quarantined := redeemAuthenticatedHindsightCredit receiptFixtureAuthority
      collateralReceipt collateralFixtureState
    let merged := unsoundMergeHindsightIntoDirect true false quarantined
    collateralReceipt.solvedTarget ≠ collateralReceipt.queriedTarget ∧
      quarantined.directCredit true () = 0 ∧
      quarantined.hindsightCredit true false () = routeCreditPacket ∧
      primaryRouteWeight (fun _ _ => 1) 1 quarantined true () = 1 ∧
      merged.directCredit true () = routeCreditPacket ∧
      primaryRouteWeight (fun _ _ => 1) 1 merged true () =
        1 + routeCreditPacket := by
  rw [redeem_collateralReceipt]
  norm_num [quarantinedCollateralState, collateralReceipt,
    collateralFixtureState, spendAccountPacket,
    hindsightAccountSupport, allocateRouteCredit, routeCreditShare,
    routeCreditPacket, AuthenticatedEdgeCreditState.directCredit,
    AuthenticatedEdgeCreditState.hindsightCredit,
    AuthenticatedEdgeCreditState.reserve, primaryRouteWeight,
    unsoundMergeHindsightIntoDirect]
  intro equality
  cases equality

/-! ## Root projection still loses query routing -/

def exactLeftAddressState : AuthenticatedEdgeCreditState Bool Unit Unit Bool where
  creditState :=
    { ledger :=
        { reserve := 0
          credit := fun account =>
            match account with
            | .direct query _ => if query = false then 1 else 0
            | .hindsight _ _ _ => 0 }
      redeemedReceipts := ∅ }
  registeredEdges := {(false, ()), (true, ())}
  declaredTotal := 1

def exactRightAddressState : AuthenticatedEdgeCreditState Bool Unit Unit Bool where
  creditState :=
    { ledger :=
        { reserve := 0
          credit := fun account =>
            match account with
            | .direct query _ => if query = true then 1 else 0
            | .hindsight _ _ _ => 0 }
      redeemedReceipts := ∅ }
  registeredEdges := {(false, ()), (true, ())}
  declaredTotal := 1

theorem exact_state_root_projection_collision :
    rootCreditProjection (directLedgerOfAuthenticatedState exactLeftAddressState) =
        rootCreditProjection (directLedgerOfAuthenticatedState exactRightAddressState) ∧
      creditedRoots (directLedgerOfAuthenticatedState exactLeftAddressState) false ≠
        creditedRoots (directLedgerOfAuthenticatedState exactRightAddressState) false := by
  constructor
  · funext root
    cases root
    simp [rootCreditProjection, directLedgerOfAuthenticatedState,
      exactLeftAddressState, exactRightAddressState,
      AuthenticatedEdgeCreditState.directCredit]
  · intro equalRouting
    have coordinate := Finset.ext_iff.mp equalRouting ()
    simp [creditedRoots, directLedgerOfAuthenticatedState,
      exactLeftAddressState, exactRightAddressState,
      AuthenticatedEdgeCreditState.directCredit] at coordinate

#print axioms redeemAuthenticatedDirectCredit_conserves_total
#print axioms redeemAuthenticatedHindsightCredit_conserves_total
#print axioms redeemAuthenticatedCreditEvents_conserves_total
#print axioms direct_redemption_is_single_use
#print axioms hindsight_redemption_is_single_use
#print axioms duplicate_root_occurrence_does_not_multiply_packet
#print axioms redeemHindsight_directCredit_unchanged
#print axioms distinct_receiptIds_same_artifact_both_redeem
#print axioms accepted_artifact_cannot_be_transplanted_to_another_fact
#print axioms artifact_as_spent_key_wrongly_suppresses_second_receipt
#print axioms collateral_quarantine_and_unsound_merge_change_routing_fixture
#print axioms exact_state_root_projection_collision

end

end Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery
