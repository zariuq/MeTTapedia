import Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.ActionMemoryConservedRouteCredit
import Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.AddressableEvidenceMemory

/-!
# Query-addressed conserved route credit

Global root credit and query-addressed route credit answer different questions.
The former records reusable root quality.  The latter records whether a root is
addressable from a particular query.  This module gives query/root edges their
own ledger type, so projecting away the query is an explicit, lossy operation.

Successful redemption moves one fixed packet from reserve to the distinct
query/root edges supported by the receipt.  The registered exact-split policy
admits one through eight edges and rejects every other fan-out without changing
the state.  Direct-query and hindsight receipts are classified and redeemed by
separate operators; neither classification is inferred from route support.
-/

namespace Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery

universe uQ uP uT uC uA uR

abbrev RouteEdge (Query : Type uQ) (Root : Type uR) := Query × Root

abbrev EdgeRouteCreditLedger (Query : Type uQ) (Root : Type uR) :=
  RouteCreditLedger (RouteEdge Query Root)

abbrev EdgeRouteCreditState
    (Query : Type uQ) (Root : Type uR) (ReceiptId : Type uC)
    [DecidableEq ReceiptId] :=
  RouteCreditState (RouteEdge Query Root) ReceiptId

/-! ## Edge support and exact splitting -/

/-- Lift the distinct roots used by one trace to query/root edges. -/
def queryEdgeSupport
    {Query : Type uQ} {Root : Type uR} [DecidableEq Query] [DecidableEq Root]
    (query : Query) (roots : Finset Root) : Finset (RouteEdge Query Root) :=
  roots.image fun root => (query, root)

@[simp] theorem mem_queryEdgeSupport
    {Query : Type uQ} {Root : Type uR} [DecidableEq Query] [DecidableEq Root]
    {query query' : Query} {root : Root} {roots : Finset Root} :
    (query', root) ∈ queryEdgeSupport query roots ↔ query' = query ∧ root ∈ roots := by
  simp [queryEdgeSupport, eq_comm, and_comm]

@[simp] theorem queryEdgeSupport_card
    {Query : Type uQ} {Root : Type uR} [DecidableEq Query] [DecidableEq Root]
    (query : Query) (roots : Finset Root) :
    (queryEdgeSupport query roots).card = roots.card := by
  classical
  exact Finset.card_image_of_injective roots (Prod.mk_right_injective query)

/-- The registered policy returns a share exactly for admitted fan-outs.  All
other fan-outs are rejected; integer remainders are never silently dropped. -/
def exactEdgeCreditShare? (count : ℕ) : Option ℕ :=
  if 1 ≤ count ∧ count ≤ 8 then some (routeCreditShare count) else none

theorem exactEdgeCreditShare?_eq_some
    {count : ℕ} (supported : SupportedRouteCount count) :
    exactEdgeCreditShare? count = some (routeCreditShare count) := by
  rcases supported with ⟨lower, upper⟩
  simp [exactEdgeCreditShare?, lower, upper]

theorem exactEdgeCreditShare?_eq_none
    {count : ℕ} (unsupported : ¬ SupportedRouteCount count) :
    exactEdgeCreditShare? count = none := by
  simp only [exactEdgeCreditShare?, SupportedRouteCount] at unsupported ⊢
  simp [unsupported]

theorem supported_query_edges_split_packet
    {Query : Type uQ} {Root : Type uR} [DecidableEq Query] [DecidableEq Root]
    (query : Query) (roots : Finset Root)
    (supported : SupportedRouteCount roots.card) :
    (queryEdgeSupport query roots).card *
        routeCreditShare (queryEdgeSupport query roots).card = routeCreditPacket := by
  rw [queryEdgeSupport_card]
  exact supportedRouteCount_exact_split supported

theorem one_through_eight_edge_counts_divide_packet
    (count : ℕ) (lower : 1 ≤ count) (upper : count ≤ 8) :
    count ∣ routeCreditPacket :=
  supportedRouteCount_dvd_packet ⟨lower, upper⟩

theorem nine_edge_support_is_rejected :
    exactEdgeCreditShare? 9 = none := by
  apply exactEdgeCreditShare?_eq_none
  simp [SupportedRouteCount]

/-! ## Total fail-closed redemption -/

/-- Interpret a failed authenticated redemption as an exact identity
transition.  A successful redemption returns the state produced by the
existing linear-receipt calculus. -/
def redeemEdgeRouteCredit
    {Query : Type uQ} {Root : Type uR} {ReceiptId : Type uC}
    [DecidableEq Query] [DecidableEq Root] [DecidableEq ReceiptId]
    (checkerAccepted : Bool) (receiptId : ReceiptId)
    (query : Query) (roots : Finset Root)
    (state : EdgeRouteCreditState Query Root ReceiptId) :
    EdgeRouteCreditState Query Root ReceiptId :=
  (redeemAuthenticatedRouteCredit? checkerAccepted receiptId
    (queryEdgeSupport query roots) state).getD state

theorem redeemEdgeRouteCredit_checker_rejection_identity
    {Query : Type uQ} {Root : Type uR} {ReceiptId : Type uC}
    [DecidableEq Query] [DecidableEq Root] [DecidableEq ReceiptId]
    (receiptId : ReceiptId) (query : Query) (roots : Finset Root)
    (state : EdgeRouteCreditState Query Root ReceiptId) :
    redeemEdgeRouteCredit false receiptId query roots state = state := by
  simp [redeemEdgeRouteCredit, redeemAuthenticatedRouteCredit?,
    redeemRouteCredit?]

theorem redeemEdgeRouteCredit_empty_support_identity
    {Query : Type uQ} {Root : Type uR} {ReceiptId : Type uC}
    [DecidableEq Query] [DecidableEq Root] [DecidableEq ReceiptId]
    (checkerAccepted : Bool) (receiptId : ReceiptId) (query : Query)
    (state : EdgeRouteCreditState Query Root ReceiptId) :
    redeemEdgeRouteCredit checkerAccepted receiptId query ∅ state = state := by
  simp [redeemEdgeRouteCredit, redeemAuthenticatedRouteCredit?,
    redeemRouteCredit?, queryEdgeSupport]

theorem redeemEdgeRouteCredit_unsupported_support_identity
    {Query : Type uQ} {Root : Type uR} {ReceiptId : Type uC}
    [DecidableEq Query] [DecidableEq Root] [DecidableEq ReceiptId]
    (receiptId : ReceiptId) (query : Query) (roots : Finset Root)
    (state : EdgeRouteCreditState Query Root ReceiptId)
    (unsupported : 8 < roots.card) :
    redeemEdgeRouteCredit true receiptId query roots state = state := by
  simp [redeemEdgeRouteCredit, redeemAuthenticatedRouteCredit?,
    redeemRouteCredit?, queryEdgeSupport_card, Nat.not_le.mpr unsupported]

theorem redeemEdgeRouteCredit_insufficient_reserve_identity
    {Query : Type uQ} {Root : Type uR} {ReceiptId : Type uC}
    [DecidableEq Query] [DecidableEq Root] [DecidableEq ReceiptId]
    (receiptId : ReceiptId) (query : Query) (roots : Finset Root)
    (state : EdgeRouteCreditState Query Root ReceiptId)
    (insufficient : state.ledger.reserve < routeCreditPacket) :
    redeemEdgeRouteCredit true receiptId query roots state = state := by
  simp [redeemEdgeRouteCredit, redeemAuthenticatedRouteCredit?,
    redeemRouteCredit?, Nat.not_le.mpr insufficient]

theorem redeemEdgeRouteCredit_spent_receipt_identity
    {Query : Type uQ} {Root : Type uR} {ReceiptId : Type uC}
    [DecidableEq Query] [DecidableEq Root] [DecidableEq ReceiptId]
    (checkerAccepted : Bool) (receiptId : ReceiptId)
    (query : Query) (roots : Finset Root)
    (state : EdgeRouteCreditState Query Root ReceiptId)
    (spent : receiptId ∈ state.redeemedReceipts) :
    redeemEdgeRouteCredit checkerAccepted receiptId query roots state = state := by
  simp [redeemEdgeRouteCredit, redeemAuthenticatedRouteCredit?, spent]

/-- Every total edge redemption preserves the conserved numeric budget,
including all identity rejection branches. -/
theorem redeemEdgeRouteCredit_conserves_total
    {Query : Type uQ} {Root : Type uR} {ReceiptId : Type uC}
    [Fintype Query] [Fintype Root]
    [DecidableEq Query] [DecidableEq Root] [DecidableEq ReceiptId]
    (checkerAccepted : Bool) (receiptId : ReceiptId)
    (query : Query) (roots : Finset Root)
    (state : EdgeRouteCreditState Query Root ReceiptId) :
    (redeemEdgeRouteCredit checkerAccepted receiptId query roots state).total =
      state.total := by
  classical
  unfold redeemEdgeRouteCredit
  cases redeemed : redeemAuthenticatedRouteCredit? checkerAccepted receiptId
      (queryEdgeSupport query roots) state with
  | none => simp
  | some next =>
      simp only [Option.getD_some]
      unfold redeemAuthenticatedRouteCredit? at redeemed
      split at redeemed
      next spent => simp at redeemed
      next fresh =>
        cases ledgerResult : redeemRouteCredit? checkerAccepted state.ledger
            (queryEdgeSupport query roots) with
        | none => simp [ledgerResult] at redeemed
        | some ledger =>
            simp [ledgerResult] at redeemed
            subst next
            unfold RouteCreditState.total
            have accepted : checkerAccepted = true := by
              unfold redeemRouteCredit? at ledgerResult
              split at ledgerResult
              next valid => exact valid.1
              next invalid => simp at ledgerResult
            subst checkerAccepted
            exact redeemRouteCredit?_conserves_total state.ledger ledger
              (queryEdgeSupport query roots) ledgerResult

/-! ## Clone safety and query locality -/

def distinctQueryEdges
    {Query : Type uQ} {Root : Type uR} [DecidableEq Query] [DecidableEq Root]
    (query : Query) (roots : List Root) : Finset (RouteEdge Query Root) :=
  queryEdgeSupport query roots.toFinset

theorem duplicate_route_record_is_edge_clone_safe
    {Query : Type uQ} {Root : Type uR} [DecidableEq Query] [DecidableEq Root]
    (query : Query) (root : Root) (rest : List Root) :
    distinctQueryEdges query (root :: root :: rest) =
      distinctQueryEdges query (root :: rest) := by
  simp [distinctQueryEdges]

theorem duplicate_route_record_does_not_multiply_edge_credit
    {Query : Type uQ} {Root : Type uR} [DecidableEq Query] [DecidableEq Root]
    (ledger : EdgeRouteCreditLedger Query Root)
    (query : Query) (root : Root) (rest : List Root) :
    allocateRouteCredit ledger (distinctQueryEdges query (root :: root :: rest)) =
      allocateRouteCredit ledger (distinctQueryEdges query (root :: rest)) := by
  rw [duplicate_route_record_is_edge_clone_safe]

theorem allocateEdgeCredit_other_query_unchanged
    {Query : Type uQ} {Root : Type uR} [DecidableEq Query] [DecidableEq Root]
    (ledger : EdgeRouteCreditLedger Query Root)
    (creditedQuery otherQuery : Query) (roots : Finset Root) (root : Root)
    (different : otherQuery ≠ creditedQuery) :
    (allocateRouteCredit ledger (queryEdgeSupport creditedQuery roots)).credit
        (otherQuery, root) = ledger.credit (otherQuery, root) := by
  apply allocateRouteCredit_ineligible_root
  simp [different]

/-- Positive-credit routing is a readout of edge accounts, not root totals. -/
def creditedRoots
    {Query : Type uQ} {Root : Type uR} [Fintype Root]
    (ledger : EdgeRouteCreditLedger Query Root) (query : Query) : Finset Root := by
  classical
  exact Finset.univ.filter fun root => 0 < ledger.credit (query, root)

theorem allocateEdgeCredit_other_query_routing_unchanged
    {Query : Type uQ} {Root : Type uR} [Fintype Root]
    [DecidableEq Query] [DecidableEq Root]
    (ledger : EdgeRouteCreditLedger Query Root)
    (creditedQuery otherQuery : Query) (roots : Finset Root)
    (different : otherQuery ≠ creditedQuery) :
    creditedRoots
        (allocateRouteCredit ledger (queryEdgeSupport creditedQuery roots)) otherQuery =
      creditedRoots ledger otherQuery := by
  classical
  ext root
  simp only [creditedRoots, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [allocateEdgeCredit_other_query_unchanged ledger creditedQuery otherQuery
    roots root different]

/-! ## Root projection loses addressability -/

/-- Forget the query and aggregate all edge credit associated with one root. -/
def rootCreditProjection
    {Query : Type uQ} {Root : Type uR} [Fintype Query]
    (ledger : EdgeRouteCreditLedger Query Root) (root : Root) : ℕ :=
  ∑ query, ledger.credit (query, root)

def leftAddressLedger : EdgeRouteCreditLedger Bool Unit where
  reserve := 0
  credit := fun edge => if edge.1 = false then 1 else 0

def rightAddressLedger : EdgeRouteCreditLedger Bool Unit where
  reserve := 0
  credit := fun edge => if edge.1 = true then 1 else 0

theorem root_projection_collision_fixture :
    rootCreditProjection leftAddressLedger =
        rootCreditProjection rightAddressLedger ∧
      creditedRoots leftAddressLedger false ≠
        creditedRoots rightAddressLedger false := by
  constructor
  · funext root
    cases root
    simp [rootCreditProjection, leftAddressLedger, rightAddressLedger]
  · intro equalRouting
    have := Finset.ext_iff.mp equalRouting ()
    simp [creditedRoots, leftAddressLedger, rightAddressLedger] at this

/-- No decoder from root totals can recover query-addressed routing on every
edge ledger. -/
theorem root_projection_does_not_recover_query_routing :
    ¬ ∃ recover : (Unit → ℕ) → Bool → Finset Unit,
      ∀ ledger : EdgeRouteCreditLedger Bool Unit,
        recover (rootCreditProjection ledger) = creditedRoots ledger := by
  rintro ⟨recover, recovers⟩
  have sameProjection := root_projection_collision_fixture.1
  have leftRecovered := recovers leftAddressLedger
  have rightRecovered := recovers rightAddressLedger
  have sameRouting : creditedRoots leftAddressLedger = creditedRoots rightAddressLedger := by
    rw [← leftRecovered, ← rightRecovered, sameProjection]
  exact root_projection_collision_fixture.2 (congrFun sameRouting false)

def leftAddressFact : MemoryFact Unit Unit Bool Unit Unit Bool Unit where
  memory := ()
  signature := ()
  query := false
  program := ()
  solvedTarget := ()
  polarity := false
  lineage := ()

def rightAddressFact : MemoryFact Unit Unit Bool Unit Unit Bool Unit where
  memory := ()
  signature := ()
  query := true
  program := ()
  solvedTarget := ()
  polarity := false
  lineage := ()

/-- The ledger collision is an instance of the general aggregate-key
accessibility boundary: equal root-level observations cannot recover the
query/program edge. -/
theorem root_projection_collision_instantiates_accessibility_boundary :
    ¬ ∃ recover : Unit × Bool → Bool × Unit,
      ∀ fact : MemoryFact Unit Unit Bool Unit Unit Bool Unit,
        recover fact.aggregateKey = fact.addressEdge := by
  apply aggregateKey_does_not_recover_accessibility
    (left := leftAddressFact) (right := rightAddressFact)
  · rfl
  · intro equalAddress
    have := congrArg Prod.fst equalAddress
    simp [leftAddressFact, rightAddressFact, MemoryFact.addressEdge] at this

#print axioms supported_query_edges_split_packet
#print axioms redeemEdgeRouteCredit_conserves_total
#print axioms redeemEdgeRouteCredit_spent_receipt_identity
#print axioms duplicate_route_record_does_not_multiply_edge_credit
#print axioms allocateEdgeCredit_other_query_routing_unchanged
#print axioms root_projection_does_not_recover_query_routing
#print axioms root_projection_collision_instantiates_accessibility_boundary

end Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery
