import Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.ActionMemoryRuntimeConformance
import Mettapedia.MachineLearning.NeuralNetworks.LocalLearning.WeightedGSLTCausalCredit

/-!
# Conserved route credit for verified action memory

This module fixes the evidence boundary between action-memory search and a
conserved-credit learner.  A route-use receipt records the query, candidate,
solved target, independent checker receipt, selected action stream, and the
set of causal roots that actually supplied retrieved evidence.  Root support
is evidence of eligibility for credit; it is deliberately not identified with
counterfactual necessity.

Successful checker adjudication may move one fixed packet from reserve to the
distinct roots named by a receipt.  The packet size is 840 quanta, the least
common multiple of one through eight, so every admitted support size has an
exact equal integer split.  Root support is a `Finset`, making exact clones
idempotent before credit is assigned.  The aggregate ledger is also related
back to the existing named-slot conserved-credit semantics rather than being
treated as an independent source of conservation.
-/

namespace Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery

open Mettapedia.MachineLearning.NeuralNetworks.LocalLearning
open WeightedGSLTConservedCredit

universe uQ uP uT uC uA uR

/-! ## Source-bound route-use receipts -/

/-- Complete provenance needed to authorize route credit after checking. -/
structure RouteUseReceipt
    (Query : Type uQ) (Program : Type uP) (Target : Type uT)
    (CheckerReceipt : Type uC) (Action : Type uA) (Root : Type uR) where
  query : Query
  program : Program
  solvedTarget : Target
  checkerReceipt : CheckerReceipt
  selectedActions : List Action
  usedRoots : Finset Root

/-- The checker-facing projection intentionally forgets route support. -/
structure CheckedOutcome
    (Query : Type uQ) (Program : Type uP) (Target : Type uT)
    (CheckerReceipt : Type uC) where
  query : Query
  program : Program
  solvedTarget : Target
  checkerReceipt : CheckerReceipt
  deriving DecidableEq, Repr

def RouteUseReceipt.checkedOutcome
    {Query : Type uQ} {Program : Type uP} {Target : Type uT}
    {CheckerReceipt : Type uC} {Action : Type uA} {Root : Type uR}
    [DecidableEq Root]
    (receipt : RouteUseReceipt Query Program Target CheckerReceipt Action Root) :
    CheckedOutcome Query Program Target CheckerReceipt :=
  { query := receipt.query
    program := receipt.program
    solvedTarget := receipt.solvedTarget
    checkerReceipt := receipt.checkerReceipt }

/-- A root is credit-eligible exactly when authenticated route telemetry says
that it supplied evidence on the selected construction path. -/
def RouteUseReceipt.Eligible
    {Query : Type uQ} {Program : Type uP} {Target : Type uT}
    {CheckerReceipt : Type uC} {Action : Type uA} {Root : Type uR}
    [DecidableEq Root]
    (receipt : RouteUseReceipt Query Program Target CheckerReceipt Action Root)
    (root : Root) : Prop :=
  root ∈ receipt.usedRoots

/-- Counterfactual necessity is strictly more demanding than observed route
support: removing the root must make the success counterfactual fail. -/
def RouteUseReceipt.CounterfactuallyNecessary
    {Query : Type uQ} {Program : Type uP} {Target : Type uT}
    {CheckerReceipt : Type uC} {Action : Type uA} {Root : Type uR}
    [DecidableEq Root]
    (receipt : RouteUseReceipt Query Program Target CheckerReceipt Action Root)
    (succeedsWithout : Root → Prop) (root : Root) : Prop :=
  receipt.Eligible root ∧ ¬ succeedsWithout root

def supportWithoutNecessityReceipt :
    RouteUseReceipt Unit Unit Unit Unit Unit Bool where
  query := ()
  program := ()
  solvedTarget := ()
  checkerReceipt := ()
  selectedActions := [()]
  usedRoots := {false}

/-- Eligibility is not a counterfactual causal claim.  The supported root in
this fixture is redundant because the outcome still succeeds without it. -/
theorem eligible_does_not_imply_counterfactual_necessity :
    supportWithoutNecessityReceipt.Eligible false ∧
      ¬ supportWithoutNecessityReceipt.CounterfactuallyNecessary
        (fun _ ↦ (0 : ℕ) = 0) false := by
  simp [RouteUseReceipt.Eligible, RouteUseReceipt.CounterfactuallyNecessary,
    supportWithoutNecessityReceipt]

def leftRouteReceipt :
    RouteUseReceipt Unit Unit Unit Unit Bool Bool where
  query := ()
  program := ()
  solvedTarget := ()
  checkerReceipt := ()
  selectedActions := [false, true]
  usedRoots := {false}

def rightRouteReceipt :
    RouteUseReceipt Unit Unit Unit Unit Bool Bool where
  query := ()
  program := ()
  solvedTarget := ()
  checkerReceipt := ()
  selectedActions := [false, true]
  usedRoots := {true}

/-- Checker output alone cannot reconstruct which source roots influenced the
selected path: two distinct route histories have the same checked outcome. -/
theorem checkedOutcome_projection_is_not_injective :
    leftRouteReceipt.checkedOutcome = rightRouteReceipt.checkedOutcome ∧
      leftRouteReceipt ≠ rightRouteReceipt := by
  constructor
  · rfl
  · intro equalReceipts
    have equalSupports := congrArg RouteUseReceipt.usedRoots equalReceipts
    simp [leftRouteReceipt, rightRouteReceipt] at equalSupports

/-- Every credited root must retain an independently authenticated source
receipt from the catalog that supplied its action trace. -/
def RouteUseReceipt.SourceBound
    {Query : Type uQ} {Program : Type uP} {Target : Type uT}
    {CheckerReceipt : Type uC} {Action : Type uA} {Root : Type uR}
    [DecidableEq Root]
    (receipt : RouteUseReceipt Query Program Target CheckerReceipt Action Root)
    (validSourceReceipt : Root → Prop) : Prop :=
  ∀ root ∈ receipt.usedRoots, validSourceReceipt root

theorem sourceBound_valid_of_eligible
    {Query : Type uQ} {Program : Type uP} {Target : Type uT}
    {CheckerReceipt : Type uC} {Action : Type uA} {Root : Type uR}
    [DecidableEq Root]
    {receipt : RouteUseReceipt Query Program Target CheckerReceipt Action Root}
    {validSourceReceipt : Root → Prop} {root : Root}
    (bound : receipt.SourceBound validSourceReceipt)
    (eligible : receipt.Eligible root) :
    validSourceReceipt root :=
  bound root eligible

theorem invalid_source_receipt_rejects_source_binding
    {Query : Type uQ} {Program : Type uP} {Target : Type uT}
    {CheckerReceipt : Type uC} {Action : Type uA} {Root : Type uR}
    [DecidableEq Root]
    {receipt : RouteUseReceipt Query Program Target CheckerReceipt Action Root}
    {validSourceReceipt : Root → Prop} {root : Root}
    (eligible : receipt.Eligible root)
    (invalid : ¬ validSourceReceipt root) :
    ¬ receipt.SourceBound validSourceReceipt := by
  intro bound
  exact invalid (bound root eligible)

/-! ## Exact clone-safe packet accounting -/

/-- One successful receipt moves this many indivisible credit quanta. -/
def routeCreditPacket : ℕ := 840

/-- The registered route fan-out admits one through eight distinct roots. -/
def SupportedRouteCount (count : ℕ) : Prop :=
  1 ≤ count ∧ count ≤ 8

def routeCreditShare (count : ℕ) : ℕ :=
  routeCreditPacket / count

theorem supportedRouteCount_dvd_packet
    {count : ℕ} (supported : SupportedRouteCount count) :
    count ∣ routeCreditPacket := by
  rcases supported with ⟨lower, upper⟩
  interval_cases count <;> norm_num [routeCreditPacket]

theorem supportedRouteCount_exact_split
    {count : ℕ} (supported : SupportedRouteCount count) :
    count * routeCreditShare count = routeCreditPacket := by
  exact Nat.mul_div_cancel' (supportedRouteCount_dvd_packet supported)

/-- An aggregate runtime view of the named conserved-credit slots. -/
structure RouteCreditLedger (Root : Type uR) where
  reserve : ℕ
  credit : Root → ℕ

def RouteCreditLedger.total
    {Root : Type uR} [Fintype Root]
    (ledger : RouteCreditLedger Root) : ℕ :=
  ledger.reserve + ∑ root, ledger.credit root

/-- Move a packet out of reserve and divide it over distinct route roots. -/
def allocateRouteCredit
    {Root : Type uR} [DecidableEq Root]
    (ledger : RouteCreditLedger Root) (roots : Finset Root) :
    RouteCreditLedger Root where
  reserve := ledger.reserve - routeCreditPacket
  credit := fun root ↦ ledger.credit root +
    if root ∈ roots then routeCreditShare roots.card else 0

/-- Fail-closed route-credit transition.  A checker rejection, empty support,
unsupported fan-out, or insufficient reserve performs no transition. -/
def redeemRouteCredit?
    {Root : Type uR} [DecidableEq Root]
    (checkerAccepted : Bool) (ledger : RouteCreditLedger Root)
    (roots : Finset Root) : Option (RouteCreditLedger Root) :=
  if checkerAccepted = true ∧ roots.Nonempty ∧ roots.card ≤ 8 ∧
      routeCreditPacket ≤ ledger.reserve then
    some (allocateRouteCredit ledger roots)
  else
    none

theorem rejected_route_credit_fails
    {Root : Type uR} [DecidableEq Root]
    (ledger : RouteCreditLedger Root) (roots : Finset Root) :
    redeemRouteCredit? false ledger roots = none := by
  simp [redeemRouteCredit?]

theorem empty_route_support_fails
    {Root : Type uR} [DecidableEq Root]
    (ledger : RouteCreditLedger Root) (checkerAccepted : Bool) :
    redeemRouteCredit? checkerAccepted ledger ∅ = none := by
  simp [redeemRouteCredit?]

theorem insufficient_reserve_fails
    {Root : Type uR} [DecidableEq Root]
    (ledger : RouteCreditLedger Root) (roots : Finset Root)
    (insufficient : ledger.reserve < routeCreditPacket) :
    redeemRouteCredit? true ledger roots = none := by
  simp [redeemRouteCredit?, Nat.not_le.mpr insufficient]

theorem routeIncrement_sum
    {Root : Type uR} [Fintype Root] [DecidableEq Root]
    (roots : Finset Root) :
    (∑ root, if root ∈ roots then routeCreditShare roots.card else 0) =
      roots.card * routeCreditShare roots.card := by
  classical
  simp

/-- A successful packet allocation preserves the exact aggregate budget. -/
theorem allocateRouteCredit_conserves_total
    {Root : Type uR} [Fintype Root] [DecidableEq Root]
    (ledger : RouteCreditLedger Root) (roots : Finset Root)
    (supported : SupportedRouteCount roots.card)
    (reserveEnough : routeCreditPacket ≤ ledger.reserve) :
    (allocateRouteCredit ledger roots).total = ledger.total := by
  classical
  change
    (ledger.reserve - routeCreditPacket) +
        ∑ root, (ledger.credit root +
          if root ∈ roots then routeCreditShare roots.card else 0) =
      ledger.reserve + ∑ root, ledger.credit root
  rw [Finset.sum_add_distrib, routeIncrement_sum,
    supportedRouteCount_exact_split supported]
  omega

theorem redeemRouteCredit?_conserves_total
    {Root : Type uR} [Fintype Root] [DecidableEq Root]
    (ledger next : RouteCreditLedger Root) (roots : Finset Root)
    (success : redeemRouteCredit? true ledger roots = some next) :
    next.total = ledger.total := by
  classical
  unfold redeemRouteCredit? at success
  split at success
  next valid =>
    rcases valid with ⟨_, nonempty, upper, reserveEnough⟩
    have lower : 1 ≤ roots.card := Finset.one_le_card.mpr nonempty
    injection success with stateEq
    subst next
    exact allocateRouteCredit_conserves_total ledger roots
      ⟨lower, upper⟩ reserveEnough
  next invalid => simp at success

theorem allocateRouteCredit_eligible_root
    {Root : Type uR} [DecidableEq Root]
    (ledger : RouteCreditLedger Root) (roots : Finset Root) {root : Root}
    (eligible : root ∈ roots) :
    (allocateRouteCredit ledger roots).credit root =
      ledger.credit root + routeCreditShare roots.card := by
  simp [allocateRouteCredit, eligible]

theorem allocateRouteCredit_ineligible_root
    {Root : Type uR} [DecidableEq Root]
    (ledger : RouteCreditLedger Root) (roots : Finset Root) {root : Root}
    (ineligible : root ∉ roots) :
    (allocateRouteCredit ledger roots).credit root = ledger.credit root := by
  simp [allocateRouteCredit, ineligible]

def distinctRouteRoots {Root : Type uR} [DecidableEq Root]
    (roots : List Root) : Finset Root :=
  roots.toFinset

/-- Duplicating a route-use record cannot increase the supported-root set. -/
theorem duplicate_route_root_is_clone_safe
    {Root : Type uR} [DecidableEq Root]
    (root : Root) (rest : List Root) :
    distinctRouteRoots (root :: root :: rest) =
      distinctRouteRoots (root :: rest) := by
  simp [distinctRouteRoots]

/-- Consequently, an exact duplicate produces the same ledger transition. -/
theorem duplicate_route_root_does_not_multiply_credit
    {Root : Type uR} [DecidableEq Root]
    (ledger : RouteCreditLedger Root) (root : Root) (rest : List Root) :
    allocateRouteCredit ledger (distinctRouteRoots (root :: root :: rest)) =
      allocateRouteCredit ledger (distinctRouteRoots (root :: rest)) := by
  rw [duplicate_route_root_is_clone_safe]

/-! ## Linear redemption of checker receipts -/

/-- Route accounting plus the identities of checker receipts already spent.
The receipt bank does not contribute to the conserved numeric total. -/
structure RouteCreditState (Root : Type uR) (ReceiptId : Type uC)
    [DecidableEq ReceiptId] where
  ledger : RouteCreditLedger Root
  redeemedReceipts : Finset ReceiptId

def RouteCreditState.total
    {Root : Type uR} {ReceiptId : Type uC}
    [Fintype Root] [DecidableEq ReceiptId]
    (state : RouteCreditState Root ReceiptId) : ℕ :=
  state.ledger.total

/-- A checker receipt is linear: successful redemption both transfers its
packet and records the receipt identity as spent. -/
def redeemAuthenticatedRouteCredit?
    {Root : Type uR} {ReceiptId : Type uC}
    [DecidableEq Root] [DecidableEq ReceiptId]
    (checkerAccepted : Bool) (receiptId : ReceiptId)
    (roots : Finset Root) (state : RouteCreditState Root ReceiptId) :
    Option (RouteCreditState Root ReceiptId) :=
  if receiptId ∈ state.redeemedReceipts then
    none
  else
    (redeemRouteCredit? checkerAccepted state.ledger roots).map fun ledger ↦
      { ledger := ledger
        redeemedReceipts := insert receiptId state.redeemedReceipts }

theorem spent_route_receipt_cannot_redeem_again
    {Root : Type uR} {ReceiptId : Type uC}
    [DecidableEq Root] [DecidableEq ReceiptId]
    (checkerAccepted : Bool) (receiptId : ReceiptId)
    (roots : Finset Root) (state : RouteCreditState Root ReceiptId)
    (spent : receiptId ∈ state.redeemedReceipts) :
    redeemAuthenticatedRouteCredit? checkerAccepted receiptId roots state = none := by
  simp [redeemAuthenticatedRouteCredit?, spent]

theorem successful_route_receipt_is_marked_spent
    {Root : Type uR} {ReceiptId : Type uC}
    [DecidableEq Root] [DecidableEq ReceiptId]
    {receiptId : ReceiptId} {roots : Finset Root}
    {state next : RouteCreditState Root ReceiptId}
    (success : redeemAuthenticatedRouteCredit? true receiptId roots state =
      some next) :
    receiptId ∈ next.redeemedReceipts := by
  unfold redeemAuthenticatedRouteCredit? at success
  split at success
  next spent => simp at success
  next fresh =>
    cases redeemed : redeemRouteCredit? true state.ledger roots with
    | none => simp [redeemed] at success
    | some ledger =>
        simp [redeemed] at success
        subst next
        simp

theorem successful_authenticated_redemption_conserves_total
    {Root : Type uR} {ReceiptId : Type uC}
    [Fintype Root] [DecidableEq Root] [DecidableEq ReceiptId]
    {receiptId : ReceiptId} {roots : Finset Root}
    {state next : RouteCreditState Root ReceiptId}
    (success : redeemAuthenticatedRouteCredit? true receiptId roots state =
      some next) :
    next.total = state.total := by
  classical
  unfold redeemAuthenticatedRouteCredit? at success
  split at success
  next spent => simp at success
  next fresh =>
    cases redeemed : redeemRouteCredit? true state.ledger roots with
    | none => simp [redeemed] at success
    | some ledger =>
        simp [redeemed] at success
        subst next
        exact redeemRouteCredit?_conserves_total state.ledger ledger roots redeemed

theorem successful_route_receipt_is_single_use
    {Root : Type uR} {ReceiptId : Type uC}
    [DecidableEq Root] [DecidableEq ReceiptId]
    {receiptId : ReceiptId} {roots : Finset Root}
    {state next : RouteCreditState Root ReceiptId}
    (success : redeemAuthenticatedRouteCredit? true receiptId roots state =
      some next) :
    redeemAuthenticatedRouteCredit? true receiptId roots next = none :=
  spent_route_receipt_cannot_redeem_again true receiptId roots next
    (successful_route_receipt_is_marked_spent success)

/-! ## Refinement into the existing named-slot credit semantics -/

def creditAccountEquiv (Root : Type uR) :
    CreditAccount Root Unit ≃ Root ⊕ Unit where
  toFun
    | .synapse root => Sum.inl root
    | .reserve neuron => Sum.inr neuron
  invFun
    | Sum.inl root => .synapse root
    | Sum.inr neuron => .reserve neuron
  left_inv account := by cases account <;> rfl
  right_inv account := by cases account <;> rfl

/-- Aggregate readout of the already-formalized named-slot credit state. -/
def ledgerOfCreditState
    {Root : Type uR} {receiptSlots : ℕ}
    [Fintype Root] [DecidableEq Root]
    (state : CreditState Root Unit receiptSlots routeCreditPacket) :
    RouteCreditLedger Root where
  reserve := accountCredits state (.reserve ())
  credit := fun root ↦ accountCredits state (.synapse root)

theorem totalCredits_decompose_route_accounts
    {Root : Type uR} {receiptSlots : ℕ}
    [Fintype Root] [DecidableEq Root]
    (state : CreditState Root Unit receiptSlots routeCreditPacket) :
    totalCredits state =
      (∑ root, accountCredits state (.synapse root)) +
        accountCredits state (.reserve ()) := by
  classical
  unfold totalCredits
  calc
    (∑ account : CreditAccount Root Unit, accountCredits state account) =
        ∑ account : Root ⊕ Unit,
          accountCredits state ((creditAccountEquiv Root).symm account) := by
      apply Fintype.sum_equiv (creditAccountEquiv Root)
      intro account
      simp
    _ = (∑ root, accountCredits state (.synapse root)) +
          accountCredits state (.reserve ()) := by
      rw [Fintype.sum_sum_type]
      simp [creditAccountEquiv]

/-- The aggregate runtime ledger inherits the exact 840-token invariant from
the existing named-slot semantics. -/
theorem ledgerOfCreditState_total_eq_packet
    {Root : Type uR} {receiptSlots : ℕ}
    [Fintype Root] [DecidableEq Root]
    (state : CreditState Root Unit receiptSlots routeCreditPacket) :
    (ledgerOfCreditState state).total = routeCreditPacket := by
  set_option maxRecDepth 4096 in
    classical
    have conserved := totalCredits_eq_budget state
    rw [totalCredits_decompose_route_accounts] at conserved
    simpa only [RouteCreditLedger.total, ledgerOfCreditState, add_comm] using conserved

/-! ## Executable positive and negative fixtures -/

def twoRootReserveLedger : RouteCreditLedger Bool where
  reserve := routeCreditPacket
  credit := fun _ ↦ 0

def twoRootSupport : Finset Bool := {false, true}

theorem two_root_packet_splits_exactly :
    redeemRouteCredit? true twoRootReserveLedger twoRootSupport =
      some
        { reserve := 0
          credit := fun _ ↦ 420 } := by
  simp [redeemRouteCredit?, twoRootReserveLedger, twoRootSupport,
    allocateRouteCredit, routeCreditPacket, routeCreditShare]

theorem rejected_two_root_packet_preserves_absence_of_transition :
    redeemRouteCredit? false twoRootReserveLedger twoRootSupport = none := by
  exact rejected_route_credit_fails _ _

#print axioms eligible_does_not_imply_counterfactual_necessity
#print axioms checkedOutcome_projection_is_not_injective
#print axioms sourceBound_valid_of_eligible
#print axioms supportedRouteCount_exact_split
#print axioms redeemRouteCredit?_conserves_total
#print axioms duplicate_route_root_does_not_multiply_credit
#print axioms successful_route_receipt_is_single_use
#print axioms successful_authenticated_redemption_conserves_total
#print axioms ledgerOfCreditState_total_eq_packet
#print axioms two_root_packet_splits_exactly

end Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery
