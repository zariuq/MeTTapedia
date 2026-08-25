import MeTTailCore.Crypto.SHA256
import Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.ActionMemoryConservedRouteCredit

/-!
# Source-bound runtime conformance for conserved route credit

The mathematical route-credit model is useful only if the executable search,
receipt, and redemption code implement the same transition.  This module is
an independent Lean consumer of a JSON fixture emitted by the Python runtime.
It reconstructs receipt identities, source authentication, single-use packet
redemption, exact conservation, and the route-weight readout.  The executable
checker also hashes the fixed source files named by the schema.

The checker exercises one accepted receipt and three distinct failures:
reusing a spent receipt, checker rejection, and a forged source receipt.  A
failed transition must return the original state exactly.
-/

namespace Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery

open Lean
open MeTTailCore.Crypto.SHA256

def conservedRouteCreditRuntimeSchema : String :=
  "tgad.action-memory.conserved-route-credit-runtime.v1"

def routeUseTraceRuntimeSchema : String :=
  "tgad.action-memory.route-use-trace.v1"

def checkedRouteReceiptRuntimeSchema : String :=
  "tgad.action-memory.checked-route-receipt.v1"

def routeEvidenceInterpretation : String :=
  "eligible observed support, not counterfactual necessity"

def conservedRouteCreditSourceLayout : List (String × String) :=
  [ ("conserved_route_credit",
      "ml/gslt-synth/models/conserved_route_credit.py")
  , ("verifier_action_memory",
      "ml/gslt-synth/models/verifier_action_memory.py")
  , ("action_memory_model",
      "ml/gslt-synth/models/tgad_action_memory_model.py")
  , ("reasoned_action_memory_model",
      "ml/gslt-synth/models/tgad_reasoned_action_memory_model.py")
  , ("tgad_search", "ml/gslt-synth/search/tgad_o2.py") ]

structure RuntimeRootReceipt where
  causalRoot : String
  sourceReceiptSha256 : String
  deriving DecidableEq, Repr

structure RuntimeRouteUseTrace where
  schema : String
  queryId : String
  programSha256 : String
  selectedActions : List Nat
  usedRootReceipts : List RuntimeRootReceipt
  evidenceInterpretation : String
  deriving DecidableEq, Repr

structure RuntimeCheckedRouteReceipt where
  trace : RuntimeRouteUseTrace
  solvedTarget : Nat
  checkerReceiptSha256 : String
  checkerAccepted : Bool
  receiptIdMaterial : String
  receiptId : String
  deriving DecidableEq, Repr

structure RuntimeRootCredit where
  causalRoot : String
  credit : Nat
  deriving DecidableEq, Repr

structure RuntimeRouteCreditState where
  reserve : Nat
  rootCredit : List RuntimeRootCredit
  redeemedReceipts : List String
  declaredTotal : Nat
  computedTotal : Nat
  deriving DecidableEq, Repr

structure RuntimeRouteCreditRedemption where
  status : String
  transferred : Nat
  eligibleRoots : List String
  state : RuntimeRouteCreditState
  deriving DecidableEq, Repr

structure RuntimeExactRoute where
  queryId : String
  causalRoot : String
  weight : ExactNonnegativeRatio
  deriving DecidableEq, Repr

structure ConservedRouteCreditRuntimeFixture where
  schema : String
  sourceFiles : List RuntimeSourceBinding
  sourceReceipts : List RuntimeRootReceipt
  acceptedReceipt : RuntimeCheckedRouteReceipt
  rejectedReceipt : RuntimeCheckedRouteReceipt
  forgedReceipt : RuntimeCheckedRouteReceipt
  initialState : RuntimeRouteCreditState
  positiveRedemption : RuntimeRouteCreditRedemption
  duplicateRedemption : RuntimeRouteCreditRedemption
  checkerRejection : RuntimeRouteCreditRedemption
  forgedSourceRejection : RuntimeRouteCreditRedemption
  baseRoutes : List RuntimeExactRoute
  creditedRoutes : List RuntimeExactRoute
  deriving DecidableEq, Repr

/-! ## Independent receipt and transition model -/

def runtimeCreditSourceLayout
    (sources : List RuntimeSourceBinding) : List (String × String) :=
  sources.map fun source ↦ (source.role, source.path)

def runtimeFrame (value : String) : String :=
  toString value.utf8ByteSize ++ ":" ++ value

def runtimeRootReceiptMaterial (receipt : RuntimeRootReceipt) : String :=
  receipt.causalRoot ++ "," ++ receipt.sourceReceiptSha256

def runtimeReceiptIdMaterial (receipt : RuntimeCheckedRouteReceipt) : String :=
  let fields :=
    [ checkedRouteReceiptRuntimeSchema
    , receipt.trace.queryId
    , receipt.trace.programSha256
    , String.intercalate "," (receipt.trace.selectedActions.map toString)
    , String.intercalate ";"
        (receipt.trace.usedRootReceipts.map runtimeRootReceiptMaterial)
    , toString receipt.solvedTarget
    , receipt.checkerReceiptSha256
    , if receipt.checkerAccepted then "1" else "0" ]
  "checked-action-memory-route-receipt-v1\u0000" ++
    String.join (fields.map runtimeFrame)

def runtimeRootNames (receipts : List RuntimeRootReceipt) : List String :=
  receipts.map RuntimeRootReceipt.causalRoot

def runtimeCreditRootNames (credits : List RuntimeRootCredit) : List String :=
  credits.map RuntimeRootCredit.causalRoot

def runtimeLookupSourceReceipt?
    (receipts : List RuntimeRootReceipt) (root : String) : Option String :=
  (receipts.find? fun receipt ↦ receipt.causalRoot == root).map
    RuntimeRootReceipt.sourceReceiptSha256

def runtimeLookupCredit?
    (credits : List RuntimeRootCredit) (root : String) : Option Nat :=
  (credits.find? fun entry ↦ entry.causalRoot == root).map
    RuntimeRootCredit.credit

def runtimeStateTotal (state : RuntimeRouteCreditState) : Nat :=
  state.reserve + (state.rootCredit.map RuntimeRootCredit.credit).sum

def runtimeStateWellFormed (state : RuntimeRouteCreditState) : Bool :=
  decide (runtimeCreditRootNames state.rootCredit).Nodup &&
    state.rootCredit.all (fun entry ↦ !entry.causalRoot.isEmpty) &&
    (state.computedTotal == runtimeStateTotal state) &&
    (state.declaredTotal == state.computedTotal) &&
    state.redeemedReceipts.all (fun receipt ↦ receipt.length == 64)

def runtimeReceiptShapeValid (receipt : RuntimeCheckedRouteReceipt) : Bool :=
  (receipt.trace.schema == routeUseTraceRuntimeSchema) &&
    (receipt.trace.evidenceInterpretation == routeEvidenceInterpretation) &&
    !receipt.trace.queryId.isEmpty &&
    (receipt.trace.programSha256.length == 64) &&
    (receipt.checkerReceiptSha256.length == 64) &&
    (receipt.receiptId.length == 64) &&
    decide (runtimeRootNames receipt.trace.usedRootReceipts).Nodup &&
    receipt.trace.usedRootReceipts.all (fun root ↦
      !root.causalRoot.isEmpty && root.sourceReceiptSha256.length == 64) &&
    (receipt.receiptIdMaterial == runtimeReceiptIdMaterial receipt) &&
    (receipt.receiptId == sha256Hex receipt.receiptIdMaterial)

def runtimeSourceReceiptsMatch
    (expected : List RuntimeRootReceipt)
    (used : List RuntimeRootReceipt) : Bool :=
  used.all fun receipt ↦
    runtimeLookupSourceReceipt? expected receipt.causalRoot ==
      some receipt.sourceReceiptSha256

def runtimeRootsKnown
    (state : RuntimeRouteCreditState) (roots : List String) : Bool :=
  roots.all fun root ↦ (runtimeLookupCredit? state.rootCredit root).isSome

def runtimeAddRootShare
    (roots : List String) (share : Nat)
    (entry : RuntimeRootCredit) : RuntimeRootCredit :=
  if roots.contains entry.causalRoot then
    { entry with credit := entry.credit + share }
  else
    entry

def runtimeAppliedState
    (state : RuntimeRouteCreditState)
    (receipt : RuntimeCheckedRouteReceipt) : RuntimeRouteCreditState :=
  let roots := runtimeRootNames receipt.trace.usedRootReceipts
  let share := routeCreditPacket / roots.length
  let nextCredits := state.rootCredit.map (runtimeAddRootShare roots share)
  { reserve := state.reserve - routeCreditPacket
    rootCredit := nextCredits
    redeemedReceipts := List.insert receipt.receiptId state.redeemedReceipts
    declaredTotal := state.declaredTotal
    computedTotal := state.reserve - routeCreditPacket +
      (nextCredits.map RuntimeRootCredit.credit).sum }

def runtimeRejectedRedemption
    (status : String) (state : RuntimeRouteCreditState)
    (roots : List String) : RuntimeRouteCreditRedemption :=
  { status := status
    transferred := 0
    eligibleRoots := roots
    state := state }

/-- Independent executable image of `redeem_checked_route_receipt`. -/
def runtimeRedeemCheckedRouteReceipt
    (expected : List RuntimeRootReceipt)
    (state : RuntimeRouteCreditState)
    (receipt : RuntimeCheckedRouteReceipt) : RuntimeRouteCreditRedemption :=
  let roots := runtimeRootNames receipt.trace.usedRootReceipts
  if !receipt.checkerAccepted then
    runtimeRejectedRedemption "CHECKER_REJECTED" state roots
  else if state.redeemedReceipts.contains receipt.receiptId then
    runtimeRejectedRedemption "RECEIPT_ALREADY_SPENT" state roots
  else if roots.isEmpty then
    runtimeRejectedRedemption "EMPTY_ROUTE_SUPPORT" state roots
  else if 8 < roots.length then
    runtimeRejectedRedemption "ROUTE_SUPPORT_EXCEEDS_EIGHT" state roots
  else if !runtimeRootsKnown state roots then
    runtimeRejectedRedemption "UNKNOWN_ROUTE_ROOT" state roots
  else if !runtimeSourceReceiptsMatch expected receipt.trace.usedRootReceipts then
    runtimeRejectedRedemption "SOURCE_RECEIPT_MISMATCH" state roots
  else if state.reserve < routeCreditPacket then
    runtimeRejectedRedemption "INSUFFICIENT_RESERVE" state roots
  else
    { status := "APPLIED"
      transferred := routeCreditPacket
      eligibleRoots := roots
      state := runtimeAppliedState state receipt }

def runtimeRouteWeightReadoutConforms
    (state : RuntimeRouteCreditState)
    (base credited : List RuntimeExactRoute) : Bool :=
  match base, credited with
  | [], [] => true
  | before :: beforeRest, after :: afterRest =>
      match runtimeLookupCredit? state.rootCredit before.causalRoot with
      | none => false
      | some credit =>
          (before.queryId == after.queryId) &&
          (before.causalRoot == after.causalRoot) &&
          decide (0 < before.weight.denominator) &&
          decide (0 < after.weight.denominator) &&
          decide (after.weight.value = before.weight.value +
            (credit : ℚ) / routeCreditPacket) &&
          runtimeRouteWeightReadoutConforms state beforeRest afterRest
  | _, _ => false

def ConservedRouteCreditRuntimeFixture.Valid
    (fixture : ConservedRouteCreditRuntimeFixture) : Prop :=
  fixture.schema = conservedRouteCreditRuntimeSchema ∧
  runtimeCreditSourceLayout fixture.sourceFiles =
    conservedRouteCreditSourceLayout ∧
  fixture.sourceFiles.all (fun source ↦ source.sha256.length = 64) = true ∧
  (runtimeRootNames fixture.sourceReceipts).Nodup ∧
  runtimeCreditRootNames fixture.initialState.rootCredit =
    runtimeRootNames fixture.sourceReceipts ∧
  runtimeStateWellFormed fixture.initialState = true ∧
  runtimeReceiptShapeValid fixture.acceptedReceipt = true ∧
  runtimeReceiptShapeValid fixture.rejectedReceipt = true ∧
  runtimeReceiptShapeValid fixture.forgedReceipt = true ∧
  runtimeRedeemCheckedRouteReceipt fixture.sourceReceipts fixture.initialState
      fixture.acceptedReceipt = fixture.positiveRedemption ∧
  runtimeStateWellFormed fixture.positiveRedemption.state = true ∧
  runtimeRedeemCheckedRouteReceipt fixture.sourceReceipts
      fixture.positiveRedemption.state fixture.acceptedReceipt =
    fixture.duplicateRedemption ∧
  runtimeRedeemCheckedRouteReceipt fixture.sourceReceipts fixture.initialState
      fixture.rejectedReceipt = fixture.checkerRejection ∧
  runtimeRedeemCheckedRouteReceipt fixture.sourceReceipts fixture.initialState
      fixture.forgedReceipt = fixture.forgedSourceRejection ∧
  fixture.duplicateRedemption.state = fixture.positiveRedemption.state ∧
  fixture.checkerRejection.state = fixture.initialState ∧
  fixture.forgedSourceRejection.state = fixture.initialState ∧
  runtimeRouteWeightReadoutConforms fixture.positiveRedemption.state
      fixture.baseRoutes fixture.creditedRoutes = true

def ConservedRouteCreditRuntimeFixture.check
    (fixture : ConservedRouteCreditRuntimeFixture) : Bool :=
  (fixture.schema == conservedRouteCreditRuntimeSchema) &&
  (runtimeCreditSourceLayout fixture.sourceFiles ==
    conservedRouteCreditSourceLayout) &&
  fixture.sourceFiles.all (fun source ↦ source.sha256.length == 64) &&
  decide (runtimeRootNames fixture.sourceReceipts).Nodup &&
  (runtimeCreditRootNames fixture.initialState.rootCredit ==
    runtimeRootNames fixture.sourceReceipts) &&
  runtimeStateWellFormed fixture.initialState &&
  runtimeReceiptShapeValid fixture.acceptedReceipt &&
  runtimeReceiptShapeValid fixture.rejectedReceipt &&
  runtimeReceiptShapeValid fixture.forgedReceipt &&
  (runtimeRedeemCheckedRouteReceipt fixture.sourceReceipts fixture.initialState
      fixture.acceptedReceipt == fixture.positiveRedemption) &&
  runtimeStateWellFormed fixture.positiveRedemption.state &&
  (runtimeRedeemCheckedRouteReceipt fixture.sourceReceipts
      fixture.positiveRedemption.state fixture.acceptedReceipt ==
    fixture.duplicateRedemption) &&
  (runtimeRedeemCheckedRouteReceipt fixture.sourceReceipts fixture.initialState
      fixture.rejectedReceipt == fixture.checkerRejection) &&
  (runtimeRedeemCheckedRouteReceipt fixture.sourceReceipts fixture.initialState
      fixture.forgedReceipt == fixture.forgedSourceRejection) &&
  (fixture.duplicateRedemption.state == fixture.positiveRedemption.state) &&
  (fixture.checkerRejection.state == fixture.initialState) &&
  (fixture.forgedSourceRejection.state == fixture.initialState) &&
  runtimeRouteWeightReadoutConforms fixture.positiveRedemption.state
    fixture.baseRoutes fixture.creditedRoutes

theorem ConservedRouteCreditRuntimeFixture.check_eq_true_iff
    (fixture : ConservedRouteCreditRuntimeFixture) :
    fixture.check = true ↔ fixture.Valid := by
  simp [ConservedRouteCreditRuntimeFixture.check,
    ConservedRouteCreditRuntimeFixture.Valid]
  tauto

/-! ## General positive and negative transition facts -/

theorem runtime_checker_rejection_preserves_state
    (expected : List RuntimeRootReceipt) (state : RuntimeRouteCreditState)
    (receipt : RuntimeCheckedRouteReceipt)
    (rejected : receipt.checkerAccepted = false) :
    (runtimeRedeemCheckedRouteReceipt expected state receipt).state = state := by
  simp [runtimeRedeemCheckedRouteReceipt, rejected,
    runtimeRejectedRedemption]

theorem runtime_spent_receipt_preserves_state
    (expected : List RuntimeRootReceipt) (state : RuntimeRouteCreditState)
    (receipt : RuntimeCheckedRouteReceipt)
    (spent : receipt.receiptId ∈ state.redeemedReceipts) :
    (runtimeRedeemCheckedRouteReceipt expected state receipt).state = state := by
  by_cases rejected : receipt.checkerAccepted = false <;>
    simp [runtimeRedeemCheckedRouteReceipt, rejected, spent,
      runtimeRejectedRedemption]

theorem runtime_forged_source_preserves_state
    (expected : List RuntimeRootReceipt) (state : RuntimeRouteCreditState)
    (receipt : RuntimeCheckedRouteReceipt)
    (accepted : receipt.checkerAccepted = true)
    (fresh : receipt.receiptId ∉ state.redeemedReceipts)
    (nonempty : (runtimeRootNames receipt.trace.usedRootReceipts).isEmpty = false)
    (bounded : ¬ 8 < (runtimeRootNames receipt.trace.usedRootReceipts).length)
    (known : runtimeRootsKnown state
      (runtimeRootNames receipt.trace.usedRootReceipts) = true)
    (forged : runtimeSourceReceiptsMatch expected
      receipt.trace.usedRootReceipts = false) :
    (runtimeRedeemCheckedRouteReceipt expected state receipt).state = state := by
  simp [runtimeRedeemCheckedRouteReceipt, accepted, fresh, nonempty,
    bounded, known, forged, runtimeRejectedRedemption]

/-! ## JSON parser and fixed source boundary -/

private def crcStringField (json : Json) (field : String) :
    Except String String :=
  json.getObjVal? field >>= Json.getStr?

private def crcNatField (json : Json) (field : String) :
    Except String Nat :=
  json.getObjVal? field >>= Json.getNat?

private def crcArrayField (json : Json) (field : String) :
    Except String (List Json) := do
  let values ← json.getObjVal? field >>= Json.getArr?
  pure values.toList

private def crcStringArray (json : Json) (field : String) :
    Except String (List String) := do
  (← crcArrayField json field).mapM Json.getStr?

private def crcNatArray (json : Json) (field : String) :
    Except String (List Nat) := do
  (← crcArrayField json field).mapM Json.getNat?

private def crcParseSource (json : Json) : Except String RuntimeSourceBinding := do
  pure
    { role := ← crcStringField json "role"
      path := ← crcStringField json "path"
      sha256 := ← crcStringField json "sha256" }

private def crcParseRootReceipt (json : Json) :
    Except String RuntimeRootReceipt := do
  pure
    { causalRoot := ← crcStringField json "causal_root"
      sourceReceiptSha256 := ← crcStringField json "source_receipt_sha256" }

private def crcParseTrace (json : Json) : Except String RuntimeRouteUseTrace := do
  let receiptJson ← crcArrayField json "used_root_receipts"
  pure
    { schema := ← crcStringField json "schema"
      queryId := ← crcStringField json "query_id"
      programSha256 := ← crcStringField json "program_sha256"
      selectedActions := ← crcNatArray json "selected_actions"
      usedRootReceipts := ← receiptJson.mapM crcParseRootReceipt
      evidenceInterpretation :=
        ← crcStringField json "evidence_interpretation" }

private def crcParseCheckedReceipt (json : Json) :
    Except String RuntimeCheckedRouteReceipt := do
  pure
    { trace := ← json.getObjVal? "trace" >>= crcParseTrace
      solvedTarget := ← crcNatField json "solved_target"
      checkerReceiptSha256 := ← crcStringField json "checker_receipt_sha256"
      checkerAccepted :=
        ← json.getObjVal? "checker_accepted" >>= Json.getBool?
      receiptIdMaterial := ← crcStringField json "receipt_id_material"
      receiptId := ← crcStringField json "receipt_id" }

private def crcParseRootCredit (json : Json) :
    Except String RuntimeRootCredit := do
  pure
    { causalRoot := ← crcStringField json "causal_root"
      credit := ← crcNatField json "credit" }

private def crcParseState (json : Json) : Except String RuntimeRouteCreditState := do
  let creditJson ← crcArrayField json "root_credit"
  pure
    { reserve := ← crcNatField json "reserve"
      rootCredit := ← creditJson.mapM crcParseRootCredit
      redeemedReceipts := ← crcStringArray json "redeemed_receipts"
      declaredTotal := ← crcNatField json "declared_total"
      computedTotal := ← crcNatField json "computed_total" }

private def crcParseRedemption (json : Json) :
    Except String RuntimeRouteCreditRedemption := do
  pure
    { status := ← crcStringField json "status"
      transferred := ← crcNatField json "transferred"
      eligibleRoots := ← crcStringArray json "eligible_roots"
      state := ← json.getObjVal? "state" >>= crcParseState }

private def crcParseRoute (json : Json) : Except String RuntimeExactRoute := do
  pure
    { queryId := ← crcStringField json "query_id"
      causalRoot := ← crcStringField json "causal_root"
      weight :=
        { numerator := ← crcNatField json "weight_numerator"
          denominator := ← crcNatField json "weight_denominator" } }

/-- Parse the runtime-emitted conserved-credit fixture. -/
def parseConservedRouteCreditRuntimeFixture (text : String) :
    Except String ConservedRouteCreditRuntimeFixture := do
  let json ← Json.parse text
  let sources ← crcArrayField json "source_files"
  let sourceReceipts ← crcArrayField json "source_receipts"
  let baseRoutes ← crcArrayField json "base_routes"
  let creditedRoutes ← crcArrayField json "credited_routes"
  pure
    { schema := ← crcStringField json "schema"
      sourceFiles := ← sources.mapM crcParseSource
      sourceReceipts := ← sourceReceipts.mapM crcParseRootReceipt
      acceptedReceipt :=
        ← json.getObjVal? "accepted_receipt" >>= crcParseCheckedReceipt
      rejectedReceipt :=
        ← json.getObjVal? "rejected_receipt" >>= crcParseCheckedReceipt
      forgedReceipt :=
        ← json.getObjVal? "forged_receipt" >>= crcParseCheckedReceipt
      initialState := ← json.getObjVal? "initial_state" >>= crcParseState
      positiveRedemption :=
        ← json.getObjVal? "positive_redemption" >>= crcParseRedemption
      duplicateRedemption :=
        ← json.getObjVal? "duplicate_redemption" >>= crcParseRedemption
      checkerRejection :=
        ← json.getObjVal? "checker_rejection" >>= crcParseRedemption
      forgedSourceRejection :=
        ← json.getObjVal? "forged_source_rejection" >>= crcParseRedemption
      baseRoutes := ← baseRoutes.mapM crcParseRoute
      creditedRoutes := ← creditedRoutes.mapM crcParseRoute }

def conservedRouteCreditSourceDigestMatches
    (binding : RuntimeSourceBinding) (source : String) : Bool :=
  sha256Hex source == binding.sha256

theorem changed_conserved_route_credit_source_is_rejected
    (binding : RuntimeSourceBinding) (source : String)
    (digestMismatch : sha256Hex source ≠ binding.sha256) :
    conservedRouteCreditSourceDigestMatches binding source = false := by
  simp [conservedRouteCreditSourceDigestMatches, digestMismatch]

def checkConservedRouteCreditRuntimeSources
    (repositoryRoot : System.FilePath)
    (fixture : ConservedRouteCreditRuntimeFixture) : IO Bool := do
  for binding in fixture.sourceFiles do
    let path := repositoryRoot / binding.path
    if !(← path.pathExists) then
      return false
    let content ← IO.FS.readFile path
    if !conservedRouteCreditSourceDigestMatches binding content then
      return false
  return true

#print axioms ConservedRouteCreditRuntimeFixture.check_eq_true_iff
#print axioms runtime_checker_rejection_preserves_state
#print axioms runtime_spent_receipt_preserves_state
#print axioms runtime_forged_source_preserves_state
#print axioms changed_conserved_route_credit_source_is_rejected

end Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery
