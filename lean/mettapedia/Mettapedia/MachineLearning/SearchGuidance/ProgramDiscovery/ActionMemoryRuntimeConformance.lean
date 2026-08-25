import MeTTailCore.Crypto.SHA256
import Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.VerifierHindsightReplay

/-!
# Source-bound verified-action-memory conformance

This module gives the Python action-memory carrier an independent Lean model.
The checked JSON payload contains records and exact observations produced by
the running Python classes.  Lean reconstructs record keys, reciprocal-root
weights, the all-record action histogram, cold-path identities, legality
masking, and the Transformer's causal mask.  A separate IO check hashes the
three source files named by the payload.

The fixture includes the corresponding unmasked counterfactual.  Thus the
legality claim is not inferred merely because the selected illegal coordinate
happened to receive zero evidence.
-/

namespace Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery

open Lean
open MeTTailCore.Crypto.SHA256

def actionMemoryConformanceSchema : String :=
  "fresh-unified.verified-action-memory-conformance.v1"

def actionTraceRecordFieldNames : List String :=
  [ "previous_action", "role_id", "parent_id", "argument_id", "depth"
  , "open_holes", "position", "next_action", "causal_root", "target_anum"
  , "receipt_sha256" ]

def actionMemoryRouteFieldNames : List String :=
  ["query_id", "causal_root", "weight"]

def constructionStateFieldNames : List String :=
  [ "previous_actions", "role_ids", "parent_ids", "argument_ids", "depths"
  , "open_holes", "positions" ]

def actionMemorySourceLayout : List (String × String) :=
  [ ("verifier_action_memory",
      "ml/gslt-synth/models/verifier_action_memory.py")
  , ("action_memory_model",
      "ml/gslt-synth/models/tgad_action_memory_model.py")
  , ("transformer_policy",
      "ml/gslt-synth/models/tgad_transformer_policy.py") ]

/-- Field-for-field Lean image of the runtime's `ActionTraceRecord`. -/
structure RuntimeActionTraceRecord where
  previousAction : Nat
  roleId : Nat
  parentId : Nat
  argumentId : Nat
  depth : Nat
  openHoles : Nat
  position : Nat
  nextAction : Nat
  causalRoot : String
  targetAnum : Nat
  receiptSha256 : String
  deriving DecidableEq, Repr

/-- Exact rational emitted by Python from a binary32 value's integer ratio. -/
structure ExactNonnegativeRatio where
  numerator : Nat
  denominator : Nat
  deriving DecidableEq, Repr

def ExactNonnegativeRatio.value (ratio : ExactNonnegativeRatio) : ℚ :=
  (ratio.numerator : ℚ) / ratio.denominator

def ExactNonnegativeRatio.valid (ratio : ExactNonnegativeRatio) : Prop :=
  0 < ratio.denominator

/-- Field-for-field exact image of the runtime's `ActionMemoryRoute`.  The
Python route weight is serialized by its exact integer ratio. -/
structure RuntimeActionMemoryRoute where
  queryId : String
  causalRoot : String
  weight : ExactNonnegativeRatio
  deriving DecidableEq, Repr

structure RuntimeSourceBinding where
  role : String
  path : String
  sha256 : String
  deriving DecidableEq, Repr

structure RuntimeMemoryParameters where
  numActions : Nat
  maxDepth : Nat
  maxActions : Nat
  topK : Nat
  topKRoots : Nat
  deriving DecidableEq, Repr

structure RuntimeBankObservation where
  weights : List ExactNonnegativeRatio
  keys : List (List ExactNonnegativeRatio)
  queryHistogram : List ExactNonnegativeRatio
  deriving DecidableEq, Repr

structure RuntimeBiasObservation where
  baseLogitsFloat32Words : List Nat
  disabledLogitsFloat32Words : List Nat
  gateZeroLogitsFloat32Words : List Nat
  legalMask : List Bool
  activeMaskedLogitsFloat32Words : List Nat
  activeUnmaskedLogitsFloat32Words : List Nat
  deriving DecidableEq, Repr

/-- Runtime observations for the deployed query-to-root-to-nearest-state
route.  Lean reconstructs every histogram from the records and routes. -/
structure RuntimeRoutingObservation where
  queryId : String
  queryKey : List ExactNonnegativeRatio
  topOneHistogram : List ExactNonnegativeRatio
  topKHistogram : List ExactNonnegativeRatio
  knownEmptyQueryId : String
  knownEmptyHistogram : List ExactNonnegativeRatio
  legalMask : List Bool
  maskedTopKHistogram : List ExactNonnegativeRatio
  unknownQueryId : String
  unknownQueryRejected : Bool
  duplicateRoutes : List RuntimeActionMemoryRoute
  duplicateQueryRootRejected : Bool
  deriving DecidableEq, Repr

structure ActionMemoryRuntimeFixture where
  schema : String
  sourceFiles : List RuntimeSourceBinding
  actionTraceRecordFields : List String
  actionMemoryRouteFields : List String
  memoryStateFields : List String
  transformerStateFields : List String
  parameters : RuntimeMemoryParameters
  records : List RuntimeActionTraceRecord
  routes : List RuntimeActionMemoryRoute
  knownQueryIds : List String
  bank : RuntimeBankObservation
  routing : RuntimeRoutingObservation
  bias : RuntimeBiasObservation
  transformerCausalMask : List (List Bool)
  deriving DecidableEq, Repr

/-! ## Independent exact model -/

/-- One-hot vector with the runtime's upper clamping convention. -/
def runtimeOneHot (size value : Nat) : List ℚ :=
  (List.range size).map fun index ↦
    if index = min value (size - 1) then 1 else 0

/-- Independent reconstruction of `_record_key`.  The zero-denominator
branches are rejected by fixture validity; assigning zero here keeps the
function total on malformed input. -/
def runtimeRecordKey
    (parameters : RuntimeMemoryParameters)
    (record : RuntimeActionTraceRecord) : List ℚ :=
  runtimeOneHot (parameters.numActions + 1) record.previousAction ++
    runtimeOneHot (parameters.numActions + 1) record.parentId ++
    runtimeOneHot 3 record.roleId ++
    runtimeOneHot 5 (min record.argumentId 4) ++
    [ if parameters.maxDepth = 0 then 0
      else (min record.depth parameters.maxDepth : ℚ) / parameters.maxDepth
    , if parameters.maxActions = 0 then 0
      else (min record.openHoles parameters.maxActions : ℚ) /
        parameters.maxActions
    , if parameters.maxActions = 0 then 0
      else (min record.position (parameters.maxActions - 1) : ℚ) /
        parameters.maxActions ]

def runtimeRootCount
    (records : List RuntimeActionTraceRecord) (root : String) : Nat :=
  (records.filter fun record ↦ record.causalRoot == root).length

/-- Executable form of one-root-one-unit record weighting. -/
def runtimeReciprocalRootWeight
    (records : List RuntimeActionTraceRecord)
    (record : RuntimeActionTraceRecord) : ℚ :=
  let count := runtimeRootCount records record.causalRoot
  if count = 0 then 0 else (count : ℚ)⁻¹

def runtimeExpectedWeights
    (records : List RuntimeActionTraceRecord) : List ℚ :=
  records.map (runtimeReciprocalRootWeight records)

/-- Histogram used by the fixture's query: `topK` covers every record, so the
nearest-neighbour ordering is deliberately irrelevant. -/
def runtimeAllRecordHistogram
    (numActions : Nat) (records : List RuntimeActionTraceRecord) : List ℚ :=
  (List.range numActions).map fun action ↦
    ((records.zip (runtimeExpectedWeights records)).map fun (record, weight) ↦
      if record.nextAction = action then weight else 0).sum

structure RuntimeStateActionRow where
  key : List ℚ
  action : Nat
  deriving DecidableEq, Repr

structure RuntimeWeightedStateActionRow extends RuntimeStateActionRow where
  weight : ℚ
  deriving DecidableEq, Repr

def runtimeRouteWeight (route : RuntimeActionMemoryRoute) : ℚ :=
  route.weight.value

def runtimeQueryRootKeys
    (routes : List RuntimeActionMemoryRoute) : List (String × String) :=
  routes.map fun route ↦ (route.queryId, route.causalRoot)

/-- The deployed builder admits at most one route for each query/root pair. -/
def runtimeRoutesHaveNoDuplicateQueryRoot
    (routes : List RuntimeActionMemoryRoute) : Bool :=
  decide (runtimeQueryRootKeys routes).Nodup

def runtimeRouteBeforeOrEqual
    (first second : RuntimeActionMemoryRoute) : Bool :=
  decide (runtimeRouteWeight second < runtimeRouteWeight first ∨
    (runtimeRouteWeight first = runtimeRouteWeight second ∧
      first.causalRoot ≤ second.causalRoot))

/-- Python sorts routes by descending weight and then ascending root name. -/
def runtimeRoutesForQuery
    (routes : List RuntimeActionMemoryRoute) (queryId : String) :
    List RuntimeActionMemoryRoute :=
  List.insertionSort
    (fun first second ↦ runtimeRouteBeforeOrEqual first second = true)
    (routes.filter fun route ↦ route.queryId == queryId)

def runtimeRootRows
    (parameters : RuntimeMemoryParameters)
    (records : List RuntimeActionTraceRecord) (root : String) :
    List RuntimeStateActionRow :=
  ((records.filter fun record ↦ record.causalRoot == root).map fun record ↦
    { key := runtimeRecordKey parameters record
      action := record.nextAction }).eraseDups

def runtimeSquaredDistance (left right : List ℚ) : ℚ :=
  (List.zipWith (fun x y ↦ (x - y) ^ 2) left right).sum

def runtimeMinimum? : List ℚ → Option ℚ
  | [] => none
  | head :: tail => some (tail.foldl min head)

def runtimeNearestRows
    (queryKey : List ℚ) (rows : List RuntimeStateActionRow) :
    List RuntimeStateActionRow :=
  match runtimeMinimum? (rows.map fun row ↦
      runtimeSquaredDistance queryKey row.key) with
  | none => []
  | some minimum => rows.filter fun row ↦
      runtimeSquaredDistance queryKey row.key == minimum

def runtimeNearestRowsHistogram
    (numActions : Nat) (queryKey : List ℚ)
    (rows : List RuntimeStateActionRow) (routeWeight : ℚ) : List ℚ :=
  let nearest := runtimeNearestRows queryKey rows
  (List.range numActions).map fun action ↦
    if nearest.isEmpty then 0
    else routeWeight *
      ((nearest.filter fun row ↦ row.action == action).length : ℚ) /
        nearest.length

def runtimeRootNearestHistogram
    (parameters : RuntimeMemoryParameters)
    (records : List RuntimeActionTraceRecord)
    (queryKey : List ℚ) (route : RuntimeActionMemoryRoute) : List ℚ :=
  runtimeNearestRowsHistogram parameters.numActions queryKey
    (runtimeRootRows parameters records route.causalRoot)
    (runtimeRouteWeight route)

def runtimeAddHistograms (left right : List ℚ) : List ℚ :=
  List.zipWith (· + ·) left right

def runtimeSelectedRouteHistogram
    (parameters : RuntimeMemoryParameters)
    (records : List RuntimeActionTraceRecord)
    (queryKey : List ℚ) (selected : List RuntimeActionMemoryRoute) : List ℚ :=
  selected.foldl
    (fun histogram route ↦ runtimeAddHistograms histogram
      (runtimeRootNearestHistogram parameters records queryKey route))
    (List.replicate parameters.numActions 0)

/-- Independent reconstruction of `routed_action_histogram`.  `none` is the
fail-closed result for a duplicate route table or an unknown query; a known
query with no roots returns `some` zero histogram. -/
def runtimeRoutedHistogram?
    (parameters : RuntimeMemoryParameters)
    (records : List RuntimeActionTraceRecord)
    (routes : List RuntimeActionMemoryRoute)
    (knownQueryIds : List String)
    (queryId : String) (queryKey : List ℚ) (topKRoots : Nat) :
    Option (List ℚ) :=
  if !runtimeRoutesHaveNoDuplicateQueryRoot routes then none
  else if !knownQueryIds.contains queryId then none
  else some (runtimeSelectedRouteHistogram parameters records queryKey
    ((runtimeRoutesForQuery routes queryId).take topKRoots))

theorem runtimeRoutedHistogram?_none_of_duplicate_query_root
    (parameters : RuntimeMemoryParameters)
    (records : List RuntimeActionTraceRecord)
    (routes : List RuntimeActionMemoryRoute)
    (knownQueryIds : List String) (queryId : String)
    (queryKey : List ℚ) (topKRoots : Nat)
    (duplicate : runtimeRoutesHaveNoDuplicateQueryRoot routes = false) :
    runtimeRoutedHistogram? parameters records routes knownQueryIds queryId
      queryKey topKRoots = none := by
  simp [runtimeRoutedHistogram?, duplicate]

theorem runtimeRoutedHistogram?_none_of_unknown_query
    (parameters : RuntimeMemoryParameters)
    (records : List RuntimeActionTraceRecord)
    (routes : List RuntimeActionMemoryRoute)
    (knownQueryIds : List String) (queryId : String)
    (queryKey : List ℚ) (topKRoots : Nat)
    (unique : runtimeRoutesHaveNoDuplicateQueryRoot routes = true)
    (unknown : queryId ∉ knownQueryIds) :
    runtimeRoutedHistogram? parameters records routes knownQueryIds queryId
      queryKey topKRoots = none := by
  simp [runtimeRoutedHistogram?, unique, unknown]

theorem runtimeRoutedHistogram?_known_empty_query_zero
    (parameters : RuntimeMemoryParameters)
    (records : List RuntimeActionTraceRecord)
    (routes : List RuntimeActionMemoryRoute)
    (knownQueryIds : List String) (queryId : String)
    (queryKey : List ℚ) (topKRoots : Nat)
    (unique : runtimeRoutesHaveNoDuplicateQueryRoot routes = true)
    (known : queryId ∈ knownQueryIds)
    (empty : runtimeRoutesForQuery routes queryId = []) :
    runtimeRoutedHistogram? parameters records routes knownQueryIds queryId
      queryKey topKRoots = some (List.replicate parameters.numActions 0) := by
  simp [runtimeRoutedHistogram?, unique, known, empty,
    runtimeSelectedRouteHistogram]

def runtimeMaskHistogram
    (legalMask : List Bool) (histogram : List ℚ) : List ℚ :=
  List.zipWith (fun legal mass ↦ if legal then mass else 0)
    legalMask histogram

def runtimeFlatRows
    (parameters : RuntimeMemoryParameters)
    (records : List RuntimeActionTraceRecord) :
    List RuntimeWeightedStateActionRow :=
  records.map fun record ↦
    { key := runtimeRecordKey parameters record
      action := record.nextAction
      weight := runtimeReciprocalRootWeight records record }

def runtimeFlatRowBeforeOrEqual
    (queryKey : List ℚ)
    (first second : RuntimeWeightedStateActionRow) : Bool :=
  decide (runtimeSquaredDistance queryKey first.key ≤
    runtimeSquaredDistance queryKey second.key)

def runtimeWeightedRowsHistogram
    (numActions : Nat) (rows : List RuntimeWeightedStateActionRow) : List ℚ :=
  (List.range numActions).map fun action ↦
    (rows.map fun row ↦ if row.action = action then row.weight else 0).sum

def runtimeFlatTopKRowsHistogram
    (numActions : Nat) (queryKey : List ℚ)
    (rows : List RuntimeWeightedStateActionRow)
    (topKRecords : Nat) : List ℚ :=
  runtimeWeightedRowsHistogram numActions
    ((List.insertionSort
      (fun first second ↦
        runtimeFlatRowBeforeOrEqual queryKey first second = true)
      rows).take topKRecords)

/-- Independent reconstruction of the historical flat record-level top-k
projection, retained to state its two failure modes exactly. -/
def runtimeFlatTopKHistogram
    (parameters : RuntimeMemoryParameters)
    (records : List RuntimeActionTraceRecord)
    (queryKey : List ℚ) (topKRecords : Nat) : List ℚ :=
  runtimeFlatTopKRowsHistogram parameters.numActions queryKey
    (runtimeFlatRows parameters records) topKRecords

def exactRatioValues (ratios : List ExactNonnegativeRatio) : List ℚ :=
  ratios.map ExactNonnegativeRatio.value

def allRatiosValid (ratios : List ExactNonnegativeRatio) : Prop :=
  ∀ ratio ∈ ratios, ratio.valid

def allRatioRowsValid (rows : List (List ExactNonnegativeRatio)) : Prop :=
  ∀ row ∈ rows, allRatiosValid row

def expectedTransformerCausalMask (size : Nat) : List (List Bool) :=
  (List.range size).map fun row ↦
    (List.range size).map fun column ↦ decide (row < column)

def preservesIllegalCoordinates :
    List Bool → List Nat → List Nat → Bool
  | [], [], [] => true
  | legal :: legalRest, base :: baseRest, output :: outputRest =>
      (legal || base == output) &&
        preservesIllegalCoordinates legalRest baseRest outputRest
  | _, _, _ => false

def changesSomeLegalCoordinate :
    List Bool → List Nat → List Nat → Bool
  | legal :: legalRest, base :: baseRest, output :: outputRest =>
      (legal && base != output) ||
        changesSomeLegalCoordinate legalRest baseRest outputRest
  | _, _, _ => false

def changesSomeIllegalCoordinate :
    List Bool → List Nat → List Nat → Bool
  | legal :: legalRest, base :: baseRest, output :: outputRest =>
      (!legal && base != output) ||
        changesSomeIllegalCoordinate legalRest baseRest outputRest
  | _, _, _ => false

/-- The source-hash layout is fixed independently of the supplied digests. -/
def sourceLayout (bindings : List RuntimeSourceBinding) :
    List (String × String) :=
  bindings.map fun binding ↦ (binding.role, binding.path)

/-- Meaningful, decidable conformance conditions checked against a runtime
payload.  The conditions reconstruct values from records rather than accepting
runtime-produced expectations as their own specification. -/
def ActionMemoryRuntimeFixture.Valid
    (fixture : ActionMemoryRuntimeFixture) : Prop :=
  fixture.schema = actionMemoryConformanceSchema ∧
  sourceLayout fixture.sourceFiles = actionMemorySourceLayout ∧
  fixture.sourceFiles.all (fun source ↦
    source.sha256.length = 64) = true ∧
  fixture.actionTraceRecordFields = actionTraceRecordFieldNames ∧
  fixture.actionMemoryRouteFields = actionMemoryRouteFieldNames ∧
  fixture.memoryStateFields = constructionStateFieldNames ∧
  fixture.transformerStateFields = constructionStateFieldNames ∧
  0 < fixture.parameters.numActions ∧
  0 < fixture.parameters.maxDepth ∧
  0 < fixture.parameters.maxActions ∧
  0 < fixture.parameters.topKRoots ∧
  fixture.parameters.topK = fixture.records.length ∧
  fixture.records.all (fun record ↦
    record.nextAction < fixture.parameters.numActions &&
      record.receiptSha256.length = 64 &&
      !record.causalRoot.isEmpty) = true ∧
  fixture.knownQueryIds.Nodup ∧
  fixture.routes.all (fun route ↦
    !route.queryId.isEmpty && !route.causalRoot.isEmpty &&
      decide (0 < route.weight.denominator) &&
      decide (0 < route.weight.value) &&
      fixture.knownQueryIds.contains route.queryId &&
      fixture.records.any (fun record ↦
        record.causalRoot == route.causalRoot)) = true ∧
  runtimeRoutesHaveNoDuplicateQueryRoot fixture.routes = true ∧
  allRatiosValid fixture.bank.weights ∧
  allRatioRowsValid fixture.bank.keys ∧
  allRatiosValid fixture.bank.queryHistogram ∧
  exactRatioValues fixture.bank.weights =
    runtimeExpectedWeights fixture.records ∧
  fixture.bank.keys.map exactRatioValues =
    fixture.records.map (runtimeRecordKey fixture.parameters) ∧
  exactRatioValues fixture.bank.queryHistogram =
    runtimeAllRecordHistogram fixture.parameters.numActions fixture.records ∧
  fixture.routing.queryKey.all (fun ratio ↦
    decide (0 < ratio.denominator)) = true ∧
  allRatiosValid fixture.routing.topOneHistogram ∧
  allRatiosValid fixture.routing.topKHistogram ∧
  allRatiosValid fixture.routing.knownEmptyHistogram ∧
  allRatiosValid fixture.routing.maskedTopKHistogram ∧
  fixture.records.head?.map (runtimeRecordKey fixture.parameters) =
    some (exactRatioValues fixture.routing.queryKey) ∧
  runtimeRoutedHistogram? fixture.parameters fixture.records fixture.routes
      fixture.knownQueryIds fixture.routing.queryId
      (exactRatioValues fixture.routing.queryKey) 1 =
    some (exactRatioValues fixture.routing.topOneHistogram) ∧
  runtimeRoutedHistogram? fixture.parameters fixture.records fixture.routes
      fixture.knownQueryIds fixture.routing.queryId
      (exactRatioValues fixture.routing.queryKey)
      fixture.parameters.topKRoots =
    some (exactRatioValues fixture.routing.topKHistogram) ∧
  runtimeRoutesForQuery fixture.routes fixture.routing.knownEmptyQueryId = [] ∧
  runtimeRoutedHistogram? fixture.parameters fixture.records fixture.routes
      fixture.knownQueryIds fixture.routing.knownEmptyQueryId
      (exactRatioValues fixture.routing.queryKey)
      fixture.parameters.topKRoots =
    some (exactRatioValues fixture.routing.knownEmptyHistogram) ∧
  fixture.routing.legalMask = fixture.bias.legalMask ∧
  runtimeMaskHistogram fixture.routing.legalMask
      (exactRatioValues fixture.routing.topKHistogram) =
    exactRatioValues fixture.routing.maskedTopKHistogram ∧
  runtimeRoutedHistogram? fixture.parameters fixture.records fixture.routes
      fixture.knownQueryIds fixture.routing.unknownQueryId
      (exactRatioValues fixture.routing.queryKey)
      fixture.parameters.topKRoots = none ∧
  fixture.routing.unknownQueryRejected = true ∧
  runtimeRoutesHaveNoDuplicateQueryRoot
      fixture.routing.duplicateRoutes = false ∧
  fixture.routing.duplicateQueryRootRejected = true ∧
  fixture.bias.baseLogitsFloat32Words.length =
    fixture.parameters.numActions ∧
  fixture.bias.legalMask.length = fixture.parameters.numActions ∧
  fixture.bias.disabledLogitsFloat32Words =
    fixture.bias.baseLogitsFloat32Words ∧
  fixture.bias.gateZeroLogitsFloat32Words =
    fixture.bias.baseLogitsFloat32Words ∧
  preservesIllegalCoordinates fixture.bias.legalMask
    fixture.bias.baseLogitsFloat32Words
    fixture.bias.activeMaskedLogitsFloat32Words = true ∧
  changesSomeLegalCoordinate fixture.bias.legalMask
    fixture.bias.baseLogitsFloat32Words
    fixture.bias.activeMaskedLogitsFloat32Words = true ∧
  changesSomeIllegalCoordinate fixture.bias.legalMask
    fixture.bias.baseLogitsFloat32Words
    fixture.bias.activeUnmaskedLogitsFloat32Words = true ∧
  fixture.transformerCausalMask = expectedTransformerCausalMask 4

def ActionMemoryRuntimeFixture.check
    (fixture : ActionMemoryRuntimeFixture) : Bool :=
  (fixture.schema == actionMemoryConformanceSchema) &&
  (sourceLayout fixture.sourceFiles == actionMemorySourceLayout) &&
  fixture.sourceFiles.all (fun source ↦ source.sha256.length == 64) &&
  (fixture.actionTraceRecordFields == actionTraceRecordFieldNames) &&
  (fixture.actionMemoryRouteFields == actionMemoryRouteFieldNames) &&
  (fixture.memoryStateFields == constructionStateFieldNames) &&
  (fixture.transformerStateFields == constructionStateFieldNames) &&
  decide (0 < fixture.parameters.numActions) &&
  decide (0 < fixture.parameters.maxDepth) &&
  decide (0 < fixture.parameters.maxActions) &&
  decide (0 < fixture.parameters.topKRoots) &&
  (fixture.parameters.topK == fixture.records.length) &&
  fixture.records.all (fun record ↦
    decide (record.nextAction < fixture.parameters.numActions) &&
      (record.receiptSha256.length == 64) &&
      !record.causalRoot.isEmpty) &&
  decide fixture.knownQueryIds.Nodup &&
  fixture.routes.all (fun route ↦
    !route.queryId.isEmpty && !route.causalRoot.isEmpty &&
      decide (0 < route.weight.denominator) &&
      decide (0 < route.weight.value) &&
      fixture.knownQueryIds.contains route.queryId &&
      fixture.records.any (fun record ↦
        record.causalRoot == route.causalRoot)) &&
  runtimeRoutesHaveNoDuplicateQueryRoot fixture.routes &&
  fixture.bank.weights.all (fun ratio ↦ decide (0 < ratio.denominator)) &&
  fixture.bank.keys.all (fun row ↦
    row.all fun ratio ↦ decide (0 < ratio.denominator)) &&
  fixture.bank.queryHistogram.all (fun ratio ↦
    decide (0 < ratio.denominator)) &&
  (exactRatioValues fixture.bank.weights ==
    runtimeExpectedWeights fixture.records) &&
  (fixture.bank.keys.map exactRatioValues ==
    fixture.records.map (runtimeRecordKey fixture.parameters)) &&
  (exactRatioValues fixture.bank.queryHistogram ==
    runtimeAllRecordHistogram fixture.parameters.numActions fixture.records) &&
  fixture.routing.queryKey.all (fun ratio ↦
    decide (0 < ratio.denominator)) &&
  fixture.routing.topOneHistogram.all (fun ratio ↦
    decide (0 < ratio.denominator)) &&
  fixture.routing.topKHistogram.all (fun ratio ↦
    decide (0 < ratio.denominator)) &&
  fixture.routing.knownEmptyHistogram.all (fun ratio ↦
    decide (0 < ratio.denominator)) &&
  fixture.routing.maskedTopKHistogram.all (fun ratio ↦
    decide (0 < ratio.denominator)) &&
  (fixture.records.head?.map (runtimeRecordKey fixture.parameters) ==
    some (exactRatioValues fixture.routing.queryKey)) &&
  (runtimeRoutedHistogram? fixture.parameters fixture.records fixture.routes
      fixture.knownQueryIds fixture.routing.queryId
      (exactRatioValues fixture.routing.queryKey) 1 ==
    some (exactRatioValues fixture.routing.topOneHistogram)) &&
  (runtimeRoutedHistogram? fixture.parameters fixture.records fixture.routes
      fixture.knownQueryIds fixture.routing.queryId
      (exactRatioValues fixture.routing.queryKey)
      fixture.parameters.topKRoots ==
    some (exactRatioValues fixture.routing.topKHistogram)) &&
  (runtimeRoutesForQuery fixture.routes
      fixture.routing.knownEmptyQueryId == []) &&
  (runtimeRoutedHistogram? fixture.parameters fixture.records fixture.routes
      fixture.knownQueryIds fixture.routing.knownEmptyQueryId
      (exactRatioValues fixture.routing.queryKey)
      fixture.parameters.topKRoots ==
    some (exactRatioValues fixture.routing.knownEmptyHistogram)) &&
  (fixture.routing.legalMask == fixture.bias.legalMask) &&
  (runtimeMaskHistogram fixture.routing.legalMask
      (exactRatioValues fixture.routing.topKHistogram) ==
    exactRatioValues fixture.routing.maskedTopKHistogram) &&
  (runtimeRoutedHistogram? fixture.parameters fixture.records fixture.routes
      fixture.knownQueryIds fixture.routing.unknownQueryId
      (exactRatioValues fixture.routing.queryKey)
      fixture.parameters.topKRoots == none) &&
  fixture.routing.unknownQueryRejected &&
  !runtimeRoutesHaveNoDuplicateQueryRoot fixture.routing.duplicateRoutes &&
  fixture.routing.duplicateQueryRootRejected &&
  (fixture.bias.baseLogitsFloat32Words.length ==
    fixture.parameters.numActions) &&
  (fixture.bias.legalMask.length == fixture.parameters.numActions) &&
  (fixture.bias.disabledLogitsFloat32Words ==
    fixture.bias.baseLogitsFloat32Words) &&
  (fixture.bias.gateZeroLogitsFloat32Words ==
    fixture.bias.baseLogitsFloat32Words) &&
  preservesIllegalCoordinates fixture.bias.legalMask
    fixture.bias.baseLogitsFloat32Words
    fixture.bias.activeMaskedLogitsFloat32Words &&
  changesSomeLegalCoordinate fixture.bias.legalMask
    fixture.bias.baseLogitsFloat32Words
    fixture.bias.activeMaskedLogitsFloat32Words &&
  changesSomeIllegalCoordinate fixture.bias.legalMask
    fixture.bias.baseLogitsFloat32Words
    fixture.bias.activeUnmaskedLogitsFloat32Words &&
  (fixture.transformerCausalMask == expectedTransformerCausalMask 4)

theorem ActionMemoryRuntimeFixture.check_eq_true_iff
    (fixture : ActionMemoryRuntimeFixture) :
    fixture.check = true ↔ fixture.Valid := by
  simp [ActionMemoryRuntimeFixture.check, ActionMemoryRuntimeFixture.Valid,
    sourceLayout, allRatiosValid, allRatioRowsValid,
    ExactNonnegativeRatio.valid]
  tauto

/-! ## General gate and legality laws -/

def maskedEvidence {Actions : Type*}
    (legal : Actions → Bool) (evidence : Actions → ℚ) (action : Actions) : ℚ :=
  if legal action then evidence action else 0

def memoryBiasedLogit {Actions : Type*}
    (base : Actions → ℚ) (gate : ℚ)
    (legal : Actions → Bool) (evidence : Actions → ℚ)
    (action : Actions) : ℚ :=
  base action + gate * maskedEvidence legal evidence action

/-- A zero gate is exact cold-path identity, regardless of retrieved evidence. -/
@[simp] theorem memoryBiasedLogit_zero_gate
    {Actions : Type*} (base evidence : Actions → ℚ)
    (legal : Actions → Bool) (action : Actions) :
    memoryBiasedLogit base 0 legal evidence action = base action := by
  simp [memoryBiasedLogit]

/-- Masking makes every illegal coordinate observationally equal to its base
logit, even under an active gate and nonzero evidence. -/
theorem memoryBiasedLogit_illegal_eq_base
    {Actions : Type*} (base evidence : Actions → ℚ) (gate : ℚ)
    (legal : Actions → Bool) (action : Actions)
    (illegal : legal action = false) :
    memoryBiasedLogit base gate legal evidence action = base action := by
  simp [memoryBiasedLogit, maskedEvidence, illegal]

/-- Negative fixture: omitting the legality mask lets retrieved evidence alter
an action that the construction state declares illegal. -/
theorem unmasked_bias_can_change_illegal_action :
    let base : Bool → ℚ := fun _ ↦ 0
    let evidence : Bool → ℚ := fun action ↦ if action then 3 / 2 else 0
    let legal : Bool → Bool := fun _ ↦ false
    memoryBiasedLogit base 1 legal evidence true = 0 ∧
      base true + 1 * evidence true = 3 / 2 := by
  norm_num [memoryBiasedLogit, maskedEvidence]

/-! ## Small exact fixtures for the reconstructed bank -/

def runtimeRecordAlphaOne : RuntimeActionTraceRecord where
  previousAction := 0
  roleId := 0
  parentId := 0
  argumentId := 0
  depth := 1
  openHoles := 2
  position := 0
  nextAction := 1
  causalRoot := "root-alpha"
  targetAnum := 45
  receiptSha256 := String.replicate 64 'a'

def runtimeRecordAlphaTwo : RuntimeActionTraceRecord where
  previousAction := 0
  roleId := 0
  parentId := 0
  argumentId := 0
  depth := 1
  openHoles := 2
  position := 0
  nextAction := 2
  causalRoot := "root-alpha"
  targetAnum := 45
  receiptSha256 := String.replicate 64 'a'

def runtimeRecordBeta : RuntimeActionTraceRecord where
  previousAction := 2
  roleId := 2
  parentId := 1
  argumentId := 2
  depth := 3
  openHoles := 2
  position := 2
  nextAction := 3
  causalRoot := "root-beta"
  targetAnum := 105
  receiptSha256 := String.replicate 64 'b'

def runtimeRecordFixture : List RuntimeActionTraceRecord :=
  [runtimeRecordAlphaOne, runtimeRecordAlphaTwo, runtimeRecordBeta]

theorem runtimeRecordFixture_weights :
    runtimeExpectedWeights runtimeRecordFixture = [1 / 2, 1 / 2, 1] := by
  norm_num [runtimeExpectedWeights, runtimeReciprocalRootWeight,
    runtimeRootCount, runtimeRecordFixture, runtimeRecordAlphaOne,
    runtimeRecordAlphaTwo, runtimeRecordBeta]
  simp

theorem runtimeRecordFixture_histogram :
    runtimeAllRecordHistogram 4 runtimeRecordFixture = [0, 1 / 2, 1 / 2, 1] := by
  rw [runtimeAllRecordHistogram, runtimeRecordFixture_weights]
  have rangeFour : List.range 4 = [0, 1, 2, 3] := by decide
  rw [rangeFour]
  norm_num [runtimeRecordFixture, runtimeRecordAlphaOne,
    runtimeRecordAlphaTwo, runtimeRecordBeta]

/-! ## Exact deployed-route fixtures -/

def runtimeRouteFixtureParameters : RuntimeMemoryParameters where
  numActions := 4
  maxDepth := 8
  maxActions := 8
  topK := 3
  topKRoots := 2

def runtimeUnitRatio : ExactNonnegativeRatio where
  numerator := 1
  denominator := 1

def runtimeThreeQuarterRatio : ExactNonnegativeRatio where
  numerator := 3
  denominator := 4

def runtimeRouteAlpha : RuntimeActionMemoryRoute where
  queryId := "fixture"
  causalRoot := "root-alpha"
  weight := runtimeUnitRatio

def runtimeRouteBeta : RuntimeActionMemoryRoute where
  queryId := "fixture"
  causalRoot := "root-beta"
  weight := runtimeThreeQuarterRatio

/-- Deliberately supplied in increasing rather than deployed priority order. -/
def runtimeRouteFixture : List RuntimeActionMemoryRoute :=
  [runtimeRouteBeta, runtimeRouteAlpha]

def runtimeRouteQueryKey : List ℚ :=
  runtimeRecordKey runtimeRouteFixtureParameters runtimeRecordAlphaOne

theorem runtimeRouteFixture_topK_orders_roots_before_states :
    (runtimeRoutesForQuery runtimeRouteFixture "fixture").take 1 =
      [runtimeRouteAlpha] ∧
    (runtimeRoutesForQuery runtimeRouteFixture "fixture").take 2 =
      [runtimeRouteAlpha, runtimeRouteBeta] := by
  norm_num [runtimeRoutesForQuery, runtimeRouteBeforeOrEqual,
    runtimeRouteWeight, ExactNonnegativeRatio.value, runtimeRouteFixture,
    runtimeRouteAlpha, runtimeRouteBeta, runtimeUnitRatio,
    runtimeThreeQuarterRatio]

def runtimeBalancedTieRows : List RuntimeStateActionRow :=
  [{ key := [0], action := 1 }, { key := [0], action := 2 }]

/-- Two equally near, distinct actions in one selected root split that root's
unit route mass exactly rather than each receiving a full unit. -/
theorem runtimeRoot_balances_nearest_tie_mass :
    runtimeNearestRowsHistogram 4 [0] runtimeBalancedTieRows 1 =
      [0, 1 / 2, 1 / 2, 0] := by
  norm_num [runtimeNearestRowsHistogram, runtimeNearestRows,
    runtimeMinimum?, runtimeSquaredDistance, runtimeBalancedTieRows,
    List.range_succ]

theorem runtimeKnownEmptyQuery_zero_and_unknown_rejected :
    runtimeRoutedHistogram? runtimeRouteFixtureParameters runtimeRecordFixture
        runtimeRouteFixture ["fixture", "known-empty"] "known-empty"
        runtimeRouteQueryKey 2 = some [0, 0, 0, 0] ∧
    runtimeRoutedHistogram? runtimeRouteFixtureParameters runtimeRecordFixture
        runtimeRouteFixture ["fixture", "known-empty"] "unknown"
        runtimeRouteQueryKey 2 = none := by
  decide

theorem runtimeDuplicateQueryRoot_rejected :
    runtimeRoutesHaveNoDuplicateQueryRoot
      [runtimeRouteBeta, runtimeRouteAlpha, runtimeRouteAlpha] = false := by
  decide

theorem runtimeCurrentLegalityMask_removes_illegal_route_mass :
    runtimeMaskHistogram [true, true, false, true]
      [0, 1 / 2, 1 / 2, 3 / 4] = [0, 1 / 2, 0, 3 / 4] := by
  norm_num [runtimeMaskHistogram]

/-! ## Why routing is root-first and target-aware -/

def runtimeTargetAgnosticRows : List RuntimeWeightedStateActionRow :=
  [ { key := [0], action := 1, weight := 1 }
  , { key := [0], action := 2, weight := 1 } ]

def runtimeTargetARows : List RuntimeStateActionRow :=
  [{ key := [0], action := 1 }]

def runtimeTargetBRows : List RuntimeStateActionRow :=
  [{ key := [0], action := 2 }]

/-- A target-agnostic flat lookup mixes two unrelated roots at the same state;
query-first routing selects the root authorized for each target. -/
theorem targetAgnostic_lookup_mixes_unrelated_roots :
    runtimeFlatTopKRowsHistogram 3 [0] runtimeTargetAgnosticRows 2 =
      [0, 1, 1] ∧
    runtimeNearestRowsHistogram 3 [0] runtimeTargetARows 1 = [0, 1, 0] ∧
    runtimeNearestRowsHistogram 3 [0] runtimeTargetBRows 1 = [0, 0, 1] := by
  norm_num [runtimeFlatTopKRowsHistogram, runtimeFlatRowBeforeOrEqual,
    runtimeWeightedRowsHistogram, runtimeTargetAgnosticRows,
    runtimeNearestRowsHistogram, runtimeNearestRows, runtimeMinimum?,
    runtimeSquaredDistance, runtimeTargetARows, runtimeTargetBRows,
    List.range_succ]

def runtimeCrowdedFlatRows : List RuntimeWeightedStateActionRow :=
  [ { key := [0], action := 1, weight := 1 / 3 }
  , { key := [1], action := 1, weight := 1 / 3 }
  , { key := [2], action := 1, weight := 1 / 3 }
  , { key := [3], action := 2, weight := 1 } ]

def runtimeCrowdedRootRows : List RuntimeStateActionRow :=
  [ { key := [0], action := 1 }
  , { key := [1], action := 1 }
  , { key := [2], action := 1 } ]

def runtimeOtherRootRows : List RuntimeStateActionRow :=
  [{ key := [3], action := 2 }]

/-- Record-level top-k spends both slots on one longer root.  Root-first top-k
gives each selected root one contribution, so the second root remains visible. -/
theorem recordLevel_topK_is_crowded_by_one_root :
    runtimeFlatTopKRowsHistogram 3 [0] runtimeCrowdedFlatRows 2 =
      [0, 2 / 3, 0] ∧
    runtimeAddHistograms
        (runtimeNearestRowsHistogram 3 [0] runtimeCrowdedRootRows 1)
        (runtimeNearestRowsHistogram 3 [0] runtimeOtherRootRows 1) =
      [0, 1, 1] := by
  norm_num [runtimeFlatTopKRowsHistogram, runtimeFlatRowBeforeOrEqual,
    runtimeWeightedRowsHistogram, runtimeCrowdedFlatRows,
    runtimeAddHistograms, runtimeNearestRowsHistogram, runtimeNearestRows,
    runtimeMinimum?, runtimeSquaredDistance, runtimeCrowdedRootRows,
    runtimeOtherRootRows, List.range_succ]

/-! ## JSON parser and source-hash boundary -/

private def parseStringField (json : Json) (field : String) :
    Except String String :=
  json.getObjVal? field >>= Json.getStr?

private def parseNatField (json : Json) (field : String) :
    Except String Nat :=
  json.getObjVal? field >>= Json.getNat?

private def parseArrayField (json : Json) (field : String) :
    Except String (List Json) := do
  let values ← json.getObjVal? field >>= Json.getArr?
  pure values.toList

private def parseStringArray (json : Json) (field : String) :
    Except String (List String) := do
  (← parseArrayField json field).mapM Json.getStr?

private def parseNatArray (json : Json) (field : String) :
    Except String (List Nat) := do
  (← parseArrayField json field).mapM Json.getNat?

private def parseBoolArray (json : Json) (field : String) :
    Except String (List Bool) := do
  (← parseArrayField json field).mapM Json.getBool?

private def parseExactRatio (json : Json) :
    Except String ExactNonnegativeRatio := do
  pure
    { numerator := ← parseNatField json "numerator"
      denominator := ← parseNatField json "denominator" }

private def parseRatioArray (json : Json) (field : String) :
    Except String (List ExactNonnegativeRatio) := do
  (← parseArrayField json field).mapM parseExactRatio

private def parseRatioRows (json : Json) (field : String) :
    Except String (List (List ExactNonnegativeRatio)) := do
  (← parseArrayField json field).mapM fun row ↦ do
    let values ← row.getArr?
    values.toList.mapM parseExactRatio

private def parseBoolRows (json : Json) (field : String) :
    Except String (List (List Bool)) := do
  (← parseArrayField json field).mapM fun row ↦ do
    let values ← row.getArr?
    values.toList.mapM Json.getBool?

private def parseSourceBinding (json : Json) :
    Except String RuntimeSourceBinding := do
  pure
    { role := ← parseStringField json "role"
      path := ← parseStringField json "path"
      sha256 := ← parseStringField json "sha256" }

private def parseRuntimeRecord (json : Json) :
    Except String RuntimeActionTraceRecord := do
  pure
    { previousAction := ← parseNatField json "previous_action"
      roleId := ← parseNatField json "role_id"
      parentId := ← parseNatField json "parent_id"
      argumentId := ← parseNatField json "argument_id"
      depth := ← parseNatField json "depth"
      openHoles := ← parseNatField json "open_holes"
      position := ← parseNatField json "position"
      nextAction := ← parseNatField json "next_action"
      causalRoot := ← parseStringField json "causal_root"
      targetAnum := ← parseNatField json "target_anum"
      receiptSha256 := ← parseStringField json "receipt_sha256" }

private def parseRuntimeRoute (json : Json) :
    Except String RuntimeActionMemoryRoute := do
  pure
    { queryId := ← parseStringField json "query_id"
      causalRoot := ← parseStringField json "causal_root"
      weight := ← json.getObjVal? "weight" >>= parseExactRatio }

private def parseParameters (json : Json) :
    Except String RuntimeMemoryParameters := do
  pure
    { numActions := ← parseNatField json "num_actions"
      maxDepth := ← parseNatField json "max_depth"
      maxActions := ← parseNatField json "max_actions"
      topK := ← parseNatField json "top_k"
      topKRoots := ← parseNatField json "top_k_roots" }

private def parseBank (json : Json) : Except String RuntimeBankObservation := do
  pure
    { weights := ← parseRatioArray json "weights"
      keys := ← parseRatioRows json "keys"
      queryHistogram := ← parseRatioArray json "query_histogram" }

private def parseBias (json : Json) : Except String RuntimeBiasObservation := do
  pure
    { baseLogitsFloat32Words :=
        ← parseNatArray json "base_logits_float32_words"
      disabledLogitsFloat32Words :=
        ← parseNatArray json "disabled_logits_float32_words"
      gateZeroLogitsFloat32Words :=
        ← parseNatArray json "gate_zero_logits_float32_words"
      legalMask := ← parseBoolArray json "legal_mask"
      activeMaskedLogitsFloat32Words :=
        ← parseNatArray json "active_masked_logits_float32_words"
      activeUnmaskedLogitsFloat32Words :=
        ← parseNatArray json "active_unmasked_logits_float32_words" }

private def parseRouting (json : Json) :
    Except String RuntimeRoutingObservation := do
  let duplicateRouteJson ← parseArrayField json "duplicate_routes"
  pure
    { queryId := ← parseStringField json "query_id"
      queryKey := ← parseRatioArray json "query_key"
      topOneHistogram := ← parseRatioArray json "top_one_histogram"
      topKHistogram := ← parseRatioArray json "top_k_histogram"
      knownEmptyQueryId := ← parseStringField json "known_empty_query_id"
      knownEmptyHistogram :=
        ← parseRatioArray json "known_empty_histogram"
      legalMask := ← parseBoolArray json "legal_mask"
      maskedTopKHistogram :=
        ← parseRatioArray json "masked_top_k_histogram"
      unknownQueryId := ← parseStringField json "unknown_query_id"
      unknownQueryRejected :=
        ← json.getObjVal? "unknown_query_rejected" >>= Json.getBool?
      duplicateRoutes := ← duplicateRouteJson.mapM parseRuntimeRoute
      duplicateQueryRootRejected :=
        ← json.getObjVal? "duplicate_query_root_rejected" >>= Json.getBool? }

/-- Parse the independently emitted runtime fixture. -/
def parseActionMemoryRuntimeFixture (text : String) :
    Except String ActionMemoryRuntimeFixture := do
  let json ← Json.parse text
  let sourceJson ← parseArrayField json "source_files"
  let recordJson ← parseArrayField json "records"
  let routeJson ← parseArrayField json "routes"
  let parametersJson ← json.getObjVal? "parameters"
  let bankJson ← json.getObjVal? "bank"
  let routingJson ← json.getObjVal? "routing"
  let biasJson ← json.getObjVal? "bias"
  pure
    { schema := ← parseStringField json "schema"
      sourceFiles := ← sourceJson.mapM parseSourceBinding
      actionTraceRecordFields :=
        ← parseStringArray json "action_trace_record_fields"
      actionMemoryRouteFields :=
        ← parseStringArray json "action_memory_route_fields"
      memoryStateFields := ← parseStringArray json "memory_state_fields"
      transformerStateFields :=
        ← parseStringArray json "transformer_state_fields"
      parameters := ← parseParameters parametersJson
      records := ← recordJson.mapM parseRuntimeRecord
      routes := ← routeJson.mapM parseRuntimeRoute
      knownQueryIds := ← parseStringArray json "known_query_ids"
      bank := ← parseBank bankJson
      routing := ← parseRouting routingJson
      bias := ← parseBias biasJson
      transformerCausalMask :=
        ← parseBoolRows json "transformer_causal_mask" }

/-- Hash every declared source from the supplied repository root.  Because
`Valid` fixes the role/path layout, a payload cannot redirect this check to a
different implementation. -/
def runtimeSourceDigestMatches
    (binding : RuntimeSourceBinding) (source : String) : Bool :=
  sha256Hex source == binding.sha256

/-- The source checker rejects any content whose independently recomputed
digest differs from the pinned digest. -/
theorem changed_runtime_source_is_rejected
    (binding : RuntimeSourceBinding) (source : String)
    (digestMismatch : sha256Hex source ≠ binding.sha256) :
    runtimeSourceDigestMatches binding source = false := by
  simp [runtimeSourceDigestMatches, digestMismatch]

def checkActionMemoryRuntimeSources
    (repositoryRoot : System.FilePath)
    (fixture : ActionMemoryRuntimeFixture) : IO Bool := do
  for binding in fixture.sourceFiles do
    let path := repositoryRoot / binding.path
    if !(← path.pathExists) then
      return false
    let content ← IO.FS.readFile path
    if !runtimeSourceDigestMatches binding content then
      return false
  return true

#print axioms ActionMemoryRuntimeFixture.check_eq_true_iff
#print axioms runtimeRoutedHistogram?_none_of_duplicate_query_root
#print axioms runtimeRoutedHistogram?_none_of_unknown_query
#print axioms runtimeRoutedHistogram?_known_empty_query_zero
#print axioms memoryBiasedLogit_zero_gate
#print axioms memoryBiasedLogit_illegal_eq_base
#print axioms unmasked_bias_can_change_illegal_action
#print axioms runtimeRecordFixture_weights
#print axioms runtimeRecordFixture_histogram
#print axioms runtimeRouteFixture_topK_orders_roots_before_states
#print axioms runtimeRoot_balances_nearest_tie_mass
#print axioms runtimeKnownEmptyQuery_zero_and_unknown_rejected
#print axioms runtimeDuplicateQueryRoot_rejected
#print axioms runtimeCurrentLegalityMask_removes_illegal_route_mass
#print axioms targetAgnostic_lookup_mixes_unrelated_roots
#print axioms recordLevel_topK_is_crowded_by_one_root
#print axioms changed_runtime_source_is_rejected

end Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery
