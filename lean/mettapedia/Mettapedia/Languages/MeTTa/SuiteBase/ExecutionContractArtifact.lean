import Mettapedia.Languages.MeTTa.SuiteBase.ExecutionContractCore

/-!
# MeTTa Execution Contract Artifact

Rendering, linting, and checksum logic for execution-contract artifacts.
-/

namespace Mettapedia.Languages.MeTTa.ExecutionContract

open Mettapedia.Languages.MeTTa.ElaboratedCore
open Mettapedia.Languages.MeTTa.RuntimeKernel
open MeTTailCore.MeTTaIL.EffectSafety
open MeTTailCore.MeTTaIL.LookupPlan

/-- Shared artifact exported for runtime consumers. Schema version 4 widens the
contract vocabulary with explicit control lanes. -/
structure ExecutionContractArtifact where
  schemaVersion : Nat := 4
  dialect : String
  entries : List ExecutionContractEntry
deriving Repr, DecidableEq, BEq

private def sortListByKey {α : Type} (xs : List α) (key : α → String) : List α :=
  (xs.toArray.qsort (fun a b => key a < key b)).toList

private def sortNatList (xs : List Nat) : List Nat :=
  (xs.toArray.qsort (fun a b => a < b)).toList

private def jsonEscape (s : String) : String :=
  s.foldl
    (fun acc c =>
      acc ++
      match c with
      | '"' => "\\\""
      | '\\' => "\\\\"
      | '\n' => "\\n"
      | '\r' => "\\r"
      | '\t' => "\\t"
      | _ => String.singleton c)
    ""

private def jsonStr (s : String) : String :=
  "\"" ++ jsonEscape s ++ "\""

private def jsonBool (b : Bool) : String :=
  if b then "true" else "false"

private def jsonNat (n : Nat) : String :=
  toString n

private def jsonOptStr : Option String → String
  | some s => jsonStr s
  | none => "null"

private def renderExecutionOwner : ExecutionOwner → String
  | .artifactBackend => "artifact_backend"
  | .groundedBuiltin => "grounded_builtin"
  | .externalOracle => "external_oracle"

private def renderBuiltinDemand : BuiltinDemandKind → String
  | .rawArgs => "raw_args"
  | .structuralEqArgs => "structural_eq_args"
  | .boolArgs => "bool_args"
  | .boolThenElseArgs => "bool_then_else_args"
  | .numericArgs => "numeric_args"
  | .floatArgs => "float_args"
  | .tupleArgs => "tuple_args"
  | .elemAndTupleArgs => "elem_and_tuple_args"

private def renderPremiseArgRole : PremiseArgRole → String
  | .pattern => "pattern"
  | .template => "template"
  | .resultVar => "result_var"
  | .plainInput => "plain_input"

private def renderResultBindingPolicy : ResultBindingPolicy → String
  | .mustBeFreshVar => "must_be_fresh_var"
  | .mayReuseBoundVar => "may_reuse_bound_var"

private def renderRelationPremiseLoweringKind : RelationPremiseLoweringKind → String
  | .factMatchEmitPayload => "fact_match_emit_payload"
  | .lookupExists => "lookup_exists"
  | .lookupEnumerate => "lookup_enumerate"

private def renderSpaceEffectPayloadKind : SpaceEffectPayloadKind → String
  | .factPayload => "fact_payload"
  | .sourceRulePayload => "source_rule_payload"

private def renderSpaceEffectSinkKind : SpaceEffectSinkKind → String
  | .insertFact => "insert_fact"
  | .removeFact => "remove_fact"
  | .insertRule => "insert_rule"
  | .removeRule => "remove_rule"

private def renderPayloadPatternShapeKind : PayloadPatternShapeKind → String
  | .anyPattern => "any_pattern"
  | .nonRewritePattern => "non_rewrite_pattern"
  | .rewriteEqRule => "rewrite_eq_rule"

private def renderGroundedBuiltinHostKind : GroundedBuiltinHostKind → String
  | .numericCompare => "numeric_compare"
  | .f64Predicate => "f64_predicate"
  | .tupleMembership => "tuple_membership"
  | .isVariableTerm => "is_variable_term"
  | .reprTerm => "repr_term"
  | .parseTerm => "parse_term"
  | .printlnTerm => "println_term"
  | .metaTypeOfTerm => "meta_type_of_term"
  | .typeOfTerm => "type_of_term"
  | .quoteTerm => "quote_term"
  | .testAssertion => "test_assertion"

private def renderAggregationCollectionKind : AggregationCollectionKind → String
  | .tupleExpr => "tuple_expr"
  | .minAtom => "min_atom"
  | .maxAtom => "max_atom"

private def renderAggregationSourceKind : AggregationSourceKind → String
  | .subevalAllResults => "subeval_all_results"

private def renderControlBuiltinKind : ControlBuiltinKind → String
  | .bindThenBody => "bind_then_body"
  | .sequenceLastResult => "sequence_last_result"

private def renderLaneEligibilityKind : LaneEligibilityKind → String
  | .always => "always"
  | .groundNumericArgs => "ground_numeric_args"
  | .groundBoolArgs => "ground_bool_args"
  | .groundConditionOnly => "ground_condition_only"
  | .groundStructuralEqArgs => "ground_structural_eq_args"

private def renderResidualPolicy : ResidualPolicy → String
  | .failClosed => "fail_closed"
  | .fallbackToRules => "fallback_to_rules"
  | .symbolicFallback => "symbolic_fallback"

private def renderNumericResultShape : NumericResultShape → String
  | .preserveIntegralIfExact => "preserve_integral_if_exact"
  | .alwaysFloat => "always_float"
  | .alwaysInteger => "always_integer"
  | .preserveInputNumericClass => "preserve_input_numeric_class"

private def renderKernelClass : RuntimeKernelClass → String
  | .ruleExec => "rule_exec"
  | .query => "query"
  | .spaceEffect => "space_effect"
  | .oracle => "oracle"
  | .metaPhase => "meta_phase"

private def renderEffectClass : EffectClass → String
  | .pureStructural => "pure_structural"
  | .readOnlyLookup => "read_only_lookup"
  | .nondeterministicReadOnly => "nondeterministic_read_only"
  | .writesState => "writes_state"
  | .oracleIO => "oracle_io"

private def renderMemoShape : MemoShape → String
  | .scalar => "scalar"
  | .outcomeSet => "outcome_set"

private def renderResourceClass : RuntimeResourceClass → String
  | .defaultAtomSpace => "default_atomspace"
  | .namedAtomSpace => "named_atomspace"
  | .mapResource => "map_resource"
  | .queueResource => "queue_resource"
  | .solverResource => "solver_resource"
  | .externalResource => "external_resource"

private def renderBindingMode : BindingMode → String
  | .bound => "bound"
  | .free => "free"

private def renderUsageKind : UsageKind → String
  | .enumerate => "enumerate"
  | .exists => "exists"
  | .negatedExists => "negated_exists"
  | .aggregateInput => "aggregate_input"

private def SignatureArg.sortKey (arg : SignatureArg) : String :=
  s!"{arg.position}:{match arg.mode with | .bound => "b" | .free => "f"}"

private def normalizeSignatureArgs (xs : List SignatureArg) : List SignatureArg :=
  sortListByKey xs SignatureArg.sortKey

private def defaultScopeSignature (sig : DemandSignature) : String :=
  let args := normalizeSignatureArgs sig.args
  if args.isEmpty then
    "all_free"
  else
    let parts := args.map fun a =>
      let mode :=
        match a.mode with
        | .bound => "b"
        | .free => "f"
      s!"{mode}{a.position}"
    String.intercalate "+" parts

private def normalizeDemandSignature (sig : DemandSignature) : DemandSignature :=
  let logicalId :=
    if sig.logicalRelationId.isEmpty then sig.relation else sig.logicalRelationId
  let scopeSig :=
    if sig.scopeSignature.isEmpty then defaultScopeSignature sig else sig.scopeSignature
  { sig with
    logicalRelationId := logicalId
    scopeSignature := scopeSig
    args := normalizeSignatureArgs sig.args
  }

private def normalizeFamily (f : LookupFamilyPlan) : LookupFamilyPlan :=
  let logicalId :=
    if f.logicalRelationId.isEmpty then f.family else f.logicalRelationId
  let demand := sortListByKey (f.demand.map normalizeDemandSignature)
    (fun d => s!"{d.logicalRelationId}:{d.scopeSignature}:{d.relation}")
  { f with
    logicalRelationId := logicalId
    keyPositions := sortNatList f.keyPositions
    demand := demand
  }

private def memoShapeSortKey : MemoShape → String
  | .scalar => "scalar"
  | .outcomeSet => "outcome_set"

private def normalizePermission (p : ExecutionPermission) : ExecutionPermission :=
  { p with
    supportedMemoShapes := (sortListByKey p.supportedMemoShapes memoShapeSortKey).eraseDups
    theoremRefs := (sortListByKey p.theoremRefs id).eraseDups
  }

private def normalizeLookupQuery (q : LookupQueryContract) : LookupQueryContract :=
  let p := normalizePermission q.permission
  { q with
    owner := p.owner
    kernelClass := p.kernelClass
    effectClass := p.effectClass
    resourceClass := p.resourceClass
    backendName := p.backendName
    supportedMemoShapes := p.supportedMemoShapes
    sourceRuleCompilable := p.sourceRuleCompilable
    queryCompilable := p.queryCompilable
    spaceEffectCompilable := p.spaceEffectCompilable
    surfaceHead := q.surfaceHead
    theoremRefs := p.theoremRefs
    lookupFamily := normalizeFamily q.lookupFamily
  }

private def normalizeSpaceEffect (e : SpaceEffectContract) : SpaceEffectContract :=
  let p := normalizePermission e.permission
  { e with
    owner := p.owner
    kernelClass := p.kernelClass
    effectClass := p.effectClass
    resourceClass := p.resourceClass
    backendName := p.backendName
    sourceRuleCompilable := p.sourceRuleCompilable
    queryCompilable := p.queryCompilable
    spaceEffectCompilable := p.spaceEffectCompilable
    theoremRefs := p.theoremRefs
  }

private def normalizeRelationPremise (e : RelationPremiseContract) : RelationPremiseContract :=
  let p := normalizePermission e.permission
  { e with
    owner := p.owner
    kernelClass := p.kernelClass
    effectClass := p.effectClass
    resourceClass := p.resourceClass
    backendName := p.backendName
    supportedMemoShapes := p.supportedMemoShapes
    theoremRefs := p.theoremRefs
    lookupFamily := normalizeFamily e.lookupFamily
  }

private def normalizeSpaceEffectPayload (e : SpaceEffectPayloadContract) :
    SpaceEffectPayloadContract :=
  let p := normalizePermission e.permission
  { e with
    owner := p.owner
    kernelClass := p.kernelClass
    effectClass := p.effectClass
    resourceClass := p.resourceClass
    backendName := p.backendName
    sourceRuleCompilable := p.sourceRuleCompilable
    queryCompilable := p.queryCompilable
    spaceEffectCompilable := p.spaceEffectCompilable
    theoremRefs := p.theoremRefs
  }

private def normalizeIntrinsicBuiltin (e : IntrinsicBuiltinContract) : IntrinsicBuiltinContract :=
  let p := normalizePermission e.permission
  { e with
    owner := p.owner
    kernelClass := p.kernelClass
    effectClass := p.effectClass
    resourceClass := p.resourceClass
    backendName := p.backendName
    supportedMemoShapes := p.supportedMemoShapes
    theoremRefs := p.theoremRefs
  }

private def normalizeGroundedBuiltin (e : GroundedBuiltinContract) : GroundedBuiltinContract :=
  let p := normalizePermission e.permission
  { e with
    owner := p.owner
    kernelClass := p.kernelClass
    effectClass := p.effectClass
    resourceClass := p.resourceClass
    backendName := p.backendName
    supportedMemoShapes := p.supportedMemoShapes
    theoremRefs := p.theoremRefs
  }

private def normalizeAggregationBuiltin (e : AggregationBuiltinContract) : AggregationBuiltinContract :=
  let p := normalizePermission e.permission
  { e with
    owner := p.owner
    kernelClass := p.kernelClass
    effectClass := p.effectClass
    resourceClass := p.resourceClass
    backendName := p.backendName
    supportedMemoShapes := p.supportedMemoShapes
    theoremRefs := p.theoremRefs
  }

private def normalizeControlBuiltin (e : ControlBuiltinContract) : ControlBuiltinContract :=
  let p := normalizePermission e.permission
  { e with
    owner := p.owner
    kernelClass := p.kernelClass
    effectClass := p.effectClass
    resourceClass := p.resourceClass
    backendName := p.backendName
    supportedMemoShapes := p.supportedMemoShapes
    theoremRefs := p.theoremRefs
  }

private def normalizeEntry : ExecutionContractEntry → ExecutionContractEntry
  | .lookupQuery entry => .lookupQuery (normalizeLookupQuery entry)
  | .spaceEffect entry => .spaceEffect (normalizeSpaceEffect entry)
  | .relationPremise entry => .relationPremise (normalizeRelationPremise entry)
  | .spaceEffectPayload entry => .spaceEffectPayload (normalizeSpaceEffectPayload entry)
  | .intrinsicBuiltin entry => .intrinsicBuiltin (normalizeIntrinsicBuiltin entry)
  | .groundedBuiltin entry => .groundedBuiltin (normalizeGroundedBuiltin entry)
  | .aggregationBuiltin entry => .aggregationBuiltin (normalizeAggregationBuiltin entry)
  | .controlBuiltin entry => .controlBuiltin (normalizeControlBuiltin entry)

private def normalizeArtifact (a : ExecutionContractArtifact) : ExecutionContractArtifact :=
  { a with
    entries := sortListByKey (a.entries.map normalizeEntry) ExecutionContractEntry.sortKey }

private def renderSignatureArg (arg : SignatureArg) : String :=
  "{"
    ++ "\"position\":" ++ jsonNat arg.position ++ ","
    ++ "\"mode\":" ++ jsonStr (renderBindingMode arg.mode)
  ++ "}"

private def renderDemandSignature (sig : DemandSignature) : String :=
  "{"
    ++ "\"relation\":" ++ jsonStr sig.relation ++ ","
    ++ "\"logical_relation_id\":" ++ jsonStr sig.logicalRelationId ++ ","
    ++ "\"scope_signature\":" ++ jsonStr sig.scopeSignature ++ ","
    ++ "\"arity\":" ++ jsonNat sig.arity ++ ","
    ++ "\"args\":[" ++ String.intercalate "," (sig.args.map renderSignatureArg) ++ "],"
    ++ "\"usage_kind\":" ++ jsonStr (renderUsageKind sig.usageKind) ++ ","
    ++ "\"negated_target\":" ++ jsonOptStr sig.negatedTarget ++ ","
    ++ "\"in_recursive_scc\":" ++ jsonBool sig.inRecursiveScc ++ ","
    ++ "\"hot_path\":" ++ jsonBool sig.hotPath
  ++ "}"

private def renderLookupFamily (f : LookupFamilyPlan) : String :=
  "{"
    ++ "\"family\":" ++ jsonStr f.family ++ ","
    ++ "\"logical_relation_id\":" ++ jsonStr f.logicalRelationId ++ ","
    ++ "\"fact_relation\":" ++ jsonStr f.factRelation ++ ","
    ++ "\"raw_relation\":" ++ jsonStr f.rawRelation ++ ","
    ++ "\"has_relation\":" ++ jsonStr f.hasRelation ++ ","
    ++ "\"result_relation\":" ++ jsonOptStr f.resultRelation ++ ","
    ++ "\"query_arity\":" ++ jsonNat f.queryArity ++ ","
    ++ "\"payload_arity\":" ++ jsonNat f.payloadArity ++ ","
    ++ "\"key_positions\":[" ++ String.intercalate "," (f.keyPositions.map jsonNat) ++ "],"
    ++ "\"demand\":[" ++ String.intercalate "," (f.demand.map renderDemandSignature) ++ "],"
    ++ "\"no_false_negatives\":" ++ jsonBool f.contracts.noFalseNegatives ++ ","
    ++ "\"exact_result\":" ++ jsonBool f.contracts.exactResult ++ ","
    ++ "\"stratified_negation_safe\":" ++ jsonBool f.contracts.stratifiedNegationSafe
  ++ "}"

private def renderPermissionCore (p : ExecutionPermission) : String :=
  "\"owner\":" ++ jsonStr (renderExecutionOwner p.owner) ++ ","
    ++ "\"fragment_kind\":" ++ jsonStr (renderKernelClass p.kernelClass) ++ ","
    ++ "\"effect_class\":" ++ jsonStr (renderEffectClass p.effectClass) ++ ","
    ++ "\"resource_class\":" ++ jsonStr (renderResourceClass p.resourceClass) ++ ","
    ++ "\"backend_name\":" ++ jsonStr p.backendName

private def renderMemoShapesField (p : ExecutionPermission) : String :=
  "\"memo_shapes\":["
    ++ String.intercalate "," (p.supportedMemoShapes.map (fun m => jsonStr (renderMemoShape m))) ++ "]"

private def renderCompilabilityFields (p : ExecutionPermission) : String :=
  "\"source_rule_compilable\":" ++ jsonBool p.sourceRuleCompilable ++ ","
    ++ "\"query_compilable\":" ++ jsonBool p.queryCompilable ++ ","
    ++ "\"space_effect_compilable\":" ++ jsonBool p.spaceEffectCompilable

private def renderTheoremRefsField (p : ExecutionPermission) : String :=
  "\"theorem_refs\":["
    ++ String.intercalate "," (p.theoremRefs.map jsonStr) ++ "]"

private def renderLookupQuery (q : LookupQueryContract) : String :=
  let p := q.permission
  "{"
    ++ "\"entry_kind\":\"lookup_query\","
    ++ "\"head\":" ++ jsonStr q.head ++ ","
    ++ "\"surface_head\":" ++ jsonOptStr q.surfaceHead ++ ","
    ++ "\"arity\":" ++ jsonNat q.arity ++ ","
    ++ renderPermissionCore p ++ ","
    ++ renderMemoShapesField p ++ ","
    ++ "\"lookup_family\":" ++ renderLookupFamily q.lookupFamily ++ ","
    ++ renderCompilabilityFields p ++ ","
    ++ "\"builtin_demand\":"
      ++ (match q.builtinDemand with
          | some d => jsonStr (renderBuiltinDemand d)
          | none => "null") ++ ","
    ++ renderTheoremRefsField p
  ++ "}"

private def renderSpaceEffect (e : SpaceEffectContract) : String :=
  let p := e.permission
  "{"
    ++ "\"entry_kind\":\"space_effect\","
    ++ "\"head\":" ++ jsonStr e.head ++ ","
    ++ "\"arity\":" ++ jsonNat e.arity ++ ","
    ++ renderPermissionCore p ++ ","
    ++ renderCompilabilityFields p ++ ","
    ++ renderTheoremRefsField p
  ++ "}"

private def renderRelationPremise (e : RelationPremiseContract) : String :=
  let p := e.permission
  "{"
    ++ "\"entry_kind\":\"relation_premise\","
    ++ "\"relation\":" ++ jsonStr e.relation ++ ","
    ++ "\"arity\":" ++ jsonNat e.arity ++ ","
    ++ renderPermissionCore p ++ ","
    ++ renderMemoShapesField p ++ ","
    ++ "\"lookup_family\":" ++ renderLookupFamily e.lookupFamily ++ ","
    ++ "\"arg_roles\":["
      ++ String.intercalate "," (e.argRoles.map (fun r => jsonStr (renderPremiseArgRole r))) ++ "],"
    ++ "\"result_binding_policy\":"
      ++ (match e.resultBindingPolicy with
          | some p => jsonStr (renderResultBindingPolicy p)
          | none => "null") ++ ","
    ++ "\"lowering_kind\":" ++ jsonStr (renderRelationPremiseLoweringKind e.loweringKind) ++ ","
    ++ renderTheoremRefsField p
  ++ "}"

private def renderSpaceEffectPayload (e : SpaceEffectPayloadContract) : String :=
  let p := e.permission
  "{"
    ++ "\"entry_kind\":\"space_effect_payload\","
    ++ "\"head\":" ++ jsonStr e.head ++ ","
    ++ "\"arity\":" ++ jsonNat e.arity ++ ","
    ++ "\"space_arg_position\":" ++ jsonNat e.spaceArgPosition ++ ","
    ++ "\"payload_arg_position\":" ++ jsonNat e.payloadArgPosition ++ ","
    ++ "\"payload_kind\":" ++ jsonStr (renderSpaceEffectPayloadKind e.payloadKind) ++ ","
    ++ "\"payload_shape\":" ++ jsonStr (renderPayloadPatternShapeKind e.payloadShape) ++ ","
    ++ "\"sink_kind\":" ++ jsonStr (renderSpaceEffectSinkKind e.sinkKind) ++ ","
    ++ renderPermissionCore p ++ ","
    ++ renderCompilabilityFields p ++ ","
    ++ renderTheoremRefsField p
  ++ "}"

private def renderIntrinsicBuiltin (e : IntrinsicBuiltinContract) : String :=
  let p := e.permission
  "{"
    ++ "\"entry_kind\":\"intrinsic_builtin\","
    ++ "\"head\":" ++ jsonStr e.head ++ ","
    ++ "\"relation\":" ++ jsonStr e.relation ++ ","
    ++ "\"min_arity\":" ++ jsonNat e.minArity ++ ","
    ++ "\"max_arity\":"
      ++ (match e.maxArity with
          | some n => jsonNat n
          | none => "null") ++ ","
    ++ renderPermissionCore p ++ ","
    ++ renderMemoShapesField p ++ ","
    ++ "\"builtin_demand\":" ++ jsonStr (renderBuiltinDemand e.builtinDemand) ++ ","
    ++ "\"numeric_result_shape\":"
      ++ (match e.numericResultShape with
          | some shape => jsonStr (renderNumericResultShape shape)
          | none => "null") ++ ","
    ++ "\"eligibility\":" ++ jsonStr (renderLaneEligibilityKind e.eligibility) ++ ","
    ++ "\"residual_policy\":" ++ jsonStr (renderResidualPolicy e.residualPolicy) ++ ","
    ++ renderTheoremRefsField p
  ++ "}"

private def renderGroundedBuiltin (e : GroundedBuiltinContract) : String :=
  let p := e.permission
  "{"
    ++ "\"entry_kind\":\"grounded_builtin\","
    ++ "\"head\":" ++ jsonStr e.head ++ ","
    ++ "\"min_arity\":" ++ jsonNat e.minArity ++ ","
    ++ "\"max_arity\":"
      ++ (match e.maxArity with
          | some n => jsonNat n
          | none => "null") ++ ","
    ++ "\"host_kind\":" ++ jsonStr (renderGroundedBuiltinHostKind e.hostKind) ++ ","
    ++ renderPermissionCore p ++ ","
    ++ renderMemoShapesField p ++ ","
    ++ "\"builtin_demand\":" ++ jsonStr (renderBuiltinDemand e.builtinDemand) ++ ","
    ++ "\"eligibility\":" ++ jsonStr (renderLaneEligibilityKind e.eligibility) ++ ","
    ++ "\"residual_policy\":" ++ jsonStr (renderResidualPolicy e.residualPolicy) ++ ","
    ++ renderTheoremRefsField p
  ++ "}"

private def renderAggregationBuiltin (e : AggregationBuiltinContract) : String :=
  let p := e.permission
  "{"
    ++ "\"entry_kind\":\"aggregation_builtin\","
    ++ "\"head\":" ++ jsonStr e.head ++ ","
    ++ "\"min_arity\":" ++ jsonNat e.minArity ++ ","
    ++ "\"max_arity\":"
      ++ (match e.maxArity with
          | some n => jsonNat n
          | none => "null") ++ ","
    ++ "\"collection_kind\":" ++ jsonStr (renderAggregationCollectionKind e.collectionKind) ++ ","
    ++ "\"source_kind\":" ++ jsonStr (renderAggregationSourceKind e.sourceKind) ++ ","
    ++ renderPermissionCore p ++ ","
    ++ renderMemoShapesField p ++ ","
    ++ "\"eligibility\":" ++ jsonStr (renderLaneEligibilityKind e.eligibility) ++ ","
    ++ "\"residual_policy\":" ++ jsonStr (renderResidualPolicy e.residualPolicy) ++ ","
    ++ renderTheoremRefsField p
  ++ "}"

private def renderControlBuiltin (e : ControlBuiltinContract) : String :=
  let p := e.permission
  "{"
    ++ "\"entry_kind\":\"control_builtin\","
    ++ "\"head\":" ++ jsonStr e.head ++ ","
    ++ "\"min_arity\":" ++ jsonNat e.minArity ++ ","
    ++ "\"max_arity\":"
      ++ (match e.maxArity with
          | some n => jsonNat n
          | none => "null") ++ ","
    ++ "\"control_kind\":" ++ jsonStr (renderControlBuiltinKind e.controlKind) ++ ","
    ++ renderPermissionCore p ++ ","
    ++ renderMemoShapesField p ++ ","
    ++ "\"eligibility\":" ++ jsonStr (renderLaneEligibilityKind e.eligibility) ++ ","
    ++ "\"residual_policy\":" ++ jsonStr (renderResidualPolicy e.residualPolicy) ++ ","
    ++ renderTheoremRefsField p
  ++ "}"

private def renderEntry : ExecutionContractEntry → String
  | .lookupQuery entry => renderLookupQuery entry
  | .spaceEffect entry => renderSpaceEffect entry
  | .relationPremise entry => renderRelationPremise entry
  | .spaceEffectPayload entry => renderSpaceEffectPayload entry
  | .intrinsicBuiltin entry => renderIntrinsicBuiltin entry
  | .groundedBuiltin entry => renderGroundedBuiltin entry
  | .aggregationBuiltin entry => renderAggregationBuiltin entry
  | .controlBuiltin entry => renderControlBuiltin entry

def ExecutionContractArtifact.renderJson (a : ExecutionContractArtifact) : String :=
  let norm := normalizeArtifact a
  "{"
    ++ "\"schema_version\":" ++ jsonNat norm.schemaVersion ++ ","
    ++ "\"dialect\":" ++ jsonStr norm.dialect ++ ","
    ++ "\"entries\":[" ++ String.intercalate "," (norm.entries.map renderEntry) ++ "]"
  ++ "}"

private def lintLookupQuery (q : LookupQueryContract) : List String :=
  let fam := q.lookupFamily.family
  let entryTag := s!"{fam}/{q.head}"
  let p := q.permission
  let headErrs :=
    if q.head.isEmpty then
      ["lookup_query entry head must be non-empty"]
    else []
  let kernelErrs :=
    if p.kernelClass = .query then [] else
      [s!"{entryTag}: lookup_query entries must use fragment_kind=query"]
  let queryErrs :=
    if p.queryCompilable then [] else
      [s!"{entryTag}: first-lane lookup certificate must set query_compilable=true"]
  let memoErrs :=
    (p.supportedMemoShapes.foldl
      (fun errs shape =>
        if p.effectClass.supportsMemoShape shape then errs
        else errs ++ [s!"{entryTag}: effect class {renderEffectClass p.effectClass} does not support memo shape {renderMemoShape shape}"])
      [])
  let builtinErrs :=
    match p.owner, q.builtinDemand with
    | .groundedBuiltin, _ => []
    | _, none => []
    | _, some _ =>
        [s!"{entryTag}: builtin_demand is only valid for grounded_builtin ownership"]
  let surfaceErrs :=
    match q.surfaceHead with
    | some s =>
        if s.isEmpty then
          [s!"{entryTag}: surface_head must be non-empty when provided"]
        else []
    | none => []
  let theoremErrs :=
    if p.theoremRefs.isEmpty then
      [s!"{entryTag}: theorem_refs cannot be empty"]
    else []
  headErrs ++ kernelErrs ++ queryErrs ++ memoErrs ++ builtinErrs ++ surfaceErrs ++ theoremErrs

private def lintSpaceEffect (e : SpaceEffectContract) : List String :=
  let entryTag := s!"space_effect/{e.head}"
  let p := e.permission
  let headErrs :=
    if e.head.isEmpty then
      ["space_effect entry head must be non-empty"]
    else []
  let kernelErrs :=
    if p.kernelClass = .spaceEffect then [] else
      [s!"{entryTag}: space_effect entries must use fragment_kind=space_effect"]
  let compileErrs :=
    if p.spaceEffectCompilable then [] else
      [s!"{entryTag}: space_effect certificate must set space_effect_compilable=true"]
  let laneErrs :=
    (if p.queryCompilable then
      [s!"{entryTag}: space_effect entries cannot set query_compilable=true"]
    else []) ++
    (if p.sourceRuleCompilable then
      [s!"{entryTag}: space_effect entries cannot set source_rule_compilable=true"]
    else [])
  let effectErrs :=
    if p.effectClass = .writesState then [] else
      [s!"{entryTag}: space_effect entries must use effect_class=writes_state"]
  let theoremErrs :=
    if p.theoremRefs.isEmpty then
      [s!"{entryTag}: theorem_refs cannot be empty"]
    else []
  headErrs ++ kernelErrs ++ compileErrs ++ laneErrs ++ effectErrs ++ theoremErrs

private def countRole (roles : List PremiseArgRole) (target : PremiseArgRole) : Nat :=
  roles.foldl (fun n role => if role = target then n + 1 else n) 0

private def lintRelationPremise (e : RelationPremiseContract) : List String :=
  let entryTag := s!"relation_premise/{e.relation}"
  let p := e.permission
  let relationErrs :=
    if e.relation.isEmpty then
      ["relation_premise entry relation must be non-empty"]
    else []
  let arityErrs :=
    (if e.lookupFamily.queryArity = e.arity then [] else
      [s!"{entryTag}: relation_premise arity must match lookup_family.query_arity"]) ++
    (if e.argRoles.length = e.arity then [] else
      [s!"{entryTag}: arg_roles length must equal arity"])
  let kernelErrs :=
    if p.kernelClass = .query then [] else
      [s!"{entryTag}: relation_premise entries must use fragment_kind=query"]
  let effectErrs :=
    if p.effectClass = .readOnlyLookup ∨ p.effectClass = .nondeterministicReadOnly then [] else
      [s!"{entryTag}: relation_premise entries must use a read-only query effect class"]
  let memoErrs :=
    p.supportedMemoShapes.foldl
      (fun errs shape =>
        if p.effectClass.supportsMemoShape shape then errs else
          errs ++ [s!"{entryTag}: effect class {renderEffectClass p.effectClass} does not support memo shape {renderMemoShape shape}"])
      []
  let roleErrs :=
    (if countRole e.argRoles .resultVar ≤ 1 then [] else
      [s!"{entryTag}: arg_roles may contain at most one result_var slot"]) ++
    (match e.resultBindingPolicy with
    | some _ =>
        if countRole e.argRoles .resultVar = 1 then [] else
          [s!"{entryTag}: result_binding_policy requires exactly one result_var slot"]
    | none => [])
  let theoremErrs :=
    if p.theoremRefs.isEmpty then
      [s!"{entryTag}: theorem_refs cannot be empty"]
    else []
  relationErrs ++ arityErrs ++ kernelErrs ++ effectErrs ++ memoErrs ++ roleErrs ++ theoremErrs

private def lintSpaceEffectPayload (e : SpaceEffectPayloadContract) : List String :=
  let entryTag := s!"space_effect_payload/{e.head}"
  let p := e.permission
  let headErrs :=
    if e.head.isEmpty then
      ["space_effect_payload entry head must be non-empty"]
    else []
  let posErrs :=
    (if e.spaceArgPosition < e.arity then [] else
      [s!"{entryTag}: space_arg_position must be < arity"]) ++
    (if e.payloadArgPosition < e.arity then [] else
      [s!"{entryTag}: payload_arg_position must be < arity"]) ++
    (if e.spaceArgPosition ≠ e.payloadArgPosition then [] else
      [s!"{entryTag}: space_arg_position and payload_arg_position must differ"])
  let kernelErrs :=
    if p.kernelClass = .spaceEffect then [] else
      [s!"{entryTag}: space_effect_payload entries must use fragment_kind=space_effect"]
  let compileErrs :=
    if p.spaceEffectCompilable then [] else
      [s!"{entryTag}: space_effect_payload entries must set space_effect_compilable=true"]
  let laneErrs :=
    (if p.queryCompilable then
      [s!"{entryTag}: space_effect_payload entries cannot set query_compilable=true"]
    else []) ++
    (if p.sourceRuleCompilable then
      [s!"{entryTag}: space_effect_payload entries cannot set source_rule_compilable=true"]
    else [])
  let effectErrs :=
    if p.effectClass = .writesState then [] else
      [s!"{entryTag}: space_effect_payload entries must use effect_class=writes_state"]
  let payloadErrs :=
    match e.payloadKind, e.payloadShape, e.sinkKind with
    | .factPayload, .rewriteEqRule, _ =>
        [s!"{entryTag}: fact_payload cannot require rewrite_eq_rule payload_shape"]
    | .sourceRulePayload, .nonRewritePattern, _ =>
        [s!"{entryTag}: source_rule_payload cannot require non_rewrite_pattern payload_shape"]
    | _, _, _ => []
  let theoremErrs :=
    if p.theoremRefs.isEmpty then
      [s!"{entryTag}: theorem_refs cannot be empty"]
    else []
  headErrs ++ posErrs ++ kernelErrs ++ compileErrs ++ laneErrs ++ effectErrs ++ payloadErrs ++ theoremErrs

private def lintIntrinsicBuiltin (e : IntrinsicBuiltinContract) : List String :=
  let entryTag := s!"intrinsic_builtin/{e.head}"
  let p := e.permission
  let headErrs :=
    if e.head.isEmpty then
      ["intrinsic_builtin entry head must be non-empty"]
    else []
  let relationErrs :=
    (if e.relation.isEmpty then
      [s!"{entryTag}: relation must be non-empty"]
    else []) ++
    (if e.relation.startsWith "intrinsic:" then
      []
    else
      [s!"{entryTag}: relation must start with intrinsic:"])
  let arityErrs :=
    match e.maxArity with
    | some maxA =>
        if e.minArity <= maxA then [] else
          [s!"{entryTag}: min_arity cannot exceed max_arity"]
    | none => []
  let ownerErrs :=
    if p.owner = .artifactBackend then [] else
      [s!"{entryTag}: intrinsic_builtin entries must use owner=artifact_backend"]
  let kernelErrs :=
    if p.kernelClass = .ruleExec then [] else
      [s!"{entryTag}: intrinsic_builtin entries must use fragment_kind=rule_exec"]
  let effectErrs :=
    if p.effectClass = .pureStructural then [] else
      [s!"{entryTag}: intrinsic_builtin entries must use effect_class=pure_structural"]
  let memoErrs :=
    (p.supportedMemoShapes.foldl
      (fun errs shape =>
        if p.effectClass.supportsMemoShape shape then errs
        else errs ++ [s!"{entryTag}: effect class {renderEffectClass p.effectClass} does not support memo shape {renderMemoShape shape}"])
      [])
  let theoremErrs :=
    if p.theoremRefs.isEmpty then
      [s!"{entryTag}: theorem_refs cannot be empty"]
    else []
  let controlErrs :=
    if e.builtinDemand = .boolThenElseArgs ∧ e.eligibility ≠ .groundConditionOnly then
      [s!"{entryTag}: bool_then_else_args lanes should declare eligibility=ground_condition_only"]
    else []
  headErrs ++ relationErrs ++ arityErrs ++ ownerErrs ++ kernelErrs ++ effectErrs ++ memoErrs ++ theoremErrs ++ controlErrs

private def lintGroundedBuiltin (e : GroundedBuiltinContract) : List String :=
  let entryTag := s!"grounded_builtin/{e.head}"
  let p := e.permission
  let headErrs :=
    if e.head.isEmpty then
      ["grounded_builtin entry head must be non-empty"]
    else []
  let arityErrs :=
    match e.maxArity with
    | some maxA =>
        if e.minArity <= maxA then [] else
          [s!"{entryTag}: min_arity cannot exceed max_arity"]
    | none => []
  let ownerErrs :=
    if p.owner = .groundedBuiltin then [] else
      [s!"{entryTag}: grounded_builtin entries must use owner=grounded_builtin"]
  let memoErrs :=
    (p.supportedMemoShapes.foldl
      (fun errs shape =>
        if p.effectClass.supportsMemoShape shape then errs
        else errs ++ [s!"{entryTag}: effect class {renderEffectClass p.effectClass} does not support memo shape {renderMemoShape shape}"])
      [])
  let theoremErrs :=
    if p.theoremRefs.isEmpty then
      [s!"{entryTag}: theorem_refs cannot be empty"]
    else []
  let hostErrs :=
    match e.hostKind, e.eligibility with
    | .tupleMembership, .always => []
    | .isVariableTerm, .always => []
    | .reprTerm, .always => []
    | .parseTerm, .always => []
    | .printlnTerm, .always => []
    | .metaTypeOfTerm, .always => []
    | .typeOfTerm, .always => []
    | .quoteTerm, .always => []
    | .testAssertion, .always => []
    | _, .always =>
        [s!"{entryTag}: grounded_builtin lanes should declare an explicit non-trivial eligibility condition"]
    | _, _ => []
  headErrs ++ arityErrs ++ ownerErrs ++ memoErrs ++ theoremErrs ++ hostErrs

private def lintAggregationBuiltin (e : AggregationBuiltinContract) : List String :=
  let entryTag := s!"aggregation_builtin/{e.head}"
  let p := e.permission
  let headErrs :=
    if e.head.isEmpty then
      ["aggregation_builtin entry head must be non-empty"]
    else []
  let arityErrs :=
    match e.maxArity with
    | some maxA =>
        if e.minArity <= maxA then [] else
          [s!"{entryTag}: min_arity cannot exceed max_arity"]
    | none => []
  let ownerErrs :=
    if p.owner = .artifactBackend then [] else
      [s!"{entryTag}: aggregation_builtin entries must use owner=artifact_backend"]
  let kernelErrs :=
    if p.kernelClass = .metaPhase then [] else
      [s!"{entryTag}: aggregation_builtin entries must use fragment_kind=meta_phase"]
  let effectErrs :=
    if p.effectClass = .readOnlyLookup ∨ p.effectClass = .nondeterministicReadOnly then [] else
      [s!"{entryTag}: aggregation_builtin entries must use a read-only effect class"]
  let theoremErrs :=
    if p.theoremRefs.isEmpty then
      [s!"{entryTag}: theorem_refs cannot be empty"]
    else []
  headErrs ++ arityErrs ++ ownerErrs ++ kernelErrs ++ effectErrs ++ theoremErrs

private def lintControlBuiltin (e : ControlBuiltinContract) : List String :=
  let entryTag := s!"control_builtin/{e.head}"
  let p := e.permission
  let headErrs :=
    if e.head.isEmpty then
      ["control_builtin entry head must be non-empty"]
    else []
  let arityErrs :=
    match e.maxArity with
    | some maxA =>
        if e.minArity <= maxA then [] else
          [s!"{entryTag}: min_arity cannot exceed max_arity"]
    | none => []
  let ownerErrs :=
    if p.owner = .artifactBackend then [] else
      [s!"{entryTag}: control_builtin entries must use owner=artifact_backend"]
  let kernelErrs :=
    if p.kernelClass = .metaPhase then [] else
      [s!"{entryTag}: control_builtin entries must use fragment_kind=meta_phase"]
  let effectErrs :=
    if p.effectClass = .writesState then [] else
      [s!"{entryTag}: control_builtin entries must conservatively use effect_class=writes_state"]
  let theoremErrs :=
    if p.theoremRefs.isEmpty then
      [s!"{entryTag}: theorem_refs cannot be empty"]
    else []
  headErrs ++ arityErrs ++ ownerErrs ++ kernelErrs ++ effectErrs ++ theoremErrs

def ExecutionContractArtifact.lintErrors (a : ExecutionContractArtifact) : List String :=
  let norm := normalizeArtifact a
  let schemaErrs :=
    if norm.schemaVersion < 1 then
      [s!"schema_version must be >= 1, got {norm.schemaVersion}"]
    else []
  let dialectErrs :=
    if norm.dialect.isEmpty then
      ["dialect must be non-empty"]
    else []
  let lookupArtifact : LookupPlanArtifact :=
    { dialect := norm.dialect
      families := norm.entries.filterMap ExecutionContractEntry.lookupFamily? }
  let lookupErrs :=
    lookupArtifact.lintErrors.map (fun err => s!"lookup-plan: {err}")
  let dupErrs :=
    let keys := norm.entries.map ExecutionContractEntry.sortKey
    if keys.length == keys.eraseDups.length then
      []
    else
      ["execution contract entries must be unique by entry kind, family, head, and arity"]
  let entryErrs :=
    norm.entries.foldl
      (fun errs entry =>
        errs ++
        match entry with
        | .lookupQuery q => lintLookupQuery q
        | .spaceEffect e => lintSpaceEffect e
        | .relationPremise e => lintRelationPremise e
        | .spaceEffectPayload e => lintSpaceEffectPayload e
        | .intrinsicBuiltin e => lintIntrinsicBuiltin e
        | .groundedBuiltin e => lintGroundedBuiltin e
        | .aggregationBuiltin e => lintAggregationBuiltin e
        | .controlBuiltin e => lintControlBuiltin e)
      []
  schemaErrs ++ dialectErrs ++ lookupErrs ++ dupErrs ++ entryErrs

def ExecutionContractArtifact.isLintClean (a : ExecutionContractArtifact) : Bool :=
  a.lintErrors.isEmpty

private def fnv64Offset : UInt64 := 14695981039346656037
private def fnv64Prime : UInt64 := 1099511628211

def checksumText (text : String) : UInt64 :=
  text.toList.foldl
    (fun h c => (h ^^^ (UInt64.ofNat c.toNat)) * fnv64Prime)
    fnv64Offset

def ExecutionContractArtifact.checksum (a : ExecutionContractArtifact) : UInt64 :=
  checksumText a.renderJson

def ExecutionContractArtifact.checksumString (a : ExecutionContractArtifact) : String :=
  toString a.checksum

section Canaries
#check @ExecutionOwner
#check @ExecutionPermission
#check @LookupQueryContract
#check @coreIntrinsicEntries
#check @ExecutionContractEntry
#check @ExecutionContractArtifact
#check @ExecutionContractArtifact.renderJson
#check @ExecutionContractArtifact.checksumString
end Canaries

end Mettapedia.Languages.MeTTa.ExecutionContract
