import Mettapedia.Languages.MeTTa.SuiteBase.ExecutionContractSchema

/-!
# MeTTa Execution Contract Core

Shared core contract constructors and entry vocabulary for MeTTa-family runtimes.
-/

namespace Mettapedia.Languages.MeTTa.ExecutionContract

open Mettapedia.Languages.MeTTa.ElaboratedCore
open Mettapedia.Languages.MeTTa.RuntimeKernel
open MeTTailCore.MeTTaIL.EffectSafety
open MeTTailCore.MeTTaIL.LookupPlan

private def intrinsicRelationName (ctor : String) : String :=
  s!"intrinsic:{ctor}"

/-- Shared specification row for the core intrinsic builtin catalog. -/
structure CoreIntrinsicSpec where
  head : String
  minArity : Nat
  maxArity : Option Nat := none
  demand : BuiltinDemandKind
deriving Repr, DecidableEq, BEq

/-- Shared specification row for grounded host builtins. -/
structure GroundedBuiltinSpec where
  head : String
  minArity : Nat
  maxArity : Option Nat := none
  demand : BuiltinDemandKind
  hostKind : GroundedBuiltinHostKind
  eligibility : LaneEligibilityKind := .groundNumericArgs
  residualPolicy : ResidualPolicy := .fallbackToRules
deriving Repr, DecidableEq, BEq

/-- The theorem anchors for the shared core intrinsic catalog itself.
They intentionally do not claim cardinality or scalar-result uniqueness for
arbitrary merged runtime builtin tables, because `mergeBuiltinTables` can
concatenate additional rows above this layer. -/
private def coreIntrinsicTheoremRefs : List String :=
  [ "Mettapedia.Languages.MeTTa.RuntimeKernel.exec_effectClass"
  , "Mettapedia.Languages.MeTTa.RuntimeKernel.exec_memo_scalar"
  , "Mettapedia.Languages.MeTTa.RuntimeKernel.exec_memo_outcomeSet"
  , "Mettapedia.Languages.MeTTa.ExecutionContract.mkCoreIntrinsicContract_relation"
  ]

/-- Shared contract constructor for the core intrinsic builtin catalog that both
HE and PeTTa inherit through `coreIntrinsicBuiltins`.

This contract is scoped to the shared intrinsic catalog layer itself, not to
arbitrary builtin environments obtained later by merging extra builtin tables. -/
def mkCoreIntrinsicContract (spec : CoreIntrinsicSpec) : IntrinsicBuiltinContract where
  head := spec.head
  relation := intrinsicRelationName spec.head
  minArity := spec.minArity
  maxArity := spec.maxArity
  owner := .artifactBackend
  kernelClass := .ruleExec
  effectClass := execFragment.effectClass
  resourceClass := execFragment.resourceClass
  backendName := execFragment.backendName
  supportedMemoShapes := [.scalar, .outcomeSet]
  builtinDemand := spec.demand
  theoremRefs := coreIntrinsicTheoremRefs

theorem mkCoreIntrinsicContract_relation (spec : CoreIntrinsicSpec) :
    (mkCoreIntrinsicContract spec).relation =
      intrinsicRelationName spec.head := rfl

def coreIntrinsicSpecs : List CoreIntrinsicSpec :=
  [ { head := "=", minArity := 2, maxArity := some 2, demand := .structuralEqArgs }
  , { head := "if", minArity := 2, maxArity := some 3, demand := .boolThenElseArgs }
  , { head := "and", minArity := 0, demand := .boolArgs }
  , { head := "or", minArity := 0, demand := .boolArgs }
  , { head := "not", minArity := 1, maxArity := some 1, demand := .boolArgs }
  , { head := "xor", minArity := 0, demand := .boolArgs }
  , { head := "append", minArity := 2, maxArity := some 2, demand := .tupleArgs }
  , { head := "is-member", minArity := 2, maxArity := some 2, demand := .elemAndTupleArgs }
  , { head := "<", minArity := 2, maxArity := some 2, demand := .numericArgs }
  , { head := ">", minArity := 2, maxArity := some 2, demand := .numericArgs }
  , { head := "<=", minArity := 2, maxArity := some 2, demand := .numericArgs }
  , { head := ">=", minArity := 2, maxArity := some 2, demand := .numericArgs }
  , { head := "==", minArity := 2, maxArity := some 2, demand := .numericArgs }
  , { head := "!=", minArity := 2, maxArity := some 2, demand := .numericArgs }
  , { head := "+", minArity := 2, demand := .numericArgs }
  , { head := "-", minArity := 1, demand := .numericArgs }
  , { head := "*", minArity := 2, demand := .numericArgs }
  , { head := "/", minArity := 2, maxArity := some 2, demand := .numericArgs }
  , { head := "%", minArity := 2, maxArity := some 2, demand := .numericArgs }
  , { head := "pow-math", minArity := 2, maxArity := some 2, demand := .floatArgs }
  , { head := "sqrt-math", minArity := 1, maxArity := some 1, demand := .floatArgs }
  , { head := "abs-math", minArity := 1, maxArity := some 1, demand := .numericArgs }
  , { head := "log-math", minArity := 2, maxArity := some 2, demand := .floatArgs }
  , { head := "trunc-math", minArity := 1, maxArity := some 1, demand := .floatArgs }
  , { head := "ceil-math", minArity := 1, maxArity := some 1, demand := .floatArgs }
  , { head := "floor-math", minArity := 1, maxArity := some 1, demand := .floatArgs }
  , { head := "round-math", minArity := 1, maxArity := some 1, demand := .floatArgs }
  , { head := "sin-math", minArity := 1, maxArity := some 1, demand := .floatArgs }
  , { head := "asin-math", minArity := 1, maxArity := some 1, demand := .floatArgs }
  , { head := "cos-math", minArity := 1, maxArity := some 1, demand := .floatArgs }
  , { head := "acos-math", minArity := 1, maxArity := some 1, demand := .floatArgs }
  , { head := "tan-math", minArity := 1, maxArity := some 1, demand := .floatArgs }
  , { head := "atan-math", minArity := 1, maxArity := some 1, demand := .floatArgs }
  , { head := "isnan-math", minArity := 1, maxArity := some 1, demand := .floatArgs }
  , { head := "isinf-math", minArity := 1, maxArity := some 1, demand := .floatArgs }
  , { head := "cons", minArity := 2, maxArity := some 2, demand := .tupleArgs }
  , { head := "min-atom", minArity := 1, maxArity := some 1, demand := .tupleArgs }
  , { head := "max-atom", minArity := 1, maxArity := some 1, demand := .tupleArgs }
  ]

def coreIntrinsicContracts : List IntrinsicBuiltinContract :=
  coreIntrinsicSpecs.map mkCoreIntrinsicContract

def LookupQueryContract.noFalseNegatives (c : LookupQueryContract) : Bool :=
  c.lookupFamily.contracts.noFalseNegatives

def LookupQueryContract.exactResult (c : LookupQueryContract) : Bool :=
  c.lookupFamily.contracts.exactResult

def LookupQueryContract.stratifiedNegationSafe (c : LookupQueryContract) : Bool :=
  c.lookupFamily.contracts.stratifiedNegationSafe

/-- Sum type for future execution-contract lanes. -/
inductive ExecutionContractEntry where
  | lookupQuery (entry : LookupQueryContract)
  | spaceEffect (entry : SpaceEffectContract)
  | relationPremise (entry : RelationPremiseContract)
  | spaceEffectPayload (entry : SpaceEffectPayloadContract)
  | intrinsicBuiltin (entry : IntrinsicBuiltinContract)
  | groundedBuiltin (entry : GroundedBuiltinContract)
  | aggregationBuiltin (entry : AggregationBuiltinContract)
  | controlBuiltin (entry : ControlBuiltinContract)
deriving Repr, DecidableEq, BEq

def ExecutionContractEntry.head : ExecutionContractEntry → String
  | .lookupQuery entry => entry.head
  | .spaceEffect entry => entry.head
  | .relationPremise entry => entry.relation
  | .spaceEffectPayload entry => entry.head
  | .intrinsicBuiltin entry => entry.head
  | .groundedBuiltin entry => entry.head
  | .aggregationBuiltin entry => entry.head
  | .controlBuiltin entry => entry.head

def ExecutionContractEntry.arity : ExecutionContractEntry → Nat
  | .lookupQuery entry => entry.arity
  | .spaceEffect entry => entry.arity
  | .relationPremise entry => entry.arity
  | .spaceEffectPayload entry => entry.arity
  | .intrinsicBuiltin entry => entry.minArity
  | .groundedBuiltin entry => entry.minArity
  | .aggregationBuiltin entry => entry.minArity
  | .controlBuiltin entry => entry.minArity

def ExecutionContractEntry.effectClass : ExecutionContractEntry → EffectClass
  | .lookupQuery entry => entry.effectClass
  | .spaceEffect entry => entry.effectClass
  | .relationPremise entry => entry.effectClass
  | .spaceEffectPayload entry => entry.effectClass
  | .intrinsicBuiltin entry => entry.effectClass
  | .groundedBuiltin entry => entry.effectClass
  | .aggregationBuiltin entry => entry.effectClass
  | .controlBuiltin entry => entry.effectClass

def ExecutionContractEntry.resourceClass : ExecutionContractEntry → RuntimeResourceClass
  | .lookupQuery entry => entry.resourceClass
  | .spaceEffect entry => entry.resourceClass
  | .relationPremise entry => entry.resourceClass
  | .spaceEffectPayload entry => entry.resourceClass
  | .intrinsicBuiltin entry => entry.resourceClass
  | .groundedBuiltin entry => entry.resourceClass
  | .aggregationBuiltin entry => entry.resourceClass
  | .controlBuiltin entry => entry.resourceClass

def ExecutionContractEntry.backendName : ExecutionContractEntry → String
  | .lookupQuery entry => entry.backendName
  | .spaceEffect entry => entry.backendName
  | .relationPremise entry => entry.backendName
  | .spaceEffectPayload entry => entry.backendName
  | .intrinsicBuiltin entry => entry.backendName
  | .groundedBuiltin entry => entry.backendName
  | .aggregationBuiltin entry => entry.backendName
  | .controlBuiltin entry => entry.backendName

def ExecutionContractEntry.lookupFamily? : ExecutionContractEntry → Option LookupFamilyPlan
  | .lookupQuery entry => some entry.lookupFamily
  | .spaceEffect _ => none
  | .relationPremise _ => none
  | .spaceEffectPayload _ => none
  | .intrinsicBuiltin _ => none
  | .groundedBuiltin _ => none
  | .aggregationBuiltin _ => none
  | .controlBuiltin _ => none

def ExecutionContractEntry.permission : ExecutionContractEntry → ExecutionPermission
  | .lookupQuery entry => entry.permission
  | .spaceEffect entry => entry.permission
  | .relationPremise entry => entry.permission
  | .spaceEffectPayload entry => entry.permission
  | .intrinsicBuiltin entry => entry.permission
  | .groundedBuiltin entry => entry.permission
  | .aggregationBuiltin entry => entry.permission
  | .controlBuiltin entry => entry.permission

def ExecutionContractEntry.sortKey : ExecutionContractEntry → String
  | .lookupQuery entry =>
      s!"lookup:{entry.lookupFamily.logicalRelationId}:{entry.head}:{entry.arity}"
  | .spaceEffect entry =>
      s!"space_effect:{entry.head}:{entry.arity}"
  | .relationPremise entry =>
      s!"relation_premise:{entry.lookupFamily.logicalRelationId}:{entry.relation}:{entry.arity}"
  | .spaceEffectPayload entry =>
      let payloadKey :=
        match entry.payloadKind with
        | .factPayload => "fact_payload"
        | .sourceRulePayload => "source_rule_payload"
      let sinkKey :=
        match entry.sinkKind with
        | .insertFact => "insert_fact"
        | .removeFact => "remove_fact"
        | .insertRule => "insert_rule"
        | .removeRule => "remove_rule"
      s!"space_effect_payload:{entry.head}:{payloadKey}:{sinkKey}:{entry.arity}"
  | .intrinsicBuiltin entry =>
      s!"intrinsic_builtin:{entry.relation}:{entry.head}:{entry.minArity}"
  | .groundedBuiltin entry =>
      let hostKey :=
        match entry.hostKind with
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
      s!"grounded_builtin:{hostKey}:{entry.head}:{entry.minArity}"
  | .aggregationBuiltin entry =>
      let collectionKey :=
        match entry.collectionKind with
        | .tupleExpr => "tuple_expr"
        | .minAtom => "min_atom"
        | .maxAtom => "max_atom"
      let sourceKey :=
        match entry.sourceKind with
        | .subevalAllResults => "subeval_all_results"
      s!"aggregation_builtin:{sourceKey}:{collectionKey}:{entry.head}:{entry.minArity}"
  | .controlBuiltin entry =>
      let controlKey :=
        match entry.controlKind with
        | .bindThenBody => "bind_then_body"
        | .sequenceLastResult => "sequence_last_result"
      s!"control_builtin:{controlKey}:{entry.head}:{entry.minArity}"

def coreIntrinsicEntries : List ExecutionContractEntry :=
  coreIntrinsicContracts.map ExecutionContractEntry.intrinsicBuiltin

end Mettapedia.Languages.MeTTa.ExecutionContract
