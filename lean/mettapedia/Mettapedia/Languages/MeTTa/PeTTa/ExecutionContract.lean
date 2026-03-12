import Algorithms.MeTTa.LookupPlans
import Algorithms.MeTTa.Simple.Relations
import Mettapedia.Languages.MeTTa.ExecutionContract
import Mettapedia.Languages.MeTTa.PeTTa.DeclarativeSpec
import Mettapedia.Languages.MeTTa.PeTTa.SpaceCoreFragment
import Mettapedia.Languages.MeTTa.PeTTa.SpaceEffectFragment
import Mettapedia.Languages.MeTTa.PeTTa.GroundedOracle

/-!
# PeTTa Execution Contract

First concrete execution-contract instance for the shared MeTTa certificate
surface.

This file intentionally exports the first honest query and space-effect entries:
- `match &self` as the `spaceMatch` lookup family
- `get-atoms &self` as the `selfFacts` lookup family
- `add-atom &self` as a MORK sink-backed space effect
- `remove-atom &self` as a MORK sink-backed space effect
- the first pure intrinsic builtin slice inherited through `coreIntrinsicBuiltins`

Positive example:
- `match &self` and `get-atoms &self` are read-only queries, MORK/MM2-backed,
  query-compilable, and admit outcome-set memoization.
- `spaceMatch` relation premises expose explicit argument roles and the fresh
  result-variable invariant needed by the MM2 compiler.
- `add-atom` and `remove-atom` are stateful space effects, MORK/MM2-backed, and
  space-effect-compilable.
- `add-atom!` and `remove-atom!` are explicit surface aliases of the same
  stateful space-effect lanes, rather than forcing Rust to guess that the bang
  forms should inherit the non-bang contracts.
- `add-atom` / `remove-atom` fact payloads expose explicit payload/sink lanes
  instead of forcing Rust to infer them from surface syntax.
- `add-atom` / `remove-atom` rewrite-rule payloads expose explicit
  `source_rule_payload` lanes instead of forcing Rust to infer dynamic rule
  updates from raw syntax.
- `+`, `-`, `*`, `/`, `%`, `abs-math`, `and`, `or`, `not`, `xor`, `if`, and
  structural `=` are the current pure intrinsic builtins, MORK/MM2-backed, and
  admit scalar/outcome-set memoization.
- `<`, `>`, `<=`, `>=`, `==`, and `!=` are exposed as grounded host builtins
  instead of being overclaimed as MM2 intrinsics; they apply only when their
  numeric-argument eligibility holds and otherwise fall back to ordinary rule
  semantics.
- `repr` and `get-metatype` are exposed as grounded host reflection lanes with
  explicit always-eligible contracts, rather than being smuggled into the MM2
  intrinsic set.
- `parse` is exposed as a grounded host reflection/meta lane, justified by the
  actual PeTTa Prolog clause `parse(Str, R) :- sread(Str, R).`
- `println!` is exposed as a grounded host I/O lane, justified by the actual
  PeTTa Prolog clause `println!(Arg, true) :- swrite(Arg, RArg), format(...)`.
- `if` is currently exported as a control lane with a ground-condition fast
  path and symbolic fallback policy, rather than as a wholly grounded builtin.
- `collapse` is exposed as an aggregation lane that collects all nested backend
  results into one tuple-style PeTTa value.
- `min-atom` and `max-atom` are exposed as structural aggregation lanes over
  nested tuple/list results, not smuggled into the numeric MM2 intrinsic set.
- `let`, `chain`, and `progn` are exposed as explicit control lanes that
  sequence nested certified evaluation instead of forcing Rust to improvise a
  separate control evaluator.

Negative example:
- this file still does not certify premise-bearing rewrite execution or arbitrary
  grounded/FFI builtin catalogs.
- this file intentionally does not export the full shared intrinsic catalog yet:
  uncertified PeTTa MM2 lowerings must fail closed rather than overclaim support.
-/

namespace Mettapedia.Languages.MeTTa.PeTTa.ExecutionContract

open Mettapedia.Languages.MeTTa.ExecutionContract
open Mettapedia.Languages.MeTTa.RuntimeKernel
open MeTTailCore.MeTTaIL.EffectSafety

/-- First PeTTa execution-contract entry: `match &self` via `spaceMatch`. -/
def spaceMatchLookupContract : LookupQueryContract where
  head := "match"
  surfaceHead := some "match"
  arity := 3
  lookupFamily := Algorithms.MeTTa.LookupPlans.pettaSpaceMatchFamily
  owner := .artifactBackend
  kernelClass := .query
  effectClass := queryFragment.effectClass
  resourceClass := queryFragment.resourceClass
  backendName := queryFragment.backendName
  supportedMemoShapes := [.scalar, .outcomeSet]
  sourceRuleCompilable := false
  queryCompilable := true
  spaceEffectCompilable := false
  builtinDemand := none
  theoremRefs :=
    [ "Mettapedia.Languages.MeTTa.RuntimeKernel.query_effectClass"
    , "Mettapedia.Languages.MeTTa.RuntimeKernel.query_memo_scalar"
    , "Mettapedia.Languages.MeTTa.RuntimeKernel.query_memo_outcomeSet"
    , "Mettapedia.Languages.MeTTa.PeTTa.SpaceCoreFragment.anyFactMatch_mem_spaceMatch"
    , "Mettapedia.Languages.MeTTa.PeTTa.SpaceCoreFragment.anyFactMatch_toComputableSourceQuery"
    ]

def spaceMatchEntry : ExecutionContractEntry :=
  .lookupQuery spaceMatchLookupContract

def getAtomsLookupContract : LookupQueryContract where
  head := "get-atoms"
  surfaceHead := some "get-atoms"
  arity := 1
  lookupFamily := Algorithms.MeTTa.LookupPlans.pettaGetAtomsFamily
  owner := .artifactBackend
  kernelClass := .query
  effectClass := queryFragment.effectClass
  resourceClass := queryFragment.resourceClass
  backendName := queryFragment.backendName
  supportedMemoShapes := [.outcomeSet]
  sourceRuleCompilable := false
  queryCompilable := true
  spaceEffectCompilable := false
  builtinDemand := none
  theoremRefs :=
    [ "Mettapedia.Languages.MeTTa.RuntimeKernel.query_effectClass"
    , "Mettapedia.Languages.MeTTa.RuntimeKernel.query_memo_outcomeSet"
    , "Mettapedia.Languages.MeTTa.PeTTa.SpaceCoreFragment.getAtoms_toComputableSourceQuery"
    ]

def getAtomsEntry : ExecutionContractEntry :=
  .lookupQuery getAtomsLookupContract

def addAtomSpaceEffectContract : SpaceEffectContract where
  head := "add-atom"
  arity := 2
  owner := .artifactBackend
  kernelClass := .spaceEffect
  effectClass := spaceEffectFragment.effectClass
  resourceClass := spaceEffectFragment.resourceClass
  backendName := spaceEffectFragment.backendName
  sourceRuleCompilable := false
  queryCompilable := false
  spaceEffectCompilable := true
  theoremRefs :=
    [ "Mettapedia.Languages.MeTTa.RuntimeKernel.spaceEffect_effectClass"
    , "Mettapedia.Languages.MeTTa.RuntimeKernel.spaceEffect_resource"
    , "Mettapedia.Languages.MeTTa.RuntimeKernel.spaceEffect_backend"
    , "Mettapedia.Languages.MeTTa.RuntimeKernel.spaceEffect_not_memo_outcomeSet"
    , "Mettapedia.Languages.MeTTa.PeTTa.SpaceEffectFragment.addAtom_fireSourceRule_mem"
    ]

def addAtomEntry : ExecutionContractEntry :=
  .spaceEffect addAtomSpaceEffectContract

def addAtomBangSpaceEffectContract : SpaceEffectContract :=
  { addAtomSpaceEffectContract with head := "add-atom!" }

def addAtomBangEntry : ExecutionContractEntry :=
  .spaceEffect addAtomBangSpaceEffectContract

def removeAtomSpaceEffectContract : SpaceEffectContract where
  head := "remove-atom"
  arity := 2
  owner := .artifactBackend
  kernelClass := .spaceEffect
  effectClass := spaceEffectFragment.effectClass
  resourceClass := spaceEffectFragment.resourceClass
  backendName := spaceEffectFragment.backendName
  sourceRuleCompilable := false
  queryCompilable := false
  spaceEffectCompilable := true
  theoremRefs :=
    [ "Mettapedia.Languages.MeTTa.RuntimeKernel.spaceEffect_effectClass"
    , "Mettapedia.Languages.MeTTa.RuntimeKernel.spaceEffect_resource"
    , "Mettapedia.Languages.MeTTa.RuntimeKernel.spaceEffect_backend"
    , "Mettapedia.Languages.MeTTa.RuntimeKernel.spaceEffect_not_memo_outcomeSet"
    , "Mettapedia.Languages.MeTTa.PeTTa.SpaceEffectFragment.removeAtom_fireSourceRule_mem"
    ]

def removeAtomEntry : ExecutionContractEntry :=
  .spaceEffect removeAtomSpaceEffectContract

def removeAtomBangSpaceEffectContract : SpaceEffectContract :=
  { removeAtomSpaceEffectContract with head := "remove-atom!" }

def removeAtomBangEntry : ExecutionContractEntry :=
  .spaceEffect removeAtomBangSpaceEffectContract

def spaceMatchRelationPremiseContract : RelationPremiseContract where
  relation := "spaceMatch"
  arity := 3
  lookupFamily := Algorithms.MeTTa.LookupPlans.pettaSpaceMatchFamily
  argRoles := [.pattern, .template, .resultVar]
  resultBindingPolicy := some .mustBeFreshVar
  loweringKind := .factMatchEmitPayload
  owner := .artifactBackend
  kernelClass := .query
  effectClass := queryFragment.effectClass
  resourceClass := queryFragment.resourceClass
  backendName := queryFragment.backendName
  supportedMemoShapes := [.scalar, .outcomeSet]
  theoremRefs :=
    [ "Mettapedia.Languages.MeTTa.RuntimeKernel.query_effectClass"
    , "Mettapedia.Languages.MeTTa.RuntimeKernel.query_memo_scalar"
    , "Mettapedia.Languages.MeTTa.RuntimeKernel.query_memo_outcomeSet"
    , "Mettapedia.Languages.MeTTa.PeTTa.SpaceCoreFragment.anyFactMatch_mem_spaceMatch"
    , "Mettapedia.Languages.MeTTa.PeTTa.SpaceCoreFragment.anyFactMatch_toComputableSourceQuery"
    ]

def spaceMatchRelationPremiseEntry : ExecutionContractEntry :=
  .relationPremise spaceMatchRelationPremiseContract

def addAtomFactPayloadContract : SpaceEffectPayloadContract where
  head := "add-atom"
  arity := 2
  spaceArgPosition := 0
  payloadArgPosition := 1
  payloadKind := .factPayload
  payloadShape := .nonRewritePattern
  sinkKind := .insertFact
  owner := .artifactBackend
  kernelClass := .spaceEffect
  effectClass := spaceEffectFragment.effectClass
  resourceClass := spaceEffectFragment.resourceClass
  backendName := spaceEffectFragment.backendName
  sourceRuleCompilable := false
  queryCompilable := false
  spaceEffectCompilable := true
  theoremRefs :=
    [ "Mettapedia.Languages.MeTTa.RuntimeKernel.spaceEffect_effectClass"
    , "Mettapedia.Languages.MeTTa.RuntimeKernel.spaceEffect_resource"
    , "Mettapedia.Languages.MeTTa.RuntimeKernel.spaceEffect_backend"
    , "Mettapedia.Languages.MeTTa.RuntimeKernel.spaceEffect_not_memo_outcomeSet"
    , "Mettapedia.Languages.MeTTa.PeTTa.SpaceEffectFragment.addAtom_fireSourceRule_mem"
    ]

def addAtomFactPayloadEntry : ExecutionContractEntry :=
  .spaceEffectPayload addAtomFactPayloadContract

def addAtomBangFactPayloadContract : SpaceEffectPayloadContract :=
  { addAtomFactPayloadContract with head := "add-atom!" }

def addAtomBangFactPayloadEntry : ExecutionContractEntry :=
  .spaceEffectPayload addAtomBangFactPayloadContract

def addAtomRulePayloadContract : SpaceEffectPayloadContract where
  head := "add-atom"
  arity := 2
  spaceArgPosition := 0
  payloadArgPosition := 1
  payloadKind := .sourceRulePayload
  payloadShape := .rewriteEqRule
  sinkKind := .insertRule
  owner := .artifactBackend
  kernelClass := .spaceEffect
  effectClass := spaceEffectFragment.effectClass
  resourceClass := spaceEffectFragment.resourceClass
  backendName := spaceEffectFragment.backendName
  sourceRuleCompilable := false
  queryCompilable := false
  spaceEffectCompilable := true
  theoremRefs :=
    [ "Mettapedia.Languages.MeTTa.RuntimeKernel.spaceEffect_effectClass"
    , "Mettapedia.Languages.MeTTa.RuntimeKernel.spaceEffect_resource"
    , "Mettapedia.Languages.MeTTa.RuntimeKernel.spaceEffect_backend"
    , "Mettapedia.Languages.MeTTa.RuntimeKernel.spaceEffect_not_memo_outcomeSet"
    , "Mettapedia.Languages.MeTTa.PeTTa.SpaceEffectFragment.addAtom_fireSourceRule_mem"
    ]

def addAtomRulePayloadEntry : ExecutionContractEntry :=
  .spaceEffectPayload addAtomRulePayloadContract

def addAtomBangRulePayloadContract : SpaceEffectPayloadContract :=
  { addAtomRulePayloadContract with head := "add-atom!" }

def addAtomBangRulePayloadEntry : ExecutionContractEntry :=
  .spaceEffectPayload addAtomBangRulePayloadContract

def removeAtomFactPayloadContract : SpaceEffectPayloadContract where
  head := "remove-atom"
  arity := 2
  spaceArgPosition := 0
  payloadArgPosition := 1
  payloadKind := .factPayload
  payloadShape := .nonRewritePattern
  sinkKind := .removeFact
  owner := .artifactBackend
  kernelClass := .spaceEffect
  effectClass := spaceEffectFragment.effectClass
  resourceClass := spaceEffectFragment.resourceClass
  backendName := spaceEffectFragment.backendName
  sourceRuleCompilable := false
  queryCompilable := false
  spaceEffectCompilable := true
  theoremRefs :=
    [ "Mettapedia.Languages.MeTTa.RuntimeKernel.spaceEffect_effectClass"
    , "Mettapedia.Languages.MeTTa.RuntimeKernel.spaceEffect_resource"
    , "Mettapedia.Languages.MeTTa.RuntimeKernel.spaceEffect_backend"
    , "Mettapedia.Languages.MeTTa.RuntimeKernel.spaceEffect_not_memo_outcomeSet"
    , "Mettapedia.Languages.MeTTa.PeTTa.SpaceEffectFragment.removeAtom_fireSourceRule_mem"
    ]

def removeAtomFactPayloadEntry : ExecutionContractEntry :=
  .spaceEffectPayload removeAtomFactPayloadContract

def removeAtomBangFactPayloadContract : SpaceEffectPayloadContract :=
  { removeAtomFactPayloadContract with head := "remove-atom!" }

def removeAtomBangFactPayloadEntry : ExecutionContractEntry :=
  .spaceEffectPayload removeAtomBangFactPayloadContract

def removeAtomRulePayloadContract : SpaceEffectPayloadContract where
  head := "remove-atom"
  arity := 2
  spaceArgPosition := 0
  payloadArgPosition := 1
  payloadKind := .sourceRulePayload
  payloadShape := .rewriteEqRule
  sinkKind := .removeRule
  owner := .artifactBackend
  kernelClass := .spaceEffect
  effectClass := spaceEffectFragment.effectClass
  resourceClass := spaceEffectFragment.resourceClass
  backendName := spaceEffectFragment.backendName
  sourceRuleCompilable := false
  queryCompilable := false
  spaceEffectCompilable := true
  theoremRefs :=
    [ "Mettapedia.Languages.MeTTa.RuntimeKernel.spaceEffect_effectClass"
    , "Mettapedia.Languages.MeTTa.RuntimeKernel.spaceEffect_resource"
    , "Mettapedia.Languages.MeTTa.RuntimeKernel.spaceEffect_backend"
    , "Mettapedia.Languages.MeTTa.RuntimeKernel.spaceEffect_not_memo_outcomeSet"
    , "Mettapedia.Languages.MeTTa.PeTTa.SpaceEffectFragment.removeAtom_fireSourceRule_mem"
    ]

def removeAtomRulePayloadEntry : ExecutionContractEntry :=
  .spaceEffectPayload removeAtomRulePayloadContract

def removeAtomBangRulePayloadContract : SpaceEffectPayloadContract :=
  { removeAtomRulePayloadContract with head := "remove-atom!" }

def removeAtomBangRulePayloadEntry : ExecutionContractEntry :=
  .spaceEffectPayload removeAtomBangRulePayloadContract

/-- PeTTa-local intrinsic slice that matches the live MM2 lowering in
`mettail-rust`.

This list is intentionally narrow. A head belongs here only when the current
MORK/MM2 backend has a concrete lowering target for it.

Positive example:
- integer numerics (`+`, `-`, `*`, `/`, `%`, `abs-math`)
  These lower to MORK pure ops such as `sum_i32`, `product_i32`, `sub_i32`,
  `div_i32`, `mod_i32`, and `abs_i32`.
- float/transcendental numerics such as `pow-math`, `sqrt-math`, `log-math`,
  `round-math`, and the trig family
  These lower to real MORK `f64` pure ops such as `powf_f64`, `sqrt_f64`,
  `ln_f64`, `round_f64`, `sin_f64`, `cos_f64`, and `tan_f64`.
- booleans (`and`, `or`, `not`, `xor`)
- `if`
- structural `=`

Negative example:
- numeric comparisons like `<` and `>=`
  These are excluded until there is either a real MORK comparison primitive to
  lower to or an explicit grounded-host contract lane.
- tuple/list operators like `append` and `cons`
- float predicates like `isnan-math` and `isinf-math`
  These stay grounded-host until the kernel exposes native MM2 primitives for
  them directly.
-/
def pettaMm2IntrinsicSpecs : List CoreIntrinsicSpec :=
  [ { head := "=", minArity := 2, maxArity := some 2, demand := .structuralEqArgs }
  , { head := "if", minArity := 2, maxArity := some 3, demand := .boolThenElseArgs }
  , { head := "and", minArity := 0, demand := .boolArgs }
  , { head := "or", minArity := 0, demand := .boolArgs }
  , { head := "not", minArity := 1, maxArity := some 1, demand := .boolArgs }
  , { head := "xor", minArity := 0, demand := .boolArgs }
  , { head := "+", minArity := 2, maxArity := none, demand := .numericArgs }
  , { head := "-", minArity := 1, maxArity := none, demand := .numericArgs }
  , { head := "*", minArity := 2, maxArity := none, demand := .numericArgs }
  , { head := "/", minArity := 2, maxArity := some 2, demand := .numericArgs }
  , { head := "%", minArity := 2, maxArity := some 2, demand := .numericArgs }
  , { head := "abs-math", minArity := 1, maxArity := some 1, demand := .numericArgs }
  , { head := "pow-math", minArity := 2, maxArity := some 2, demand := .floatArgs }
  , { head := "sqrt-math", minArity := 1, maxArity := some 1, demand := .floatArgs }
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
  ]

private def tunePeTTaMm2IntrinsicContract (c : IntrinsicBuiltinContract) :
    IntrinsicBuiltinContract :=
  let c :=
    { c with
      numericResultShape := Mettapedia.Languages.MeTTa.PeTTa.numericResultShapeOf c.head }
  if c.head = "if" then
    { c with
      eligibility := .groundConditionOnly
      residualPolicy := .symbolicFallback }
  else if c.builtinDemand = .boolArgs then
    { c with
      residualPolicy := .symbolicFallback }
  else
    c

def pettaMm2IntrinsicContracts : List IntrinsicBuiltinContract :=
  pettaMm2IntrinsicSpecs.map (fun spec =>
    tunePeTTaMm2IntrinsicContract (mkCoreIntrinsicContract spec))

def pettaMm2IntrinsicEntries : List ExecutionContractEntry :=
  pettaMm2IntrinsicContracts.map .intrinsicBuiltin

/-- PeTTa-local grounded host slice for operations that are pure and
deterministic but do not currently have a direct MM2/MORK primitive.

Positive example:
- numeric comparisons such as `<` and `>=`
- `is-var` / `is-variable`, which inspect variable structure directly and do
  not currently lower to a native MM2 primitive

Negative example:
- these heads are not exported as MM2 intrinsics while the MORK kernel lacks a
  corresponding comparison primitive to lower to directly.
-/
private def groundedComparisonTheoremRefs : List String :=
  [ "Mettapedia.Languages.MeTTa.PeTTa.GroundedOracle.meTTaEvalG_groundedCall_mk"
  , "Mettapedia.Languages.MeTTa.PeTTa.GroundedOracle.meTTaEvalG_executable_total"
  ]

def mkPeTTaGroundedBuiltinContract (spec : GroundedBuiltinSpec) : GroundedBuiltinContract where
  head := spec.head
  minArity := spec.minArity
  maxArity := spec.maxArity
  hostKind := spec.hostKind
  owner := .groundedBuiltin
  kernelClass := .ruleExec
  effectClass := .pureStructural
  resourceClass := .defaultAtomSpace
  backendName := "grounded-host"
  supportedMemoShapes := [.scalar, .outcomeSet]
  builtinDemand := spec.demand
  eligibility := spec.eligibility
  residualPolicy := spec.residualPolicy
  theoremRefs := groundedComparisonTheoremRefs

def pettaGroundedComparisonSpecs : List GroundedBuiltinSpec :=
  [ { head := "<", minArity := 2, maxArity := some 2, demand := .numericArgs
    , hostKind := .numericCompare, eligibility := .groundNumericArgs
    , residualPolicy := .fallbackToRules }
  , { head := ">", minArity := 2, maxArity := some 2, demand := .numericArgs
    , hostKind := .numericCompare, eligibility := .groundNumericArgs
    , residualPolicy := .fallbackToRules }
  , { head := "<=", minArity := 2, maxArity := some 2, demand := .numericArgs
    , hostKind := .numericCompare, eligibility := .groundNumericArgs
    , residualPolicy := .fallbackToRules }
  , { head := ">=", minArity := 2, maxArity := some 2, demand := .numericArgs
    , hostKind := .numericCompare, eligibility := .groundNumericArgs
    , residualPolicy := .fallbackToRules }
  , { head := "==", minArity := 2, maxArity := some 2, demand := .numericArgs
    , hostKind := .numericCompare, eligibility := .groundNumericArgs
    , residualPolicy := .fallbackToRules }
  , { head := "!=", minArity := 2, maxArity := some 2, demand := .numericArgs
    , hostKind := .numericCompare, eligibility := .groundNumericArgs
    , residualPolicy := .fallbackToRules }
  ]

def pettaGroundedComparisonContracts : List GroundedBuiltinContract :=
  pettaGroundedComparisonSpecs.map mkPeTTaGroundedBuiltinContract

def pettaGroundedComparisonEntries : List ExecutionContractEntry :=
  pettaGroundedComparisonContracts.map .groundedBuiltin

/--
Variable predicates are currently grounded-host lanes.

Why grounded-host:
- the live PeTTa/MM2 slice has no theorem-backed native MM2 variable predicate
- the predicate only inspects raw term structure, so it fits the grounded host
  lane cleanly

Why residual fallback:
- the contract should not reserve the head forever; future/user rule semantics
  may still extend it
-/
def pettaGroundedVarPredicateSpecs : List GroundedBuiltinSpec :=
  [ { head := "is-var", minArity := 1, maxArity := some 1, demand := .rawArgs
    , hostKind := .isVariableTerm, eligibility := .always
    , residualPolicy := .fallbackToRules }
  , { head := "is-variable", minArity := 1, maxArity := some 1, demand := .rawArgs
    , hostKind := .isVariableTerm, eligibility := .always
    , residualPolicy := .fallbackToRules }
  ]

def pettaGroundedVarPredicateContracts : List GroundedBuiltinContract :=
  pettaGroundedVarPredicateSpecs.map fun spec =>
    { mkPeTTaGroundedBuiltinContract spec with theoremRefs := groundedComparisonTheoremRefs }

def pettaGroundedVarPredicateEntries : List ExecutionContractEntry :=
  pettaGroundedVarPredicateContracts.map .groundedBuiltin

/--
Float predicates remain grounded-host for now.

Why grounded-host:
- the MORK kernel exposes real `f64` arithmetic and transcendental primitives
  such as `sum_f64`, `powf_f64`, `sqrt_f64`, `ln_f64`, `sin_f64`, and friends
- it does not currently expose direct `is_nan` / `is_infinite` MM2 primitives
  to certify as native intrinsic lanes

Why residual fallback:
- future/user rule semantics should still be able to extend these heads
- if the argument is not yet ground-numeric, this lane should not reserve the
  head permanently
-/
def pettaGroundedFloatPredicateSpecs : List GroundedBuiltinSpec :=
  [ { head := "isnan-math", minArity := 1, maxArity := some 1, demand := .floatArgs
    , hostKind := .f64Predicate, eligibility := .groundNumericArgs
    , residualPolicy := .fallbackToRules }
  , { head := "isinf-math", minArity := 1, maxArity := some 1, demand := .floatArgs
    , hostKind := .f64Predicate, eligibility := .groundNumericArgs
    , residualPolicy := .fallbackToRules }
  ]

def pettaGroundedFloatPredicateContracts : List GroundedBuiltinContract :=
  pettaGroundedFloatPredicateSpecs.map fun spec =>
    { mkPeTTaGroundedBuiltinContract spec with theoremRefs := groundedComparisonTheoremRefs }

def pettaGroundedFloatPredicateEntries : List ExecutionContractEntry :=
  pettaGroundedFloatPredicateContracts.map .groundedBuiltin

private def groundedReflectionTheoremRefs : List String :=
  [ "Mettapedia.Languages.MeTTa.PeTTa.GroundedOracle.meTTaEvalG_groundedCall_mk"
  , "Mettapedia.Languages.MeTTa.PeTTa.GroundedOracle.meTTaEvalG_executable_total"
  ]

private def groundedIOTheoremRefs : List String :=
  [ "Mettapedia.Languages.MeTTa.RuntimeKernel.externalOracle_effectClass"
  ]

private def groundedTypeQueryTheoremRefs : List String :=
  [ "Mettapedia.Languages.MeTTa.PeTTa.GroundedOracle.meTTaEvalG_groundedCall_mk"
  , "Mettapedia.Languages.MeTTa.PeTTa.GroundedOracle.meTTaEvalG_executable_total"
  ]

def pettaGroundedReflectionSpecs : List GroundedBuiltinSpec :=
  [ { head := "repr", minArity := 1, maxArity := some 1, demand := .rawArgs
    , hostKind := .reprTerm, eligibility := .always, residualPolicy := .failClosed }
  , { head := "parse", minArity := 1, maxArity := some 1, demand := .rawArgs
    , hostKind := .parseTerm, eligibility := .always, residualPolicy := .failClosed }
  , { head := "get-metatype", minArity := 1, maxArity := some 1, demand := .rawArgs
    , hostKind := .metaTypeOfTerm, eligibility := .always, residualPolicy := .failClosed }
  ]

def pettaGroundedReflectionContracts : List GroundedBuiltinContract :=
  pettaGroundedReflectionSpecs.map fun spec =>
    { mkPeTTaGroundedBuiltinContract spec with theoremRefs := groundedReflectionTheoremRefs }

def pettaGroundedReflectionEntries : List ExecutionContractEntry :=
  pettaGroundedReflectionContracts.map .groundedBuiltin

/--
`println!` is a grounded host I/O lane.

Why grounded-host:
- upstream PeTTa defines `println!(Arg, true) :- swrite(Arg, RArg), format(...)`
- MM2/MORK has no theorem-backed stdout/stderr primitive to certify as a native
  backend lane

Why not memoized:
- this is observable host I/O, so it belongs to the `oracle_io` effect class
  and must not pretend to be a pure structural reduction
-/
def printlnGroundedContract : GroundedBuiltinContract where
  head := "println!"
  minArity := 1
  maxArity := some 1
  hostKind := .printlnTerm
  owner := .groundedBuiltin
  kernelClass := .oracle
  effectClass := .oracleIO
  resourceClass := .externalResource
  backendName := "grounded-host"
  supportedMemoShapes := []
  builtinDemand := .rawArgs
  eligibility := .always
  residualPolicy := .failClosed
  theoremRefs := groundedIOTheoremRefs

def printlnGroundedEntry : ExecutionContractEntry :=
  .groundedBuiltin printlnGroundedContract

/--
`get-type` is currently a grounded host read-only query lane.

Why grounded-host:
- the current live PeTTa/MM2 backend already has honest MM2 support for
  arithmetic, but not a theorem-backed native type-query family yet
- the original PeTTa semantics computes a baseline type candidate relation from
  host-observable facts such as numeric/string literals, direct `(: term ty)`
  annotations, list component types, and arrow-type application

Why residual fallback:
- user programs may define their own `get-type` rules
- the grounded host lane should therefore supply the baseline candidate
  semantics when it applies, but yield to ordinary rule semantics when the
  runtime chooses not to answer from that baseline lane

Positive example:
- `(get-type 42)` may reduce on the grounded-host lane to `Number`

Negative example:
- we do not claim that `get-type` is a native MM2 lookup family yet, and we do
  not reserve the `get-type` head against future/user rule extensions
-/
def getTypeGroundedContract : GroundedBuiltinContract where
  head := "get-type"
  minArity := 1
  maxArity := some 1
  hostKind := .typeOfTerm
  owner := .groundedBuiltin
  kernelClass := .query
  effectClass := .readOnlyLookup
  resourceClass := .defaultAtomSpace
  backendName := "grounded-host"
  supportedMemoShapes := [.outcomeSet]
  builtinDemand := .rawArgs
  eligibility := .always
  residualPolicy := .fallbackToRules
  theoremRefs := groundedTypeQueryTheoremRefs

def getTypeGroundedEntry : ExecutionContractEntry :=
  .groundedBuiltin getTypeGroundedContract

private def collapseAggregationTheoremRefs : List String :=
  [ "Mettapedia.Languages.MeTTa.PeTTa.Eval.petta_eval_collapse_singleton"
  , "Mettapedia.Languages.MeTTa.PeTTa.MeTTaEval.meTTaEval_collapse_to_pettaEval"
  , "Mettapedia.Languages.MeTTa.PeTTa.MeTTaEval.meTTaEval_collapse_singleton"
  , "Mettapedia.Languages.MeTTa.PeTTa.DeclarativeSpec.collapse_intro"
  ]

/--
`min-atom` / `max-atom` currently use structural aggregation contracts.

Why aggregation:
- upstream PeTTa defines them over list/tuple data via `min_list` / `max_list`
- they are structural reductions over a nested collection value, not MM2 kernel
  arithmetic primitives

Why not MM2 intrinsic:
- the current MORK/MM2 kernel exposes numeric arithmetic primitives, but not a
  native tuple-extrema primitive to lower to directly
- keeping them out of the intrinsic lane avoids overclaiming backend support
-/
private def atomExtremaAggregationTheoremRefs : List String :=
  [ "Mettapedia.Languages.MeTTa.RuntimeKernel.query_effectClass"
  , "Mettapedia.Languages.MeTTa.RuntimeKernel.query_memo_outcomeSet"
  ]

private def controlBuiltinTheoremRefs : List String :=
  [ "Mettapedia.Languages.MeTTa.PeTTa.DeclarativeSpec.ControlDeclClause.letToChain"
  , "Mettapedia.Languages.MeTTa.PeTTa.StdLib.let_to_chain"
  , "Mettapedia.Languages.MeTTa.PeTTa.StdLib.chain_reduces"
  , "Mettapedia.Languages.MeTTa.PeTTa.DeclarativeSpec.CoreDecl.progn"
  , "Mettapedia.Languages.MeTTa.PeTTa.DeclarativeSpec.PredicateControlDeclClause.prognStateful"
  ]

/--
`let`, `chain`, and `progn` currently use explicit control contracts.

Why control lanes:
- these forms orchestrate nested evaluation and binding/sequence structure
  rather than denoting standalone query/effect primitives
- the scope artifact already classifies the binder/value/body structure for
  `let` and `chain`, so the runtime can consume that structure instead of
  inventing per-head control behavior

Why conservatively `writes_state`:
- these control forms may sequence nested space effects such as `add-atom`
  and `remove-atom`
- the control lane therefore must not pretend to be pure or memo-safe
-/
def letControlContract : ControlBuiltinContract where
  head := "let"
  minArity := 3
  maxArity := some 3
  controlKind := .bindThenBody
  owner := .artifactBackend
  kernelClass := .metaPhase
  effectClass := spaceEffectFragment.effectClass
  resourceClass := spaceEffectFragment.resourceClass
  backendName := spaceEffectFragment.backendName
  supportedMemoShapes := []
  eligibility := .always
  residualPolicy := .failClosed
  theoremRefs := controlBuiltinTheoremRefs

def letControlEntry : ExecutionContractEntry :=
  .controlBuiltin letControlContract

def chainControlContract : ControlBuiltinContract where
  head := "chain"
  minArity := 3
  maxArity := some 3
  controlKind := .bindThenBody
  owner := .artifactBackend
  kernelClass := .metaPhase
  effectClass := spaceEffectFragment.effectClass
  resourceClass := spaceEffectFragment.resourceClass
  backendName := spaceEffectFragment.backendName
  supportedMemoShapes := []
  eligibility := .always
  residualPolicy := .failClosed
  theoremRefs := controlBuiltinTheoremRefs

def chainControlEntry : ExecutionContractEntry :=
  .controlBuiltin chainControlContract

def prognControlContract : ControlBuiltinContract where
  head := "progn"
  minArity := 1
  maxArity := none
  controlKind := .sequenceLastResult
  owner := .artifactBackend
  kernelClass := .metaPhase
  effectClass := spaceEffectFragment.effectClass
  resourceClass := spaceEffectFragment.resourceClass
  backendName := spaceEffectFragment.backendName
  supportedMemoShapes := []
  eligibility := .always
  residualPolicy := .failClosed
  theoremRefs := controlBuiltinTheoremRefs

def prognControlEntry : ExecutionContractEntry :=
  .controlBuiltin prognControlContract

def collapseAggregationContract : AggregationBuiltinContract where
  head := "collapse"
  minArity := 1
  maxArity := some 1
  collectionKind := .tupleExpr
  sourceKind := .subevalAllResults
  owner := .artifactBackend
  kernelClass := .metaPhase
  effectClass := queryFragment.effectClass
  resourceClass := queryFragment.resourceClass
  backendName := queryFragment.backendName
  supportedMemoShapes := [.outcomeSet]
  eligibility := .always
  residualPolicy := .failClosed
  theoremRefs := collapseAggregationTheoremRefs

def collapseAggregationEntry : ExecutionContractEntry :=
  .aggregationBuiltin collapseAggregationContract

def minAtomAggregationContract : AggregationBuiltinContract where
  head := "min-atom"
  minArity := 1
  maxArity := some 1
  collectionKind := .minAtom
  sourceKind := .subevalAllResults
  owner := .artifactBackend
  kernelClass := .metaPhase
  effectClass := queryFragment.effectClass
  resourceClass := queryFragment.resourceClass
  backendName := queryFragment.backendName
  supportedMemoShapes := [.outcomeSet]
  eligibility := .always
  residualPolicy := .failClosed
  theoremRefs := atomExtremaAggregationTheoremRefs

def minAtomAggregationEntry : ExecutionContractEntry :=
  .aggregationBuiltin minAtomAggregationContract

def maxAtomAggregationContract : AggregationBuiltinContract where
  head := "max-atom"
  minArity := 1
  maxArity := some 1
  collectionKind := .maxAtom
  sourceKind := .subevalAllResults
  owner := .artifactBackend
  kernelClass := .metaPhase
  effectClass := queryFragment.effectClass
  resourceClass := queryFragment.resourceClass
  backendName := queryFragment.backendName
  supportedMemoShapes := [.outcomeSet]
  eligibility := .always
  residualPolicy := .failClosed
  theoremRefs := atomExtremaAggregationTheoremRefs

def maxAtomAggregationEntry : ExecutionContractEntry :=
  .aggregationBuiltin maxAtomAggregationContract

def pettaExecutionContractArtifact : ExecutionContractArtifact where
  dialect := "petta"
  entries :=
    [ spaceMatchEntry
    , getAtomsEntry
    , addAtomEntry
    , addAtomBangEntry
    , removeAtomEntry
    , removeAtomBangEntry
    , spaceMatchRelationPremiseEntry
    , addAtomFactPayloadEntry
    , addAtomBangFactPayloadEntry
    , addAtomRulePayloadEntry
    , addAtomBangRulePayloadEntry
    , removeAtomFactPayloadEntry
    , removeAtomBangFactPayloadEntry
    , removeAtomRulePayloadEntry
    , removeAtomBangRulePayloadEntry
    , letControlEntry
    , chainControlEntry
    , prognControlEntry
    , collapseAggregationEntry
    , minAtomAggregationEntry
    , maxAtomAggregationEntry
    , getTypeGroundedEntry
    , printlnGroundedEntry
    ] ++ pettaMm2IntrinsicEntries ++ pettaGroundedComparisonEntries
      ++ pettaGroundedFloatPredicateEntries
      ++ pettaGroundedVarPredicateEntries
      ++ pettaGroundedReflectionEntries

theorem spaceMatch_effectClass :
    spaceMatchLookupContract.effectClass = .readOnlyLookup := rfl

theorem spaceMatch_resource :
    spaceMatchLookupContract.resourceClass = .defaultAtomSpace := rfl

theorem spaceMatch_backend :
    spaceMatchLookupContract.backendName = "MORK/MM2" := rfl

theorem spaceMatch_noFalseNegatives :
    spaceMatchLookupContract.noFalseNegatives = true := rfl

theorem spaceMatch_exactResult :
    spaceMatchLookupContract.exactResult = false := rfl

theorem spaceMatch_stratifiedNegationSafe :
    spaceMatchLookupContract.stratifiedNegationSafe = true := rfl

theorem spaceMatch_scalarMemo :
    spaceMatchLookupContract.effectClass.supportsMemoShape .scalar = true := by
  simpa [spaceMatchLookupContract] using query_memo_scalar

theorem spaceMatch_outcomeSetMemo :
    spaceMatchLookupContract.effectClass.supportsMemoShape .outcomeSet = true := by
  simpa [spaceMatchLookupContract] using query_memo_outcomeSet

theorem getAtoms_effectClass :
    getAtomsLookupContract.effectClass = .readOnlyLookup := rfl

theorem getAtoms_resource :
    getAtomsLookupContract.resourceClass = .defaultAtomSpace := rfl

theorem getAtoms_backend :
    getAtomsLookupContract.backendName = "MORK/MM2" := rfl

theorem getAtoms_exactResult :
    getAtomsLookupContract.exactResult = true := rfl

theorem getAtoms_outcomeSetMemo :
    getAtomsLookupContract.effectClass.supportsMemoShape .outcomeSet = true := by
  simpa [getAtomsLookupContract] using query_memo_outcomeSet

theorem addAtom_effectClass :
    addAtomSpaceEffectContract.effectClass = .writesState := rfl

theorem addAtom_spaceEffectCompilable :
    addAtomSpaceEffectContract.spaceEffectCompilable = true := rfl

theorem removeAtom_effectClass :
    removeAtomSpaceEffectContract.effectClass = .writesState := rfl

theorem removeAtom_spaceEffectCompilable :
    removeAtomSpaceEffectContract.spaceEffectCompilable = true := rfl

theorem spaceMatchRelationPremise_freshResult :
    spaceMatchRelationPremiseContract.resultBindingPolicy = some .mustBeFreshVar := rfl

theorem addAtomFactPayload_sink :
    addAtomFactPayloadContract.sinkKind = .insertFact := rfl

theorem removeAtomFactPayload_sink :
    removeAtomFactPayloadContract.sinkKind = .removeFact := rfl

theorem addAtomRulePayload_sink :
    addAtomRulePayloadContract.sinkKind = .insertRule := rfl

theorem removeAtomRulePayload_sink :
    removeAtomRulePayloadContract.sinkKind = .removeRule := rfl

theorem plusIntrinsic_effectClass :
    (mkCoreIntrinsicContract { head := "+", minArity := 2, demand := .numericArgs }).effectClass = .pureStructural := rfl

theorem plusIntrinsic_scalarMemo :
    (mkCoreIntrinsicContract { head := "+", minArity := 2, demand := .numericArgs }).effectClass.supportsMemoShape .scalar = true := by
  simpa [mkCoreIntrinsicContract] using exec_memo_scalar

theorem ifIntrinsic_relation :
    (mkCoreIntrinsicContract { head := "if", minArity := 2, maxArity := some 3, demand := .boolThenElseArgs }).relation =
      Algorithms.MeTTa.Simple.intrinsicRelationName "if" := rfl

def exportPeTTaExecutionContract (outDir : System.FilePath) : IO UInt32 := do
  let artifact := pettaExecutionContractArtifact
  let lintErrs := artifact.lintErrors
  if !lintErrs.isEmpty then
    IO.println s!"petta execution contract lint failed:\n{String.intercalate "\n" lintErrs}"
    pure 2
  else
    let jsonPath := outDir / "petta.execution_contract.json"
    let checksumPath := outDir / "petta.execution_contract.checksum"
    IO.FS.createDirAll outDir
    IO.FS.writeFile jsonPath (artifact.renderJson ++ "\n")
    IO.FS.writeFile checksumPath (artifact.checksumString ++ "\n")
    IO.println s!"exported petta execution contract to {outDir}"
    pure 0

def checkPeTTaExecutionContract (outDir : System.FilePath) : IO UInt32 := do
  let artifact := pettaExecutionContractArtifact
  let lintErrs := artifact.lintErrors
  if !lintErrs.isEmpty then
    IO.println s!"petta execution contract lint failed:\n{String.intercalate "\n" lintErrs}"
    pure 2
  else
    let jsonPath := outDir / "petta.execution_contract.json"
    let checksumPath := outDir / "petta.execution_contract.checksum"
    try
      let jsonText ← IO.FS.readFile jsonPath
      let checksumText ← IO.FS.readFile checksumPath
      let jsonOk := jsonText.trimAscii.toString == artifact.renderJson.trimAscii.toString
      let checksumOk := checksumText.trimAscii.toString == artifact.checksumString.trimAscii.toString
      if jsonOk && checksumOk then
        IO.println s!"[ok] petta execution contract matches at {outDir}"
        pure 0
      else
        if !jsonOk then
          IO.println s!"[drift] petta execution contract json mismatch at {jsonPath}"
        if !checksumOk then
          IO.println s!"[drift] petta execution contract checksum mismatch at {checksumPath}"
        pure 3
    catch e =>
      IO.println s!"petta execution contract check failed: {e}"
      pure 2

section Canaries
#check @spaceMatchLookupContract
#check @pettaExecutionContractArtifact
#check @exportPeTTaExecutionContract
#check @checkPeTTaExecutionContract
end Canaries

end Mettapedia.Languages.MeTTa.PeTTa.ExecutionContract
