import Mettapedia.Languages.MeTTa.RuntimeKernel
import MeTTailCore.MeTTaIL.LookupPlan

/-!
# MeTTa Execution Contract Schema

Shared schema and permission vocabulary for MeTTa-family execution contracts.
This internal module is backend-neutral and does not import `Algorithms`.
-/

namespace Mettapedia.Languages.MeTTa.ExecutionContract

open Mettapedia.Languages.MeTTa.ElaboratedCore
open Mettapedia.Languages.MeTTa.RuntimeKernel
open MeTTailCore.MeTTaIL.EffectSafety
open MeTTailCore.MeTTaIL.LookupPlan

/-- Who owns the execution of a certified entry. -/
inductive ExecutionOwner where
  | artifactBackend
  | groundedBuiltin
  | externalOracle
deriving Repr, DecidableEq, BEq

/-- Stable demand vocabulary for builtin execution contracts. -/
inductive BuiltinDemandKind where
  | rawArgs
  | structuralEqArgs
  | boolArgs
  | boolThenElseArgs
  | numericArgs
  | floatArgs
  | tupleArgs
  | elemAndTupleArgs
deriving Repr, DecidableEq, BEq

/-- Structural argument roles for relation-premise lowering contracts. -/
inductive PremiseArgRole where
  | pattern
  | template
  | resultVar
  | plainInput
deriving Repr, DecidableEq, BEq

/-- Binding discipline for relation-premise result variables. -/
inductive ResultBindingPolicy where
  | mustBeFreshVar
  | mayReuseBoundVar
deriving Repr, DecidableEq, BEq

/-- Structural lowering family for relation-premise compilation. -/
inductive RelationPremiseLoweringKind where
  | factMatchEmitPayload
  | lookupExists
  | lookupEnumerate
deriving Repr, DecidableEq, BEq

/-- Payload categories for stateful space-effect contracts. -/
inductive SpaceEffectPayloadKind where
  | factPayload
  | sourceRulePayload
deriving Repr, DecidableEq, BEq

/-- Sink categories for stateful space-effect compilation. -/
inductive SpaceEffectSinkKind where
  | insertFact
  | removeFact
  | insertRule
  | removeRule
deriving Repr, DecidableEq, BEq

/-- Contract-level payload-shape classifier for stateful space effects. -/
inductive PayloadPatternShapeKind where
  | anyPattern
  | nonRewritePattern
  | rewriteEqRule
deriving Repr, DecidableEq, BEq

/-- Structural lowering family for grounded host builtins.

This describes the kind of host-side implementation a runtime may attach after
validating the exported contract. It is intentionally structural: it classifies
the lowering discipline rather than embedding host code or MM2 text. -/
inductive GroundedBuiltinHostKind where
  | numericCompare
  | f64Predicate
  | tupleMembership
  | isVariableTerm
  | reprTerm
  | parseTerm
  | printlnTerm
  | metaTypeOfTerm
  | typeOfTerm
  | quoteTerm
  | testAssertion
deriving Repr, DecidableEq, BEq

/-- How an aggregation lane packages collected backend results. -/
inductive AggregationCollectionKind where
  | tupleExpr
  | minAtom
  | maxAtom
deriving Repr, DecidableEq, BEq

/-- Where an aggregation lane obtains the results it packages. -/
inductive AggregationSourceKind where
  | subevalAllResults
deriving Repr, DecidableEq, BEq

/-- Structural control families that orchestrate nested certified evaluation. -/
inductive ControlBuiltinKind where
  | bindThenBody
  | sequenceLastResult
deriving Repr, DecidableEq, BEq

/-- Structural eligibility conditions for executable lanes.

These do not assign ownership of a surface head forever. They describe when a
particular execution lane may fire.

Positive example:
- a grounded integer-comparison lane may require `groundNumericArgs`

Negative example:
- this is not a blanket statement that a symbol like `<` is "owned by Rust". -/
inductive LaneEligibilityKind where
  | always
  | groundNumericArgs
  | groundBoolArgs
  | groundConditionOnly
  | groundStructuralEqArgs
deriving Repr, DecidableEq, BEq

/-- What to do when a certified lane is present but inapplicable.

Positive example:
- grounded comparisons can say `fallbackToRules`, allowing ordinary symbolic
  rule semantics to try when the args are not yet ground
- `if` can say `symbolicFallback`, reserving room for a future symbolic/MM2
  guard path instead of forcing a hard failure

Negative example:
- this is not permission to silently invent a new execution path in Rust; the
  residual policy only governs what happens after the exported lane is found to
  be inapplicable. -/
inductive ResidualPolicy where
  | failClosed
  | fallbackToRules
  | symbolicFallback
deriving Repr, DecidableEq, BEq

/-- Declarative result-shape class for numeric builtins.

This is part of observable evaluation semantics, not a formatting afterthought.
It records the fixed operator-class part of SWI/PeTTa numeric result behavior,
while the runtime may still need to inspect the actual argument classes to pick
the concrete MM2 lowering lane.

Positive example:
- `sqrt-math` is `alwaysFloat`
- `round-math` is `alwaysInteger`
- `+` is `preserveIntegralIfExact`

Negative example:
- this does not say that every numeric head always returns floats, and it does
  not collapse operator-specific behavior into one coarse "numeric" bucket. -/
inductive NumericResultShape where
  | preserveIntegralIfExact
  | alwaysFloat
  | alwaysInteger
  | preserveInputNumericClass
deriving Repr, DecidableEq, BEq

/-- Shared execution-permission envelope carried by every contract lane. -/
structure ExecutionPermission where
  owner : ExecutionOwner
  kernelClass : RuntimeKernelClass
  effectClass : EffectClass
  resourceClass : RuntimeResourceClass
  backendName : String
  supportedMemoShapes : List MemoShape := []
  sourceRuleCompilable : Bool := false
  queryCompilable : Bool := false
  spaceEffectCompilable : Bool := false
  theoremRefs : List String := []
deriving Repr, DecidableEq, BEq

/-- First contract lane: a lookup/query optimization certificate. -/
structure LookupQueryContract where
  head : String
  surfaceHead : Option String := none
  arity : Nat
  lookupFamily : LookupFamilyPlan
  owner : ExecutionOwner
  kernelClass : RuntimeKernelClass := .query
  effectClass : EffectClass
  resourceClass : RuntimeResourceClass
  backendName : String
  supportedMemoShapes : List MemoShape := []
  sourceRuleCompilable : Bool := false
  queryCompilable : Bool := false
  spaceEffectCompilable : Bool := false
  builtinDemand : Option BuiltinDemandKind := none
  theoremRefs : List String := []
deriving Repr, DecidableEq, BEq

/-- Second contract lane: stateful space-effect certificates. -/
structure SpaceEffectContract where
  head : String
  arity : Nat
  owner : ExecutionOwner
  kernelClass : RuntimeKernelClass := .spaceEffect
  effectClass : EffectClass
  resourceClass : RuntimeResourceClass
  backendName : String
  sourceRuleCompilable : Bool := false
  queryCompilable : Bool := false
  spaceEffectCompilable : Bool := false
  theoremRefs : List String := []
deriving Repr, DecidableEq, BEq

/-- Relation-premise certificates used to lower premise chains without
re-deriving argument roles or binding policies in Rust. -/
structure RelationPremiseContract where
  relation : String
  arity : Nat
  lookupFamily : LookupFamilyPlan
  argRoles : List PremiseArgRole
  resultBindingPolicy : Option ResultBindingPolicy := none
  loweringKind : RelationPremiseLoweringKind
  owner : ExecutionOwner
  kernelClass : RuntimeKernelClass := .query
  effectClass : EffectClass
  resourceClass : RuntimeResourceClass
  backendName : String
  supportedMemoShapes : List MemoShape := []
  theoremRefs : List String := []
deriving Repr, DecidableEq, BEq

/-- Space-effect payload certificates make the payload lane explicit instead of
forcing Rust to guess from surface syntax. -/
structure SpaceEffectPayloadContract where
  head : String
  arity : Nat
  spaceArgPosition : Nat
  payloadArgPosition : Nat
  payloadKind : SpaceEffectPayloadKind
  payloadShape : PayloadPatternShapeKind
  sinkKind : SpaceEffectSinkKind
  owner : ExecutionOwner
  kernelClass : RuntimeKernelClass := .spaceEffect
  effectClass : EffectClass
  resourceClass : RuntimeResourceClass
  backendName : String
  sourceRuleCompilable : Bool := false
  queryCompilable : Bool := false
  spaceEffectCompilable : Bool := false
  theoremRefs : List String := []
deriving Repr, DecidableEq, BEq

/-- Third contract lane: pure intrinsic builtins exposed through relation-backed
execution rather than rewrite rules or external grounded calls. -/
structure IntrinsicBuiltinContract where
  head : String
  relation : String
  minArity : Nat
  maxArity : Option Nat := none
  owner : ExecutionOwner
  kernelClass : RuntimeKernelClass := .ruleExec
  effectClass : EffectClass
  resourceClass : RuntimeResourceClass
  backendName : String
  supportedMemoShapes : List MemoShape := []
  builtinDemand : BuiltinDemandKind
  numericResultShape : Option NumericResultShape := none
  eligibility : LaneEligibilityKind := .always
  residualPolicy : ResidualPolicy := .failClosed
  theoremRefs : List String := []
deriving Repr, DecidableEq, BEq

/-- Fourth contract lane: host-grounded builtins that are not currently exposed
through the MM2 intrinsic surface.

Positive example:
- integer comparisons such as `<` can be certified here as pure, deterministic,
  host-grounded reductions with explicit numeric demand.

Negative example:
- this lane is not a loophole for language-local evaluators: the runtime still
  has to validate the exported contract entry and may only attach the specific
  host-lowering family described by `hostKind`. -/
structure GroundedBuiltinContract where
  head : String
  minArity : Nat
  maxArity : Option Nat := none
  hostKind : GroundedBuiltinHostKind
  owner : ExecutionOwner
  kernelClass : RuntimeKernelClass := .ruleExec
  effectClass : EffectClass
  resourceClass : RuntimeResourceClass
  backendName : String
  supportedMemoShapes : List MemoShape := []
  builtinDemand : BuiltinDemandKind
  eligibility : LaneEligibilityKind := .always
  residualPolicy : ResidualPolicy := .failClosed
  theoremRefs : List String := []
deriving Repr, DecidableEq, BEq

/-- Fifth contract lane: aggregation/control forms that collect results from a
nested certified evaluation lane and package them structurally.

Positive example:
- `collapse` can be certified here as "run the body through the real backend,
  collect all terminal results, and package them into one tuple-style result"

Negative example:
- this is not permission to embed MM2 text templates inside the artifact; the
  contract describes the aggregation shape, while the runtime remains
  responsible for honest MM2/MORK lowering. -/
structure AggregationBuiltinContract where
  head : String
  minArity : Nat
  maxArity : Option Nat := none
  collectionKind : AggregationCollectionKind
  sourceKind : AggregationSourceKind
  owner : ExecutionOwner
  kernelClass : RuntimeKernelClass := .metaPhase
  effectClass : EffectClass
  resourceClass : RuntimeResourceClass
  backendName : String
  supportedMemoShapes : List MemoShape := []
  eligibility : LaneEligibilityKind := .always
  residualPolicy : ResidualPolicy := .failClosed
  theoremRefs : List String := []
deriving Repr, DecidableEq, BEq

/-- Sixth contract lane: control forms that sequence or bind nested certified
execution without inventing a parallel evaluator. -/
structure ControlBuiltinContract where
  head : String
  minArity : Nat
  maxArity : Option Nat := none
  controlKind : ControlBuiltinKind
  owner : ExecutionOwner
  kernelClass : RuntimeKernelClass := .metaPhase
  effectClass : EffectClass
  resourceClass : RuntimeResourceClass
  backendName : String
  supportedMemoShapes : List MemoShape := []
  eligibility : LaneEligibilityKind := .always
  residualPolicy : ResidualPolicy := .failClosed
  theoremRefs : List String := []
deriving Repr, DecidableEq, BEq

def LookupQueryContract.permission (c : LookupQueryContract) : ExecutionPermission :=
  { owner := c.owner
    kernelClass := c.kernelClass
    effectClass := c.effectClass
    resourceClass := c.resourceClass
    backendName := c.backendName
    supportedMemoShapes := c.supportedMemoShapes
    sourceRuleCompilable := c.sourceRuleCompilable
    queryCompilable := c.queryCompilable
    spaceEffectCompilable := c.spaceEffectCompilable
    theoremRefs := c.theoremRefs }

def SpaceEffectContract.permission (c : SpaceEffectContract) : ExecutionPermission :=
  { owner := c.owner
    kernelClass := c.kernelClass
    effectClass := c.effectClass
    resourceClass := c.resourceClass
    backendName := c.backendName
    sourceRuleCompilable := c.sourceRuleCompilable
    queryCompilable := c.queryCompilable
    spaceEffectCompilable := c.spaceEffectCompilable
    theoremRefs := c.theoremRefs }

def RelationPremiseContract.permission (c : RelationPremiseContract) : ExecutionPermission :=
  { owner := c.owner
    kernelClass := c.kernelClass
    effectClass := c.effectClass
    resourceClass := c.resourceClass
    backendName := c.backendName
    supportedMemoShapes := c.supportedMemoShapes
    theoremRefs := c.theoremRefs }

def SpaceEffectPayloadContract.permission (c : SpaceEffectPayloadContract) : ExecutionPermission :=
  { owner := c.owner
    kernelClass := c.kernelClass
    effectClass := c.effectClass
    resourceClass := c.resourceClass
    backendName := c.backendName
    sourceRuleCompilable := c.sourceRuleCompilable
    queryCompilable := c.queryCompilable
    spaceEffectCompilable := c.spaceEffectCompilable
    theoremRefs := c.theoremRefs }

def IntrinsicBuiltinContract.permission (c : IntrinsicBuiltinContract) : ExecutionPermission :=
  { owner := c.owner
    kernelClass := c.kernelClass
    effectClass := c.effectClass
    resourceClass := c.resourceClass
    backendName := c.backendName
    supportedMemoShapes := c.supportedMemoShapes
    theoremRefs := c.theoremRefs }

def GroundedBuiltinContract.permission (c : GroundedBuiltinContract) : ExecutionPermission :=
  { owner := c.owner
    kernelClass := c.kernelClass
    effectClass := c.effectClass
    resourceClass := c.resourceClass
    backendName := c.backendName
    supportedMemoShapes := c.supportedMemoShapes
    theoremRefs := c.theoremRefs }

def AggregationBuiltinContract.permission (c : AggregationBuiltinContract) : ExecutionPermission :=
  { owner := c.owner
    kernelClass := c.kernelClass
    effectClass := c.effectClass
    resourceClass := c.resourceClass
    backendName := c.backendName
    supportedMemoShapes := c.supportedMemoShapes
    theoremRefs := c.theoremRefs }

def ControlBuiltinContract.permission (c : ControlBuiltinContract) : ExecutionPermission :=
  { owner := c.owner
    kernelClass := c.kernelClass
    effectClass := c.effectClass
    resourceClass := c.resourceClass
    backendName := c.backendName
    supportedMemoShapes := c.supportedMemoShapes
    theoremRefs := c.theoremRefs }

end Mettapedia.Languages.MeTTa.ExecutionContract
