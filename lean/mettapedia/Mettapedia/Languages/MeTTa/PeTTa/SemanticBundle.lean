import Mettapedia.Languages.MeTTa.PeTTa.OSLFPackage
import Mettapedia.Languages.MeTTa.PeTTa.StageFiber
import Mettapedia.Languages.MeTTa.PeTTa.BoundaryContract
import Mettapedia.Languages.MeTTa.PeTTa.ContractCatalog
import MeTTailCore.MeTTaIL.TransitionSpec
import MeTTailCore.MeTTaIL.RewriteIR
import MeTTailCore.MeTTaIL.EffectSafety
import MeTTailCore.Crypto.SHA256

/-!
# PeTTa Semantic Bundle — Canonical GSLT Semantic Object

The `PeTTaSemanticBundle` is the canonical semantic object from which all
downstream views (OSLF type system, proof-side NTT, runtime native profile)
are derived. It unifies the per-stage semantic package with the artifact
pipeline in a single typed record.

## Design Rationale

GPT-5.4 Pro's audit identified that the GSLT vertex for PeTTa should be a
**semantic bundle**, not merely a `LanguageDef` at a fiber vertex:

- **OSLF** comes from `lang + relEnv`
- **Runtime NTT** comes from `transitionSpec + rewriteIR + exec/scope/boundary`
- Both come from the **same** bundle

This prevents architectural drift between the proof side and the runtime side.

## Architecture

```
PeTTaSemanticBundle
    │
    ├──→ bundleOSLF        → OSLFTypeSystem     (proof-side OSLF)
    ├──→ bundleProofNTT    → NativeType          (proof-side NTT)
    │
    └──→ bundleNativeProfile → PeTTaNativeProfile (runtime-side, populated)
             │
             ├──→ inputs            (artifact checksums for stale-profile detection)
             ├──→ ruleProfiles      (from RewriteIR, with planMode + semanticMode)
             ├──→ contractProfiles  (from execution contracts, with contractKey/arity/kind)
             ├──→ scopeProfiles     (from scope contracts, with arity/valuePositions)
             ├──→ boundaryProfiles  (from boundary contracts)
             │
             └──→ renderJson / exportPeTTaNativeProfile → JSON for Rust
```

## Key Invariants

- All stages share the same `LanguageDef` (`pettaSpaceToLangDef s`)
- Only 2 distinct OSLF classes exist (sourceCore vs all others)
- Stage-filtered exec/scope entries are monotone
- The bundle at `sourceCore` projects to existing `pettaOSLF`
- Boundary entries are cross-checked against execution contracts
- Input checksums enable Rust-side stale-profile detection

## References

- `Mettapedia.Languages.MeTTa.PeTTa.OSLFPackage` — `PeTTaOSLFPackage`, `pettaPkg`
- `Mettapedia.Languages.MeTTa.PeTTa.StageFiber` — `pettaStageFiber`, `pettaStageOSLF`
- `Mettapedia.Languages.MeTTa.PeTTa.BoundaryContract` — `BoundaryContractArtifact`
- `MeTTailCore.MeTTaIL.TransitionSpec` — `TransitionSpecArtifact`
- `MeTTailCore.MeTTaIL.RewriteIR` — `RewriteIRArtifact`
-/

namespace Mettapedia.Languages.MeTTa.PeTTa.SemanticBundle

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.Languages.MeTTa.ExecutionContract
  (ExecutionContractArtifact ExecutionContractEntry)
open Mettapedia.Languages.MeTTa.ScopeContract
  (ScopeContractArtifact ScopeContractEntry ScopeKind)
open Mettapedia.Languages.MeTTa.PeTTa.StageIndex
open Mettapedia.Languages.MeTTa.PeTTa.LPSoundness
open Mettapedia.Languages.MeTTa.PeTTa.OSLFPackage
open Mettapedia.Languages.MeTTa.PeTTa.OSLFInstance
open Mettapedia.Languages.MeTTa.PeTTa.StageFiber
open Mettapedia.Languages.MeTTa.PeTTa.BoundaryContract
open Mettapedia.Languages.MeTTa.PeTTa.ExecutionContract
  (pettaExecutionContractArtifact)
open MeTTailCore.MeTTaIL.TransitionSpec (TransitionSpecArtifact)
open MeTTailCore.MeTTaIL.RewriteIR (RewriteIRArtifact RewriteIRRule RewriteIRRuleMode)
open MeTTailCore.MeTTaIL.EffectSafety (EffectClass)
open Mettapedia.Languages.MeTTa.ElaboratedCore (RuntimeResourceClass)

/-! ## §1 Canonical Semantic Bundle -/

/-- The canonical PeTTa semantic bundle: a single typed record from which
    all proof-side and runtime-side views are derived.

    This is the semantic object that the council recommends freezing as the
    ownership point for PeTTa's GSLT → OSLF → NTT pipeline. -/
structure PeTTaSemanticBundle where
  /-- The PeTTa stage this bundle represents. -/
  stage : PeTTaStage
  /-- The underlying PeTTa space (facts + rules). -/
  space : PeTTaSpace
  /-- The compiled `LanguageDef` (derived from `space.rules`). -/
  lang : LanguageDef
  /-- The relation environment for premise-aware reductions. -/
  relEnv : RelationEnv
  /-- The transition specification artifact (rule priorities, semantic keys). -/
  transitionSpec : TransitionSpecArtifact
  /-- The rewrite IR artifact (rule modes, variable flow, root update hints). -/
  rewriteIR : RewriteIRArtifact
  /-- Stage-filtered execution contract entries. -/
  execArtifact : ExecutionContractArtifact
  /-- Stage-filtered scope contract entries. -/
  scopeArtifact : ScopeContractArtifact
  /-- Boundary contract entries (only meaningful at `boundaryAware`). -/
  boundaryArtifact : BoundaryContractArtifact
  /-- The `lang` field equals `pettaSpaceToLangDef space`. -/
  lang_eq : lang = pettaSpaceToLangDef space
  /-- The `relEnv` field equals `(pettaPkg stage space).relEnv`. -/
  relEnv_eq : relEnv = (pettaPkg stage space).relEnv

/-! ## §2 Bundle Construction -/

/-- Construct the canonical semantic bundle for a PeTTa space at a given stage.

    The `transitionSpec` and `rewriteIR` are provided externally because their
    derivation is fallible (`Except String`). The caller is responsible for
    ensuring they correspond to the given space. -/
def mkBundle (stage : PeTTaStage) (s : PeTTaSpace)
    (ts : TransitionSpecArtifact) (ir : RewriteIRArtifact) :
    PeTTaSemanticBundle where
  stage := stage
  space := s
  lang := pettaSpaceToLangDef s
  relEnv := (pettaPkg stage s).relEnv
  transitionSpec := ts
  rewriteIR := ir
  execArtifact :=
    { dialect := "PeTTa"
    , entries := stageExecEntries stage }
  scopeArtifact :=
    { dialect := "PeTTa"
    , wildcardSymbol := "_"
    , entries := stageScopeEntries stage }
  boundaryArtifact := pettaBoundaryContractArtifact
  lang_eq := rfl
  relEnv_eq := rfl

/-! ## §3 Proof-Side Views -/

/-- The OSLF type system derived from the bundle.

    Uses `langOSLFUsing` with the bundle's `relEnv` and `lang`.
    This is the type system that governs predicate semantics,
    ◇/□ modalities, and substitutability at this stage. -/
def bundleOSLF (B : PeTTaSemanticBundle) :=
  langOSLFUsing B.relEnv B.lang "Expr"

/-- The proof-side native type derived from the bundle.

    A native type is a (sort, predicate) pair from the OSLF type system.
    This is the NTT object used for proof obligations (not runtime). -/
def bundleProofNTT (B : PeTTaSemanticBundle) :=
  langNativeTypeUsing B.relEnv B.lang "Expr"

/-- The Galois connection ◇ ⊣ □ at the bundle's stage. -/
theorem bundleGalois (B : PeTTaSemanticBundle) :
    GaloisConnection
      (langDiamondUsing B.relEnv B.lang)
      (langBoxUsing B.relEnv B.lang) :=
  langGaloisUsing B.relEnv B.lang

/-! ## §4 Runtime-Side Native Profile

Schema v2: split planMode/semanticMode, conservative memoEligible,
enriched ContractProfile, input checksums for stale-profile detection. -/

/-- Semantic classification of a rewrite rule for runtime lane policy.

    Separate from `RewriteIRRuleMode` (the physical application mode).
    `planMode` drives `RuleApplicationPlan`; `semanticMode` drives strict
    classification and lane policy. -/
inductive RuleSemanticClass where
  /-- Ordinary forward rewrite (no constraints, no free RHS vars, no premises). -/
  | ordinaryForward
  /-- Rule with premise relations requiring query resolution. -/
  | premiseAware
  /-- Compat-head rule requiring two-phase constraint matching. -/
  | compatHead
  /-- Rule with unbound RHS variables producing symbolic output. -/
  | symbolicOutput
  deriving DecidableEq, Repr

/-- A per-rule profile for runtime consumption.

    `planMode` is the physical RewriteIR mode (how the rule fires).
    `semanticMode` is the semantic classification (what lane policy applies).
    This split avoids conflating two distinct concerns in a single enum. -/
structure RuleProfile where
  /-- Rule identifier (from RewriteIR). -/
  ruleId : String
  /-- Source instruction head. -/
  sourceHead : String
  /-- Physical rule-application mode. -/
  planMode : RewriteIRRuleMode
  /-- Semantic classification for lane policy. -/
  semanticMode : RuleSemanticClass
  /-- Whether the rule is deterministic (at most one result). -/
  deterministic : Bool := false
  /-- Whether the rule is eligible for memoization.
      Conservative: only `ordinaryForward` is memo-eligible. -/
  memoEligible : Bool := false
  /-- Premise relation names (empty for premise-free rules). -/
  premiseRelations : List String := []
  deriving Repr

/-- Kind of execution contract entry, for the contract profile summary.

    This enum lives in SemanticBundle.lean (not SuiteBase) to avoid a
    layering inversion — the suite-base layer must not depend on
    PeTTa-specific types. -/
inductive ContractProfileKind where
  | lookupQuery
  | relationPremise
  | spaceEffect
  | spaceEffectPayload
  | intrinsicBuiltin
  | groundedBuiltin
  | aggregationBuiltin
  | controlBuiltin
  deriving DecidableEq, Repr

/-- A per-contract profile for runtime consumption.

    Enriched over the previous `OpProfile`: includes `contractKey` (from
    `ExecutionContractEntry.sortKey`), `arity`, and `kind`. -/
structure ContractProfile where
  /-- Unique contract key (from `ExecutionContractEntry.sortKey`). -/
  contractKey : String
  /-- Operation head symbol. -/
  head : String
  /-- Arity. -/
  arity : Nat
  /-- Contract entry kind. -/
  kind : ContractProfileKind
  /-- Effect class. -/
  effectClass : EffectClass
  /-- Resource class. -/
  resourceClass : RuntimeResourceClass
  /-- Backend name for dispatch. -/
  backendName : String
  deriving Repr

/-- A per-scope profile for runtime consumption.

    Enriched: includes `arity`, `valuePositions`, `sequential`, `allowsWildcard`
    from `ScopeContractEntry`. -/
structure ScopeProfile where
  /-- Scope head symbol. -/
  head : String
  /-- Arity. -/
  arity : Nat
  /-- Scope kind. -/
  scopeKind : ScopeKind
  /-- Binder positions. -/
  binderPositions : List Nat := []
  /-- Value positions. -/
  valuePositions : List Nat := []
  /-- Body positions. -/
  bodyPositions : List Nat := []
  /-- Whether evaluation is sequential. -/
  sequential : Bool := false
  /-- Whether wildcard is allowed. -/
  allowsWildcard : Bool := true
  deriving Repr

/-- A per-boundary profile for runtime consumption. -/
structure BoundaryProfile where
  /-- Operation head symbol. -/
  head : String
  /-- Boundary kind. -/
  boundaryKind : BoundaryKind
  /-- Witness lane strategy. -/
  witnessLane : WitnessLane
  /-- Residual lane strategy. -/
  residualLane : ResidualLane
  deriving Repr

/-- Input artifact checksums embedded in the native profile.

    Rust uses these for stale-profile detection at load time: if the
    checksums don't match the currently-loaded artifacts, the profile
    was derived from different artifacts and must be rejected. -/
structure NativeProfileInputs where
  transitionSpecChecksum : String
  rewriteIRChecksum : String
  execContractChecksum : String
  scopeContractChecksum : String
  boundaryContractChecksum : String
  deriving Repr

/-- The runtime-side native profile derived from a semantic bundle.

    Schema version 3. This is the object Rust should load in strict mode.
    It contains everything needed for lane selection without reconstructing
    semantics heuristically.

    Design principle: **Profile chooses. Contracts execute.**
    The profile is a certified dispatch summary, not a replacement for
    the detailed execution/scope/boundary contracts. -/
structure PeTTaNativeProfile where
  /-- The stage this profile was derived from. -/
  stage : PeTTaStage
  /-- Explicit semantic variant tag.
      Enables distinguishing semantic variants across runtimes and languages.
      E.g., `"petta-2026-03-boundary-aware"`, `"he-impl-fluid-let"`. -/
  semanticsVariant : String := "petta-2026-03-boundary-aware"
  /-- Input artifact checksums for stale-profile detection. -/
  inputs : NativeProfileInputs
  /-- Per-rule profiles from the rewrite IR. -/
  ruleProfiles : List RuleProfile
  /-- Per-contract profiles from execution contracts. -/
  contractProfiles : List ContractProfile
  /-- Per-scope profiles from scope contracts. -/
  scopeProfiles : List ScopeProfile
  /-- Per-boundary profiles from boundary contracts. -/
  boundaryProfiles : List BoundaryProfile
  deriving Repr

/-! ## §5 Profile Derivation -/

/-- Classify a RewriteIR rule into a semantic class.

    The semantic class is distinct from `RewriteIRRuleMode` (the physical
    application mode). `ordinaryForward` with premises becomes `premiseAware`. -/
def deriveRuleSemanticClass (rule : RewriteIRRule) : RuleSemanticClass :=
  match rule.ruleMode with
  | .ordinaryForward =>
    if rule.premiseRelations.isEmpty then .ordinaryForward else .premiseAware
  | .compatHead => .compatHead
  | .symbolicOutput => .symbolicOutput

/-- Derive per-rule profiles from the rewrite IR artifact.

    `memoEligible` is conservative: only `ordinaryForward` (no premises,
    no compat-head, no symbolic output) is memo-eligible. This can be
    relaxed later with a proof of a narrower safe fragment. -/
def deriveRuleProfiles (ir : RewriteIRArtifact) : List RuleProfile :=
  ir.rules.map fun rule =>
    let sc := deriveRuleSemanticClass rule
    { ruleId := rule.ruleId
    , sourceHead := rule.sourceInstr
    , planMode := rule.ruleMode
    , semanticMode := sc
    , deterministic := sc == .ordinaryForward
    , memoEligible := sc == .ordinaryForward
    , premiseRelations := rule.premiseRelations }

/-- Map an `ExecutionContractEntry` to its `ContractProfileKind`.

    This mapping lives here (not in SuiteBase) to avoid a layering inversion. -/
private def entryToContractKind : ExecutionContractEntry → ContractProfileKind
  | .lookupQuery _ => .lookupQuery
  | .spaceEffect _ => .spaceEffect
  | .relationPremise _ => .relationPremise
  | .spaceEffectPayload _ => .spaceEffectPayload
  | .intrinsicBuiltin _ => .intrinsicBuiltin
  | .groundedBuiltin _ => .groundedBuiltin
  | .aggregationBuiltin _ => .aggregationBuiltin
  | .controlBuiltin _ => .controlBuiltin

/-- Derive per-contract profiles from execution contract entries. -/
def deriveContractProfiles (entries : List ExecutionContractEntry) :
    List ContractProfile :=
  entries.map fun e =>
    { contractKey := e.sortKey
    , head := e.head
    , arity := e.arity
    , kind := entryToContractKind e
    , effectClass := e.effectClass
    , resourceClass := e.resourceClass
    , backendName := e.backendName }

/-- Derive per-scope profiles from scope contract entries. -/
def deriveScopeProfiles (entries : List ScopeContractEntry) :
    List ScopeProfile :=
  entries.map fun e =>
    { head := e.head
    , arity := e.arity
    , scopeKind := e.scopeKind
    , binderPositions := e.binderPositions
    , valuePositions := e.valuePositions
    , bodyPositions := e.bodyPositions
    , sequential := e.sequential
    , allowsWildcard := e.allowsWildcard }

/-- Derive boundary profiles from the boundary contract artifact. -/
def deriveBoundaryProfiles (ba : BoundaryContractArtifact) :
    List BoundaryProfile :=
  ba.entries.map fun e =>
    { head := e.head
    , boundaryKind := e.boundaryKind
    , witnessLane := e.witnessLane
    , residualLane := e.residualLane }

/-! ## §5b Boundary Artifact Checksum -/

private def fnv64Offset : UInt64 := 14695981039346656037
private def fnv64Prime : UInt64 := 1099511628211

private def checksumText (text : String) : UInt64 :=
  text.toList.foldl
    (fun h c => (h ^^^ (UInt64.ofNat c.toNat)) * fnv64Prime)
    fnv64Offset

/-- Canonical rendering of a `BoundaryContractArtifact` for checksum purposes. -/
private def renderBoundaryArtifactForChecksum (ba : BoundaryContractArtifact) : String :=
  let renderEntry (e : BoundaryContractEntry) : String :=
    s!"{e.head}:{repr e.boundaryKind}:{repr e.witnessLane}:{repr e.residualLane}"
  s!"{ba.dialect}:" ++ String.intercalate ";" (ba.entries.map renderEntry)

/-- FNV-64 checksum of a `BoundaryContractArtifact`. -/
private def boundaryArtifactChecksumString (ba : BoundaryContractArtifact) : String :=
  toString (checksumText (renderBoundaryArtifactForChecksum ba))

/-- Derive the runtime-side native profile from a semantic bundle.

    All profile lists are populated from the bundle's artifacts:
    - `inputs` from artifact checksums (for Rust stale-profile detection)
    - `ruleProfiles` from `rewriteIR`
    - `contractProfiles` from `execArtifact`
    - `scopeProfiles` from `scopeArtifact`
    - `boundaryProfiles` from `boundaryArtifact` -/
def bundleNativeProfile (B : PeTTaSemanticBundle) :
    PeTTaNativeProfile where
  stage := B.stage
  semanticsVariant := "petta-2026-03-boundary-aware"
  inputs :=
    { transitionSpecChecksum := B.transitionSpec.checksumString
    , rewriteIRChecksum := B.rewriteIR.checksumString
    , execContractChecksum := B.execArtifact.checksumString
    , scopeContractChecksum := B.scopeArtifact.checksumString
    , boundaryContractChecksum := boundaryArtifactChecksumString B.boundaryArtifact }
  ruleProfiles := deriveRuleProfiles B.rewriteIR
  contractProfiles := deriveContractProfiles B.execArtifact.entries
  scopeProfiles := deriveScopeProfiles B.scopeArtifact.entries
  boundaryProfiles := deriveBoundaryProfiles B.boundaryArtifact

/-! ## §6 Boundary Cross-Checks -/

/-- Every boundary entry head appears in the execution contract artifact. -/
def boundaryHeadsInExecArtifact (ba : BoundaryContractArtifact)
    (ea : ExecutionContractArtifact) : Bool :=
  ba.entries.all fun be =>
    ea.entries.any fun ee => ee.head == be.head

#guard boundaryHeadsInExecArtifact pettaBoundaryContractArtifact
        pettaExecutionContractArtifact = true

/-! ## §7 JSON Export -/

private def jsonEscape (s : String) : String :=
  s.foldl (fun acc c =>
    acc ++ match c with
    | '"' => "\\\""
    | '\\' => "\\\\"
    | '\n' => "\\n"
    | _ => String.singleton c) ""

private def jsonStr (s : String) : String :=
  "\"" ++ jsonEscape s ++ "\""

private def jsonBool (b : Bool) : String :=
  if b then "true" else "false"

private def jsonNat (n : Nat) : String :=
  toString n

private def jsonStrList (xs : List String) : String :=
  "[" ++ String.intercalate "," (xs.map jsonStr) ++ "]"

private def jsonNatList (xs : List Nat) : String :=
  "[" ++ String.intercalate "," (xs.map jsonNat) ++ "]"

private def effectClassToJson : EffectClass → String
  | .pureStructural => "\"pure_structural\""
  | .readOnlyLookup => "\"read_only_lookup\""
  | .nondeterministicReadOnly => "\"nondeterministic_read_only\""
  | .writesState => "\"writes_state\""
  | .oracleIO => "\"oracle_io\""

private def resourceClassToJson : RuntimeResourceClass → String
  | .defaultAtomSpace => "\"default_atomspace\""
  | .namedAtomSpace => "\"named_atomspace\""
  | .mapResource => "\"map_resource\""
  | .queueResource => "\"queue_resource\""
  | .solverResource => "\"solver_resource\""
  | .externalResource => "\"external_resource\""

private def scopeKindToJson : ScopeKind → String
  | .letLike => "\"let_like\""
  | .chainLike => "\"chain_like\""
  | .letStarLike => "\"let_star_like\""
  | .matchLike => "\"match_like\""
  | .lambdaLike => "\"lambda_like\""
  | .caseLike => "\"case_like\""
  | .sourceRulePayload => "\"source_rule_payload\""

private def ruleSemanticClassToJson : RuleSemanticClass → String
  | .ordinaryForward => "\"ordinary_forward\""
  | .premiseAware => "\"premise_aware\""
  | .compatHead => "\"compat_head\""
  | .symbolicOutput => "\"symbolic_output\""

private def rewriteIRRuleModeToJson : RewriteIRRuleMode → String
  | .ordinaryForward => "\"ordinary_forward\""
  | .compatHead => "\"compat_head\""
  | .symbolicOutput => "\"symbolic_output\""

private def contractProfileKindToJson : ContractProfileKind → String
  | .lookupQuery => "\"lookup_query\""
  | .relationPremise => "\"relation_premise\""
  | .spaceEffect => "\"space_effect\""
  | .spaceEffectPayload => "\"space_effect_payload\""
  | .intrinsicBuiltin => "\"intrinsic_builtin\""
  | .groundedBuiltin => "\"grounded_builtin\""
  | .aggregationBuiltin => "\"aggregation_builtin\""
  | .controlBuiltin => "\"control_builtin\""

private def boundaryKindToJson : BoundaryKind → String
  | .compatHead => "\"compat_head\""
  | .groundedResidual => "\"grounded_residual\""
  | .groundedFailClosed => "\"grounded_fail_closed\""

private def witnessLaneToJson : WitnessLane → String
  | .spaceMatch => "\"space_match\""
  | .groundEval => "\"ground_eval\""
  | .typeQuery => "\"type_query\""
  | .none => "\"none\""

private def residualLaneToJson : ResidualLane → String
  | .symbolicFallback => "\"symbolic_fallback\""
  | .fallbackToRules => "\"fallback_to_rules\""
  | .failClosed => "\"fail_closed\""

private def stageToJson : PeTTaStage → String
  | .sourceCore => "\"source_core\""
  | .queryCore => "\"query_core\""
  | .statefulCore => "\"stateful_core\""
  | .boundaryAware => "\"boundary_aware\""

private def renderInputs (i : NativeProfileInputs) : String :=
  "{" ++ String.intercalate ","
    [ "\"transition_spec_checksum\":" ++ jsonStr i.transitionSpecChecksum
    , "\"rewrite_ir_checksum\":" ++ jsonStr i.rewriteIRChecksum
    , "\"exec_contract_checksum\":" ++ jsonStr i.execContractChecksum
    , "\"scope_contract_checksum\":" ++ jsonStr i.scopeContractChecksum
    , "\"boundary_contract_checksum\":" ++ jsonStr i.boundaryContractChecksum
    ] ++ "}"

private def renderRuleProfile (r : RuleProfile) : String :=
  "{" ++ String.intercalate ","
    [ "\"rule_id\":" ++ jsonStr r.ruleId
    , "\"source_head\":" ++ jsonStr r.sourceHead
    , "\"plan_mode\":" ++ rewriteIRRuleModeToJson r.planMode
    , "\"semantic_mode\":" ++ ruleSemanticClassToJson r.semanticMode
    , "\"deterministic\":" ++ jsonBool r.deterministic
    , "\"memo_eligible\":" ++ jsonBool r.memoEligible
    , "\"premise_relations\":" ++ jsonStrList r.premiseRelations
    ] ++ "}"

private def renderContractProfile (c : ContractProfile) : String :=
  "{" ++ String.intercalate ","
    [ "\"contract_key\":" ++ jsonStr c.contractKey
    , "\"head\":" ++ jsonStr c.head
    , "\"arity\":" ++ jsonNat c.arity
    , "\"kind\":" ++ contractProfileKindToJson c.kind
    , "\"effect_class\":" ++ effectClassToJson c.effectClass
    , "\"resource_class\":" ++ resourceClassToJson c.resourceClass
    , "\"backend_name\":" ++ jsonStr c.backendName
    ] ++ "}"

private def renderScopeProfile (s : ScopeProfile) : String :=
  "{" ++ String.intercalate ","
    [ "\"head\":" ++ jsonStr s.head
    , "\"arity\":" ++ jsonNat s.arity
    , "\"scope_kind\":" ++ scopeKindToJson s.scopeKind
    , "\"binder_positions\":" ++ jsonNatList s.binderPositions
    , "\"value_positions\":" ++ jsonNatList s.valuePositions
    , "\"body_positions\":" ++ jsonNatList s.bodyPositions
    , "\"sequential\":" ++ jsonBool s.sequential
    , "\"allows_wildcard\":" ++ jsonBool s.allowsWildcard
    ] ++ "}"

private def renderBoundaryProfile (b : BoundaryProfile) : String :=
  "{" ++ String.intercalate ","
    [ "\"head\":" ++ jsonStr b.head
    , "\"boundary_kind\":" ++ boundaryKindToJson b.boundaryKind
    , "\"witness_lane\":" ++ witnessLaneToJson b.witnessLane
    , "\"residual_lane\":" ++ residualLaneToJson b.residualLane
    ] ++ "}"

/-- Render the native profile as a JSON string (schema v3). -/
def PeTTaNativeProfile.renderJson (p : PeTTaNativeProfile) : String :=
  "{" ++ String.intercalate ","
    [ "\"schema_version\":3"
    , "\"dialect\":\"PeTTa\""
    , "\"semantics_variant\":" ++ jsonStr p.semanticsVariant
    , "\"stage\":" ++ stageToJson p.stage
    , "\"inputs\":" ++ renderInputs p.inputs
    , "\"rule_profiles\":[" ++
        String.intercalate "," (p.ruleProfiles.map renderRuleProfile) ++ "]"
    , "\"contract_profiles\":[" ++
        String.intercalate "," (p.contractProfiles.map renderContractProfile) ++ "]"
    , "\"scope_profiles\":[" ++
        String.intercalate "," (p.scopeProfiles.map renderScopeProfile) ++ "]"
    , "\"boundary_profiles\":[" ++
        String.intercalate "," (p.boundaryProfiles.map renderBoundaryProfile) ++ "]"
    ] ++ "}"

/-- SHA-256 checksum of the rendered JSON (schema v3).
    Returns a 64-character lowercase hex string. -/
def PeTTaNativeProfile.checksumString (p : PeTTaNativeProfile) : String :=
  MeTTailCore.Crypto.SHA256.sha256Hex p.renderJson

/-- Export the native profile as JSON + checksum files.

    Follows the same pattern as other PeTTa artifact exports
    (`exportPeTTaRewriteIR`, `exportPeTTaScopeContract`, etc.). -/
def exportPeTTaNativeProfile (outDir : System.FilePath)
    (s : PeTTaSpace) (stage : PeTTaStage)
    (ts : TransitionSpecArtifact) (ir : RewriteIRArtifact) : IO UInt32 := do
  let bundle := mkBundle stage s ts ir
  let profile := bundleNativeProfile bundle
  let jsonPath := outDir / "petta.native_profile.json"
  let checksumPath := outDir / "petta.native_profile.checksum"
  IO.FS.createDirAll outDir
  IO.FS.writeFile jsonPath (profile.renderJson ++ "\n")
  IO.FS.writeFile checksumPath (profile.checksumString ++ "\n")
  IO.println s!"exported petta native profile to {outDir}"
  pure 0

/-- Check that a previously-exported native profile matches the current
    artifacts. Verifies:

    1. **Checksum match** — stored checksum equals freshly-derived checksum
    2. **JSON content match** — stored JSON equals freshly-derived JSON

    The embedded `inputs` checksums are for **Rust-side** stale-profile
    detection at load time (against the Rust-loaded artifacts), not for
    this Lean-side check. The canonical JSON equality in check (2) inherently
    covers the inputs field. -/
def checkPeTTaNativeProfile (outDir : System.FilePath)
    (s : PeTTaSpace) (stage : PeTTaStage)
    (ts : TransitionSpecArtifact) (ir : RewriteIRArtifact) : IO UInt32 := do
  let bundle := mkBundle stage s ts ir
  let profile := bundleNativeProfile bundle
  let jsonPath := outDir / "petta.native_profile.json"
  let checksumPath := outDir / "petta.native_profile.checksum"
  try
    let jsonText ← IO.FS.readFile jsonPath
    let checksumText ← IO.FS.readFile checksumPath
    let checksumOk := checksumText.trimAscii == profile.checksumString.trimAscii
    let jsonOk := jsonText.trimAscii == profile.renderJson.trimAscii
    if checksumOk && jsonOk then
      pure 0
    else
      if !checksumOk then IO.println "native-profile: checksum mismatch"
      if !jsonOk then IO.println "native-profile: JSON content mismatch"
      pure 3
  catch _ =>
    IO.println "native-profile: file not found"
    pure 2

/-! ## §8 Compatibility Theorems -/

/-- The bundle's OSLF at `sourceCore` equals `pettaOSLF`. -/
theorem bundleOSLF_sourceCore_eq_pettaOSLF (s : PeTTaSpace)
    (ts : TransitionSpecArtifact) (ir : RewriteIRArtifact) :
    bundleOSLF (mkBundle .sourceCore s ts ir) = pettaOSLF s := rfl

/-- The bundle's OSLF equals the staged OSLF from `StageFiber.lean`. -/
theorem bundleOSLF_eq_pettaStageOSLF (s : PeTTaSpace) (stage : PeTTaStage)
    (ts : TransitionSpecArtifact) (ir : RewriteIRArtifact) :
    bundleOSLF (mkBundle stage s ts ir) = pettaStageOSLF s stage := rfl

/-- The bundle's `lang` equals `pettaSpaceToLangDef`. -/
theorem mkBundle_lang (stage : PeTTaStage) (s : PeTTaSpace)
    (ts : TransitionSpecArtifact) (ir : RewriteIRArtifact) :
    (mkBundle stage s ts ir).lang = pettaSpaceToLangDef s := rfl

/-- The bundle's `relEnv` equals the staged package's `relEnv`. -/
theorem mkBundle_relEnv (stage : PeTTaStage) (s : PeTTaSpace)
    (ts : TransitionSpecArtifact) (ir : RewriteIRArtifact) :
    (mkBundle stage s ts ir).relEnv = (pettaPkg stage s).relEnv := rfl

/-- The bundle's exec entries match the stage-filtered entries. -/
theorem mkBundle_execEntries (stage : PeTTaStage) (s : PeTTaSpace)
    (ts : TransitionSpecArtifact) (ir : RewriteIRArtifact) :
    (mkBundle stage s ts ir).execArtifact.entries = stageExecEntries stage := rfl

/-- The bundle's scope entries match the stage-filtered entries. -/
theorem mkBundle_scopeEntries (stage : PeTTaStage) (s : PeTTaSpace)
    (ts : TransitionSpecArtifact) (ir : RewriteIRArtifact) :
    (mkBundle stage s ts ir).scopeArtifact.entries = stageScopeEntries stage := rfl

/-- Honest 2-class: bundles at queryCore/statefulCore/boundaryAware share OSLF. -/
theorem bundleOSLF_queryCore_eq_statefulCore (s : PeTTaSpace)
    (ts₁ ts₂ : TransitionSpecArtifact) (ir₁ ir₂ : RewriteIRArtifact) :
    bundleOSLF (mkBundle .queryCore s ts₁ ir₁) =
    bundleOSLF (mkBundle .statefulCore s ts₂ ir₂) := rfl

theorem bundleOSLF_queryCore_eq_boundaryAware (s : PeTTaSpace)
    (ts₁ ts₂ : TransitionSpecArtifact) (ir₁ ir₂ : RewriteIRArtifact) :
    bundleOSLF (mkBundle .queryCore s ts₁ ir₁) =
    bundleOSLF (mkBundle .boundaryAware s ts₂ ir₂) := rfl

/-! ## §9 Stage Refinement via Bundle -/

/-- Reductions at the sourceCore bundle refine to any later stage's bundle. -/
theorem bundleReduces_sourceCore_refines_stage (s : PeTTaSpace)
    (stage : PeTTaStage) {p q : Pattern}
    (ts₁ ts₂ : TransitionSpecArtifact) (ir₁ ir₂ : RewriteIRArtifact)
    (hred : langReducesUsing (mkBundle .sourceCore s ts₁ ir₁).relEnv
              (mkBundle .sourceCore s ts₁ ir₁).lang p q) :
    langReducesUsing (mkBundle stage s ts₂ ir₂).relEnv
      (mkBundle stage s ts₂ ir₂).lang p q :=
  sourceCore_refines_stage_general s stage hred

/-! ## §10 Future LLM Instruction Block

> For PeTTa, the GSLT vertex is a semantic bundle, not just a `LanguageDef`.
> `OSLF = langOSLFUsing bundle.relEnv bundle.lang "Expr"`.
> `ProofNTT = langNativeTypeUsing bundle.relEnv bundle.lang "Expr"`.
> `RuntimeNTT = bundleNativeProfile bundle` (populated from all artifact fields).
> Profile chooses. Contracts execute. Rust must consume `RuntimeNTT` exported
> via `exportPeTTaNativeProfile` and must not reconstruct semantics heuristically.
> Do not claim 4 distinct OSLF stages unless stage-specific semantics beyond
> `relEnv` are encoded into the OSLF input object.

## §11 Summary

**0 sorries. 0 axioms. Schema v2.**

- `PeTTaSemanticBundle` — canonical semantic object for all downstream views
- `mkBundle` — stage-parameterized constructor
- `bundleOSLF` / `bundleProofNTT` — proof-side views
- `bundleNativeProfile` — runtime-side native profile (fully populated)
  - `inputs` — 5 artifact checksums (ts, ir, exec, scope, boundary)
  - `ruleProfiles` from RewriteIR (planMode + semanticMode, conservative memo)
  - `contractProfiles` from execution contracts (contractKey/arity/kind)
  - `scopeProfiles` from scope contracts (arity/valuePositions/sequential/allowsWildcard)
  - `deriveBoundaryProfiles` from boundary contracts (lanes)
- `PeTTaNativeProfile.renderJson` / `exportPeTTaNativeProfile` — JSON export
- `checkPeTTaNativeProfile` — checksum + canonical JSON equality check
- `boundaryHeadsInExecArtifact` — cross-check (kernel-verified `#guard`)
- Compatibility: `bundleOSLF_sourceCore_eq_pettaOSLF` (projects to existing OSLF)
- Honest 2-class: `bundleOSLF_queryCore_eq_*` (all `rfl`)
- Refinement: `bundleReduces_sourceCore_refines_stage`
-/

end Mettapedia.Languages.MeTTa.PeTTa.SemanticBundle
