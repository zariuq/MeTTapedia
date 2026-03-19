import Mettapedia.Languages.MeTTa.HE.ContractExport
import Mettapedia.Languages.MeTTa.HE.ScopeContract
import Mettapedia.Languages.MeTTa.HE.OpProfile
import MeTTailCore.Crypto.SHA256

/-!
# HE Native Profile

Runtime-facing manifest for the HE MeTTa dialect. Tells the MM2/MORK backend
exactly what operators exist, their execution lanes, scope info, and which
runtime builtins are required.

## Contract-First Rule

Per `mettail-rust/CLAUDE.md`: profile chooses, contracts execute, Rust lowers
certified lanes. This file IS the profile. The execution contract and scope
contract are the contracts. Rust implements what's listed here and nothing else.

## Source of Truth

- **Execution lanes**: `ContractCatalog.lean` (heExecutionEntries)
- **Scope info**: `ScopeContract.lean` (heScopeContractArtifact)
- **Op classification**: `OpProfile.lean` (tier1Ops)
- **Computable spec**: `EvalSpec.lean` + `MinimalMeTTa.lean`
- **Backend**: MM2/MORK (NOT Datalog/Ascent)

## What This Exports

For each HE operator:
- head name, arity, classification category
- execution lane (control, grounded, minimal-instruction, etc.)
- effect class, resource class, backend name
- scope kind and binder/value/body positions (if applicable)
-/

namespace Mettapedia.Languages.MeTTa.HE.NativeProfile

open Mettapedia.Languages.MeTTa.HE.ExecutionContract
open Mettapedia.Languages.MeTTa.HE.ScopeContract
open Mettapedia.Languages.MeTTa.HE.OpProfile
open Mettapedia.Languages.MeTTa.ScopeContract
open Mettapedia.Languages.MeTTa.ExecutionContract
open MeTTailCore.MeTTaIL.EffectSafety

/-! ## Op Profile Entry (JSON-exportable) -/

structure OpProfileEntry where
  name : String
  category : String
  interpreterRef : String
  languageDefRule : Option String
deriving Repr, DecidableEq

private def opCategoryToString : OpCategory → String
  | .surfaceSugar => "surfaceSugar"
  | .preludeEqAndType => "preludeEqAndType"
  | .mettaCallControl => "mettaCallControl"
  | .minimalInstruction => "minimalInstruction"
  | .groundedBuiltin => "groundedBuiltin"

private def opEntryToProfileEntry (e : OpEntry) : OpProfileEntry where
  name := e.name
  category := opCategoryToString e.category
  interpreterRef := e.interpreterRef
  languageDefRule := e.languageDefRule

/-! ## Contract Profile Entry (from execution contract) -/

structure ContractProfileEntry where
  head : String
  contractKind : String
  effectClass : String
  backendName : String
deriving Repr, DecidableEq

private def effectClassToString : EffectClass → String
  | .pureStructural => "pureStructural"
  | .readOnlyLookup => "readOnlyLookup"
  | .nondeterministicReadOnly => "nondeterministicReadOnly"
  | .writesState => "writesState"
  | .oracleIO => "oracleIO"

private def contractKindToString : ExecutionContractEntry → String
  | .lookupQuery _ => "lookupQuery"
  | .spaceEffect _ => "spaceEffect"
  | .relationPremise _ => "relationPremise"
  | .spaceEffectPayload _ => "spaceEffectPayload"
  | .intrinsicBuiltin _ => "intrinsicBuiltin"
  | .groundedBuiltin _ => "groundedBuiltin"
  | .aggregationBuiltin _ => "aggregationBuiltin"
  | .controlBuiltin _ => "controlBuiltin"

private def entryEffectClass : ExecutionContractEntry → EffectClass
  | .lookupQuery e => e.effectClass
  | .spaceEffect e => e.effectClass
  | .relationPremise e => e.effectClass
  | .spaceEffectPayload e => e.effectClass
  | .intrinsicBuiltin e => e.effectClass
  | .groundedBuiltin e => e.effectClass
  | .aggregationBuiltin e => e.effectClass
  | .controlBuiltin e => e.effectClass

private def entryBackendName : ExecutionContractEntry → String
  | .lookupQuery e => e.backendName
  | .spaceEffect e => e.backendName
  | .relationPremise e => e.backendName
  | .spaceEffectPayload e => e.backendName
  | .intrinsicBuiltin e => e.backendName
  | .groundedBuiltin e => e.backendName
  | .aggregationBuiltin e => e.backendName
  | .controlBuiltin e => e.backendName

private def execEntryToContractProfile (e : ExecutionContractEntry) : ContractProfileEntry where
  head := e.head
  contractKind := contractKindToString e
  effectClass := effectClassToString (entryEffectClass e)
  backendName := entryBackendName e

/-! ## Scope Profile Entry (from scope contract) -/

structure ScopeProfileEntry where
  head : String
  arity : Nat
  scopeKind : String
  binderPositions : List Nat
  valuePositions : List Nat
  bodyPositions : List Nat
  sequential : Bool
  allowsWildcard : Bool
deriving Repr, DecidableEq

private def scopeKindToString : ScopeKind → String
  | .letLike => "letLike"
  | .chainLike => "chainLike"
  | .letStarLike => "letStarLike"
  | .matchLike => "matchLike"
  | .lambdaLike => "lambdaLike"
  | .caseLike => "caseLike"
  | .sourceRulePayload => "sourceRulePayload"

private def scopeEntryToProfileEntry (e : ScopeContractEntry) : ScopeProfileEntry where
  head := e.head
  arity := e.arity
  scopeKind := scopeKindToString e.scopeKind
  binderPositions := e.binderPositions
  valuePositions := e.valuePositions
  bodyPositions := e.bodyPositions
  sequential := e.sequential
  allowsWildcard := e.allowsWildcard

/-! ## HE Native Profile -/

structure HENativeProfile where
  dialect : String
  backend : String
  opProfiles : List OpProfileEntry
  contractProfiles : List ContractProfileEntry
  scopeProfiles : List ScopeProfileEntry
deriving Repr

def heNativeProfile : HENativeProfile where
  dialect := "he"
  backend := "MM2/MORK"
  opProfiles := tier1Ops.map opEntryToProfileEntry
  contractProfiles := heExecutionEntries.map execEntryToContractProfile
  scopeProfiles := heScopeContractArtifact.entries.map scopeEntryToProfileEntry

/-! ## JSON Rendering -/

private def jsonEscape (s : String) : String :=
  s.foldl (fun acc c =>
    if c == '"' then acc ++ "\\\""
    else if c == '\\' then acc ++ "\\\\"
    else if c == '\n' then acc ++ "\\n"
    else acc.push c) ""

private def jsonStr (s : String) : String := s!"\"{jsonEscape s}\""
private def jsonBool (b : Bool) : String := if b then "true" else "false"
private def jsonNat (n : Nat) : String := s!"{n}"

private def jsonOptStr : Option String → String
  | some s => jsonStr s
  | none => "null"

private def jsonNatList (xs : List Nat) : String :=
  "[" ++ String.intercalate ", " (xs.map jsonNat) ++ "]"

private def renderOpProfile (e : OpProfileEntry) : String :=
  "    {"
    ++ s!" \"name\": {jsonStr e.name}"
    ++ s!", \"category\": {jsonStr e.category}"
    ++ s!", \"interpreterRef\": {jsonStr e.interpreterRef}"
    ++ s!", \"languageDefRule\": {jsonOptStr e.languageDefRule}"
    ++ " }"

private def renderContractProfile (e : ContractProfileEntry) : String :=
  "    {"
    ++ s!" \"head\": {jsonStr e.head}"
    ++ s!", \"contractKind\": {jsonStr e.contractKind}"
    ++ s!", \"effectClass\": {jsonStr e.effectClass}"
    ++ s!", \"backendName\": {jsonStr e.backendName}"
    ++ " }"

private def renderScopeProfile (e : ScopeProfileEntry) : String :=
  "    {"
    ++ s!" \"head\": {jsonStr e.head}"
    ++ s!", \"arity\": {jsonNat e.arity}"
    ++ s!", \"scopeKind\": {jsonStr e.scopeKind}"
    ++ s!", \"binderPositions\": {jsonNatList e.binderPositions}"
    ++ s!", \"valuePositions\": {jsonNatList e.valuePositions}"
    ++ s!", \"bodyPositions\": {jsonNatList e.bodyPositions}"
    ++ s!", \"sequential\": {jsonBool e.sequential}"
    ++ s!", \"allowsWildcard\": {jsonBool e.allowsWildcard}"
    ++ " }"

def HENativeProfile.renderJson (p : HENativeProfile) : String :=
  let opLines := String.intercalate ",\n" (p.opProfiles.map renderOpProfile)
  let contractLines := String.intercalate ",\n" (p.contractProfiles.map renderContractProfile)
  let scopeLines := String.intercalate ",\n" (p.scopeProfiles.map renderScopeProfile)
  "{\n"
    ++ s!"  \"dialect\": {jsonStr p.dialect},\n"
    ++ s!"  \"backend\": {jsonStr p.backend},\n"
    ++ s!"  \"opProfiles\": [\n{opLines}\n  ],\n"
    ++ s!"  \"contractProfiles\": [\n{contractLines}\n  ],\n"
    ++ s!"  \"scopeProfiles\": [\n{scopeLines}\n  ]\n"
    ++ "}"

def HENativeProfile.checksumString (p : HENativeProfile) : String :=
  MeTTailCore.Crypto.SHA256.sha256Hex p.renderJson

/-! ## Export / Check -/

def exportHeNativeProfile (outDir : System.FilePath) : IO UInt32 := do
  let profile := heNativeProfile
  let jsonPath := outDir / "he.native_profile.json"
  let checksumPath := outDir / "he.native_profile.checksum"
  IO.FS.createDirAll outDir
  IO.FS.writeFile jsonPath (profile.renderJson ++ "\n")
  IO.FS.writeFile checksumPath (profile.checksumString ++ "\n")
  IO.println s!"exported he native profile to {outDir}"
  pure 0

def checkHeNativeProfile (outDir : System.FilePath) : IO UInt32 := do
  let profile := heNativeProfile
  let jsonPath := outDir / "he.native_profile.json"
  let checksumPath := outDir / "he.native_profile.checksum"
  try
    let jsonText ← IO.FS.readFile jsonPath
    let checksumText ← IO.FS.readFile checksumPath
    let jsonOk := jsonText.trimAscii.toString == profile.renderJson.trimAscii.toString
    let checksumOk := checksumText.trimAscii.toString == profile.checksumString.trimAscii.toString
    if jsonOk && checksumOk then
      IO.println s!"[ok] he native profile matches at {outDir}"
      pure 0
    else
      if !jsonOk then
        IO.println s!"[drift] he native profile json mismatch at {jsonPath}"
      if !checksumOk then
        IO.println s!"[drift] he native profile checksum mismatch at {checksumPath}"
      pure 3
  catch e =>
    IO.println s!"he native profile check failed: {e}"
    pure 2

/-! ## Summary -/

section Canaries
#check @heNativeProfile
#check @exportHeNativeProfile
#check @checkHeNativeProfile
end Canaries

end Mettapedia.Languages.MeTTa.HE.NativeProfile
