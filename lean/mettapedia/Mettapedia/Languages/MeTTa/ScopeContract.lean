import Mettapedia.Languages.MeTTa.ExecutionContract

/-!
# MeTTa Scope Contract

Shared local-scope contract surface for MeTTa-family runtimes.

This artifact is deliberately separate from the execution contract. It governs
free-variable analysis and local binder scope for compiler/runtime plumbing,
not execution ownership.

Positive example:
- `let`, `chain`, and `let*` can declare where binders, values, and bodies
  live, so Rust does not have to rediscover those forms by head-specific
  pattern walkers.

Negative example:
- this file does not describe MM2 text, and it does not assign executable
  backend ownership to surface heads.
-/

namespace Mettapedia.Languages.MeTTa.ScopeContract

open Mettapedia.Languages.MeTTa.ExecutionContract

/-- Shared scope/binder classes used by compiler-side free-variable analysis. -/
inductive ScopeKind where
  | letLike
  | chainLike
  | letStarLike
  | lambdaLike
  | caseLike
  | sourceRulePayload
deriving Repr, DecidableEq, BEq

/-- Structural scope contract for one surface head. -/
structure ScopeContractEntry where
  head : String
  arity : Nat
  scopeKind : ScopeKind
  binderPositions : List Nat := []
  valuePositions : List Nat := []
  bodyPositions : List Nat := []
  scopedPayloadPositions : List Nat := []
  payloadShape : Option PayloadPatternShapeKind := none
  sequential : Bool := false
  allowsWildcard : Bool := true
  theoremRefs : List String := []
deriving Repr, DecidableEq, BEq

structure ScopeContractArtifact where
  schemaVersion : Nat := 1
  dialect : String
  wildcardSymbol : String := "_"
  entries : List ScopeContractEntry
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

private def renderScopeKind : ScopeKind → String
  | .letLike => "let_like"
  | .chainLike => "chain_like"
  | .letStarLike => "let_star_like"
  | .lambdaLike => "lambda_like"
  | .caseLike => "case_like"
  | .sourceRulePayload => "source_rule_payload"

private def renderPayloadPatternShapeKind : PayloadPatternShapeKind → String
  | .anyPattern => "any_pattern"
  | .nonRewritePattern => "non_rewrite_pattern"
  | .rewriteEqRule => "rewrite_eq_rule"

def ScopeContractEntry.sortKey (e : ScopeContractEntry) : String :=
  let payloadKey :=
    match e.payloadShape with
    | some .anyPattern => "any_pattern"
    | some .nonRewritePattern => "non_rewrite_pattern"
    | some .rewriteEqRule => "rewrite_eq_rule"
    | none => "none"
  s!"{e.head}:{renderScopeKind e.scopeKind}:{payloadKey}:{e.arity}"

private def normalizeEntry (e : ScopeContractEntry) : ScopeContractEntry :=
  { e with
    binderPositions := sortNatList e.binderPositions |>.eraseDups
    valuePositions := sortNatList e.valuePositions |>.eraseDups
    bodyPositions := sortNatList e.bodyPositions |>.eraseDups
    scopedPayloadPositions := sortNatList e.scopedPayloadPositions |>.eraseDups
    theoremRefs := sortListByKey e.theoremRefs id |>.eraseDups
  }

private def normalizeArtifact (a : ScopeContractArtifact) : ScopeContractArtifact :=
  { a with
    entries := sortListByKey (a.entries.map normalizeEntry) ScopeContractEntry.sortKey
  }

private def renderNatListField (name : String) (xs : List Nat) : String :=
  "\"" ++ name ++ "\":["
    ++ String.intercalate "," (xs.map jsonNat)
    ++ "]"

private def renderEntry (e : ScopeContractEntry) : String :=
  "{"
    ++ "\"head\":" ++ jsonStr e.head ++ ","
    ++ "\"arity\":" ++ jsonNat e.arity ++ ","
    ++ "\"scope_kind\":" ++ jsonStr (renderScopeKind e.scopeKind) ++ ","
    ++ renderNatListField "binder_positions" e.binderPositions ++ ","
    ++ renderNatListField "value_positions" e.valuePositions ++ ","
    ++ renderNatListField "body_positions" e.bodyPositions ++ ","
    ++ renderNatListField "scoped_payload_positions" e.scopedPayloadPositions ++ ","
    ++ "\"payload_shape\":"
      ++ jsonOptStr (e.payloadShape.map renderPayloadPatternShapeKind) ++ ","
    ++ "\"sequential\":" ++ jsonBool e.sequential ++ ","
    ++ "\"allows_wildcard\":" ++ jsonBool e.allowsWildcard ++ ","
    ++ "\"theorem_refs\":["
      ++ String.intercalate "," (e.theoremRefs.map jsonStr) ++ "]"
  ++ "}"

def ScopeContractArtifact.renderJson (a : ScopeContractArtifact) : String :=
  let norm := normalizeArtifact a
  "{"
    ++ "\"schema_version\":" ++ jsonNat norm.schemaVersion ++ ","
    ++ "\"dialect\":" ++ jsonStr norm.dialect ++ ","
    ++ "\"wildcard_symbol\":" ++ jsonStr norm.wildcardSymbol ++ ","
    ++ "\"entries\":[" ++ String.intercalate "," (norm.entries.map renderEntry) ++ "]"
  ++ "}"

private def lintEntry (e : ScopeContractEntry) : List String :=
  let tag := s!"scope:{e.head}:{renderScopeKind e.scopeKind}:{e.arity}"
  let headErrs :=
    if e.head.isEmpty then
      ["scope entry head must be non-empty"]
    else []
  let posErrs :=
    ((e.binderPositions ++ e.valuePositions ++ e.bodyPositions ++ e.scopedPayloadPositions).foldl
      (fun errs pos =>
        if pos < e.arity then errs else errs ++ [s!"{tag}: position {pos} must be < arity {e.arity}"])
      [])
  let theoremErrs :=
    if e.theoremRefs.isEmpty then
      [s!"{tag}: theorem_refs cannot be empty"]
    else []
  let kindErrs :=
    match e.scopeKind with
    | .letLike =>
        let binderErrs :=
          if e.binderPositions = [0] && e.valuePositions = [1] && e.bodyPositions = [2] then
            []
          else
            [s!"{tag}: let_like expects binder=[0], value=[1], body=[2]"]
        let seqErrs :=
          if !e.sequential then [] else [s!"{tag}: let_like must not be sequential"]
        binderErrs ++ seqErrs
    | .chainLike =>
        let binderErrs :=
          if e.binderPositions = [1] && e.valuePositions = [0] && e.bodyPositions = [2] then
            []
          else
            [s!"{tag}: chain_like expects binder=[1], value=[0], body=[2]"]
        let seqErrs :=
          if !e.sequential then [] else [s!"{tag}: chain_like must not be sequential"]
        binderErrs ++ seqErrs
    | .letStarLike =>
        let posErrs :=
          if e.valuePositions = [0] && e.bodyPositions = [1] && e.binderPositions.isEmpty then
            []
          else
            [s!"{tag}: let_star_like expects values=[0], body=[1], and no top-level binder positions"]
        let seqErrs :=
          if e.sequential then [] else [s!"{tag}: let_star_like must be sequential"]
        posErrs ++ seqErrs
    | .lambdaLike =>
        let posErrs :=
          if e.binderPositions = [0] && e.bodyPositions = [1] && e.valuePositions.isEmpty then
            []
          else
            [s!"{tag}: lambda_like expects binder=[0], body=[1], and no value positions"]
        let seqErrs :=
          if !e.sequential then [] else [s!"{tag}: lambda_like must not be sequential"]
        posErrs ++ seqErrs
    | .caseLike =>
        let posErrs :=
          if e.valuePositions = [0] && e.bodyPositions = [1] && e.binderPositions.isEmpty then
            []
          else
            [s!"{tag}: case_like expects scrutinee/value=[0], branches/body=[1], and no top-level binder positions"]
        let seqErrs :=
          if !e.sequential then [] else [s!"{tag}: case_like must not be sequential"]
        posErrs ++ seqErrs
    | .sourceRulePayload =>
        let payloadErrs :=
          if !e.scopedPayloadPositions.isEmpty then
            []
          else
            [s!"{tag}: source_rule_payload requires at least one scoped payload position"]
        let shapeErrs :=
          match e.payloadShape with
          | some .rewriteEqRule => []
          | _ => [s!"{tag}: source_rule_payload currently requires payload_shape=rewrite_eq_rule"]
        payloadErrs ++ shapeErrs
  headErrs ++ posErrs ++ theoremErrs ++ kindErrs

def ScopeContractArtifact.lintErrors (a : ScopeContractArtifact) : List String :=
  let norm := normalizeArtifact a
  let schemaErrs :=
    if norm.schemaVersion < 1 then
      [s!"schema_version must be >= 1, got {norm.schemaVersion}"]
    else []
  let dialectErrs :=
    if norm.dialect.isEmpty then ["dialect must be non-empty"] else []
  let wildcardErrs :=
    if norm.wildcardSymbol.isEmpty then ["wildcard_symbol must be non-empty"] else []
  let dupErrs :=
    let keys := norm.entries.map ScopeContractEntry.sortKey
    if keys.length == keys.eraseDups.length then
      []
    else
      ["scope contract entries must be unique by head, scope kind, payload shape, and arity"]
  let entryErrs := (norm.entries.map lintEntry).foldr List.append []
  schemaErrs ++ dialectErrs ++ wildcardErrs ++ dupErrs ++ entryErrs

def ScopeContractArtifact.isLintClean (a : ScopeContractArtifact) : Bool :=
  a.lintErrors.isEmpty

def ScopeContractArtifact.checksum (a : ScopeContractArtifact) : UInt64 :=
  checksumText a.renderJson

def ScopeContractArtifact.checksumString (a : ScopeContractArtifact) : String :=
  toString a.checksum

section Canaries
#check @ScopeKind
#check @ScopeContractEntry
#check @ScopeContractArtifact
#check @ScopeContractArtifact.renderJson
#check @ScopeContractArtifact.checksumString
end Canaries

end Mettapedia.Languages.MeTTa.ScopeContract
