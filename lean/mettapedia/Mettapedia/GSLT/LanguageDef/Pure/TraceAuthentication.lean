/-
# Lean authentication gate for external Pure atomic traces

The gate accepts JSONL claims whose subject is either a frozen DTTBench-31
statement name or one of the seven parity fixtures.  Goals are resolved from
Lean-owned tables; caller-supplied goal encodings are never trusted.
-/

import Mettapedia.GSLT.LanguageDef.Pure.LinearTraceChecker
import MeTTailCore.Crypto.SHA256

namespace Mettapedia.GSLT.LanguageDef.PureTraceAuthentication

open Lean
open Mettapedia.GSLT.LanguageDef.Pure
open Mettapedia.GSLT.LanguageDef.PureAtomicFixtures
open Mettapedia.GSLT.LanguageDef.PureAtomicRefinement
open Mettapedia.GSLT.LanguageDef.PureDTTBench31
open Mettapedia.GSLT.LanguageDef.PureLinearTraceChecker

structure Claim where
  id : String
  subjectKind : String
  subjectName : String
  maxRefinements : Nat
  actions : List AtomicAction
  claimedSpineLengths : List (Option Nat)
  claimedTerminal : Bool
  expectedAccepted : Option Bool
  negativeClass : Option String
  deriving Repr

private def parseStringField (json : Json) (field : String) : Except String String :=
  json.getObjVal? field >>= Json.getStr?

private def parseNatField (json : Json) (field : String) : Except String Nat :=
  json.getObjVal? field >>= Json.getNat?

private def parseBoolField (json : Json) (field : String) : Except String Bool :=
  json.getObjVal? field >>= Json.getBool?

private def parseAction (json : Json) : Except String AtomicAction := do
  let kind ← parseStringField json "kind"
  if kind != "refine" then
    throw s!"unsupported action kind: {kind}"
  let hole ← parseNatField json "hole"
  let head ← parseNatField json "head"
  pure ⟨hole, head⟩

private def parseExpectedAccepted (json : Json) : Except String (Option Bool) :=
  match json.getObjVal? "expected_accepted" with
  | .error _ => pure none
  | .ok value => return some (← value.getBool?)

private def parseNegativeClass (json : Json) : Except String (Option String) :=
  match json.getObjVal? "negative_class" with
  | .error _ => pure none
  | .ok .null => pure none
  | .ok value => return some (← value.getStr?)

private def parseEffectClaims (json : Json) (actionCount : Nat) :
    Except String (List (Option Nat)) := do
  let mut claims : Array (Option Nat) := Array.replicate actionCount none
  let effects ← match json.getObjVal? "effect_claims" with
    | .error _ => pure #[]
    | .ok value => value.getArr?
  for effect in effects do
    let step ← parseNatField effect "step"
    let arity ← parseNatField effect "claimed_spine_length"
    if step >= actionCount then
      throw s!"effect claim step out of bounds: {step}"
    claims := claims.set! step (some arity)
  pure claims.toList

def parseClaim (json : Json) : Except String Claim := do
  let kind ← parseStringField json "kind"
  if kind != "claim" then
    throw s!"expected kind=claim, got {kind}"
  let id ← parseStringField json "id"
  let subjectKind ← parseStringField json "subject_kind"
  let subjectName ← parseStringField json "subject_name"
  if subjectKind != "statement" && subjectKind != "fixture" then
    throw s!"subject_kind must be statement or fixture, got {subjectKind}"
  let maxRefinements ← parseNatField json "max_refinements"
  let actionJson ← json.getObjVal? "actions" >>= Json.getArr?
  let actions ← actionJson.toList.mapM parseAction
  let claimedSpineLengths ← parseEffectClaims json actions.length
  let claimedTerminal ← parseBoolField json "claimed_terminal"
  let expectedAccepted ← parseExpectedAccepted json
  let negativeClass ← parseNegativeClass json
  pure
    { id := id
      subjectKind := subjectKind
      subjectName := subjectName
      maxRefinements := maxRefinements
      actions := actions
      claimedSpineLengths := claimedSpineLengths
      claimedTerminal := claimedTerminal
      expectedAccepted := expectedAccepted
      negativeClass := negativeClass }

def resolveGoal (claim : Claim) : Except String Pure.Expr :=
  if claim.subjectKind = "fixture" then
    match atomicTraceFixtures.find? fun fixture => fixture.name = claim.subjectName with
    | none => throw s!"unknown fixture: {claim.subjectName}"
    | some fixture => pure fixture.goal
  else if claim.subjectKind = "statement" then
    match statements.find? fun statement => statement.name = claim.subjectName with
    | none => throw s!"unknown DTTBench-31 statement: {claim.subjectName}"
    | some statement => pure statement.goal
  else
    throw s!"unsupported subject kind: {claim.subjectKind}"

private def resolutionProbe (subjectKind subjectName : String) : Claim :=
  { id := "resolution_probe"
    subjectKind := subjectKind
    subjectName := subjectName
    maxRefinements := 0
    actions := []
    claimedSpineLengths := []
    claimedTerminal := false
    expectedAccepted := none
    negativeClass := none }

/-- Every frozen DTTBench-31 name resolves to its Lean-owned goal exactly. -/
def statementResolutionGate : Bool :=
  statements.all fun statement =>
    match resolveGoal (resolutionProbe "statement" statement.name) with
    | .ok goal => goal == statement.goal
    | .error _ => false

/-- Every frozen parity-fixture name resolves to its Lean-owned goal exactly. -/
def fixtureResolutionGate : Bool :=
  atomicTraceFixtures.all fun fixture =>
    match resolveGoal (resolutionProbe "fixture" fixture.name) with
    | .ok goal => goal == fixture.goal
    | .error _ => false

/-- The executable refuses to authenticate unless both reference tables resolve. -/
def referenceResolutionGate : Bool :=
  statementResolutionGate && fixtureResolutionGate

private def jsonEscapeChar : Char → String
  | '"' => "\\\""
  | '\\' => "\\\\"
  | '\n' => "\\n"
  | '\r' => "\\r"
  | '\t' => "\\t"
  | c => c.toString

private def jsonString (value : String) : String :=
  "\"" ++ String.join (value.toList.map jsonEscapeChar) ++ "\""

private def jsonBool (value : Bool) : String := if value then "true" else "false"

private def jsonArray (values : List String) : String :=
  "[" ++ String.intercalate "," values ++ "]"

private def renderOptionNat : Option Nat → String
  | none => "null"
  | some value => toString value

private def renderOptionBool : Option Bool → String
  | none => "null"
  | some value => jsonBool value

private def renderOptionString : Option String → String
  | none => "null"
  | some value => jsonString value

private def renderAction (action : AtomicAction) : String :=
  "{" ++
    "\"kind\":\"refine\"," ++
    "\"hole\":" ++ toString action.hole ++ "," ++
    "\"head\":" ++ toString action.head ++
  "}"

private def renderEffectClaims : Nat → List (Option Nat) → List String
  | _, [] => []
  | index, claim :: rest =>
      match claim with
      | none => renderEffectClaims (index + 1) rest
      | some arity =>
          ("{" ++
            "\"step\":" ++ toString index ++ "," ++
            "\"claimed_spine_length\":" ++ toString arity ++
          "}") :: renderEffectClaims (index + 1) rest

private def renderClaim (fixture : AtomicTraceFixture) : String :=
  "{" ++
    "\"kind\":\"claim\"," ++
    "\"id\":" ++ jsonString fixture.name ++ "," ++
    "\"subject_kind\":\"fixture\"," ++
    "\"subject_name\":" ++ jsonString fixture.name ++ "," ++
    "\"max_refinements\":" ++ toString fixture.maxRefinements ++ "," ++
    "\"actions\":" ++ jsonArray (fixture.translation.actions.map renderAction) ++ "," ++
    "\"effect_claims\":" ++
      jsonArray (renderEffectClaims 0 fixture.translation.claimedSpineLengths) ++ "," ++
    "\"claimed_terminal\":" ++ jsonBool fixture.translation.claimedTerminal ++ "," ++
    "\"expected_accepted\":" ++ jsonBool fixture.expectedAccepted ++ "," ++
    "\"negative_class\":" ++ renderOptionString fixture.negativeClass ++
  "}"

def renderSampleClaims : String :=
  String.intercalate "\n" (atomicTraceFixtures.map renderClaim) ++ "\n"

private def renderNatList (values : List Nat) : String :=
  "[" ++ String.intercalate "," (values.map toString) ++ "]"

/-- Hash one reified expression without expanding shared structure through `Repr`. -/
private def exprHash (expression : Pure.Expr) : String :=
  MeTTailCore.Crypto.SHA256.sha256Hex (renderNatList expression.encode)

private def hashParts (tag : String) (parts : List String) : String :=
  MeTTailCore.Crypto.SHA256.sha256Hex
    (tag ++ ":" ++ String.intercalate ":" parts)

private def contextHash (context : Pure.Ctx) : String :=
  hashParts "context" (context.map exprHash)

private def normalFormHash (term : Pure.Nf) : String :=
  hashParts "normal_form" [exprHash term.erase]

private def frameHash : PureRefinement.Frame → String
  | .lambda domain => hashParts "lambda" [exprHash domain]
  | .spine context head arguments body expected =>
      hashParts "spine"
        [contextHash context, toString head,
          hashParts "arguments" (arguments.map normalFormHash),
          exprHash body, exprHash expected]

private def framesHash (frames : List PureRefinement.Frame) : String :=
  hashParts "frames" (frames.map frameHash)

private def coreHash : PureRefinement.Core → String
  | .needHole hole context target frames =>
      hashParts "need_hole"
        [toString hole, contextHash context, exprHash target, framesHash frames]
  | .needHead hole context target frames =>
      hashParts "need_head"
        [toString hole, contextHash context, exprHash target, framesHash frames]
  | .needSpine hole context target frames head headType =>
      hashParts "need_spine"
        [toString hole, contextHash context, exprHash target, framesHash frames,
          toString head, exprHash headType]
  | .done term => hashParts "done" [normalFormHash term]
  | .finished term => hashParts "finished" [normalFormHash term]

def stateHash (goal : Pure.Expr)
    (state : Mettapedia.GSLT.LanguageDef.PureRefinement.State) : String :=
  let payload :=
    "goal=" ++ exprHash goal ++
    ";core=" ++ coreHash state.core ++
    ";tokens=" ++ toString state.tokensEmitted ++
    ";max=" ++ toString state.maxLen
  MeTTailCore.Crypto.SHA256.sha256Hex payload

structure Verdict where
  id : String
  subjectKind : String
  subjectName : String
  accepted : Bool
  firstIllegalStep : Option Nat
  stateHash : String
  reason : String
  expectedAccepted : Option Bool
  negativeClass : Option String
  deriving Repr

def checkClaim (claim : Claim) : Verdict :=
  match resolveGoal claim with
  | .error message =>
      { id := claim.id
        subjectKind := claim.subjectKind
        subjectName := claim.subjectName
        accepted := false
        firstIllegalStep := none
        stateHash := MeTTailCore.Crypto.SHA256.sha256Hex
          (claim.subjectKind ++ ":" ++ claim.subjectName)
        reason := message
        expectedAccepted := claim.expectedAccepted
        negativeClass := claim.negativeClass }
  | .ok goal =>
      let translation : Translation :=
        { actions := claim.actions
          claimedSpineLengths := claim.claimedSpineLengths
          claimedTerminal := claim.claimedTerminal }
      let result := PureLinearTraceChecker.replay goal claim.maxRefinements translation
      let isAccepted := PureLinearTraceChecker.accepted goal claim.maxRefinements translation
      let firstIllegal :=
        PureLinearTraceChecker.firstRejectedAt goal claim.maxRefinements translation
      let reason :=
        if isAccepted then "accepted"
        else if !result.completed then "illegal_action_or_effect_claim"
        else if !claim.claimedTerminal then "terminal_not_claimed"
        else "terminal_predicate_false"
      { id := claim.id
        subjectKind := claim.subjectKind
        subjectName := claim.subjectName
        accepted := isAccepted
        firstIllegalStep := firstIllegal
        stateHash := stateHash goal result.state
        reason := reason
        expectedAccepted := claim.expectedAccepted
        negativeClass := claim.negativeClass }

private def parseErrorVerdict (lineNumber : Nat) (line message : String) : Verdict :=
  { id := s!"line_{lineNumber}"
    subjectKind := "invalid"
    subjectName := "invalid"
    accepted := false
    firstIllegalStep := none
    stateHash := MeTTailCore.Crypto.SHA256.sha256Hex line
    reason := "parse_error: " ++ message
    expectedAccepted := none
    negativeClass := none }

private def renderVerdict (verdict : Verdict) : String :=
  "{" ++
    "\"kind\":\"verdict\"," ++
    "\"id\":" ++ jsonString verdict.id ++ "," ++
    "\"subject_kind\":" ++ jsonString verdict.subjectKind ++ "," ++
    "\"subject_name\":" ++ jsonString verdict.subjectName ++ "," ++
    "\"accepted\":" ++ jsonBool verdict.accepted ++ "," ++
    "\"first_illegal_step\":" ++ renderOptionNat verdict.firstIllegalStep ++ "," ++
    "\"state_hash\":" ++ jsonString verdict.stateHash ++ "," ++
    "\"reason\":" ++ jsonString verdict.reason ++ "," ++
    "\"expected_accepted\":" ++ renderOptionBool verdict.expectedAccepted ++ "," ++
    "\"negative_class\":" ++ renderOptionString verdict.negativeClass ++
  "}"

structure BatchResult where
  verdicts : List Verdict
  output : String

def authenticateContent (input : String) : BatchResult :=
  let lines := input.splitOn "\n" |>.filter fun line => !line.trimAscii.isEmpty
  let verdicts := lines.mapIdx fun index line =>
    match Json.parse line with
    | .error message => parseErrorVerdict (index + 1) line message
    | .ok json =>
        match parseClaim json with
        | .error message => parseErrorVerdict (index + 1) line message
        | .ok claim => checkClaim claim
  { verdicts := verdicts
    output := String.intercalate "\n" (verdicts.map renderVerdict) ++ "\n" }

def renderManifest (input output : String) (verdicts : List Verdict) : String :=
  let acceptedRows := (verdicts.filter fun verdict => verdict.accepted).length
  "{" ++
    "\"schema\":\"gslt.pure.atomic_trace_authentication.manifest.v1\"," ++
    "\"claim_rows\":" ++ toString verdicts.length ++ "," ++
    "\"accepted_rows\":" ++ toString acceptedRows ++ "," ++
    "\"rejected_rows\":" ++ toString (verdicts.length - acceptedRows) ++ "," ++
    "\"resolved_statement_rows\":" ++ toString statements.length ++ "," ++
    "\"resolved_fixture_rows\":" ++ toString atomicTraceFixtures.length ++ "," ++
    "\"input_sha256\":" ++ jsonString
      (MeTTailCore.Crypto.SHA256.sha256Hex input) ++ "," ++
    "\"output_sha256\":" ++ jsonString
      (MeTTailCore.Crypto.SHA256.sha256Hex output) ++
  "}\n"

private def writeOrCheck (mode path expected label : String) : IO UInt32 := do
  match mode with
  | "write" =>
      IO.FS.writeFile path expected
      IO.println s!"wrote {label}: {path}"
      pure 0
  | "check" =>
      let actual ← IO.FS.readFile path
      if actual == expected then
        IO.println s!"{label} OK: {path}"
        pure 0
      else
        IO.eprintln s!"{label} is stale: {path}"
        pure 1
  | _ =>
      IO.eprintln "mode must be write or check"
      pure 1

def main (arguments : List String) : IO UInt32 := do
  if !referenceResolutionGate then
    IO.eprintln "Lean-owned statement or fixture resolution gate failed"
    return 2
  match arguments with
  | ["sample", mode, inputPath] =>
      writeOrCheck mode inputPath renderSampleClaims "sample claim JSONL"
  | ["authenticate", mode, inputPath, outputPath, manifestPath] =>
      let input ← IO.FS.readFile inputPath
      let result := authenticateContent input
      let manifest := renderManifest input result.output result.verdicts
      let outputCode ← writeOrCheck mode outputPath result.output "trace verdict JSONL"
      if outputCode != 0 then return outputCode
      writeOrCheck mode manifestPath manifest "trace authentication manifest"
  | _ =>
      IO.eprintln (
        "usage: PureTraceAuthentication sample (write|check) <claims.jsonl>\n" ++
        "   or: PureTraceAuthentication authenticate (write|check) " ++
        "<claims.jsonl> <verdicts.jsonl> <manifest.json>")
      pure 1

end Mettapedia.GSLT.LanguageDef.PureTraceAuthentication
