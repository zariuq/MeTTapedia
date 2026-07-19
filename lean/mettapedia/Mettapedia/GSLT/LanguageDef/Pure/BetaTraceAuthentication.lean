/-
# Authentication gate for Pure beta-conversion atomic traces

This gate consumes the same claim schema and Lean-owned statement table as the
conversion-free gate.  It changes only the root used for deterministic replay
and records conversion-fuel exhaustion separately from ordinary rejection.
-/

import Mettapedia.GSLT.LanguageDef.Pure.TraceAuthentication
import Mettapedia.GSLT.LanguageDef.Pure.BetaLinearTraceChecker
import MeTTailCore.Crypto.SHA256

namespace Mettapedia.GSLT.LanguageDef.PureBetaTraceAuthentication

open Lean
open Mettapedia.GSLT.LanguageDef.Pure
open Mettapedia.GSLT.LanguageDef.PureAtomicFixtures
open Mettapedia.GSLT.LanguageDef.PureBeta
open Mettapedia.GSLT.LanguageDef.PureBetaAtomicRefinement
open Mettapedia.GSLT.LanguageDef.PureBetaLinearTraceChecker

abbrev Claim := Mettapedia.GSLT.LanguageDef.PureTraceAuthentication.Claim

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

private def renderOptionNat : Option Nat → String
  | none => "null"
  | some value => toString value

private def renderOptionBool : Option Bool → String
  | none => "null"
  | some value => jsonBool value

private def renderOptionString : Option String → String
  | none => "null"
  | some value => jsonString value

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

private def unresolvedVerdict (claim : Claim) (message : String) : Verdict :=
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

private def statusReason (claimedTerminal : Bool)
    (result : PureBetaLinearTraceChecker.ReplayResult)
    (terminal : CheckResult Nf) : String :=
  match result.status with
  | .effectClaimMismatch => "effect_claim_mismatch"
  | .actionRejected => "beta_action_rejected"
  | .conversionFuelExhausted => "conversion_fuel_exhausted"
  | .malformedClaim => "malformed_effect_claim_vector"
  | .budgetExceeded => "atomic_budget_exceeded"
  | .completed =>
      if !claimedTerminal then "terminal_not_claimed"
      else
        match terminal with
        | .ok _ => "accepted"
        | .rejected => "terminal_beta_check_rejected"
        | .conversionFuelExhausted => "conversion_fuel_exhausted"

def checkClaim (claim : Claim) : Verdict :=
  match Mettapedia.GSLT.LanguageDef.PureTraceAuthentication.resolveGoal claim with
  | .error message => unresolvedVerdict claim message
  | .ok goal =>
      let translation : Translation :=
        { actions := claim.actions
          claimedSpineLengths := claim.claimedSpineLengths
          claimedTerminal := claim.claimedTerminal }
      let result := PureBetaLinearTraceChecker.replay
        goal claim.maxRefinements translation
      let terminal := terminalResult goal result.state.core
      let isAccepted := PureBetaLinearTraceChecker.accepted
        goal claim.maxRefinements translation
      { id := claim.id
        subjectKind := claim.subjectKind
        subjectName := claim.subjectName
        accepted := isAccepted
        firstIllegalStep := PureBetaLinearTraceChecker.firstRejectedAt
          goal claim.maxRefinements translation
        stateHash :=
          Mettapedia.GSLT.LanguageDef.PureTraceAuthentication.stateHash goal result.state
        reason := statusReason claim.claimedTerminal result terminal
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
    "\"root\":\"pure_beta\"," ++
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

/-- Immutable conversion-free v6 verdict ledger paired with this beta rerun. -/
def conversionFreeVerdictSha256 : String :=
  "31ca1d761a111fda14f82aa0400d8d061594e10ab72fab0fbbddaaaf1f340af0"

def authenticateContent (input : String) : BatchResult :=
  let lines := input.splitOn "\n" |>.filter fun line => !line.trimAscii.isEmpty
  let verdicts := lines.mapIdx fun index line =>
    match Json.parse line with
    | .error message => parseErrorVerdict (index + 1) line message
    | .ok json =>
        match Mettapedia.GSLT.LanguageDef.PureTraceAuthentication.parseClaim json with
        | .error message => parseErrorVerdict (index + 1) line message
        | .ok claim => checkClaim claim
  { verdicts := verdicts
    output := String.intercalate "\n" (verdicts.map renderVerdict) ++ "\n" }

def renderManifest (input output : String) (verdicts : List Verdict) : String :=
  let acceptedRows := (verdicts.filter fun verdict => verdict.accepted).length
  let exhaustedRows :=
    (verdicts.filter fun verdict => verdict.reason = "conversion_fuel_exhausted").length
  "{" ++
    "\"schema\":\"gslt.pure.beta_atomic_trace_authentication.manifest.v1\"," ++
    "\"conversion\":\"beta_only\"," ++
    "\"normalization_fuel\":" ++ toString normalizationFuel ++ "," ++
    "\"claim_rows\":" ++ toString verdicts.length ++ "," ++
    "\"accepted_rows\":" ++ toString acceptedRows ++ "," ++
    "\"rejected_rows\":" ++ toString (verdicts.length - acceptedRows) ++ "," ++
    "\"conversion_fuel_exhausted_rows\":" ++ toString exhaustedRows ++ "," ++
    "\"conversion_free_accepted_rows\":2," ++
    "\"conversion_free_rejected_rows\":29," ++
    "\"conversion_free_verdict_sha256\":" ++
      jsonString conversionFreeVerdictSha256 ++ "," ++
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
  if !Mettapedia.GSLT.LanguageDef.PureTraceAuthentication.referenceResolutionGate then
    IO.eprintln "Lean-owned statement or fixture resolution gate failed"
    return 2
  match arguments with
  | [mode, inputPath, outputPath, manifestPath] =>
      let input ← IO.FS.readFile inputPath
      let result := authenticateContent input
      let manifest := renderManifest input result.output result.verdicts
      let outputCode ← writeOrCheck mode outputPath result.output "beta trace verdict JSONL"
      if outputCode != 0 then return outputCode
      writeOrCheck mode manifestPath manifest "beta trace authentication manifest"
  | _ =>
      IO.eprintln
        "usage: PureBetaTraceAuthentication (write|check) <claims.jsonl> <verdicts.jsonl> <manifest.json>"
      pure 1

end Mettapedia.GSLT.LanguageDef.PureBetaTraceAuthentication
