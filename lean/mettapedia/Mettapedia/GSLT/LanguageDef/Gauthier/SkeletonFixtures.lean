/-
# Cross-runtime fixtures for the authenticated GSLT skeleton

This executable renders deterministic JSONL fixtures from the Lean table,
bounded mask, postfix parser, and role trace.  `write` refreshes the shared
artifact; `check` reads that artifact and rejects any byte-level drift.
-/

import Mettapedia.GSLT.LanguageDef.Gauthier.SkeletonTrace

namespace Mettapedia.GSLT.LanguageDef.GauthierSkeletonFixtures

open Mettapedia.GSLT.LanguageDef.GauthierE1
open Mettapedia.GSLT.LanguageDef.GauthierSkeleton
open Mettapedia.GSLT.LanguageDef.GauthierSkeletonMask
open Mettapedia.GSLT.LanguageDef.GauthierSkeletonTrace

private def jsonEscapeChar : Char → String
  | '"' => "\\\""
  | '\\' => "\\\\"
  | '\n' => "\\n"
  | '\r' => "\\r"
  | '\t' => "\\t"
  | c => c.toString

private def jsonString (value : String) : String :=
  "\"" ++ String.join (value.toList.map jsonEscapeChar) ++ "\""

private def jsonBool (value : Bool) : String :=
  if value then "true" else "false"

private def jsonArray (values : List String) : String :=
  "[" ++ String.intercalate "," values ++ "]"

private def renderNatArray (values : List Nat) : String :=
  jsonArray (values.map toString)

private def renderIntArray (values : List Int) : String :=
  jsonArray (values.map toString)

private def roleName : ChildRole → String
  | .code => "code"
  | .value => "value"

private def boundedCanComplete (state : MaskState) : Bool :=
  state.tokensEmitted ≤ state.maxLen &&
    canComplete orgMemoSignature state.depth (state.maxLen - state.tokensEmitted)

private def fixtureStatesAt (maxLen : Nat) : List MaskState :=
  (List.range (maxLen + 2)).flatMap fun tokensEmitted =>
    (List.range (maxLen + 3)).map fun depth =>
      { depth := depth, tokensEmitted := tokensEmitted, maxLen := maxLen }

def maskFixtureStates : List MaskState :=
  ((List.range 8).flatMap fixtureStatesAt) ++
    [{ depth := 5, tokensEmitted := 5, maxLen := 9 }]

private def renderTransition (state : MaskState) (token : PyToken) : String :=
  match step? orgMemoSignature state token with
  | none =>
      "{" ++
        "\"token\":" ++ toString token ++ "," ++
        "\"accepted\":false" ++
      "}"
  | some next =>
      "{" ++
        "\"token\":" ++ toString token ++ "," ++
        "\"accepted\":true," ++
        "\"next_depth\":" ++ toString next.depth ++ "," ++
        "\"next_tokens_emitted\":" ++ toString next.tokensEmitted ++
      "}"

private def renderMaskFixture (state : MaskState) : String :=
  let legal := legalTokens orgMemoSignature state
  let transitions := legal.map (renderTransition state)
  "{" ++
    "\"kind\":\"mask\"," ++
    "\"depth\":" ++ toString state.depth ++ "," ++
    "\"tokens_emitted\":" ++ toString state.tokensEmitted ++ "," ++
    "\"max_len\":" ++ toString state.maxLen ++ "," ++
    "\"can_complete\":" ++ jsonBool (boundedCanComplete state) ++ "," ++
    "\"legal_tokens\":" ++ renderIntArray legal ++ "," ++
    "\"transitions\":" ++ jsonArray transitions ++
  "}"

structure TraceFixture where
  name : String
  tokens : List Nat

def traceFixtures : List TraceFixture :=
  [ { name := "zero", tokens := [0] }
  , { name := "heterogeneous_compr", tokens := [10, 11, 12] }
  , { name := "higher_order_stateful", tokens := rpnTokens roleRichProgram }
  , { name := "higher_arity_force_close_regression", tokens := [0, 1, 2, 10, 11, 15, 13] }
  , { name := "underflow", tokens := [3] }
  , { name := "unfinished_forest", tokens := [0, 0] }
  , { name := "unknown_operator", tokens := [99] }
  ]

private def renderRoleRecord (record : RoleRecord) : String :=
  "{" ++
    "\"op_id\":" ++ toString record.opId ++ "," ++
    "\"arity\":" ++ toString record.arity ++ "," ++
    "\"ho_arity\":" ++ toString record.higherOrderArity ++ "," ++
    "\"child_roles\":" ++
      jsonArray (record.childRoles.map (jsonString ∘ roleName)) ++
  "}"

private def renderTraceFixture (fixture : TraceFixture) : String :=
  let header :=
    "{" ++
      "\"kind\":\"trace\"," ++
      "\"name\":" ++ jsonString fixture.name ++ "," ++
      "\"tokens\":" ++ renderNatArray fixture.tokens ++ ","
  match recognize orgMemoSignature fixture.tokens with
  | none =>
      header ++
        "\"recognized\":false," ++
        "\"roundtrip_tokens\":[]," ++
        "\"nodes\":[]" ++
      "}"
  | some program =>
      header ++
        "\"recognized\":true," ++
        "\"roundtrip_tokens\":" ++ renderNatArray (rpnTokens program) ++ "," ++
        "\"nodes\":" ++ jsonArray ((roleRecords orgMemoSignature program).map renderRoleRecord) ++
      "}"

private def metaFixture : String :=
  "{" ++
    "\"kind\":\"meta\"," ++
    "\"schema\":\"gslt.skeleton.parity.v1\"," ++
    "\"mask_rows\":" ++ toString maskFixtureStates.length ++ "," ++
    "\"trace_rows\":" ++ toString traceFixtures.length ++
  "}"

def renderFixtures : String :=
  String.intercalate "\n"
    (metaFixture ::
      maskFixtureStates.map renderMaskFixture ++
      traceFixtures.map renderTraceFixture) ++ "\n"

/-! Lean-side canaries for the rows Python treats as named regressions. -/

example : 15 ∈ legalTokens orgMemoSignature
    { depth := 5, tokensEmitted := 5, maxLen := 9 } := by decide

example : recognize orgMemoSignature [0, 1, 2, 10, 11, 15, 13] |>.isSome := by
  decide

example : recognize orgMemoSignature [10, 11, 12] =
    some (.node 12 [.node 10 [], .node 11 []]) := by
  rfl

example : (roleRecord orgMemoSignature 12).childRoles = [.code, .value] := by
  decide

def main (arguments : List String) : IO UInt32 := do
  match arguments with
  | ["write", outputPath] =>
      let output := renderFixtures
      IO.FS.writeFile outputPath output
      IO.println s!"wrote {output.toUTF8.size} bytes to {outputPath}"
      pure 0
  | ["check", fixturePath] =>
      let actual ← IO.FS.readFile fixturePath
      if actual = renderFixtures then
        IO.println s!"fixture parity OK: {fixturePath}"
        pure 0
      else
        IO.eprintln s!"fixture drift: regenerate {fixturePath} from SkeletonFixtures.lean"
        pure 1
  | _ =>
      IO.eprintln "usage: SkeletonFixtures (write|check) <fixture.jsonl>"
      pure 1

end Mettapedia.GSLT.LanguageDef.GauthierSkeletonFixtures

def main (arguments : List String) : IO UInt32 :=
  Mettapedia.GSLT.LanguageDef.GauthierSkeletonFixtures.main arguments
