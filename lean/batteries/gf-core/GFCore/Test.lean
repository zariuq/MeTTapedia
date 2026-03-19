/-
# GFCore.Test — Smoke tests for the GF core types

Verifies JSON round-trip, check, and erase on a tiny grammar fragment.
-/

import GFCore.Syntax
import GFCore.Json
import GFCore.Check
import GFCore.Export

open GFCore

-- ============================================================
-- A tiny grammar: PredVP(UsePN(john_PN), UseV(walk_V)) : S
-- ============================================================

private def johnDecl : FunDecl :=
  { name := "john_PN", argCats := #[], resultCat := "PN", status := .constructor }

private def walkDecl : FunDecl :=
  { name := "walk_V", argCats := #[], resultCat := "V", status := .constructor }

private def usePNDecl : FunDecl :=
  { name := "UsePN", argCats := #["PN"], resultCat := "NP" }

private def useVDecl : FunDecl :=
  { name := "UseV", argCats := #["V"], resultCat := "VP" }

private def predVPDecl : FunDecl :=
  { name := "PredVP", argCats := #["NP", "VP"], resultCat := "Cl" }

private def tinySig : GrammarSig := {
  grammar := "TinyTest"
  startCats := #["Cl"]
  funs := Std.HashMap.ofList [
    ("john_PN", johnDecl),
    ("walk_V", walkDecl),
    ("UsePN", usePNDecl),
    ("UseV", useVDecl),
    ("PredVP", predVPDecl)
  ]
  sourceHash := "test"
}

-- Raw tree: PredVP(UsePN(john_PN), UseV(walk_V))
private def rawJohnWalks : RawTerm :=
  .app "PredVP" none #[
    .app "UsePN" none #[.app "john_PN" none #[]],
    .app "UseV" none #[.app "walk_V" none #[]]
  ]

-- ============================================================
-- Test: check succeeds
-- ============================================================

#eval do
  match check tinySig rawJohnWalks with
  | .ok expr =>
    IO.println s!"check OK: root = {expr.funName}, cat = {expr.resultCat}"
    -- Verify structure
    assert! expr.funName == "PredVP"
    assert! expr.resultCat == "Cl"
    assert! expr.args.size == 2
    assert! expr.args[0]!.funName == "UsePN"
    assert! expr.args[0]!.resultCat == "NP"
    assert! expr.args[1]!.funName == "UseV"
    assert! expr.args[1]!.resultCat == "VP"
    IO.println "all assertions passed"
  | .error e =>
    IO.println s!"check FAILED: {e}"
    assert! false

-- ============================================================
-- Test: check rejects bad arity
-- ============================================================

#eval do
  let badTree := RawTerm.app "PredVP" none #[RawTerm.leaf "john_PN"]  -- 1 arg, needs 2
  match check tinySig badTree with
  | .ok _ => IO.println "UNEXPECTED: should have failed" ; assert! false
  | .error (.wrongArity f e g) =>
    IO.println s!"correctly rejected: {f} expected {e} got {g}"
    assert! f == "PredVP" && e == 2 && g == 1
  | .error e => IO.println s!"wrong error type: {e}" ; assert! false

-- ============================================================
-- Test: check rejects unknown function
-- ============================================================

#eval do
  let badTree := RawTerm.leaf "nonexistent_fun"
  match check tinySig badTree with
  | .ok _ => assert! false
  | .error (.unknownFun n) =>
    IO.println s!"correctly rejected unknown: {n}"
    assert! n == "nonexistent_fun"
  | .error _ => assert! false

-- ============================================================
-- Test: check rejects category mismatch
-- ============================================================

#eval do
  -- PredVP expects (NP, VP) but we give (VP, NP)
  let badTree := RawTerm.app "PredVP" none #[
    .app "UseV" none #[.app "walk_V" none #[]],   -- VP, not NP
    .app "UsePN" none #[.app "john_PN" none #[]]   -- NP, not VP
  ]
  match check tinySig badTree with
  | .ok _ => assert! false
  | .error (.catMismatch f i e g) =>
    IO.println s!"correctly rejected cat mismatch: {f} arg {i}: expected {e}, got {g}"
    assert! f == "PredVP" && i == 0 && e == "NP" && g == "VP"
  | .error e => IO.println s!"wrong error: {e}" ; assert! false

-- ============================================================
-- Test: erase → check round-trip
-- ============================================================

#eval do
  match check tinySig rawJohnWalks with
  | .ok expr =>
    let erased := erase expr
    match check tinySig erased with
    | .ok expr2 =>
      assert! expr2.funName == expr.funName
      assert! expr2.resultCat == expr.resultCat
      IO.println "erase → check round-trip OK"
    | .error e => IO.println s!"round-trip check failed: {e}" ; assert! false
  | .error e => IO.println s!"initial check failed: {e}" ; assert! false

-- ============================================================
-- Test: JSON round-trip for RawTerm
-- ============================================================

open Lean in
#eval do
  let json := toJson rawJohnWalks
  let jsonStr := json.pretty
  IO.println s!"JSON:\n{jsonStr}"
  match Json.parse jsonStr with
  | .ok parsed =>
    match fromJson? (α := RawTerm) parsed with
    | .ok decoded =>
      -- Re-encode and compare
      let reEncoded := (toJson decoded).pretty
      assert! jsonStr == reEncoded
      IO.println "JSON round-trip OK"
    | .error e => IO.println s!"decode failed: {e}" ; assert! false
  | .error e => IO.println s!"parse failed: {e}" ; assert! false

-- ============================================================
-- Test: JSON round-trip for GrammarSig
-- ============================================================

open Lean in
#eval do
  let json := toJson tinySig
  let jsonStr := json.pretty
  match Json.parse jsonStr >>= fromJson? (α := GrammarSig) with
  | .ok decoded =>
    assert! decoded.grammar == "TinyTest"
    assert! decoded.startCats == #["Cl"]
    assert! decoded.funs.size == 5
    -- Check a specific function survived
    match decoded.findFun? "PredVP" with
    | some d =>
      assert! d.argCats == #["NP", "VP"]
      assert! d.resultCat == "Cl"
      IO.println "GrammarSig JSON round-trip OK"
    | none => IO.println "PredVP not found after round-trip" ; assert! false
  | .error e => IO.println s!"sig round-trip failed: {e}" ; assert! false
