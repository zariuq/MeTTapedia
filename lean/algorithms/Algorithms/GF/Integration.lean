/-
# GF Integration Test

End-to-end test: GF parse → RawTerm → check → CheckedExpr → erase → linearize.
Uses the PaperAmbiguity grammar with "John sees the man with the telescope".
-/

import GFCore

open GFCore

/-- Build the PaperAmbiguity GrammarSig directly in Lean (26 functions).
    In production this would be auto-generated or loaded from JSON. -/
def paperAmbiguitySig : GrammarSig := {
  grammar := "PaperAmbiguity"
  startCats := #["S"]
  funs := Std.HashMap.ofList [
    ("ASimul",     { name := "ASimul",     argCats := #[],                   resultCat := "Ant" }),
    ("AdvCN",      { name := "AdvCN",      argCats := #["CN", "Adv"],        resultCat := "CN" }),
    ("AdvVP",      { name := "AdvVP",      argCats := #["VP", "Adv"],        resultCat := "VP" }),
    ("ComplSlash", { name := "ComplSlash", argCats := #["VPSlash", "NP"],    resultCat := "VP" }),
    ("DetCN",      { name := "DetCN",      argCats := #["Det", "CN"],        resultCat := "NP" }),
    ("PPos",       { name := "PPos",       argCats := #[],                   resultCat := "Pol" }),
    ("PredVP",     { name := "PredVP",     argCats := #["NP", "VP"],         resultCat := "Cl" }),
    ("PrepNP",     { name := "PrepNP",     argCats := #["Prep", "NP"],       resultCat := "Adv" }),
    ("SlashV2a",   { name := "SlashV2a",   argCats := #["V2"],              resultCat := "VPSlash" }),
    ("TPast",      { name := "TPast",      argCats := #[],                   resultCat := "Tense" }),
    ("TPres",      { name := "TPres",      argCats := #[],                   resultCat := "Tense" }),
    ("TTAnt",      { name := "TTAnt",      argCats := #["Tense", "Ant"],     resultCat := "Temp" }),
    ("UseCl",      { name := "UseCl",      argCats := #["Temp", "Pol", "Cl"], resultCat := "S" }),
    ("UseN",       { name := "UseN",       argCats := #["N"],               resultCat := "CN" }),
    ("UsePN",      { name := "UsePN",      argCats := #["PN"],              resultCat := "NP" }),
    ("anna_PN",    { name := "anna_PN",    argCats := #[],                   resultCat := "PN" }),
    ("baby_N",     { name := "baby_N",     argCats := #[],                   resultCat := "N" }),
    ("crib_N",     { name := "crib_N",     argCats := #[],                   resultCat := "N" }),
    ("dress_V2",   { name := "dress_V2",   argCats := #[],                   resultCat := "V2" }),
    ("in_Prep",    { name := "in_Prep",    argCats := #[],                   resultCat := "Prep" }),
    ("john_PN",    { name := "john_PN",    argCats := #[],                   resultCat := "PN" }),
    ("man_N",      { name := "man_N",      argCats := #[],                   resultCat := "N" }),
    ("see_V2",     { name := "see_V2",     argCats := #[],                   resultCat := "V2" }),
    ("telescope_N",{ name := "telescope_N",argCats := #[],                   resultCat := "N" }),
    ("the_Det",    { name := "the_Det",    argCats := #[],                   resultCat := "Det" }),
    ("with_Prep",  { name := "with_Prep",  argCats := #[],                   resultCat := "Prep" })
  ]
  sourceHash := "gf-3.12-paper-ambiguity"
}

-- ============================================================
-- Test: parse GF expression strings (the format GF --run outputs)
-- ============================================================

-- GF outputs trees like: UseCl (TTAnt TPres ASimul) PPos (PredVP (UsePN john_PN) ...)
-- Two parses for "John sees the man with the telescope":
-- Parse 1: VP attachment (sees [the man] [with the telescope])
-- Parse 2: NP attachment (sees [the man with the telescope])

private def telescopeGFExpr1 : String :=
  "UseCl (TTAnt TPres ASimul) PPos (PredVP (UsePN john_PN) (AdvVP (ComplSlash (SlashV2a see_V2) (DetCN the_Det (UseN man_N))) (PrepNP with_Prep (DetCN the_Det (UseN telescope_N)))))"

private def telescopeGFExpr2 : String :=
  "UseCl (TTAnt TPres ASimul) PPos (PredVP (UsePN john_PN) (ComplSlash (SlashV2a see_V2) (DetCN the_Det (AdvCN (UseN man_N) (PrepNP with_Prep (DetCN the_Det (UseN telescope_N)))))))"

-- Test: parse GF expression → RawTerm
#eval do
  match GFDriver.parseGFExpr telescopeGFExpr1 with
  | .ok tree =>
    IO.println s!"Parse 1 root: {tree.funName}, args: {tree.args.size}"
    assert! tree.funName == "UseCl"
    assert! tree.args.size == 3
    IO.println "GF expr parse 1 OK"
  | .error e => IO.println s!"FAILED: {e}" ; assert! false

#eval do
  match GFDriver.parseGFExpr telescopeGFExpr2 with
  | .ok tree =>
    IO.println s!"Parse 2 root: {tree.funName}, args: {tree.args.size}"
    assert! tree.funName == "UseCl"
    IO.println "GF expr parse 2 OK"
  | .error e => IO.println s!"FAILED: {e}" ; assert! false

-- ============================================================
-- Test: check parsed trees against PaperAmbiguity signature
-- ============================================================

#eval do
  match GFDriver.parseGFExpr telescopeGFExpr1 with
  | .error e => IO.println s!"parse failed: {e}" ; assert! false
  | .ok rawTree =>
    match check paperAmbiguitySig rawTree with
    | .error e => IO.println s!"check failed: {e}" ; assert! false
    | .ok checkedExpr =>
      IO.println s!"Checked: {checkedExpr.funName} : {checkedExpr.resultCat}"
      assert! checkedExpr.resultCat == "S"
      -- The VP subtree should contain AdvVP (VP attachment)
      let cl := checkedExpr.args[2]!  -- Cl
      let vp := cl.args[1]!           -- VP
      assert! vp.funName == "AdvVP"
      IO.println "Parse 1 check OK (VP attachment: AdvVP)"

#eval do
  match GFDriver.parseGFExpr telescopeGFExpr2 with
  | .error e => IO.println s!"parse failed: {e}" ; assert! false
  | .ok rawTree =>
    match check paperAmbiguitySig rawTree with
    | .error e => IO.println s!"check failed: {e}" ; assert! false
    | .ok checkedExpr =>
      assert! checkedExpr.resultCat == "S"
      let cl := checkedExpr.args[2]!
      let vp := cl.args[1]!
      assert! vp.funName == "ComplSlash"
      -- The NP should contain AdvCN (NP attachment)
      let np := vp.args[1]!
      let cn := np.args[1]!
      assert! cn.funName == "AdvCN"
      IO.println "Parse 2 check OK (NP attachment: AdvCN)"

-- ============================================================
-- Test: erase → re-check round-trip
-- ============================================================

#eval do
  match GFDriver.parseGFExpr telescopeGFExpr1 with
  | .error e => IO.println s!"parse failed: {e}" ; assert! false
  | .ok rawTree =>
    match check paperAmbiguitySig rawTree with
    | .error e => IO.println s!"check failed: {e}" ; assert! false
    | .ok checkedExpr =>
      let erased := erase checkedExpr
      match check paperAmbiguitySig erased with
      | .error e => IO.println s!"re-check failed: {e}" ; assert! false
      | .ok rechecked =>
        assert! rechecked.funName == checkedExpr.funName
        assert! rechecked.resultCat == checkedExpr.resultCat
        IO.println "erase → re-check round-trip OK"

-- ============================================================
-- Test: RGLView on telescope parses
-- ============================================================

#eval do
  -- VP attachment parse
  match GFDriver.parseGFExpr telescopeGFExpr1 with
  | .error e => IO.println s!"parse failed: {e}" ; assert! false
  | .ok rawTerm =>
    match check paperAmbiguitySig rawTerm with
    | .error e => IO.println s!"check failed: {e}" ; assert! false
    | .ok expr =>
      let view := toRGLView expr
      IO.println s!"VP attachment RGLView: {view.pretty}"

#eval do
  -- NP attachment parse
  match GFDriver.parseGFExpr telescopeGFExpr2 with
  | .error e => IO.println s!"parse failed: {e}" ; assert! false
  | .ok rawTerm =>
    match check paperAmbiguitySig rawTerm with
    | .error e => IO.println s!"check failed: {e}" ; assert! false
    | .ok expr =>
      let view := toRGLView expr
      IO.println s!"NP attachment RGLView: {view.pretty}"

-- ============================================================
-- Test: JSON round-trip for checked telescope parse
-- ============================================================

open Lean in
#eval do
  match GFDriver.parseGFExpr telescopeGFExpr1 with
  | .error _ => assert! false
  | .ok rawTree =>
    -- Encode to JSON
    let json := toJson rawTree
    let jsonStr := json.pretty
    -- Decode back
    match Json.parse jsonStr >>= fromJson? (α := RawTerm) with
    | .error e => IO.println s!"JSON round-trip failed: {e}" ; assert! false
    | .ok decoded =>
      -- Check the decoded tree
      match check paperAmbiguitySig decoded with
      | .error e => IO.println s!"check after JSON failed: {e}" ; assert! false
      | .ok checked =>
        IO.println "JSON → decode → check OK"
        -- Test RGLView
        let view := toRGLView checked
        IO.println s!"RGLView: {view.pretty}"
