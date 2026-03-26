/-
# Full Pipeline Demo: ParseEng → Check → RGLView

Reads pre-parsed entailment bank sentences (JSON from Python PGF API),
checks them against the ParseEng grammar signature (loaded at runtime),
and displays the readable RGLView output.

Run: lake exe gfDemo
-/

import GFCore
import Lean.Data.Json

open GFCore Lean

structure DemoParse where
  sentence : String
  tree : RawTerm
  prob : Float
  deriving Inhabited

instance : FromJson DemoParse where
  fromJson? j := do
    let sentence ← j.getObjValAs? String "sentence"
    let tree ← j.getObjValAs? RawTerm "tree"
    let prob ← j.getObjValAs? Float "prob"
    pure { sentence, tree, prob }

def main : IO Unit := do
  IO.println "=== GF → Lean Full Pipeline Demo ==="
  IO.println ""

  -- Load ParseEng grammar signature
  IO.print "Loading ParseEng signature (115K functions)... "
  let sig ← GrammarSig.readFromFile "gf_fragments/ParseEng_sig.json"
  IO.println s!"OK ({sig.funs.size} functions)"

  -- Load pre-parsed demo sentences
  let contents ← IO.FS.readFile "gf_fragments/entailment/demo_parses.json"
  let json ← IO.ofExcept (Json.parse contents)
  let parses ← IO.ofExcept (fromJson? (α := Array DemoParse) json)
  IO.println s!"Loaded {parses.size} parsed sentences"
  IO.println ""

  let mut checked : Nat := 0
  let mut failed : Nat := 0

  for p in parses do
    IO.println s!"--- \"{p.sentence}\" ---"

    -- Step 1: Check against signature
    match check sig p.tree with
    | .error e =>
      IO.println s!"  CHECK FAILED: {e}"
      failed := failed + 1
    | .ok expr =>
      checked := checked + 1
      IO.println s!"  CheckedExpr: {expr.funName} : {expr.resultCat}"

      -- Step 2: RGLView
      let view := toRGLView expr
      IO.println s!"  RGLView: {view.pretty}"
      IO.println ""

  IO.println s!"=== Results: {checked} checked, {failed} failed ==="
