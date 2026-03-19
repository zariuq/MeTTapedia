/-
# GF Round-Trip Test (executable)

Full pipeline: English → GF parse → RawTerm → check → CheckedExpr → erase → GF linearize → English/Czech

Run with: lake exe gfRoundTrip
-/

import GFCore
import Algorithms.GF.Generated.PaperAmbiguitySig  -- AUTO-GENERATED signature

open GFCore

def main (args : List String) : IO Unit := do
  let pgfPath := match args with
    | [p] => p
    | _ => "gf_fragments/PaperAmbiguity.pgf"
  let driver ← GFDriver.fromEnv pgfPath
  let sig := Algorithms.GF.Generated.PaperAmbiguitySig.sig

  IO.println "=== GF ↔ Lean Round-Trip Test ==="
  IO.println ""

  -- Step 1: Parse English through GF
  let surface := "John sees the man with the telescope"
  IO.println s!"Input: \"{surface}\""
  IO.println ""

  let trees ← driver.parse "PaperAmbiguityEng" "S" surface
  IO.println s!"GF returned {trees.size} parse(s)"

  if trees.isEmpty then
    IO.println "ERROR: no parses returned"
    return

  -- Step 2: Check each parse against grammar signature
  for h : i in [:trees.size] do
    let tree := trees[i]
    IO.println s!"\n--- Parse {i} ---"
    IO.println s!"RawTerm root: {tree.funName}"

    match check sig tree with
    | .error e =>
      IO.println s!"CHECK FAILED: {e}"
    | .ok checkedExpr =>
      IO.println s!"CheckedExpr: {checkedExpr.funName} : {checkedExpr.resultCat}"

      -- Identify the ambiguity
      let cl := checkedExpr.args[2]!
      let vp := cl.args[1]!
      if vp.funName == "AdvVP" then
        IO.println "  Interpretation: VP attachment (sees the man) (with the telescope)"
      else if vp.funName == "ComplSlash" then
        IO.println "  Interpretation: NP attachment (sees the man with the telescope)"

      -- Step 3: Erase back to RawTerm
      let erased := erase checkedExpr

      -- Step 4: Linearize through GF → English
      let engSurface ← driver.linearize "PaperAmbiguityEng" erased
      IO.println s!"  → English: {engSurface}"

      -- Step 5: Linearize through GF → Czech
      let czeSurface ← driver.linearize "PaperAmbiguityCze" erased
      IO.println s!"  → Czech:   {czeSurface}"

      -- Verify round-trip
      if engSurface == surface then
        IO.println "  ✓ English round-trip matches!"
      else
        IO.println s!"  ✗ English mismatch: got \"{engSurface}\""

  IO.println "\n=== Done ==="
