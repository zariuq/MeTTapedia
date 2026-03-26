/-
# Entailment Eval — Systematic dev set evaluation

Reads dev_eval.json (10 unseen dev examples), runs full pipeline:
  Parse → Check → RGLView → Frame → Entailment Rules

Reports: extraction coverage + verification rate.

Run: lake exe gfEntailEval
-/

import GFCore
import Lean.Data.Json

open GFCore Lean

def main : IO Unit := do
  IO.println "=== Dev Set Entailment Evaluation ==="
  IO.println ""

  IO.print "Loading signature... "
  let sig ← GrammarSig.readFromFile "gf_fragments/ParseEng_sig.json"
  IO.println s!"OK ({sig.funs.size} functions)"

  let contents ← IO.FS.readFile "gf_fragments/entailment/dev_eval.json"
  let json ← IO.ofExcept (Json.parse contents)
  let examples ← IO.ofExcept (json.getArr?)

  let mut totalExamples : Nat := 0
  let mut allParsed : Nat := 0
  let mut allExtracted : Nat := 0
  let mut entailVerified : Nat := 0
  let mut ruleUsed : Std.HashMap String Nat := {}

  for ex in examples do
    totalExamples := totalExamples + 1
    let id := (ex.getObjValAs? String "id").toOption.getD "?"
    let hyp := (ex.getObjValAs? String "hypothesis").toOption.getD "?"
    IO.println s!"--- [{totalExamples}] {id} ---"
    IO.println s!"  Hypothesis: {hyp}"

    -- Check and extract frames for premises
    let premisesJson := (ex.getObjValAs? (Array Json) "premises").toOption.getD #[]
    let mut premFrames : Array Frame := #[]
    let mut premOk := true
    for pj in premisesJson do
      let sent := (pj.getObjValAs? String "sentence").toOption.getD "?"
      match pj.getObjValAs? RawTerm "tree" with
      | .ok tree =>
        match check sig tree with
        | .ok expr =>
          let view := toRGLView expr
          let frame := extractFrame view
          premFrames := premFrames.push frame
          let extracted := !frame.pretty.startsWith "Opaque"
          if extracted then
            IO.println s!"  Premise: {sent}"
            IO.println s!"    Frame: {frame.pretty}"
          else
            IO.println s!"  Premise: {sent}"
            IO.println s!"    Frame: {frame.pretty} (opaque)"
            premOk := false
        | .error e =>
          IO.println s!"  Premise CHECK FAILED: {sent} — {e}"
          premOk := false
      | .error e =>
        IO.println s!"  Premise JSON ERROR: {e}"
        premOk := false

    -- Check and extract frame for hypothesis
    match ex.getObjValAs? RawTerm "hyp_tree" with
    | .ok hypTree =>
      match check sig hypTree with
      | .ok hypExpr =>
        allParsed := allParsed + 1
        let hypView := toRGLView hypExpr
        let hypFrame := extractFrame hypView
        let hypExtracted := !hypFrame.pretty.startsWith "Opaque"
        IO.println s!"  Hyp frame: {hypFrame.pretty}"

        if premOk && hypExtracted then
          allExtracted := allExtracted + 1

        -- Try verification
        let result := verifyEntailment premFrames hypFrame
        match result with
        | .verified rule _ =>
          entailVerified := entailVerified + 1
          ruleUsed := ruleUsed.insert rule ((ruleUsed.getD rule 0) + 1)
          IO.println s!"  ✓ VERIFIED ({rule})"
        | .notVerified reason =>
          IO.println s!"  ✗ not verified: {reason}"

      | .error e =>
        IO.println s!"  Hyp CHECK FAILED: {e}"
    | .error e =>
      IO.println s!"  Hyp JSON ERROR: {e}"

    IO.println ""

  IO.println "=========================================="
  IO.println "=== Summary ==="
  IO.println s!"Total examples:     {totalExamples}"
  IO.println s!"All parsed+checked: {allParsed}"
  IO.println s!"Non-opaque frames:  {allExtracted}"
  IO.println s!"Entailment verified: {entailVerified}/{totalExamples}"
  IO.println ""
  IO.println "Rules used:"
  for (rule, count) in ruleUsed.toArray do
    IO.println s!"  {rule}: {count}"
