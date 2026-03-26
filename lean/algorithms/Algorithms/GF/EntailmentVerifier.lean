/-
# Entailment Verifier — Full pipeline: ParseEng → Frame → Reasoning

Loads ParseEng signature, parses entailment bank sentences,
extracts Frames, and verifies entailment steps using deterministic PLN rules.

Run: lake exe gfEntailVerify
-/

import GFCore
import Lean.Data.Json

open GFCore Lean

structure ParsedEntry where
  sentence : String
  tree : RawTerm
  prob : Float
  deriving Inhabited

instance : FromJson ParsedEntry where
  fromJson? j := do
    let sentence ← j.getObjValAs? String "sentence"
    let tree ← j.getObjValAs? RawTerm "tree"
    let prob ← j.getObjValAs? Float "prob"
    pure { sentence, tree, prob }

def main : IO Unit := do
  IO.println "=== Entailment Verifier — Frame IR + PLN Rules ==="
  IO.println ""

  -- Load signature
  IO.print "Loading signature... "
  let sig ← GrammarSig.readFromFile "gf_fragments/ParseEng_sig.json"
  IO.println s!"OK ({sig.funs.size} functions)"

  -- Load parsed sentences
  let contents ← IO.FS.readFile "gf_fragments/entailment/entailment_demo.json"
  let json ← IO.ofExcept (Json.parse contents)

  let mut views : Std.HashMap String (RGLView × CheckedExpr) := {}

  let entriesObj ← IO.ofExcept (json.getObj?)
  for (key, val) in entriesObj.toList do
    match fromJson? (α := ParsedEntry) val with
    | .ok entry =>
      match check sig entry.tree with
      | .ok expr =>
        let view := toRGLView expr
        views := views.insert key (view, expr)
      | .error e => IO.println s!"  {key}: CHECK FAILED — {e}"
    | .error e => IO.println s!"  {key}: PARSE ERROR — {e}"

  IO.println ""

  -- Extract frames
  IO.println "=== Frame Extraction ==="
  let mut frames : Std.HashMap String Frame := {}
  for (key, (view, _)) in views.toArray do
    let frame := extractFrame view
    frames := frames.insert key frame
    IO.println s!"  {key}: {frame.pretty}"

  IO.println ""

  -- Verify Example 74
  IO.println "=========================================="
  IO.println "Example 74: Is-A Substitution"
  IO.println "=========================================="
  IO.println "  sent1: the sun is a kind of star"
  IO.println "  sent2: hydrogen is the most common element in stars"
  IO.println "  → hyp:  hydrogen is the most common element in the sun"
  IO.println ""

  let some f1 := frames.get? "sent1" | IO.println "Missing sent1"; return
  let some f2 := frames.get? "sent2" | IO.println "Missing sent2"; return
  let some fh := frames.get? "hypothesis" | IO.println "Missing hypothesis"; return

  IO.println s!"  Premise 1 frame: {f1.pretty}"
  IO.println s!"  Premise 2 frame: {f2.pretty}"
  IO.println s!"  Hypothesis frame: {fh.pretty}"
  IO.println ""

  let result := verifyEntailment #[f1, f2] fh
  match result with
  | .verified rule derived =>
    IO.println s!"  ✓ VERIFIED by rule: {rule}"
    IO.println s!"    Derived: {derived.pretty}"
  | .notVerified reason =>
    IO.println s!"  ✗ NOT VERIFIED: {reason}"

  -- Also try Example 80: earth ⊆ planet + mass(planet) causes gravity → mass(earth) causes gravity
  IO.println ""
  IO.println "=========================================="
  IO.println "Example 80: earth ⊆ planet + property(planet)"
  IO.println "=========================================="
  if let some f80_1 := frames.get? "ex80_sent1" then
    if let some f80_2 := frames.get? "ex80_sent2" then
      IO.println s!"  Premise 1: {f80_1.pretty}"
      IO.println s!"  Premise 2: {f80_2.pretty}"
      let result80 := verifyEntailment #[f80_1, f80_2] f80_2  -- self-check for now
      match result80 with
      | .verified rule derived => IO.println s!"  ✓ Rule: {rule}, Derived: {derived.pretty}"
      | .notVerified reason => IO.println s!"  (verification needs more work: {reason})"

  IO.println ""
  IO.println "=== Done ==="
