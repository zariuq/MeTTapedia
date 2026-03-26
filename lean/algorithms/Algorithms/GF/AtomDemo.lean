/-
# Atom Pipeline Demo — New Term/Atom/NormClause extraction with grounding

Tests the redesigned Layer 4 on Example 74 and the 10 demo sentences.
Now with WordNet synset grounding and background hypernymy.

Run: lake exe gfAtomDemo
-/

import GFCore
import Lean.Data.Json

open GFCore Lean

def main : IO Unit := do
  IO.println "=== New Atom Pipeline (Grounded) ==="
  IO.println ""

  IO.print "Loading signature... "
  let sig ← GrammarSig.readFromFile "gf_fragments/ParseEng_sig.json"
  IO.println s!"OK ({sig.funs.size} functions)"

  IO.print "Loading grounding table... "
  let gt ← GroundingTable.readFromFile "gf_fragments/concept_grounding.json"
  IO.println s!"OK ({gt.entries.size} concepts)"

  IO.print "Loading background knowledge... "
  let bg ← Background.readFromFile "gf_fragments/hypernymy.json"
  IO.println s!"OK ({bg.chains.size} chains, {bg.direct.size} direct)"

  -- Load demo parses
  let contents ← IO.FS.readFile "gf_fragments/entailment/entailment_demo.json"
  let json ← IO.ofExcept (Json.parse contents)
  let entriesObj ← IO.ofExcept (json.getObj?)

  let mut atoms : Std.HashMap String Atom := {}

  IO.println ""
  IO.println "=== Extraction (RGLView → NormClause → Atom → Ground) ==="
  for (key, val) in entriesObj.toList do
    match val.getObjValAs? RawTerm "tree" with
    | .ok tree =>
      match check sig tree with
      | .ok expr =>
        let view := toRGLView expr
        let norm := normClause view
        let rawAtom := extractAtom norm
        let atom := groundAtom gt rawAtom
        atoms := atoms.insert key atom
        -- Show synset info for head concepts
        let heads := atom.allHeads
        let groundedHeads := heads.filter (·.synset?.isSome)
        IO.println s!"  {key}:"
        IO.println s!"    Atom: {atom.pretty}"
        if !groundedHeads.isEmpty then
          let synInfo := groundedHeads.map fun h =>
            s!"{h.baseName}={h.synset?.getD "?"}"
          IO.println s!"    Synsets: {String.intercalate ", " synInfo}"
      | .error e => IO.println s!"  {key}: CHECK FAILED — {e}"
    | .error e => IO.println s!"  {key}: JSON ERROR — {e}"

  IO.println ""
  IO.println "=========================================="
  IO.println "Example 74: Is-A Substitution"
  IO.println "=========================================="
  IO.println "  sent1: the sun is a kind of star"
  IO.println "  sent2: hydrogen is the most common element in stars"
  IO.println "  → hyp: hydrogen is the most common element in the sun"
  IO.println ""

  let some a1 := atoms.get? "sent1" | IO.println "Missing sent1"; return
  let some a2 := atoms.get? "sent2" | IO.println "Missing sent2"; return
  let some ah := atoms.get? "hypothesis" | IO.println "Missing hyp"; return

  IO.println s!"  Premise 1: {a1.pretty}"
  IO.println s!"  Premise 2: {a2.pretty}"
  IO.println s!"  Hypothesis: {ah.pretty}"
  IO.println ""

  -- Try without background
  let result := verifyAtomEntailment #[a1, a2] ah
  match result with
  | .verified rule derived =>
    IO.println s!"  ✓ VERIFIED by {rule}"
    IO.println s!"    Derived: {derived.pretty}"
  | .notVerified reason =>
    IO.println s!"  ✗ NOT VERIFIED (no bg): {reason}"
    -- Try with background
    let bgResult := verifyWithBackground bg #[a1, a2] ah
    match bgResult with
    | .verified rule derived =>
      IO.println s!"  ✓ VERIFIED with background by {rule}"
      IO.println s!"    Derived: {derived.pretty}"
    | .notVerified reason2 =>
      IO.println s!"  ✗ NOT VERIFIED (with bg): {reason2}"

  -- Also test Example 80
  IO.println ""
  IO.println "=== Example 80 ==="
  if let some a80_1 := atoms.get? "ex80_sent1" then
    if let some a80_2 := atoms.get? "ex80_sent2" then
      IO.println s!"  P1: {a80_1.pretty}"
      IO.println s!"  P2: {a80_2.pretty}"
      let r80 := verifyAtomEntailment #[a80_1, a80_2] a80_2
      match r80 with
      | .verified rule _ => IO.println s!"  ✓ ({rule})"
      | .notVerified reason => IO.println s!"  ✗ {reason}"

  IO.println ""
  -- Summary: how many substantive atoms?
  let total := atoms.size
  let substantive := atoms.fold (init := 0) fun acc _ a =>
    if a.isSubstantive then acc + 1 else acc
  let grounded := atoms.fold (init := 0) fun acc _ a =>
    let heads := a.allHeads
    if heads.any (·.synset?.isSome) then acc + 1 else acc
  IO.println s!"=== Summary: {substantive}/{total} substantive, {grounded}/{total} grounded ==="
