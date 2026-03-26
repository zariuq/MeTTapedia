/-
# Entailment PoC — Pattern-match on RGLView to verify entailment steps

Example 74:
  sent1: "the sun is a kind of star"        → isA(sun, star)
  sent2: "hydrogen is the most common element in stars"
  → "hydrogen is the most common element in the sun"

Reasoning: sun ⊆ star, so "in stars" can become "in the sun"

Run: lake exe gfEntailPoC
-/

import GFCore
import Lean.Data.Json

open GFCore Lean

structure EntailmentEntry where
  sentence : String
  tree : RawTerm
  prob : Float
  deriving Inhabited

instance : FromJson EntailmentEntry where
  fromJson? j := do
    let sentence ← j.getObjValAs? String "sentence"
    let tree ← j.getObjValAs? RawTerm "tree"
    let prob ← j.getObjValAs? Float "prob"
    pure { sentence, tree, prob }

-- We define these as top-level partial defs because RGLView is a
-- nested inductive (contains List RGLView), so dot notation fails.

partial def rglLeaves : RGLView → List String
  | .noun n => [n]
  | .adj a => [a]
  | .verb v => [v]
  | .prep p => [p]
  | .adv a => [a]
  | .properNoun n => [n]
  | .pronoun p => [p]
  | .det _ _ cn => rglLeaves cn
  | .mass cn => rglLeaves cn
  | .adjMod a c => rglLeaves a ++ rglLeaves c
  | .advMod a v => rglLeaves a ++ rglLeaves v
  | .prepNP p n => rglLeaves p ++ rglLeaves n
  | .pred s v => rglLeaves s ++ rglLeaves v
  | .comp s c => rglLeaves s ++ rglLeaves c
  | .transV v o => rglLeaves v ++ rglLeaves o
  | .passiveV v => rglLeaves v
  | .reflV v a => rglLeaves v ++ rglLeaves a
  | .sentence _ _ c => rglLeaves c
  | .coordAnd xs => xs.flatMap rglLeaves
  | .coordOr xs => xs.flatMap rglLeaves
  | .kindOf k o => rglLeaves k ++ rglLeaves o
  | .opaque _ args => args.flatMap rglLeaves

partial def containsKindOf? : RGLView → Option String
  | .kindOf _ o => (rglLeaves o).head?
  | .opaque _ args => args.findSome? containsKindOf?
  | .sentence _ _ c => containsKindOf? c
  | .comp _ c => containsKindOf? c
  | .pred _ vp => containsKindOf? vp
  | .det _ _ cn => containsKindOf? cn
  | .mass cn => containsKindOf? cn
  | .adjMod _ cn => containsKindOf? cn
  | _ => none

partial def findIsA? : RGLView → Option (String × String)
  -- "X is a kind of Y" → (X, Y) — works for any structure containing kind_of
  | v@(.pred subj vp) =>
    match containsKindOf? vp with
    | some sup => some ((rglLeaves subj).head?.getD "?", sup)
    | none => none
  | v@(.comp subj compl) =>
    match containsKindOf? compl with
    | some sup => some ((rglLeaves subj).head?.getD "?", sup)
    | none => none
  | .sentence _ _ core => findIsA? core
  | _ => none

def stripSense (s : String) : String :=
  -- "star_8_N" → "star", "starMasc_2_N" → "star"
  let parts := s.splitOn "_"
  if parts.length ≥ 3 then
    (String.intercalate "_" (parts.take (parts.length - 2))).toLower
  else if parts.length == 2 then
    parts[0]!.toLower
  else s.toLower

def sameConcept (a b : String) : Bool :=
  stripSense a == stripSense b

def main : IO Unit := do
  IO.println "=== Entailment PoC ==="
  IO.println ""

  -- Load signature
  IO.print "Loading signature... "
  let sig ← GrammarSig.readFromFile "gf_fragments/ParseEng_sig.json"
  IO.println s!"OK ({sig.funs.size} functions)"

  -- Load parsed sentences
  let contents ← IO.FS.readFile "gf_fragments/entailment/entailment_demo.json"
  let json ← IO.ofExcept (Json.parse contents)

  let mut views : Std.HashMap String RGLView := {}

  let entriesObj ← IO.ofExcept (json.getObj?)
  for (key, val) in entriesObj.toList do
    match fromJson? (α := EntailmentEntry) val with
    | .ok entry =>
      match check sig entry.tree with
      | .ok expr =>
        let view := toRGLView expr
        views := views.insert key view
        IO.println s!"  {key}: {view.pretty}"
      | .error e => IO.println s!"  {key}: CHECK FAILED — {e}"
    | .error e => IO.println s!"  {key}: JSON ERROR — {e}"

  IO.println ""
  IO.println "=========================================="
  IO.println "Example 74: Is-A Substitution"
  IO.println "=========================================="
  IO.println ""
  IO.println "  sent1: the sun is a kind of star"
  IO.println "  sent2: hydrogen is the most common element in stars"
  IO.println "  → hyp:  hydrogen is the most common element in the sun"
  IO.println ""

  let some sent1View := views.get? "sent1" | IO.println "Missing sent1"; return
  let some sent2View := views.get? "sent2" | IO.println "Missing sent2"; return
  let some hypView := views.get? "hypothesis" | IO.println "Missing hypothesis"; return

  -- Step 1: Extract is-a from sent1
  IO.println "Step 1: Find is-a relation in sent1"
  match findIsA? sent1View with
  | some (sub, sup) =>
    IO.println s!"  ✓ Found: {stripSense sub} ⊆ {stripSense sup}"

    -- Step 2: Check leaves
    IO.println ""
    IO.println "Step 2: Compare leaves"
    let s2leaves := rglLeaves sent2View |>.map stripSense
    let hleaves := rglLeaves hypView |>.map stripSense
    IO.println s!"  sent2 concepts: {s2leaves}"
    IO.println s!"  hyp concepts:   {hleaves}"

    -- Step 3: Verify substitution
    IO.println ""
    IO.println "Step 3: Verify substitution"
    let supInSent2 := s2leaves.any (· == stripSense sup)
    let subInHyp := hleaves.any (· == stripSense sub)
    IO.println s!"  '{stripSense sup}' in sent2: {supInSent2}"
    IO.println s!"  '{stripSense sub}' in hypothesis: {subInHyp}"

    -- Step 4: Check everything else matches
    let s2other := s2leaves.filter (· != stripSense sup)
    let hother := hleaves.filter (· != stripSense sub)
    let otherMatch := s2other == hother
    IO.println s!"  Other concepts match: {otherMatch}"
    IO.println s!"    sent2 (minus '{stripSense sup}'): {s2other}"
    IO.println s!"    hyp (minus '{stripSense sub}'):   {hother}"

    if supInSent2 && subInHyp then
      IO.println ""
      IO.println "  ✓✓ ENTAILMENT VERIFIED"
      IO.println s!"    Rule: {stripSense sub} ⊆ {stripSense sup} (from sent1)"
      IO.println s!"    Applied: replace '{stripSense sup}' with '{stripSense sub}' in sent2"
      IO.println s!"    Result: hypothesis follows"

  | none =>
    IO.println "  ✗ No is-a relation found"

  IO.println ""
  IO.println "=== Done ==="
