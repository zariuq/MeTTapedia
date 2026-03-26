/-
# Dev Set Eval v2 — Term/Atom/NormClause pipeline with grounding + background
Run: lake exe gfEntailEval2
-/

import GFCore
import Lean.Data.Json

open GFCore Lean

def main : IO Unit := do
  IO.println "=== Dev Set Eval v2 (Grounded Term/Atom Pipeline) ==="

  IO.print "Loading signature... "
  let sig ← GrammarSig.readFromFile "gf_fragments/ParseEng_sig.json"
  IO.println s!"OK ({sig.funs.size} functions)"

  IO.print "Loading grounding table... "
  let gt ← GroundingTable.readFromFile "gf_fragments/concept_grounding.json"
  IO.println s!"OK ({gt.entries.size} concepts)"

  IO.print "Loading background knowledge... "
  let bg ← Background.readFromFile "gf_fragments/hypernymy.json"
  IO.println s!"OK ({bg.chains.size} chains, {bg.direct.size} direct)"

  let contents ← IO.FS.readFile "gf_fragments/entailment/dev_eval.json"
  let json ← IO.ofExcept (Json.parse contents)
  let examples ← IO.ofExcept (json.getArr?)

  let mut total : Nat := 0
  let mut allChecked : Nat := 0
  let mut premSubstantive : Nat := 0
  let mut premTotal : Nat := 0
  let mut hypSubstantive : Nat := 0
  let mut verified : Nat := 0
  let mut ruleUsed : Std.HashMap String Nat := {}

  for ex in examples do
    total := total + 1
    let hyp := (ex.getObjValAs? String "hypothesis").toOption.getD "?"
    IO.println s!"--- [{total}] {hyp} ---"

    let premisesJson := (ex.getObjValAs? (Array Json) "premises").toOption.getD #[]
    let mut premAtoms : Array Atom := #[]
    for pj in premisesJson do
      premTotal := premTotal + 1
      let sent := (pj.getObjValAs? String "sentence").toOption.getD "?"
      match pj.getObjValAs? RawTerm "tree" with
      | .ok tree =>
        match check sig tree with
        | .ok expr =>
          let view := toRGLView expr
          let rawAtom := extractSemantics view
          let atom := groundAtom gt rawAtom
          premAtoms := premAtoms.push atom
          if atom.isSubstantive then premSubstantive := premSubstantive + 1
          IO.println s!"  P: {atom.pretty}  ← {sent}"
        | .error e => IO.println s!"  P: CHECK FAIL — {e}"
      | .error e => IO.println s!"  P: JSON ERROR — {e}"

    match ex.getObjValAs? RawTerm "hyp_tree" with
    | .ok hypTree =>
      match check sig hypTree with
      | .ok hypExpr =>
        allChecked := allChecked + 1
        let hypView := toRGLView hypExpr
        let rawHypAtom := extractSemantics hypView
        let hypAtom := groundAtom gt rawHypAtom
        if hypAtom.isSubstantive then hypSubstantive := hypSubstantive + 1
        IO.println s!"  H: {hypAtom.pretty}"

        -- Try without background first, then with
        let result := verifyAtomEntailment premAtoms hypAtom
        match result with
        | .verified rule derived =>
          verified := verified + 1
          ruleUsed := ruleUsed.insert rule ((ruleUsed.getD rule 0) + 1)
          IO.println s!"  ✓ VERIFIED ({rule}): {derived.pretty}"
        | .notVerified _ =>
          -- Try with background knowledge
          let bgResult := verifyWithBackground bg premAtoms hypAtom
          match bgResult with
          | .verified rule derived =>
            verified := verified + 1
            ruleUsed := ruleUsed.insert rule ((ruleUsed.getD rule 0) + 1)
            IO.println s!"  ✓ VERIFIED ({rule}): {derived.pretty}"
          | .notVerified _ =>
            IO.println s!"  ✗ not verified"
      | .error e => IO.println s!"  H: CHECK FAIL — {e}"
    | .error e => IO.println s!"  H: JSON ERROR — {e}"
    IO.println ""

  IO.println "=========================================="
  IO.println s!"Total examples:        {total}"
  IO.println s!"All checked:           {allChecked}/{total}"
  IO.println s!"Premises substantive:  {premSubstantive}/{premTotal} ({if premTotal > 0 then 100 * premSubstantive / premTotal else 0}%)"
  IO.println s!"Hypotheses substantive: {hypSubstantive}/{total} ({if total > 0 then 100 * hypSubstantive / total else 0}%)"
  IO.println s!"Entailment verified:   {verified}/{total} ({if total > 0 then 100 * verified / total else 0}%)"
  if !ruleUsed.isEmpty then
    IO.println "Rules:"
    for (rule, count) in ruleUsed.toArray do
      IO.println s!"  {rule}: {count}"
