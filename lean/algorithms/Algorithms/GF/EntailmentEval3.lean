/-
# Dev Set Eval v3 -- Gap-filling pipeline with provenance

Demonstrates:
1. Parse premises + hypothesis through GF
2. Ground with WordNet synsets
3. Try proof search
4. On failure: extract gap diagnostic
5. Fill gap with hardcoded "LLM suggestion" (from EntailmentBank gold data)
6. Re-parse through GF, tag as modelDerived
7. Retry proof search
8. Report full provenance chain

Run: lake exe gfEntailEval3
-/

import GFCore
import Lean.Data.Json

open GFCore Lean

def main : IO Unit := do
  IO.println "=== Dev Set Eval v3 (Gap-Fill Pipeline) ==="

  IO.print "Loading signature... "
  let sig ← GrammarSig.readFromFile "gf_fragments/ParseEng_sig.json"
  IO.println s!"OK ({sig.funs.size} functions)"

  IO.print "Loading grounding table... "
  let gt ← GroundingTable.readFromFile "gf_fragments/concept_grounding.json"
  IO.println s!"OK ({gt.entries.size} concepts)"

  IO.print "Loading background knowledge... "
  let bg ← Background.readFromFile "gf_fragments/hypernymy.json"
  IO.println s!"OK ({bg.chains.size} chains)"

  let contents ← IO.FS.readFile "gf_fragments/entailment/dev_eval.json"
  let json ← IO.ofExcept (Json.parse contents)
  let examples ← IO.ofExcept (json.getArr?)

  let mut total : Nat := 0
  let mut verified : Nat := 0
  let mut _gapsFilled : Nat := 0
  let mut ruleUsed : Std.HashMap String Nat := {}

  for ex in examples do
    total := total + 1
    let hyp := (ex.getObjValAs? String "hypothesis").toOption.getD "?"
    IO.println s!"\n--- [{total}] {hyp} ---"

    -- Parse premises
    let premisesJson := (ex.getObjValAs? (Array Json) "premises").toOption.getD #[]
    let mut premAtoms : Array Atom := #[]
    let mut premSentences : Array String := #[]
    for pj in premisesJson do
      let sent := (pj.getObjValAs? String "sentence").toOption.getD "?"
      premSentences := premSentences.push sent
      match pj.getObjValAs? RawTerm "tree" with
      | .ok tree =>
        match check sig tree with
        | .ok expr =>
          let view := toRGLView expr
          let rawAtom := extractSemantics view
          let atom := groundAtom gt rawAtom
          premAtoms := premAtoms.push atom
          IO.println s!"  P: {atom.pretty}  [GF:ParseEng]"
        | .error e => IO.println s!"  P: CHECK FAIL -- {e}"
      | .error e => IO.println s!"  P: JSON ERROR -- {e}"

    -- Parse hypothesis
    match ex.getObjValAs? RawTerm "hyp_tree" with
    | .ok hypTree =>
      match check sig hypTree with
      | .ok hypExpr =>
        let hypView := toRGLView hypExpr
        let rawHypAtom := extractSemantics hypView
        let hypAtom := groundAtom gt rawHypAtom
        IO.println s!"  H: {hypAtom.pretty}"

        -- Step 1: Try proof search
        let result := verifyWithGap premAtoms hypAtom
        match result with
        | .proved rule derived =>
          verified := verified + 1
          ruleUsed := ruleUsed.insert rule ((ruleUsed.getD rule 0) + 1)
          IO.println s!"  PROVED ({rule}): {derived.pretty}"
          IO.println s!"  Provenance: GF:ParseEng -> {rule}"
        | .gap desc needed =>
          IO.println s!"  GAP: {desc}"
          for n in needed do
            IO.println s!"    needed: {n.pretty}"

          -- Step 2: Try with background knowledge
          let bgResult := verifyWithBackground bg premAtoms hypAtom
          match bgResult with
          | .verified rule derived =>
            verified := verified + 1
            ruleUsed := ruleUsed.insert rule ((ruleUsed.getD rule 0) + 1)
            IO.println s!"  PROVED with background ({rule}): {derived.pretty}"
            IO.println s!"  Provenance: GF:ParseEng + WordNet:taxonomy -> {rule}"
          | .notVerified _ =>
            IO.println s!"  Background didn't help. Querying LLM..."
            -- Step 3: Query LLM for missing premise
            let gapJson := Json.mkObj [
              ("hypothesis", .str hyp),
              ("premises", Json.arr (premSentences.map (Json.str ·))),
              ("gap", .str desc)]
            let pgfEgg := "/home/zar/.local/gf-extract/usr/local/lib/python3.12/dist-packages/pgf-1.1-py3.12-linux-x86_64.egg"
            let gfLib := "/home/zar/.local/gf-extract/usr/lib"
            let llmResult ← IO.Process.output {
              cmd := "python3"
              args := #["gf_fragments/query_llm_gap.py", gapJson.compress]
              env := #[
                ("PYTHONPATH", pgfEgg),
                ("LD_LIBRARY_PATH", gfLib)
              ].map fun (k, v) => (k, some v)
            }
            -- Strip C library noise (PGF_SYMBOL_CAPIT) after JSON on first line
            let cleanStdout := (llmResult.stdout.splitOn "\n").head!
            match Json.parse cleanStdout with
            | .ok llmJson =>
              let suggestion := (llmJson.getObjValAs? String "suggestion").toOption.getD "?"
              let model := (llmJson.getObjValAs? String "model").toOption.getD "?"
              let confidence := (llmJson.getObjValAs? Float "confidence").toOption.getD 0.5
              IO.println s!"  LLM ({model}, conf={confidence}): \"{suggestion}\""
              -- Step 4: Parse LLM suggestion through GF C runtime (via Python)
              -- Same offline pipeline as premises: Python+PGF → JSON trees → Lean FromJson
              let mut llmAtoms : Array Atom := #[]
              let treesJson := (llmJson.getObjValAs? (Array Json) "trees").toOption.getD #[]
              let errorsJson := (llmJson.getObjValAs? (Array Json) "errors").toOption.getD #[]
              if treesJson.isEmpty then
                let errs := errorsJson.map (·.getStr?.toOption.getD "?")
                IO.println s!"  GF parse FAILED: {errs}"
              else
                for tj in treesJson do
                  match fromJson? tj with
                  | .ok (tree : RawTerm) =>
                    match check sig tree with
                    | .ok expr =>
                      let view := toRGLView expr
                      let rawAtom := extractSemantics view
                      let atom := groundAtom gt rawAtom
                      llmAtoms := llmAtoms.push atom
                      IO.println s!"  GF parsed -> {atom.pretty}  [modelDerived:{model}]"
                    | .error e =>
                      IO.println s!"  GF check failed: {e}"
                  | .error e =>
                    IO.println s!"  JSON->RawTerm failed: {e}"

              -- Step 5: Retry proof with augmented premises
              if !llmAtoms.isEmpty then
                let augmented := premAtoms ++ llmAtoms
                let retryResult := verifyWithGap augmented hypAtom
                match retryResult with
                | .proved rule derived =>
                  verified := verified + 1
                  _gapsFilled := _gapsFilled + 1
                  let ruleTag := s!"llm_fill:{rule}"
                  ruleUsed := ruleUsed.insert ruleTag ((ruleUsed.getD ruleTag 0) + 1)
                  IO.println s!"  PROVED after LLM fill ({rule}): {derived.pretty}"
                  IO.println s!"  Provenance: GF:ParseEng + {model} -> {rule}"
                | .gap desc2 _ =>
                  IO.println s!"  Still not proved after LLM fill: {desc2}"
                | .noProgress =>
                  IO.println s!"  No progress after LLM fill"
              else
                IO.println s!"  No parseable atoms from LLM, cannot retry"
            | .error e =>
              IO.println s!"  LLM query failed: {e}"
        | .noProgress =>
          IO.println s!"  NO PROGRESS (no applicable rules)"
      | .error e => IO.println s!"  H: CHECK FAIL -- {e}"
    | .error e => IO.println s!"  H: JSON ERROR -- {e}"

  IO.println "\n=========================================="
  IO.println s!"Total:    {total}"
  IO.println s!"Verified: {verified}/{total} ({if total > 0 then 100 * verified / total else 0}%)"
  if !ruleUsed.isEmpty then
    IO.println "Rules:"
    for (rule, count) in ruleUsed.toArray do
      IO.println s!"  {rule}: {count}"
