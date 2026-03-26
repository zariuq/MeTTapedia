/-
# Generate GF lexicon modules from JSONL data

Usage:
  lake exe gfGenLex <lexicon.jsonl> <output_dir> <module_name>

Example:
  lake exe gfGenLex gf_fragments/entailment/lexicon.jsonl gf_fragments/entailment/ EntailmentLex

Generates:
  <output_dir>/<module_name>.gf      -- abstract
  <output_dir>/<module_name>Eng.gf   -- English concrete
-/

import GFCore

open GFCore

def main (args : List String) : IO UInt32 := do
  match args with
  | [lexPath, outDir, modName] =>
    let rows ← readLexicon lexPath
    IO.println s!"Read {rows.size} lexicon rows from {lexPath}"

    let absGF := generateAbstractGF modName rows
    match generateConcreteEngGF modName (modName ++ "Eng") rows with
    | .error errors =>
      IO.eprintln s!"ERROR: {errors.size} lexicon rows have unsupported categories:"
      for e in errors do
        IO.eprintln s!"  {e}"
      return 1
    | .ok engGF =>

    let absPath := outDir ++ "/" ++ modName ++ ".gf"
    let engPath := outDir ++ "/" ++ modName ++ "Eng.gf"
    IO.FS.writeFile absPath absGF
    IO.FS.writeFile engPath engGF

    IO.println s!"Wrote: {absPath}"
    IO.println s!"Wrote: {engPath}"

    -- Stats
    let bycat : Std.HashMap String Nat := rows.foldl (init := {})
      fun acc r => acc.insert r.cat ((acc.getD r.cat 0) + 1)
    for (cat, count) in bycat.toArray do
      IO.println s!"  {cat}: {count}"

    return 0
  | _ =>
    IO.eprintln "Usage: gfGenLex <lexicon.jsonl> <output_dir> <module_name>"
    return 1
