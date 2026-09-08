import Mettapedia.GSLT.Parsing.CanonicalSourceHornElaboration

/-!
# Canonical authored-GSLT source checker

This opt-in executable parses authored MeTTa source, decodes the exact
`gslt-presentation-v1` schema, checks canonical re-encoding, and runs the
structural source admission predicate.  It authenticates the source artifact;
semantic adequacy of its directed rules is a separate theorem obligation.
-/

namespace Mettapedia.GSLT.Tools.CheckCanonicalSourceGSLT

open Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation
open Mettapedia.GSLT.LanguageDef.CanonicalSourceGSLT
open Mettapedia.GSLT.Parsing.CanonicalSourceHornElaboration

private def usage : String :=
  "usage: CheckCanonicalSourceGSLT (--schema | --composition | --horn-composition) source1.metta [source2.metta ...]"

private def decodeFile (path : String) : IO (Option Source) := do
  let contents <- IO.FS.readFile path
  match Algorithms.MeTTa.Simple.Parser.parseSExprWithDetailed
      MeTTailCore.MeTTaSyntax.petta contents with
  | .error message =>
      IO.eprintln s!"{path}: MeTTa source parse failed: {message}"
      pure none
  | .ok raw =>
      match decode raw with
      | some source =>
          if encode source != raw then
            IO.eprintln s!"{path}: source GSLT is not canonically encoded"
            pure none
          else if !source.hasValidSchema then
            IO.eprintln s!"{path}: source GSLT fails open-component schema admission"
            pure none
          else
            IO.println s!"(CanonicalSourceGSLTAcceptedV1 {path} {source.name} {source.operators.length} {source.equations.length} {source.rewrites.length})"
            pure (some source)
      | none =>
          IO.eprintln s!"{path}: expected exactly one canonical gslt-presentation-v1 fact"
          pure none

private def decodeFiles : List String -> IO (Option (List Source))
  | [] => pure (some [])
  | path :: paths => do
      let source <- decodeFile path
      let sources <- decodeFiles paths
      pure do
        let head <- source
        let tail <- sources
        some (head :: tail)

def run (args : List String) : IO UInt32 := do
  match args with
  | "--schema" :: paths | "--composition" :: paths |
      "--horn-composition" :: paths =>
    if paths.isEmpty then
      IO.eprintln usage
      pure 1
    else
      match <- decodeFiles paths with
      | none => pure 1
      | some sources =>
          if (args.head? == some "--composition" ||
              args.head? == some "--horn-composition") &&
              !compositionValid sources then
            IO.eprintln "source GSLTs do not form a closed valid composition"
            pure 1
          else
            if args.head? == some "--composition" then
              IO.println s!"(CanonicalSourceGSLTCompositionAcceptedV1 {sources.length} {(compositionOperators sources).length} {(compositionRewriteNames sources).length})"
              pure 0
            else if args.head? == some "--horn-composition" then
              match elaborateProgram? sources with
              | none =>
                  IO.eprintln "source GSLT composition is outside the admitted first-order Horn fragment"
                  pure 1
              | some program =>
                  IO.println s!"(CanonicalSourceHornCompositionAcceptedV1 {sources.length} {program.length})"
                  pure 0
            else
              pure 0
  | _ =>
    IO.eprintln usage
    pure 1

end Mettapedia.GSLT.Tools.CheckCanonicalSourceGSLT

def main (args : List String) : IO UInt32 :=
  Mettapedia.GSLT.Tools.CheckCanonicalSourceGSLT.run args
