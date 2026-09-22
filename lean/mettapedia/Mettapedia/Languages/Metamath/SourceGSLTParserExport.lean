import Mettapedia.Languages.Metamath.SourceGSLTParserDefinition

/-!
# Emitting the canonical Metamath source parser

Parser data and their correspondence proofs live in `SourceGSLTParserDefinition`.
This module owns the exporter and its command-line entry point.
-/

namespace Mettapedia.Languages.Metamath.SourceGSLTParserExport

open Mettapedia.Languages.Metamath.SourceGSLTParserDefinition

def main (arguments : List String) : IO UInt32 := do
  match arguments with
  | [outputPath] =>
      IO.FS.writeFile outputPath renderedPresentation
      IO.println s!"wrote {renderedPresentation.toUTF8.size} bytes to {outputPath}"
      pure 0
  | _ =>
      IO.eprintln "usage: SourceGSLTParserExport <output.metta>"
      pure 1

end Mettapedia.Languages.Metamath.SourceGSLTParserExport

def main (arguments : List String) : IO UInt32 :=
  Mettapedia.Languages.Metamath.SourceGSLTParserExport.main arguments
