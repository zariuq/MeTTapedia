import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCProgram
import Mettapedia.GSLT.LanguageDef.InferenceMeTTaRender

namespace Mettapedia.OSLF.Tools.ExportPeTTaMainlineCallGuardStructuredC

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceMeTTaRender
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCProgram

/-- Canonical structural Pattern wire consumed by the StructuredC emitter. -/
def programWire : String := renderPattern generatedColdProgram ++ "\n"

def main (arguments : List String) : IO UInt32 := do
  match arguments with
  | [languagePath, programPath] =>
      IO.FS.writeFile languagePath StructuredC.wire
      IO.FS.writeFile programPath programWire
      pure 0
  | _ =>
      IO.eprintln
        "usage: export-petta-mainline-call-guard-structured-c <language> <program>"
      pure 2

end Mettapedia.OSLF.Tools.ExportPeTTaMainlineCallGuardStructuredC

def main (arguments : List String) : IO UInt32 :=
  Mettapedia.OSLF.Tools.ExportPeTTaMainlineCallGuardStructuredC.main arguments
