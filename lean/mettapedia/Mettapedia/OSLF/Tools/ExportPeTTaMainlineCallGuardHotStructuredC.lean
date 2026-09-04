import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteStructuredCProgram
import Mettapedia.GSLT.LanguageDef.InferenceMeTTaRender

namespace Mettapedia.OSLF.Tools.ExportPeTTaMainlineCallGuardHotStructuredC

open Mettapedia.GSLT.LanguageDef.InferenceMeTTaRender
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteStructuredCProgram

/-- Canonical structural Pattern wire consumed by the StructuredC emitter. -/
def programWire : String := renderPattern generatedHotModeProgram ++ "\n"

def main (arguments : List String) : IO UInt32 := do
  match arguments with
  | [programPath] =>
      IO.FS.writeFile programPath programWire
      pure 0
  | _ =>
      IO.eprintln
        "usage: export-petta-mainline-call-guard-hot-structured-c <program>"
      pure 2

end Mettapedia.OSLF.Tools.ExportPeTTaMainlineCallGuardHotStructuredC

def main (arguments : List String) : IO UInt32 :=
  Mettapedia.OSLF.Tools.ExportPeTTaMainlineCallGuardHotStructuredC.main arguments
