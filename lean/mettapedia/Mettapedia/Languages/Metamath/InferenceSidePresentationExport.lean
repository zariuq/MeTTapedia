import Mettapedia.GSLT.LanguageDef.InferenceMeTTaRender
import Mettapedia.Languages.Metamath.InferenceSideConditions

/-!
# Export the admitted Metamath inference side calculus

The output is the canonical `GPresentation` wire value consumed by the generic
native inference checker.  It contains the finite substitution and
distinct-variable rules, not an implementation-specific callback table.
-/

namespace Mettapedia.Languages.Metamath.InferenceSidePresentationExport

open Mettapedia.GSLT.LanguageDef.InferenceMeTTaRender
open Mettapedia.Languages.Metamath.InferenceSideConditions

def renderedPresentation : String :=
  renderPresentation sidePresentation ++ "\n"

theorem exportedRuleCount : sideRules.length = 22 := by
  decide

def main (arguments : List String) : IO UInt32 := do
  match arguments with
  | [outputPath] =>
      if sidePresentation.isValidV2 then
        if outputPath == "-" then
          IO.print renderedPresentation
        else
          IO.FS.writeFile outputPath renderedPresentation
          IO.println s!"wrote {renderedPresentation.toUTF8.size} bytes"
        pure 0
      else
        IO.eprintln "Metamath inference side presentation is invalid"
        pure 1
  | _ =>
      IO.eprintln "usage: InferenceSidePresentationExport <output.metta>"
      pure 2

end Mettapedia.Languages.Metamath.InferenceSidePresentationExport

def main (arguments : List String) : IO UInt32 :=
  Mettapedia.Languages.Metamath.InferenceSidePresentationExport.main arguments
