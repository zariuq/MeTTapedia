import Mettapedia.GSLT.LanguageDef.InferenceMeTTaRender
import Mettapedia.Languages.Metamath.InferenceSideConditions

/-!
# Export the admitted Metamath inference side language

The output is the canonical inference-language wire value consumed by the generic
native inference checker.  It contains the finite substitution and
distinct-variable rules, not an implementation-specific callback table.
-/

namespace Mettapedia.Languages.Metamath.InferenceSideLanguageExport

open Mettapedia.GSLT.LanguageDef.InferenceMeTTaRender
open Mettapedia.Languages.Metamath.InferenceSideConditions

def renderedDefinition : String :=
  renderDefinition sideDefinition ++ "\n"

theorem exportedRuleCount : sideRules.length = 22 := by
  decide

def main (arguments : List String) : IO UInt32 := do
  match arguments with
  | [outputPath] =>
      if sideDefinition.isValid then
        if outputPath == "-" then
          IO.print renderedDefinition
        else
          IO.FS.writeFile outputPath renderedDefinition
          IO.println s!"wrote {renderedDefinition.toUTF8.size} bytes"
        pure 0
      else
        IO.eprintln "Metamath inference side language is invalid"
        pure 1
  | _ =>
      IO.eprintln "usage: InferenceSideLanguageExport <output.metta>"
      pure 2

end Mettapedia.Languages.Metamath.InferenceSideLanguageExport

def main (arguments : List String) : IO UInt32 :=
  Mettapedia.Languages.Metamath.InferenceSideLanguageExport.main arguments
