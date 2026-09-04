import Mettapedia.GSLT.LanguageDef.CanonicalWire
import Mettapedia.Languages.ProcessCalculi.MORK.MM2SyntaxNTT

/-!
# MM2 syntax wire projection

The generic ParserPack compiler consumes this canonical rendering of the same
authored MM2 syntax definition used by the Lean parser and OSLF/NTT results.
-/

namespace Mettapedia.Languages.ProcessCalculi.MORK.MM2SyntaxWire

open Mettapedia.Languages.ProcessCalculi.MORK.MM2SyntaxNTT

abbrev renderLanguage? :=
  Mettapedia.GSLT.LanguageDef.CanonicalWire.renderLanguage?

theorem wire_isSome : (renderLanguage? mm2Syntax).isSome := by
  decide +kernel

/-- Canonical generated wire text for the authored MM2 syntax. -/
def wire : String := (renderLanguage? mm2Syntax).getD ""

theorem wire_nonempty : wire ≠ "" := by
  decide +kernel

/-- Removing the variable constructor changes the authenticated language
source rather than merely changing generated metadata. -/
private def mm2SyntaxWithoutVariable := {
  mm2Syntax with
  terms := mm2Syntax.terms.filter (fun rule => rule.label != "mm2:variable")
}

/-- The negative source mutation really removes one declared constructor;
wire provenance therefore cannot authenticate it as the original source. -/
theorem removing_variable_changes_source :
    mm2SyntaxWithoutVariable.terms.length + 1 = mm2Syntax.terms.length := by
  decide +kernel

def writeWire (path : System.FilePath) : IO Unit :=
  IO.FS.writeFile path wire

#print axioms wire_isSome
#print axioms wire_nonempty
#print axioms removing_variable_changes_source

end Mettapedia.Languages.ProcessCalculi.MORK.MM2SyntaxWire
