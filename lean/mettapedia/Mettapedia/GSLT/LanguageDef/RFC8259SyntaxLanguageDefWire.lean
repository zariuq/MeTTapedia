import Mettapedia.GSLT.LanguageDef.RFC8259SyntaxNTT
import Mettapedia.GSLT.LanguageDef.CanonicalWire

/-!
# RFC 8259 syntax wire projection

The external parser compiler consumes the canonical rendering of the same
authored `LanguageDef` whose spatial and operational structure is analyzed by
OSLF/NTT.  The checked wire artifact is therefore not a parallel JSON grammar.
-/

namespace Mettapedia.GSLT.LanguageDef.RFC8259SyntaxLanguageDefWire

open Mettapedia.GSLT.LanguageDef.RFC8259SyntaxNTT

abbrev renderLanguage? :=
  Mettapedia.GSLT.LanguageDef.CanonicalWire.renderLanguage?

theorem wire_isSome :
    (renderLanguage? rfc8259Syntax).isSome := by
  decide +kernel

/-- Canonical generated wire text for the authored RFC 8259 syntax. -/
def wire : String :=
  (renderLanguage? rfc8259Syntax).getD ""

theorem wire_nonempty : wire != "" := by
  decide +kernel

def writeWire (path : System.FilePath) : IO Unit :=
  IO.FS.writeFile path wire

#print axioms wire_isSome
#print axioms wire_nonempty

end Mettapedia.GSLT.LanguageDef.RFC8259SyntaxLanguageDefWire
