import Mettapedia.GSLT.LanguageDef.RFC8259ParserProfileNTT
import Mettapedia.GSLT.Parsing.ParserProfileWire

/-!
# RFC 8259 parser-profile wire projection

The external ParserPack compiler consumes the canonical rendering of the same
lexical profile whose classes and structural schema are analyzed in Lean.
-/

namespace Mettapedia.GSLT.LanguageDef.RFC8259ParserProfileWire

open Mettapedia.GSLT.LanguageDef.RFC8259ParserProfileNTT

/-- Canonical wire rendering of a parser-profile layer. -/
abbrev renderProfile := Mettapedia.GSLT.Parsing.ParserProfileWire.render

/-- Canonical generated wire text for the authored RFC 8259 parser profile. -/
def wire : String := renderProfile rfc8259ParserProfile

theorem wire_nonempty : wire != "" := by
  decide +kernel

def writeWire (path : System.FilePath) : IO Unit :=
  IO.FS.writeFile path wire

#print axioms wire_nonempty

end Mettapedia.GSLT.LanguageDef.RFC8259ParserProfileWire
