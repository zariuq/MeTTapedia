import Mettapedia.GSLT.Parsing.ParserProfileWire
import Mettapedia.Languages.ProcessCalculi.MORK.MM2SyntaxNTT

/-!
# MM2 parser-profile wire projection

The lexical profile is serialized by the generic parser-profile renderer.  It
is a separate authenticated input to ParserPack compilation, not a hidden
reader table selected by the MM2 language name.
-/

namespace Mettapedia.Languages.ProcessCalculi.MORK.MM2ParserProfileWire

open Mettapedia.GSLT.Parsing.ParserProfileSemantics
open Mettapedia.Languages.ProcessCalculi.MORK.MM2SyntaxNTT

abbrev renderProfile := Mettapedia.GSLT.Parsing.ParserProfileWire.render

/-- Canonical generated wire text for the authored MM2 lexical profile. -/
def wire : String := renderProfile mm2ParserProfile

theorem wire_nonempty : wire ≠ "" := by
  exact Mettapedia.GSLT.Parsing.ParserProfileWire.render_nonempty _

private def profileWithoutDollarBoundary : ParserProfileLayer := {
  mm2ParserProfile with
  classes := mm2ParserProfile.classes.map fun declaration =>
    if declaration.name == "MM2BareHeadClass" then
      { declaration with kind := .except [9, 10, 32, 34, 40, 41, 59] }
    else declaration
}

/-- The negative profile mutation accepts dollar as a bare-token head while
the authenticated MM2 profile rejects it. -/
theorem dollar_boundary_mutation_changes_language :
    profileWithoutDollarBoundary.classAccepts? "MM2BareHeadClass" 36 =
        some true ∧
      mm2ParserProfile.classAccepts? "MM2BareHeadClass" 36 = some false := by
  decide +kernel

def writeWire (path : System.FilePath) : IO Unit :=
  IO.FS.writeFile path wire

#print axioms wire_nonempty
#print axioms dollar_boundary_mutation_changes_language

end Mettapedia.Languages.ProcessCalculi.MORK.MM2ParserProfileWire
