import Mettapedia.GSLT.LanguageDef.ModuleFormat.ScalarSyntaxPrintInverse
import Mettapedia.GSLT.Parsing.LanguageDefScalarUnicode

/-! Text-level inverse of the shared syntax printer, including exact Unicode
transport. The recovered tree is a source derivation, not merely a tree that
the constructor projector happens to accept. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.ScalarSyntaxCore

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.Parsing
open LanguageDefScalarSyntax LanguageDefScalarPrinter PresentationExprSemantics

theorem printScalars_valid (description : Description) (sort : String) (pattern : Pattern) (points : List Nat)
    (printed : printScalars? description sort pattern = some points) :
    ∀ point ∈ points, point.isValidChar := by
  obtain ⟨_, source, _⟩ := print_source description sort pattern points printed (sequence_self points)
  simpa only [full_source source] using render_valid source

theorem printText_scalars (description : Description) (sort : String) (pattern : Pattern) (text : String)
    (printed : printText? description sort pattern = some text) :
    printScalars? description sort pattern = some (stringScalars text) := by
  obtain ⟨points, scalars, textEq⟩ := Option.map_eq_some_iff.mp printed
  rw [← textEq, stringScalars_of_valid points (printScalars_valid description sort pattern points scalars)]
  exact scalars

theorem printed_text_readback (description : Description) (shape : Shape description)
    (sort : String) (pattern : Pattern) (text : String)
    (printed : printText? description sort pattern = some text) :
    ∃ tree, Nonempty (DerivesAt (fun text => some (stringScalars text))
      description.profile description.grammar (stringScalars text) sort 0 (stringScalars text).length tree) ∧
      lowerCST? description sort tree = some pattern :=
  printed_source_readback description shape sort pattern (stringScalars text)
    (printText_scalars description sort pattern text printed)

end Mettapedia.GSLT.LanguageDef.ModuleFormat.ScalarSyntaxCore
