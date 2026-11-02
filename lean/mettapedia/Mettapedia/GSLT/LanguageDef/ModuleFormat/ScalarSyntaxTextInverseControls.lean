import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceSyntaxIOControls

/-! Source existence and separating controls for the text-level inverse.
Ambiguous constructors stay distinct even when they print the same text. -/

set_option autoImplicit false
set_option maxRecDepth 32768

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.ScalarSyntaxCore.TextInverseControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.Parsing
open LanguageDefScalarSyntax LanguageDefScalarPrinter

def digitDescription : Description := {
  grammar := { name := "DigitSyntax", types := ["Digit"], terms := [], equations := [], rewrites := [] }
  profile := {
    name := "DigitSyntax"
    startSort := "Digit"
    classes := [⟨"digit", .points [48,49,50,51,52,53,54,55,56,57]⟩]
    states := [{resultSort := "Digit", className := "digit", ruleLabel := "digit-leaf"}] }
  leafPrefix := "scalar:" }

theorem digit_shape : Shape digitDescription := (checkShape_exact _).mp (by decide_cbv)

def seven : Pattern := wordLeaf digitDescription ⟨0, by decide⟩ 55

theorem printed_digit_is_source :
    ∃ tree, Nonempty (DerivesAt (fun text => some (stringScalars text))
      digitDescription.profile digitDescription.grammar [55] "Digit" 0 1 tree) ∧
      lowerCST? digitDescription "Digit" tree = some seven :=
  printed_text_readback digitDescription digit_shape "Digit" seven "7" (by decide_cbv)

theorem wrong_class_refused :
    printText? digitDescription "Digit" (wordLeaf digitDescription ⟨0, by decide⟩ 955) = none := by
  decide_cbv

theorem surrogate_refused :
    printText? digitDescription "Digit" (wordLeaf digitDescription ⟨0, by decide⟩ 55296) = none := by
  decide_cbv

theorem malformed_scalar_refused :
    printText? digitDescription "Digit" (.apply "scalar:Digit" [.apply "R16Pack24" []]) = none := by
  decide_cbv

theorem ambiguous_printing_is_not_injective :
    ¬ Function.Injective (SourceSyntaxIO.print? SourceSyntaxIO.Controls.spec) := by
  intro injective
  have same := injective (show SourceSyntaxIO.print? SourceSyntaxIO.Controls.spec (.apply "First" []) =
      SourceSyntaxIO.print? SourceSyntaxIO.Controls.spec (.apply "Second" []) from by decide_cbv)
  exact (by decide : Pattern.apply "First" [] ≠ Pattern.apply "Second" []) same

theorem missing_child_refused :
    SourceSyntaxIO.print? SourceSyntaxIO.Controls.spec (.apply "Pair" [.apply "First" []]) = none := by
  decide_cbv

end Mettapedia.GSLT.LanguageDef.ModuleFormat.ScalarSyntaxCore.TextInverseControls
