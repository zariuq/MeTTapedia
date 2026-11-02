import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogPrinterValueLaws

/-! Source constructor controls distinguish numeric spelling from magnitude,
retain the signed width boundary, and reject malformed scalar categories. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.ScalarControls

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.Datalog
open SourcePrinter

def decimal (text : String) : Pattern :=
  node "integer-decimal" [(digits? text.toList).toOption.getD (.apply "Invalid" [])]

theorem decimal_text (text : String) (digits : Pattern) (built : digits? text.toList = .ok digits) :
    Frontend.sourceText? (decimal text) = some text := by
  unfold decimal
  rw [built]
  change Frontend.sourceText? (node "integer-decimal" [digits]) = _
  rw [source_integer_decimal, integer_decimal, digits_print _ _ built]
  simp

def zeroDigits : Pattern := (digits? "00012".toList).toOption.get (by decide +kernel)

theorem leading_zeros_text : Frontend.sourceText? (decimal "00012") = some "00012" :=
  decimal_text "00012" zeroDigits (by decide +kernel)

theorem leading_zeros_read :
    Frontend.value? "IntegerValue" (decimal "00012") = some (IRCodec.value (.number 12)) := by
  change ((Frontend.sourceText? (decimal "00012")).bind fun spelling =>
    (NumericSpelling.readInteger? spelling).bind fun value =>
      if Mettapedia.Languages.Datalog.Value.fits64 (.number value) then some (IRCodec.value (.number value)) else none) = _
  rw [leading_zeros_text]
  decide +kernel

theorem positive_width_refused :
    NumericSpelling.readInteger? "9223372036854775808" = some (2^63) ∧
    Mettapedia.Languages.Datalog.Value.fits64 (.number (2^63)) = false := by decide +kernel

theorem maximum_width_read :
    NumericSpelling.readInteger? "9223372036854775807" = some (2^63-1) ∧
    Mettapedia.Languages.Datalog.Value.fits64 (.number (2^63-1)) = true := by decide +kernel

theorem float_still_refused : Frontend.value? "FloatValue" (decimal "1") = none := rfl

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.ScalarControls
