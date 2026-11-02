import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogPrinterSource
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogPrinterProgramControls

/-! The text-level theorem covers duplicate statements, escaping and Unicode.
Malformed source spellings remain refusals rather than invented syntax. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourcePrinter.Controls

open Mettapedia.Languages.Datalog
open Mettapedia.GSLT.Parsing.LanguageDefScalarPrinter

def basicText : String := ".decl N(x: number)\nN(-1).\nN(-1).\n.output N\n"

theorem basic_scalars : CorePrinter.printScalars? "DlProgram" basicTree = some (stringScalars basicText) := by
  decide_cbv

theorem basic_printed : print? basic = .ok basicText := by
  have built : programTree? basic = .ok basicTree := by decide +kernel
  have rendered : CorePrinter.printText? "DlProgram" basicTree = some basicText := by
    unfold CorePrinter.printText?
    rw [basic_scalars]
    simp [stringScalars, List.map_map, Function.comp_def]
  simp [print?, built, bind, Except.bind, rendered, pure, Except.pure]

theorem duplicate_text_has_source : ReferenceReader.SourceProgram (stringScalars basicText) basic :=
  printed_program_source basic basicText basic_printed

theorem duplicate_text_reference_readback : basic ∈ ReferenceReader.programs (stringScalars basicText) :=
  printed_program_in_reference basic basicText basic_printed

theorem unicode_print_has_source (text : String) (printed : print? literalContents = .ok text) :
    ReferenceReader.SourceProgram (stringScalars text) literalContents :=
  printed_program_source literalContents text printed

theorem invalid_identifier_cannot_be_printed :
    (print? ⟨[.declaration ⟨["not a name"], []⟩]⟩).isOk = false := by decide_cbv

theorem out_of_range_literal_cannot_be_printed :
    (print? ⟨[.fact ⟨["N"], [.number (2^63)]⟩]⟩).isOk = false := by decide_cbv

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourcePrinter.Controls
