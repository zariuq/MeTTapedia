import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogPrinterShared
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogPrinterProgramLaws
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogReferenceReader

/-! Datalog's independent program printer produces genuine source syntax.
The shared print inverse supplies the grammar/profile derivation; the program
roundtrip theorem supplies exact independent IR readback. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourcePrinter

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.Datalog
open Mettapedia.GSLT.Parsing
open LanguageDefScalarPrinter

theorem printed_program_source (program : Program) (text : String)
    (printed : print? program = .ok text) :
    ReferenceReader.SourceProgram (stringScalars text) program := by
  cases built : programTree? program with
  | error reason => simp [print?, built, bind, Except.bind] at printed
  | ok pattern =>
    cases rendered : CorePrinter.printText? "DlProgram" pattern with
    | none => simp [print?, built, bind, Except.bind, rendered] at printed
    | some result =>
      have same : result = text := by simpa [print?, built, bind, Except.bind, rendered, pure, Except.pure] using printed
      subst result
      have common : ScalarSyntaxCore.printText? description "DlProgram" pattern = some text :=
        (shared_print _ _).trans rendered
      obtain ⟨tree, source, lowered⟩ := ScalarSyntaxCore.printed_text_readback
        description description_shape "DlProgram" pattern text common
      refine ⟨tree, pattern, source, ?_, program_tree_roundtrip program pattern built⟩
      exact (shared_lower _ _).symm.trans lowered

theorem printed_program_in_reference (program : Program) (text : String)
    (printed : print? program = .ok text) :
    program ∈ ReferenceReader.programs (stringScalars text) :=
  ReferenceReader.programs_complete _ _ (printed_program_source program text printed)

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourcePrinter
