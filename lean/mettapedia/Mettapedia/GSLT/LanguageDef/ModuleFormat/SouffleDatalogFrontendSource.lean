import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogPrinterShared
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogReferenceReader

/-! The ordinary frontend's input-readback check entails an independent
source-grammar derivation, including lexical classes and exact Unicode input.
Native forest completeness is not assumed or asserted by this soundness law. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.Frontend

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.Datalog
open Mettapedia.GSLT.Parsing.LanguageDefScalarPrinter

theorem read_source (environment : Engine.RelationEnv) (input : String) (tree : SourceAtom)
    (program : Program)
    (accepted : read input (.expression [.symbol "result", tree, .symbol "nil"]) = .ok program) :
    ReferenceReader.SourceProgram (stringScalars input) program := by
  obtain ⟨source, _, printed, projected, projectedStep, normalized⟩ :=
    SourceMeaning.read_sound environment input tree program accepted
  have common : ScalarSyntaxCore.printText? SourcePrinter.description "DlProgram" source = some input :=
    (SourcePrinter.shared_print _ _).trans printed
  obtain ⟨cst, derived, lowered⟩ := ScalarSyntaxCore.printed_text_readback
    SourcePrinter.description SourcePrinter.description_shape "DlProgram" source input common
  refine ⟨cst, source, derived, (SourcePrinter.shared_lower _ _).symm.trans lowered, ?_⟩
  have projectedRead := (ProgramProjection.Program.reference_exact environment source projected).mp projectedStep
  rw [projectedRead, Option.bind_some, SourceMeaning.normalization_complete normalized,
    Option.bind_some, IRCodec.program_roundtrip]

theorem read_in_reference (environment : Engine.RelationEnv) (input : String) (tree : SourceAtom)
    (program : Program)
    (accepted : read input (.expression [.symbol "result", tree, .symbol "nil"]) = .ok program) :
    program ∈ ReferenceReader.programs (stringScalars input) :=
  ReferenceReader.programs_complete _ _ (read_source environment input tree program accepted)

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.Frontend
