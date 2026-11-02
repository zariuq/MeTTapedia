import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourcePacketCoverage
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogPrinterSource

/-! The shared packet inverse reaches Datalog's independent program IR.
Its declaration profile is computed from the actual Datalog parser tables.
Native enumeration and uniqueness of selected programs are separate laws. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.PacketCoverage

open Mettapedia.GSLT.Parsing
open Mettapedia.Languages.Datalog
open Mettapedia.OSLF.MeTTaIL.Syntax

def parser : ScalarSyntaxCore.Parser SourcePrinter.description := {
  rules := SourceReader.rules
  plan := SourceReader.plan
  rulesCompiled := SourceReader.rules_compiled
  planCompiled := SourceReader.plan_compiled }

theorem profile : SourcePacketEncoding.Profile parser.plan :=
  (SourcePacketEncoding.checkProfile_exact _).mp (by decide +kernel)

theorem source_program_packet (input : List Nat) (program : Program)
    (source : ReferenceReader.SourceProgram input program) :
    ∃ packet pattern,
      SourcePacketCertificate.core? SourcePrinter.description parser SourcePrinter.description_shape
        input "DlProgram" packet = some pattern ∧
      ((ProgramProjection.Reference.projectProgram? pattern).bind Frontend.normalize?).bind IRCodec.program? = some program := by
  obtain ⟨tree, pattern, ⟨derived⟩, lowered, projected⟩ := source
  have common : ScalarSyntaxCore.lowerCST? SourcePrinter.description "DlProgram" tree = some pattern :=
    (SourcePrinter.shared_lower _ _).trans lowered
  have same : ScalarSyntaxCore.reify SourcePrinter.description derived = pattern :=
    Option.some.inj ((ScalarSyntaxCore.lowerCST_source SourcePrinter.description SourcePrinter.description_shape derived).symm.trans common)
  refine ⟨SourcePacketEncoding.encode tree, pattern, ?_, projected⟩
  exact (SourcePacketCoverage.core_complete parser SourcePrinter.description_shape profile derived).trans
    (congrArg some same)

theorem printed_program_packet (program : Program) (text : String)
    (printed : SourcePrinter.print? program = .ok text) :
    ∃ packet pattern,
      SourcePacketCertificate.core? SourcePrinter.description parser SourcePrinter.description_shape
        (LanguageDefScalarPrinter.stringScalars text) "DlProgram" packet = some pattern ∧
      ((ProgramProjection.Reference.projectProgram? pattern).bind Frontend.normalize?).bind IRCodec.program? = some program :=
  source_program_packet _ _ (SourcePrinter.printed_program_source program text printed)

#print axioms profile
#print axioms source_program_packet
#print axioms printed_program_packet

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.PacketCoverage
