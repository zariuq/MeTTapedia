import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogPrinterShared
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogSourceReader
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogSourcePolicy
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceSelectedMeaning

/-! The Datalog frontend uses the shared checked source reader with the
grammar's declared selection policy. Its core is the replayed source fold. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SelectedReader

open Mettapedia.GSLT.Parsing
open Mettapedia.OSLF.MeTTaIL.Syntax

def parser : ScalarSyntaxCore.Parser SourcePrinter.description := {
  rules := SourceReader.rules
  plan := SourceReader.plan
  rulesCompiled := SourceReader.rules_compiled
  planCompiled := SourceReader.plan_compiled }

theorem profile : SourcePacketEncoding.Profile parser.plan :=
  (SourcePacketEncoding.checkProfile_exact _).mp (by decide +kernel)

def core? (input : String) (packet : SourcePacket.Packet) : Option Pattern :=
  SourcePacketSelection.core? SourcePrinter.description parser SourcePrinter.description_shape
    SourcePolicy.filters (input.toList.map Char.toNat) "DlProgram" packet

theorem core?_prints {input : String} {packet : SourcePacket.Packet} {core : Pattern}
    (read : core? input packet = some core) : CorePrinter.printText? "DlProgram" core = some input := by
  have printed := SourcePacketSelection.core?_prints read
  rw [← SourcePrinter.shared_print]
  unfold ScalarSyntaxCore.printText?
  rw [printed]
  simp [List.map_map, Function.comp_def]

theorem core?_source {input : String} {packet : SourcePacket.Packet} {core : Pattern}
    (read : core? input packet = some core) :
    SourcePacketSelection.Source SourcePrinter.description parser SourcePolicy.filters
      (input.toList.map Char.toNat) "DlProgram" core :=
  SourcePacketSelection.core?_sound read

theorem source_has_packet {input : String} {core : Pattern}
    (source : SourcePacketSelection.Source SourcePrinter.description parser SourcePolicy.filters
      (input.toList.map Char.toNat) "DlProgram" core) :
    ∃ packet, core? input packet = some core :=
  SourcePacketSelection.source_has_packet parser SourcePrinter.description_shape profile source

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SelectedReader
