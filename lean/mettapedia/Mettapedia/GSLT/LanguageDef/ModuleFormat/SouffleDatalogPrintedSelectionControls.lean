import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogPrintedSelection
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogPrinterSourceControls
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogSourcePolicyControls

/-! Duplicate programs and literal keyword contents retain selected-source
meaning; reserved identifiers and malformed packets remain refusals. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourcePrinter.Controls

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.Datalog

theorem duplicates_have_selected_source (environment : Engine.RelationEnv) :
    SelectedSource.ProgramMeaning environment basicText basic :=
  printed_selected_source environment basic basicText basic_printed

theorem duplicates_have_selected_packet (environment : Engine.RelationEnv) :
    ∃ tree, Frontend.read basicText (.expression [.symbol "result", tree, .symbol "nil"]) = .ok basic :=
  SelectedSource.read_complete environment basicText basic (duplicates_have_selected_source environment)

theorem keyword_literal_has_selected_source (environment : Engine.RelationEnv) :
    ∃ text, SelectedSource.ProgramMeaning environment text ⟨[.fact ⟨["Text"], [.symbol "count"]⟩]⟩ := by
  let program : Program := ⟨[.fact ⟨["Text"], [.symbol "count"]⟩]⟩
  have admitted : ProgramAdmitted program := (checkProgram_exact program).mp (by decide +kernel)
  obtain ⟨text, printed⟩ := print_total program admitted
  exact ⟨text, printed_selected_source environment program text printed⟩

theorem malformed_packet_refused (input : String) :
    Frontend.read input (.expression [.symbol "result", .symbol "not-a-tree", .symbol "nil"]) =
      .error "source packet violates checked grammar or declared selection" := by
  simp [Frontend.read, SelectedReader.core?, SourcePacketSelection.core?, SourcePacketSelection.read?,
    SourcePacketCertificate.readPacket?, SourcePacketCertificate.propose?, SourcePacketCertificate.proposeFuel,
    SourcePacket.packetNodes, SourcePacket.node?]

theorem reserved_identifier_still_refused :
    (print? ⟨[.declaration ⟨["count"], []⟩]⟩).isOk = false := by decide_cbv

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourcePrinter.Controls
