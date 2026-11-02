import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SouffleDatalogCatalogueExecution
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogPrinterDomain
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogPrintedSelection

/-! Total admitted source printing composes with independent source meaning
and retained MeTTa execution. Re-reading a printed program through a complete
checked singleton catalogue recovers the exact program, including order and
duplicate statements. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SnapshotClosureExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.GSLT.LanguageDef.ModuleFormat DatalogIR SouffleDatalog
open Mettapedia.GSLT.Parsing.LanguageDefScalarPrinter
open Mettapedia.Languages.Datalog
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit

theorem admitted_program_prints_and_runs (state : State) (program : Program)
    (sourceAdmitted : SourcePrinter.ProgramAdmitted program)
    (seeds : List GroundFact) (typed : ProgramStatic.ProgramTyped program)
    (inputs : ∀ fact ∈ seeds, StaticTyping.FactTyped (ProgramStatic.signature program) fact)
    (supported : Executable.Nonfloating program seeds) (quantum : Nat) (positive : 0 < quantum) :
    ∃ text, SourcePrinter.print? program = .ok text ∧
      ReferenceReader.SourceProgram (stringScalars text) program ∧
      ∃ prepared, Executable.prepare program seeds = .ok prepared ∧
        ∃ ticks,
          (ClosureMachine.advance prepared ticks quantum (ClosureMachine.begin prepared)).complete = true ∧
          (ClosureMachine.advance prepared ticks quantum (ClosureMachine.begin prepared)).fault = none ∧
          PureReturns runtime [] state
            (apply "gslt:snapshot:advance"
              [encoded (ClosureMachine.machineTerm prepared (ClosureMachine.begin prepared)), number ticks, number quantum]) state
            (encoded (ClosureMachine.machineTerm prepared
              (ClosureMachine.advance prepared ticks quantum (ClosureMachine.begin prepared)))) ∧
          ∀ fact : GroundFact,
            fact ∈ ((ClosureMachine.advance prepared ticks quantum (ClosureMachine.begin prepared)).facts.filterMap
              (Executable.decodeFact? prepared)) ↔ Closure.Derives Executable.policy program seeds fact := by
  obtain ⟨text, printed, source⟩ := SourcePrinter.admitted_prints_source program sourceAdmitted
  exact ⟨text, printed, source, (run_complete_source_reference state (stringScalars text) program source
    seeds typed inputs supported quantum positive).2⟩

theorem printed_readback_exact (environment : Engine.RelationEnv) (program : Program) (text : String)
    (printed : SourcePrinter.print? program = .ok text) (tree : Frontend.SourceAtom) (result : Program)
    (read : Frontend.read text (.expression [.symbol "result", tree, .symbol "nil"]) = .ok result)
    (forestBytes identityBytes : List UInt8) (forestRounds catalogueRounds : Nat)
    (forestComplete : SourceSyntaxForest.complete? SelectedSource.spec text forestBytes identityBytes forestRounds = some true)
    (catalogueComplete : SourceCatalogue.validate? SelectedSource.spec SourcePolicy.filters text forestBytes identityBytes
      [.expression [.symbol "result", tree, .symbol "nil"]] catalogueRounds = some true) : result = program :=
  SelectedSource.checked_unique_program forestComplete catalogueComplete environment result program
    (SelectedSource.read_sound environment text tree result read)
    (SourcePrinter.printed_selected_source environment program text printed)

theorem admitted_program_has_selected_packet (environment : Engine.RelationEnv) (program : Program)
    (admitted : SourcePrinter.ProgramAdmitted program) :
    ∃ text, SourcePrinter.print? program = .ok text ∧
      ∃ tree, Frontend.read text (.expression [.symbol "result", tree, .symbol "nil"]) = .ok program := by
  obtain ⟨text, printed⟩ := SourcePrinter.print_total program admitted
  exact ⟨text, printed, SelectedSource.read_complete environment text program
    (SourcePrinter.printed_selected_source environment program text printed)⟩

#print axioms admitted_program_prints_and_runs
#print axioms printed_readback_exact
#print axioms admitted_program_has_selected_packet

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SnapshotClosureExecution
