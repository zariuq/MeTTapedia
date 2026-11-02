import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SouffleDatalogSourceCoverage
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogReferenceReader

/-! The complete source reference composes with actual preparation and the
retained MeTTa closure. Native parser qualification remains separate. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SnapshotClosureExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR
open Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog
open Mettapedia.Languages.Datalog
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit

theorem run_complete_source_reference (state : State) (input : List Nat) (program : Program)
    (source : ReferenceReader.SourceProgram input program)
    (seeds : List GroundFact) (typed : ProgramStatic.ProgramTyped program)
    (inputs : ∀ fact ∈ seeds, StaticTyping.FactTyped (ProgramStatic.signature program) fact)
    (supported : Executable.Nonfloating program seeds)
    (quantum : Nat) (positive : 0 < quantum) :
    program ∈ ReferenceReader.programs input ∧
      ∃ prepared, Executable.prepare program seeds = .ok prepared ∧
        ∃ ticks,
          (ClosureMachine.advance prepared ticks quantum (ClosureMachine.begin prepared)).complete = true ∧
          (ClosureMachine.advance prepared ticks quantum (ClosureMachine.begin prepared)).fault = none ∧
          PureReturns runtime [] state
            (apply "gslt:snapshot:advance"
              [encoded (ClosureMachine.machineTerm prepared (ClosureMachine.begin prepared)),number ticks,number quantum]) state
            (encoded (ClosureMachine.machineTerm prepared
              (ClosureMachine.advance prepared ticks quantum (ClosureMachine.begin prepared)))) ∧
          ∀ fact : GroundFact,
            fact ∈ ((ClosureMachine.advance prepared ticks quantum (ClosureMachine.begin prepared)).facts.filterMap
              (Executable.decodeFact? prepared)) ↔ Closure.Derives Executable.policy program seeds fact := by
  obtain ⟨prepared,accepted⟩ := Executable.prepare_complete program seeds typed inputs supported
  exact ⟨ReferenceReader.programs_complete input program source,prepared,accepted,
    run_prepared_total state program seeds prepared accepted quantum positive⟩

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SnapshotClosureExecution
