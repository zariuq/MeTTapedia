import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SouffleDatalogSourceExecution
import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRExecutableCoverage

/-! Typed, supported ordinary-source programs reach the retained MeTTa
closure without assuming compiler preparation success. Parser packet
selection remains an explicit frontend boundary. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SnapshotClosureExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR
open Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog
open Mettapedia.Languages.Datalog
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit

theorem run_typed_ordinary_source_total (state : State) (environment : Engine.RelationEnv)
    (input : String) (tree : Frontend.SourceAtom) (program : Program)
    (read : Frontend.read input (.expression [.symbol "result",tree,.symbol "nil"]) = .ok program)
    (seeds : List GroundFact) (typed : ProgramStatic.ProgramTyped program)
    (inputs : ∀ fact ∈ seeds, StaticTyping.FactTyped (ProgramStatic.signature program) fact)
    (supported : Executable.Nonfloating program seeds)
    (quantum : Nat) (positive : 0 < quantum) :
    ∃ prepared, Executable.prepare program seeds = .ok prepared ∧
      ∃ source, SelectedReader.core? input tree = some source ∧
        CorePrinter.printText? "DlProgram" source = some input ∧
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
              (Executable.decodeFact? prepared)) ↔
            ∃ meaningProgram, SourceMeaning.Denotes environment source meaningProgram ∧
              Closure.Derives Executable.policy meaningProgram seeds fact := by
  obtain ⟨prepared,accepted⟩ := Executable.prepare_complete program seeds typed inputs supported
  exact ⟨prepared,accepted,run_ordinary_source_total state environment input tree program read
    seeds prepared accepted quantum positive⟩

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SnapshotClosureExecution
