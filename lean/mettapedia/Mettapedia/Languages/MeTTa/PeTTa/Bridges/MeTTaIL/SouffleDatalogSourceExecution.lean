import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogFrontendMeaning
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SnapshotClosureSourceExact

/-! Selected ordinary-source packets and admitted preparation compose with
the retained MeTTa loop. Completed facts preserve and reflect the authored
source projection and independent literal/name meaning. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SnapshotClosureExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR
open Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog
open Mettapedia.Languages.Datalog
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit

theorem run_ordinary_source_total (state : State) (environment : Engine.RelationEnv)
    (input : String) (tree : Frontend.SourceAtom) (program : Program)
    (read : Frontend.read input (.expression [.symbol "result",tree,.symbol "nil"]) = .ok program)
    (seeds : List GroundFact) (prepared : Executable.Prepared)
    (accepted : Executable.prepare program seeds = .ok prepared)
    (quantum : Nat) (positive : 0 < quantum) :
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
  obtain ⟨source,sourceRead,textRead,meaning⟩ := SourceMeaning.read_sound environment input tree program read
  obtain ⟨ticks,finished,noFault,returns,facts⟩ :=
    run_prepared_total state program seeds prepared accepted quantum positive
  refine ⟨source,sourceRead,textRead,ticks,finished,noFault,returns,?_⟩
  intro fact
  constructor
  · intro present
    exact ⟨program,meaning,(facts fact).mp present⟩
  · rintro ⟨other,otherMeaning,derived⟩
    have same := SourceMeaning.denotes_functional environment source other program otherMeaning meaning
    subst other
    exact (facts fact).mpr derived

#print axioms run_ordinary_source_total

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SnapshotClosureExecution
