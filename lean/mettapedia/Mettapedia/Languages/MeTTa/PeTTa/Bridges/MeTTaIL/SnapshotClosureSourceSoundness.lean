import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SnapshotClosureAdvanceExecution
import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRClosureSoundness

/-! The retained MeTTa loop returns the model frame whose facts satisfy the
independent Datalog derivability judgment. This is the preservation direction;
source-firing coverage and settled equality are separate obligations. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SnapshotClosureExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR
open Mettapedia.Languages.Datalog
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit

theorem run_source_sound (state : State) (program : Mettapedia.Languages.Datalog.Program)
    (seeds : List GroundFact) (prepared : Executable.Prepared)
    (accepted : Executable.prepare program seeds = .ok prepared)
    (admitted : (Executable.plan prepared prepared.seedFacts.eraseDups).complete = true)
    (scope : GeneralPremise.Static.checkLanguage (GeneralPlanEnvironment.environment (Executable.plan prepared prepared.seedFacts)) = true)
    (ticks quantum : Nat) :
    PureReturns runtime [] state
      (apply "gslt:snapshot:advance"
        [encoded (ClosureMachine.machineTerm prepared (ClosureMachine.begin prepared)),number ticks,number quantum]) state
      (encoded (ClosureMachine.machineTerm prepared
        (ClosureMachine.advance prepared ticks quantum (ClosureMachine.begin prepared)))) ∧
    ClosureMachine.FactsSound prepared program seeds
      (ClosureMachine.advance prepared ticks quantum (ClosureMachine.begin prepared)).facts :=
  ⟨run_returns state prepared admitted ticks quantum,
    ClosureMachine.run_factsSound program seeds prepared accepted scope ticks quantum⟩

#print axioms run_source_sound

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SnapshotClosureExecution
