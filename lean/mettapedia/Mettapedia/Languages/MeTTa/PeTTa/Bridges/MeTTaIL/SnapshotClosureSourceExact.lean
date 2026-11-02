import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SnapshotClosureSourceSoundness
import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRClosureExact
import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRClosureTermination
import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRPlanAdmission
import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRLanguageValidation

/-! The retained MeTTa closure loop returns a frame whose completed fact
observation is exactly the independent Datalog derivability judgment. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SnapshotClosureExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR
open Mettapedia.Languages.Datalog
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit

theorem run_source_exact (state : State) (program : Mettapedia.Languages.Datalog.Program)
    (seeds : List GroundFact) (prepared : Executable.Prepared)
    (accepted : Executable.prepare program seeds = .ok prepared)
    (admitted : (Executable.plan prepared prepared.seedFacts.eraseDups).complete = true)
    (scope : GeneralPremise.Static.checkLanguage (GeneralPlanEnvironment.environment (Executable.plan prepared prepared.seedFacts)) = true)
    (ticks quantum : Nat) (finished : (ClosureMachine.advance prepared ticks quantum (ClosureMachine.begin prepared)).complete = true) :
    PureReturns runtime [] state
      (apply "gslt:snapshot:advance"
        [encoded (ClosureMachine.machineTerm prepared (ClosureMachine.begin prepared)),number ticks,number quantum]) state
      (encoded (ClosureMachine.machineTerm prepared
        (ClosureMachine.advance prepared ticks quantum (ClosureMachine.begin prepared)))) ∧
    ∀ fact : GroundFact,
      fact ∈ ((ClosureMachine.advance prepared ticks quantum (ClosureMachine.begin prepared)).facts.filterMap (Executable.decodeFact? prepared)) ↔
        Closure.Derives Executable.policy program seeds fact :=
  ⟨run_returns state prepared admitted ticks quantum,
    ClosureMachine.run_facts_exact program seeds prepared accepted admitted scope ticks quantum finished⟩

theorem run_source_total (state : State) (program : Mettapedia.Languages.Datalog.Program)
    (seeds : List GroundFact) (prepared : Executable.Prepared)
    (accepted : Executable.prepare program seeds = .ok prepared)
    (admitted : (Executable.plan prepared prepared.seedFacts.eraseDups).complete = true)
    (scope : GeneralPremise.Static.checkLanguage (GeneralPlanEnvironment.environment (Executable.plan prepared prepared.seedFacts)) = true)
    (quantum : Nat) (positive : 0 < quantum) :
    ∃ ticks,
      (ClosureMachine.advance prepared ticks quantum (ClosureMachine.begin prepared)).complete = true ∧
      (ClosureMachine.advance prepared ticks quantum (ClosureMachine.begin prepared)).fault = none ∧
      PureReturns runtime [] state
        (apply "gslt:snapshot:advance"
          [encoded (ClosureMachine.machineTerm prepared (ClosureMachine.begin prepared)),number ticks,number quantum]) state
        (encoded (ClosureMachine.machineTerm prepared
          (ClosureMachine.advance prepared ticks quantum (ClosureMachine.begin prepared)))) ∧
      ∀ fact : GroundFact,
        fact ∈ ((ClosureMachine.advance prepared ticks quantum (ClosureMachine.begin prepared)).facts.filterMap (Executable.decodeFact? prepared)) ↔
          Closure.Derives Executable.policy program seeds fact := by
  obtain ⟨ticks,finished⟩ := ClosureMachine.run_eventually_complete program seeds prepared accepted scope quantum positive
  have exactRun := run_source_exact state program seeds prepared accepted admitted scope ticks quantum finished
  exact ⟨ticks,finished,ClosureMachine.run_noFault program seeds prepared accepted scope ticks quantum,exactRun.1,exactRun.2⟩

theorem run_prepared_total (state : State) (program : Mettapedia.Languages.Datalog.Program)
    (seeds : List GroundFact) (prepared : Executable.Prepared)
    (accepted : Executable.prepare program seeds = .ok prepared)
    (quantum : Nat) (positive : 0 < quantum) :
    ∃ ticks,
      (ClosureMachine.advance prepared ticks quantum (ClosureMachine.begin prepared)).complete = true ∧
      (ClosureMachine.advance prepared ticks quantum (ClosureMachine.begin prepared)).fault = none ∧
      PureReturns runtime [] state
        (apply "gslt:snapshot:advance"
          [encoded (ClosureMachine.machineTerm prepared (ClosureMachine.begin prepared)),number ticks,number quantum]) state
        (encoded (ClosureMachine.machineTerm prepared
          (ClosureMachine.advance prepared ticks quantum (ClosureMachine.begin prepared)))) ∧
      ∀ fact : GroundFact,
        fact ∈ ((ClosureMachine.advance prepared ticks quantum (ClosureMachine.begin prepared)).facts.filterMap (Executable.decodeFact? prepared)) ↔
          Closure.Derives Executable.policy program seeds fact :=
  run_source_total state program seeds prepared accepted (LanguageValidation.initial_admitted program seeds prepared accepted)
    (PlanAdmission.scope_checked program seeds prepared accepted prepared.seedFacts) quantum positive

#print axioms run_source_exact
#print axioms run_source_total
#print axioms run_prepared_total

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SnapshotClosureExecution
