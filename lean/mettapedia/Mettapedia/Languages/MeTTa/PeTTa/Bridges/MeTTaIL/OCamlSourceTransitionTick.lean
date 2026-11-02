import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlAdmittedRunningTick
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlSourceStepNormalized

/-! Actual loaded MeTTa ticks at ordinary source states keep searching or
enter a control point for the independent source successor. Together with
administrative ticks this covers both execution phases.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlSourceTransitionTick

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.OCamlCompilation
open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval WireKit OCamlControllerSource OCamlInstallExecution

theorem returns_with_source_transition (state : State) (program : OCaml.Program) (prepared : Prepared)
    (table : GeneralPremise.ProviderSnapshot) (source nextSource : OCaml.MachineState)
    (runner : CompleteExecution.ClassMachine (epochPlan prepared table)) (epochs : Term) (quantum : Nat)
    (built : prepare program = .ok prepared) (signatures : table.signatures = provider.signatures)
    (closed : GeneralPremise.checkProviderClosed prepared.compiled (epochSnapshot prepared table).free table = true)
    (finite : table.dynamicRelations = [])
    (reached : Mettapedia.Machines.ResumableSearchRunner.Reached
      (Complete.Normalized.search (epochPlan prepared table) [] (.base "MlConfig") .canonical) runner)
    (encodedSource : state? (patterns program) source = some runner.state)
    (sourceStep : OCaml.machineStep program source = .ok (some nextSource)) (running : runner.phase = .running) :
    let plan := CompletePlanWire.planTerm (epochPlan prepared table) [] [] (.base "MlConfig")
    let standard := OCamlEpochStandard.standard prepared
    let next := Mettapedia.Machines.ResumableSearchRunner.Machine.tick
      (Complete.Normalized.search (epochPlan prepared table) [] (.base "MlConfig") .canonical) runner quantum
    PureReturns runtime [] state
      (apply "gslt:ml:tick" [encoded (machine "MlRunning" plan standard
        (CompleteExecution.classMachineTerm (epochPlan prepared table) runner) epochs), number quantum]) state
      (encoded (machine "MlRunning" plan standard (CompleteExecution.classMachineTerm (epochPlan prepared table) next) epochs)) ∧
    (ControlPoint program source next.state 0 ∨ ∃ rank, ControlPoint program nextSource next.state rank) :=
  ⟨OCamlAdmittedRunningTick.returns state program prepared table source runner epochs quantum built signatures
      closed finite reached encodedSource running,
    source_runner_tick program prepared table runner quantum source nextSource built reached encodedSource sourceStep⟩

#print axioms returns_with_source_transition

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlSourceTransitionTick
