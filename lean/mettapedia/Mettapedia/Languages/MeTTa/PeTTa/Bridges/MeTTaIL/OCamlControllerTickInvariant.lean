import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlControllerInvariant
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlOccurrenceFailureService
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlRunningTick
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlControlProgress
import Mettapedia.OSLF.MeTTaIL.Complete.NormalizedPhase

/-! Every running controller value related to a finite independent source
result has a loaded tick execution preserving that result relation. All
runner phases, services and terminal outcomes are selected from proved
source and search invariants rather than assumed by the caller.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlControllerTickInvariant

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.OCamlCompilation
open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise
open Mettapedia.Machines.ResumableSearchRunner
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval WireKit OCamlControllerSource OCamlInstallExecution OCamlControllerInvariant

def epochHistory (prepared : Prepared) (table : ProviderSnapshot)
    (runner : CompleteExecution.ClassMachine (epochPlan prepared table)) (epochs : Term) : Term :=
  .application "LCons" [.application "MlEpoch" [CompletePlanWire.planTerm (epochPlan prepared table) [] [] (.base "MlConfig"),
    CompleteExecution.classMachineTerm (epochPlan prepared table) runner], epochs]

theorem running_tick (state : State) (program : OCaml.Program) (prepared : Prepared) (table : ProviderSnapshot)
    (runner : CompleteExecution.ClassMachine (epochPlan prepared table)) (epochs : Term) (quantum : Nat)
    (source : OCaml.MachineState) (rank work : Nat) (expected : OCaml.Result)
    (built : prepare program = .ok prepared) (invariant : SourceEpochInvariant program prepared table)
    (reached : Reached (Complete.Normalized.search (epochPlan prepared table) [] (.base "MlConfig") .canonical) runner)
    (point : ControlPoint program source runner.state rank) (completed : OCaml.run program work source = .complete expected) :
    ∃ next, PureReturns runtime [] state
      (apply "gslt:ml:tick" [encoded (controller prepared table "MlRunning" runner epochs), number quantum]) state (encoded next) ∧
      Realizes program prepared expected next := by
  rcases Complete.Normalized.reached_phase (epochPlan prepared table) [] (.base "MlConfig") .canonical runner reached with running | done
  · have computed := OCamlRunningTick.returns state prepared table runner epochs quantum (invariant.complete built) invariant.finite reached
      (control_point_epoch_checked program prepared table built point).2 running
    obtain ⟨nextSource, nextRank, remaining, nextPoint, later⟩ := runner_tick_preserves_completed_source program prepared table runner quantum
      built invariant.source reached point completed
    have nextReached := tick_reached (Complete.Normalized.search_lawful (epochPlan prepared table) [] (.base "MlConfig") .canonical) reached quantum
    exact ⟨_, computed, .running table _ epochs nextSource nextRank remaining invariant nextReached nextPoint later⟩
  · rcases settled_control_point_cases program prepared table runner built invariant point completed reached done with service | terminal
    · generalize request : runner.state = config at service
      cases service with
      | primitive operator arguments result rest encodedRest resolved evaluated =>
        obtain ⟨nextInvariant, nextReached, nextPoint, computed⟩ := OCamlServiceSourcePreservation.primitive_tick state program prepared table
          operator arguments result rest encodedRest runner epochs quantum source rank point built invariant resolved reached done request evaluated
        let next := ProviderAppend.appendRows table [primitiveRow operator arguments result]
        let fresh := OCamlRunnerBeginExecution.begun prepared next runner.state
        refine ⟨controller prepared next "MlRunning" fresh (epochHistory prepared table runner epochs), ?_, ?_⟩
        · exact computed
        · exact .running next fresh _ source rank work nextInvariant nextReached nextPoint completed
      | matchFailure index parameter argument body captured rest encodedRest indexed resolved failed =>
        obtain ⟨_, nextInvariant, nextReached, nextPoint, computed⟩ := OCamlOccurrenceFailureService.match_failure_tick state program prepared table
          index parameter argument body captured rest encodedRest runner epochs quantum source rank point built invariant indexed resolved reached done request
        let next := ProviderAppend.appendRows table [failureRow index argument]
        let fresh := OCamlRunnerBeginExecution.begun prepared next runner.state
        refine ⟨controller prepared next "MlRunning" fresh (epochHistory prepared table runner epochs), computed, ?_⟩
        exact .running next fresh _ source rank work nextInvariant nextReached nextPoint completed
      | clauseFailure index clause clauses later argument captured rest encodedRest indexed listed resolved failed =>
        obtain ⟨_, nextInvariant, nextReached, nextPoint, computed⟩ := OCamlOccurrenceFailureService.clause_failure_tick state program prepared table
          index clause.pattern argument clause.body captured clauses later rest encodedRest runner epochs quantum source rank point built invariant
          indexed listed resolved reached done request
        let next := ProviderAppend.appendRows table [failureRow index argument]
        let fresh := OCamlRunnerBeginExecution.begun prepared next runner.state
        refine ⟨controller prepared next "MlRunning" fresh (epochHistory prepared table runner epochs), computed, ?_⟩
        exact .running next fresh _ source rank work nextInvariant nextReached nextPoint completed
    · refine ⟨controller prepared table "MlComplete" runner epochs, ?_, .complete table runner epochs invariant reached done terminal⟩
      cases expected with
      | ok actual =>
        have same : runner.state = node "MlDone" [value actual] := Option.some.inj terminal.symm
        apply OCamlSettledTick.terminal_returns state (epochPlan prepared table) (OCamlEpochStandard.standard prepared)
          (encodeList InferenceCettaWire.encodePattern [value actual]) epochs "MlDone" (.inl rfl) runner quantum reached done
        simp only [same, node, InferenceCettaWire.encodePattern, InferenceCettaWire.encodePatterns_eq_encodeList]
      | error error =>
        have same : runner.state = node "MlFault" [fault error] := Option.some.inj terminal.symm
        apply OCamlSettledTick.terminal_returns state (epochPlan prepared table) (OCamlEpochStandard.standard prepared)
          (encodeList InferenceCettaWire.encodePattern [fault error]) epochs "MlFault" (.inr rfl) runner quantum reached done
        simp only [same, node, InferenceCettaWire.encodePattern, InferenceCettaWire.encodePatterns_eq_encodeList]

#print axioms running_tick

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlControllerTickInvariant
