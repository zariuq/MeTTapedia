import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlEmittedControllerCalls

/-! Named O0 entries execute the checked controller in the actual emitted
extension. The run wrapper uses evaluated numeric arguments. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlEmittedWrapperExecution

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.OCamlCompilation
open Mettapedia.Languages
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit OCamlEmittedEntrySource OCamlEmittedControllerCalls
open OCamlInstallExecution OCamlControllerInvariant

def initialController (program : OCaml.Program) (prepared : Prepared) : Term :=
  controller prepared provider "MlRunning"
    (OCamlRunnerBeginExecution.begun prepared provider (initial program)) (.symbol "LNil")

theorem begin_returns (state : State) (program : OCaml.Program) (prepared : Prepared)
    (name : String) (emitted : SpaceSemantics.Program)
    (preparedSource : prepare program = .ok prepared) (built : ExecutionData.emit? prepared name = .ok emitted) :
    PureReturns (moduleRuntime prepared name) [] state (apply (ExecutionData.beginHead name) []) state
      (encoded (initialController program prepared)) := by
  apply Library.call (checked built) (call_contracts built).1 [] state state [] [] _
    (by rw [begin_formals]; rfl) rfl
  rw [begin_body, begin_formals]
  change PureReturns (moduleRuntime prepared name) [] state (ExecutionData.beginBody prepared) state _
  have start := begin_lift state built _ _ _ _ (OCamlBeginExecution.returns state program prepared preparedSource)
  have same := (prepare_readback program prepared preparedSource).1
  have footprint : Mettapedia.OSLF.MeTTaIL.Complete.Footprint.declaredFootprint (plan prepared) = [] := by
    exact epoch_footprint prepared provider (by rfl)
  have samePlan : epochPlan prepared provider = plan prepared := by rfl
  have sameTable : CompleteEmission.table (ExecutionData.spec prepared) = OCamlEpochStandard.names prepared := by
    unfold CompleteEmission.table ExecutionData.spec OCamlEpochStandard.names
    rw [footprint]
  have sameBody : ExecutionData.beginBody prepared = apply "gslt:ml:begin"
      [encoded (CompletePlanWire.planTerm (epochPlan prepared provider) [] [] (.base "MlConfig")),
        encoded (OCamlEpochStandard.standard prepared), encoded (InferenceCettaWire.encodePattern (initial program))] := by
    simp only [ExecutionData.beginBody, ExecutionData.arguments, List.map_cons, List.map_nil, same,
      samePlan, sameTable, OCamlEpochStandard.standard]
  rw [sameBody]
  simpa only [ExecutionData.beginBody, ExecutionData.arguments, List.map_cons, List.map_nil,
    initialController, OCamlControllerInvariant.controller] using start

theorem run_returns (state : State) (program : OCaml.Program) (prepared : Prepared)
    (name : String) (emitted : SpaceSemantics.Program) (ticks quantum : Nat) (answer observed : Term)
    (preparedSource : prepare program = .ok prepared) (built : ExecutionData.emit? prepared name = .ok emitted)
    (advanced : PureReturns OCamlControllerSource.runtime [] state
      (apply "gslt:ml:advance" [number ticks, number quantum, encoded (initialController program prepared)]) state (encoded answer))
    (readout : PureReturns OCamlControllerSource.runtime [] state (apply "gslt:ml:result" [encoded answer]) state (encoded observed)) :
    PureReturns (moduleRuntime prepared name) [] state
      (apply (ExecutionData.runHead name) [number ticks, number quantum]) state (encoded observed) := by
  have contracts := call_contracts built
  have ready : Library.demandReady (ExecutionData.library prepared name)
      ⟨ExecutionData.runHead name, [.var "ticks", .var "quantum"], ExecutionData.runBody name⟩ = true := by
    simpa only [run_equation, Option.any_some] using contracts.2.1
  apply Library.demand_call (checked built) (run_equation prepared name) ready [] state state state
    [number ticks, number quantum] [number ticks, number quantum] _ (by rw [run_formals]; rfl)
  · exact ArgumentsReturn.evaluated contracts.2.2.1 (number_returns _ _ state ticks)
      (.evaluated contracts.2.2.2 (number_returns _ _ state quantum) (.nil _ _))
  · rw [run_body, run_formals]
    unfold ExecutionData.runBody
    apply pure_let_star_returns _ _ _ _ _ _ _ rfl
    apply pure_let_returns _ _ _ "initial" _ (encoded (initialController program prepared)) _ _ (by rfl)
    · have begun := begin_returns state program prepared name emitted preparedSource built
      apply Library.capture (checked built) contracts.1 _ state state [] [] _ (by rw [begin_formals]; rfl) rfl begun
    · apply pure_let_returns _ _ _ "finished" _ (encoded answer) _ _ (by rfl)
      · have advancedHere := advance_lift state built ticks quantum _ _ advanced
        apply capture_controller state built "gslt:ml:advance" _ _ _ _ (by decide +kernel) (by decide)
          _ (by rfl) _ advancedHere
        · simp only [List.zipIdx_cons, List.zipIdx_nil, List.all_cons, List.all_nil]
          have raw : argumentIsRaw OCamlControllerSource.runtime "gslt:ml:advance" 2 = true := by decide +kernel
          simp only [show 0 + 1 + 1 = 2 from rfl, raw, number, encoded, CettaWireAtom.encode,
            passiveArgument, Bool.or_true, Bool.true_or, Bool.and_self]
        · simp [applySubst, Subst.lookup, Library.bind, CettaWireAtom.applySubst_encode]
      · have readHere := result_lift state built _ _ readout
        apply capture_controller state built "gslt:ml:result" _ _ _ _ (by decide +kernel) (by decide)
          _ (by rfl) _ readHere
        · simp only [List.zipIdx_cons, List.zipIdx_nil, List.all_cons, List.all_nil]
          have raw : argumentIsRaw OCamlControllerSource.runtime "gslt:ml:result" 0 = true := by decide +kernel
          simp only [raw, Bool.true_or, Bool.and_self]
        · simp [applySubst, Subst.lookup, Library.bind, CettaWireAtom.applySubst_encode]

#print axioms begin_returns
#print axioms run_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlEmittedWrapperExecution
