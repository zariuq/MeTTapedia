import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangActorProcessStoreExecution

/-! Loaded process-store operations preserve and reflect source process
selection. The reachable-world invariant discharges the index/pid boundary
for every successful finite schedule prefix, without requiring termination.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangActorProcessStoreCorrespondence

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.ErlangActorProcessWire
open Mettapedia.Languages.Erlang
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval DeclarativeSpec WireKit ErlangControllerSource

theorem source_lookup_realized (box : Mailbox Value → Term) (machine : MachineState → Term)
    (state : State) {system : ActorSystem} (valid : system.CanonicalPids)
    {index : Nat} {selected : LocalProcess} (found : system.processes[index]? = some selected) :
    PureReturns runtime [] state (apply "gslt:er-actor:get"
      [number index, encoded (encodeList (process box machine) system.processes)]) state
      (encoded (.application "Some" [process box machine selected])) := by
  simpa only [ActorProcessStore.get_source_index valid found, encodeOption_some] using
    ErlangActorProcessStoreExecution.get_returns box machine state index system.processes

theorem source_update_realized (box : Mailbox Value → Term) (machine : MachineState → Term)
    (state : State) {system : ActorSystem} (valid : system.CanonicalPids)
    {index : Nat} {selected : LocalProcess} (found : system.processes[index]? = some selected)
    (replacement : LocalProcess) :
    PureReturns runtime [] state (apply "gslt:er-actor:put"
      [number index, encoded (process box machine replacement), encoded (encodeList (process box machine) system.processes)]) state
      (encoded (encodeList (process box machine) (system.replace index replacement).processes)) := by
  simpa only [ActorProcessStore.put_source_index valid found, ActorSystem.replace] using
    ErlangActorProcessStoreExecution.put_returns box machine state index replacement system.processes

theorem scheduled_source_lookup (box : Mailbox Value → Term) (machine : MachineState → Term)
    (state : State) (program : Program) (choices : List ActorChoice) {system : ActorSystem}
    (executed : ActorSystem.runChoices choices (ActorSystem.begin program) = .ok system)
    {index : Nat} {selected : LocalProcess} (found : system.processes[index]? = some selected) :
    PureReturns runtime [] state (apply "gslt:er-actor:get"
      [number index, encoded (encodeList (process box machine) system.processes)]) state
      (encoded (.application "Some" [process box machine selected])) :=
  source_lookup_realized box machine state (ActorSystem.started_run_canonical program choices executed) found

theorem completed_lookup_authorized (box : Mailbox Value → Term) (machine : MachineState → Term)
    (state after : State) {system : ActorSystem} (valid : system.CanonicalPids) (index : Nat) (observed : Term)
    (read : Runs runtime {state := state, control := .evaluate [] (apply "gslt:er-actor:get"
      [number index, encoded (encodeList (process box machine) system.processes)])}
      (.complete after [encoded (.application "Some" [observed])] [] [])) :
    ∃ selected, system.processes[index]? = some selected ∧ process box machine selected = observed := by
  have actual := ErlangActorProcessStoreExecution.get_returns box machine state index system.processes
  have values := (pure_returns_derivation_iff runtime [] state state _ _ actual after _ [] []).mp read |>.2.1
  have same := CettaWireAtom.encode_injective _ _ (List.cons.inj values).1
  cases selected : ActorProcessStore.get index system.processes with
  | none =>
    simp only [selected, encodeOption_none] at same
    cases same
  | some selectedProcess =>
    simp only [selected, encodeOption_some] at same
    have payload : process box machine selectedProcess = observed :=
      (List.cons.inj (Term.application.inj same).2).1.symm
    exact ⟨selectedProcess, (ActorProcessStore.get_source_index_iff valid).mp selected, payload⟩

theorem unavailable_process_not_published (box : Mailbox Value → Term) (machine : MachineState → Term)
    (state after : State) {system : ActorSystem} (valid : system.CanonicalPids) (index : Nat)
    (missing : system.processes[index]? = none) (observed : Term) :
    ¬ Runs runtime {state := state, control := .evaluate [] (apply "gslt:er-actor:get"
      [number index, encoded (encodeList (process box machine) system.processes)])}
      (.complete after [encoded (.application "Some" [observed])] [] []) := by
  intro read
  obtain ⟨selected, found, _⟩ := completed_lookup_authorized box machine state after valid index observed read
  rw [missing] at found
  cases found

theorem completed_update_readback (box : Mailbox Value → Term) (machine : MachineState → Term)
    (state after : State) {system : ActorSystem} (valid : system.CanonicalPids)
    {index : Nat} {selected : LocalProcess} (found : system.processes[index]? = some selected)
    (replacement : LocalProcess) (observed : Term)
    (read : Runs runtime {state := state, control := .evaluate [] (apply "gslt:er-actor:put"
      [number index, encoded (process box machine replacement), encoded (encodeList (process box machine) system.processes)])}
      (.complete after [encoded observed] [] [])) :
    observed = encodeList (process box machine) (system.replace index replacement).processes := by
  have actual := source_update_realized box machine state valid found replacement
  have values := (pure_returns_derivation_iff runtime [] state state _ _ actual after _ [] []).mp read |>.2.1
  exact CettaWireAtom.encode_injective _ _ (List.cons.inj values).1

#print axioms source_lookup_realized
#print axioms source_update_realized
#print axioms scheduled_source_lookup
#print axioms completed_lookup_authorized
#print axioms unavailable_process_not_published
#print axioms completed_update_readback

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangActorProcessStoreCorrespondence
