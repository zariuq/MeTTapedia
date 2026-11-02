import Mettapedia.Languages.Erlang.ActorProcessStore
import Mettapedia.Languages.Erlang.ActorControls
import Mettapedia.Languages.Erlang.StandardActorExamples
import Mettapedia.Languages.Erlang.ParallelActorExamples

/-! Reachable pid stores and separating noncanonical inputs. Duplicate
payloads are allowed; duplicate process identities invalidate the relation
between a source list position and a target pid lookup. -/

set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 32768

namespace Mettapedia.Languages.Erlang.ActorIdentityControls

def canonicalResult : Except ActorError ActorSystem → Bool
  | .error _ => false
  | .ok system => system.processes.map LocalProcess.identity == List.range system.nextPid

#guard canonicalResult ActorControls.selfResult
#guard canonicalResult ActorControls.spawnResult
#guard canonicalResult ActorControls.receiveResult
#guard canonicalResult ActorControls.pendingSystem
#guard canonicalResult ActorControls.awakenedResult
#guard canonicalResult StandardActorExamples.pingPongResult
#guard canonicalResult StandardActorExamples.counterResult
#guard canonicalResult ParallelActorExamples.parallelMapReverseResult
#guard canonicalResult ParallelActorExamples.duplicateMapReverseResult
#guard canonicalResult ParallelActorExamples.causalReverseResult

def duplicateSystem : ActorSystem := {
  ActorSystem.begin ActorControls.selfProgram with
  processes := [⟨0, Erlang.begin ActorControls.selfProgram, {}⟩,
    ⟨0, Erlang.begin ActorControls.selfProgram, {}⟩]
  nextPid := 2 }

theorem duplicate_ids_refused : ¬ duplicateSystem.CanonicalPids := by
  intro valid
  have distinct := ActorProcessStore.canonical_unique valid
  change ([0, 0] : List Nat).Nodup at distinct
  simp at distinct

#guard (ActorProcessStore.get 1 duplicateSystem.processes).isNone
#guard duplicateSystem.processes[1]?.map LocalProcess.identity == some 0

theorem counter_mismatch_refused :
    ¬ ({ActorSystem.begin ActorControls.selfProgram with nextPid := 0} : ActorSystem).CanonicalPids := by
  intro valid
  have size := valid.length
  change 1 = 0 at size
  omega

theorem replacement_identity_refused :
    ¬ ((ActorSystem.begin ActorControls.selfProgram).replace 0
      ⟨17, Erlang.begin ActorControls.selfProgram, {}⟩).CanonicalPids := by
  intro valid
  have identity := valid.at (index := 0) (process := ⟨17, Erlang.begin ActorControls.selfProgram, {}⟩) rfl
  change 17 = 0 at identity
  omega

theorem duplicate_pid_shadows_index (first second : MachineState) (different : first ≠ second) :
    ActorProcessStore.get 0 [⟨0, first, {}⟩, ⟨0, second, {}⟩] ≠
      ([⟨0, first, {}⟩, ⟨0, second, {}⟩] : List LocalProcess)[1]? := by
  intro same
  change (some ⟨0, first, {}⟩ : Option LocalProcess) = some ⟨0, second, {}⟩ at same
  exact different (congrArg LocalProcess.machine (Option.some.inj same))

theorem duplicate_pid_update_shadows_index (first second replacement : MachineState)
    (changed : replacement ≠ first) :
    ActorProcessStore.put 0 ⟨0, replacement, {}⟩ [⟨0, first, {}⟩, ⟨0, second, {}⟩] ≠
      ([⟨0, first, {}⟩, ⟨0, second, {}⟩] : List LocalProcess).set 1 ⟨0, replacement, {}⟩ := by
  intro same
  change ([⟨0, replacement, {}⟩, ⟨0, second, {}⟩] : List LocalProcess) =
    [⟨0, first, {}⟩, ⟨0, replacement, {}⟩] at same
  exact changed (congrArg LocalProcess.machine (List.cons.inj same).1)

example (program : Program) (first second : List ActorChoice) {middle final : ActorSystem}
    (executed : ActorSystem.runChoices first (ActorSystem.begin program) = .ok middle)
    (resumed : ActorSystem.runChoices second middle = .ok final) : final.CanonicalPids :=
  (ActorSystem.started_run_canonical program first executed).runChoices second resumed

#print axioms duplicate_ids_refused
#print axioms counter_mismatch_refused
#print axioms replacement_identity_refused
#print axioms duplicate_pid_shadows_index
#print axioms duplicate_pid_update_shadows_index

end Mettapedia.Languages.Erlang.ActorIdentityControls
