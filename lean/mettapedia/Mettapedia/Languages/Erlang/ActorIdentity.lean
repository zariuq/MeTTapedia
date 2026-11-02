import Mettapedia.Languages.Erlang.Actors

/-! Process identities in reachable local actor configurations. Processes
are retained after termination, and spawning appends the next identity.
Consequently source list indices and controller pid keys agree. -/

set_option autoImplicit false

namespace Mettapedia.Languages.Erlang.ActorSystem

structure CanonicalPids (system : ActorSystem) : Prop where
  identities : system.processes.map LocalProcess.identity = List.range system.nextPid

theorem CanonicalPids.begin (program : Program) : CanonicalPids (ActorSystem.begin program) :=
  ⟨rfl⟩

theorem CanonicalPids.length {system : ActorSystem} (valid : CanonicalPids system) :
    system.processes.length = system.nextPid := by
  simpa only [List.length_map, List.length_range] using congrArg List.length valid.identities

theorem CanonicalPids.bounded {system : ActorSystem} (valid : CanonicalPids system)
    {process : LocalProcess} (member : process ∈ system.processes) : process.identity < system.nextPid := by
  apply List.mem_range.mp
  rw [← valid.identities]
  exact List.mem_map.mpr ⟨process, member, rfl⟩

theorem CanonicalPids.at {system : ActorSystem} (valid : CanonicalPids system)
    {index : Nat} {process : LocalProcess} (found : system.processes[index]? = some process) :
    process.identity = index := by
  obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp found
  have within : index < system.nextPid := by rw [← valid.length]; exact bound
  have mapped : (system.processes.map LocalProcess.identity)[index]? = some process.identity := by
    simp only [List.getElem?_map, found, Option.map_some]
  rw [valid.identities, List.getElem?_range within] at mapped
  exact (Option.some.inj mapped).symm

theorem CanonicalPids.no_collision {system : ActorSystem} (valid : CanonicalPids system) :
    (system.processes.any fun process => process.identity == system.nextPid) = false := by
  apply Bool.eq_false_iff.mpr
  intro collided
  obtain ⟨process, member, same⟩ := List.any_eq_true.mp collided
  have bound := valid.bounded member
  have equal : process.identity = system.nextPid := by simpa only [beq_iff_eq] using same
  omega

theorem identities_set {processes : List LocalProcess} {index : Nat} {old replacement : LocalProcess}
    (found : processes[index]? = some old) (same : replacement.identity = old.identity) :
    (processes.set index replacement).map LocalProcess.identity = processes.map LocalProcess.identity := by
  rw [List.map_set, same]
  obtain ⟨bound, value⟩ := List.getElem?_eq_some_iff.mp found
  have selected : (processes.map LocalProcess.identity)[index]'(by simpa using bound) = old.identity := by
    simp only [List.getElem_map, value]
  rw [← selected, List.set_getElem_self]

theorem CanonicalPids.replace {system : ActorSystem} (valid : CanonicalPids system)
    {index : Nat} {old replacement : LocalProcess} (found : system.processes[index]? = some old)
    (same : replacement.identity = old.identity) : CanonicalPids (system.replace index replacement) := by
  constructor
  exact (identities_set found same).trans valid.identities

theorem CanonicalPids.deliver {system next : ActorSystem} (valid : CanonicalPids system)
    {index : Nat} (delivered : system.deliver? index = some next) : CanonicalPids next := by
  unfold deliver? at delivered
  cases selected : Network.deliverAt? index system.network with
  | none => simp [selected] at delivered
  | some pair =>
    rcases pair with ⟨message, pending⟩
    simp only [selected] at delivered
    dsimp at delivered
    cases delivered
    constructor
    rw [List.map_map]
    simp only [Function.comp_def]
    have same : (fun process : LocalProcess =>
        (if process.identity = message.key.receiver && !stopped process.machine then
          {process with mailbox := process.mailbox.deliver message.payload} else process).identity) =
        LocalProcess.identity := by
      funext process
      split <;> rfl
    rw [same]
    exact valid.identities

end Mettapedia.Languages.Erlang.ActorSystem
