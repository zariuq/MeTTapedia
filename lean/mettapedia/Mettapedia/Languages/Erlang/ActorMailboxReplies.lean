import Mettapedia.Languages.Erlang.Actors

/-! Source observations at actor mailbox requests. A local infinite wait
has no actor transition when its unread suffix is empty; queued network
messages still prevent a global blocked observation. -/

set_option autoImplicit false

namespace Mettapedia.Languages.Erlang.ActorSystem

theorem replace_index_selected {system : ActorSystem} {index : Nat} {selected : LocalProcess}
    (found : system.processes[index]? = some selected) : system.replace index selected = system := by
  obtain ⟨bounded, same⟩ := List.getElem?_eq_some_iff.mp found
  simp only [replace, ← same, List.set_getElem_self bounded]

theorem wait_request_empty (system : ActorSystem) (index : Nat) (selected : LocalProcess)
    (continuation : Continuation) (empty : selected.mailbox.unread = []) :
    system.request? index selected .waitInfinity continuation = .ok none := by
  simp [request?, empty]
  rfl

theorem wait_request_ready (system : ActorSystem) (index : Nat) (selected : LocalProcess)
    (continuation : Continuation) (nonempty : selected.mailbox.unread ≠ []) :
    system.request? index selected .waitInfinity continuation =
      .ok (some (system.replace index (resume selected [boolean false] continuation))) := by
  have unread : selected.mailbox.unread.isEmpty = false := List.isEmpty_eq_false_iff.mpr nonempty
  simp [request?, unread]
  rfl

theorem wait_execute_empty {system : ActorSystem} {index : Nat} {selected : LocalProcess}
    (found : system.processes[index]? = some selected) (continuation : Continuation)
    (requested : selected.machine = .request .waitInfinity continuation) (empty : selected.mailbox.unread = []) :
    system.execute? index = .ok none := by
  simp only [execute?, found, requested]
  exact wait_request_empty system index selected continuation empty

theorem pending_network_not_blocked (system : ActorSystem) (pending : system.network ≠ []) :
    system.blocked = false := by
  have nonempty : system.network.isEmpty = false := List.isEmpty_eq_false_iff.mpr pending
  simp [blocked, nonempty]

end Mettapedia.Languages.Erlang.ActorSystem
