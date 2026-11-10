import Mettapedia.Languages.HOLLight.ExportCodec
import Mettapedia.Languages.HOLLight.ExportReplayComposition

/-!
# Incrementally retained source-history equations

Every received row already checks its registered command, addresses and
claimed conclusions. The retained receipt equation composes these checks into
the exact replay premise used by source-model construction. Carrying that
proof adds no new acceptance path and requires no second traversal of the
completed command history.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.ExportReceiptHistory

open Mettapedia.Languages.OpenTheory ProofExecution DefinitionAdapters

variable (initial : TheoryContext) (policy : AxiomPolicy) [DecidablePred policy]

def History (state : ExportReplay.State) : Prop :=
  ExportReplay.replayFrom policy (ExportReplay.empty initial) state.receipts.toList = some state

theorem empty_history : History initial policy (ExportReplay.empty initial) := rfl

theorem apply_history {before after : ExportReplay.State} {event : ExportReplay.Event}
    (history : History initial policy before) (accepted : ExportReplay.apply policy before event = some after) :
    History initial policy after := by
  unfold History at history ⊢
  rw [(ExportReplay.apply_checked policy accepted).2.2.2.1]
  simp only [Array.toList_push]
  rw [ExportReplay.replayFrom_append, history]
  simp only [ExportReplay.replayFrom, accepted, bind, Option.bind]

theorem receive_history {before after : ExportCodec.State} {json : Lean.Json}
    (history : History initial policy before.received)
    (accepted : ExportCodec.receive? policy before json = some after) :
    History initial policy after.received := by
  obtain ⟨event, received⟩ := ExportCodec.receive?_checked policy accepted
  exact apply_history initial policy history received

theorem registered_history (state : ExportReplay.State) (history : History initial policy state) :
    Registered.replayFrom policy (Registered.empty initial)
      (state.receipts.toList.map ExportReplay.Event.command) = some state.registered :=
  ExportReplay.replayFrom_registered policy (ExportReplay.empty initial) _ state history

structure Checked where
  state : ExportCodec.State
  history : History initial policy state.received

namespace Checked

def start (basis : ExportCodec.State) (empty : basis.received = ExportReplay.empty initial) :
    Checked initial policy :=
  ⟨basis, empty.symm ▸ empty_history initial policy⟩

def receive? (before : Checked initial policy) (json : Lean.Json) : Option (Checked initial policy) :=
  match accepted : ExportCodec.receive? policy before.state json with
  | none => none
  | some after => some ⟨after, receive_history initial policy before.history accepted⟩

/-- Proof-carrying receipt accumulation leaves both success and refusal data
identical to the original source receiver. -/
theorem receive_state (before : Checked initial policy) (json : Lean.Json) :
    ((receive? initial policy before json).map (·.state)) = ExportCodec.receive? policy before.state json := by
  unfold receive?
  split <;> rename_i accepted
  all_goals exact accepted.symm

theorem registered (checked : Checked initial policy) :
    Registered.replayFrom policy (Registered.empty initial)
      (checked.state.received.receipts.toList.map ExportReplay.Event.command) =
        some checked.state.received.registered :=
  registered_history initial policy checked.state.received checked.history

end Checked

end Mettapedia.Languages.HOLLight.ExportReceiptHistory
