import Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangMailboxExecution

/-! Actor cursor requests first peek to normalize incoming messages, then
advance or remove on that normalized mailbox. Wake is restricted to a local
waiter; ordinary network arrival uses delivery for every mailbox. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangMailbox.Execution

open Mettapedia.OSLF.MeTTaIL Syntax Match
open Mettapedia.Languages.Erlang

variable {α : Type*}

theorem normalized_next_none_iff (box : Mailbox α) : box.normalize.next? = none ↔ box.peek = none := by
  rcases box with ⟨saved, front, rear⟩
  cases front with
  | cons head tail => simp [Mailbox.normalize, Mailbox.next?, Mailbox.peek, Mailbox.unread]
  | nil =>
      cases reverse : rear.reverse <;>
        simp [Mailbox.normalize, Mailbox.next?, Mailbox.peek, Mailbox.unread, reverse]

theorem normalized_remove_none_iff (box : Mailbox α) : box.normalize.remove? = none ↔ box.peek = none := by
  rcases box with ⟨saved, front, rear⟩
  cases front with
  | cons head tail => simp [Mailbox.normalize, Mailbox.remove?, Mailbox.peek, Mailbox.unread]
  | nil =>
      cases reverse : rear.reverse <;>
        simp [Mailbox.normalize, Mailbox.remove?, Mailbox.peek, Mailbox.unread, reverse]

theorem next_after_peek (base : ContextualStep.BasePremiseEvaluator) (encode : α → Pattern)
    (box result : Mailbox α) (authorized : box.normalize.next? = some result) :
    Settles base (node "ErPeek" [mailbox encode box]) (peekAnswer encode box) ∧
      Settles base (node "ErNext" [mailbox encode box.normalize]) (node "ErAdvanced" [mailbox encode result]) :=
  ⟨peek base encode box, next base encode authorized⟩

theorem remove_after_peek (base : ContextualStep.BasePremiseEvaluator) (encode : α → Pattern)
    (box result : Mailbox α) (authorized : box.normalize.remove? = some result) :
    Settles base (node "ErPeek" [mailbox encode box]) (peekAnswer encode box) ∧
      Settles base (node "ErRemove" [mailbox encode box.normalize]) (node "ErRemoved" [mailbox encode result]) :=
  ⟨peek base encode box, remove base encode authorized⟩

theorem wake_front_no_step (base : ContextualStep.BasePremiseEvaluator) (message saved head tail rear target : Pattern) :
    ¬ ContextualStep.Step base language
      (node "ErWake" [message, node "ErMailbox" [saved, node "ErValuesCons" [head, tail], rear]]) target := by
  simp [step_iff_mem, reducts, schemata, node, matchPattern, matchArgs, mergeBindings]

theorem wake_rear_no_step (base : ContextualStep.BasePremiseEvaluator) (message saved head tail target : Pattern) :
    ¬ ContextualStep.Step base language
      (node "ErWake" [message, node "ErMailbox" [saved, node "ErValuesNil", node "ErValuesCons" [head, tail]]]) target := by
  simp [step_iff_mem, reducts, schemata, node, matchPattern, matchArgs, mergeBindings]

theorem nonempty_wake_no_step (base : ContextualStep.BasePremiseEvaluator) (encode : α → Pattern)
    (message : α) (box : Mailbox α) (nonempty : box.unread ≠ []) (target : Pattern) :
    ¬ ContextualStep.Step base language (node "ErWake" [encode message, mailbox encode box]) target := by
  rcases box with ⟨saved, front, rear⟩
  cases front with
  | cons head tail => exact wake_front_no_step base _ _ _ _ _ target
  | nil =>
      cases rear with
      | nil => exact False.elim (nonempty rfl)
      | cons head tail => exact wake_rear_no_step base _ _ _ _ target

end Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangMailbox.Execution
