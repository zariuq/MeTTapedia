import Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangMailboxValueAdmission
import Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangMailboxRunnerAgreement

/-! Source-valued mailbox commands discharge their runner input conditions
uniformly. Completed results reflect to the independent queue operation;
finite tick budgets are never assumed sufficient for completion. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangMailbox.Execution.SourceValues

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.Erlang
open ErlangCompilation (value)

theorem peek_done (box : Mailbox Value) (ticks quantum : Nat)
    (done : (Runner.run (node "ErPeek" [mailbox value box]) ticks quantum).phase = .done) :
    (Runner.run (node "ErPeek" [mailbox value box]) ticks quantum).state = peekAnswer value box :=
  Runner.done_value (peek Runner.base value box) (Admission.unary_canonical _ box)
    (Admission.peek_sorted box) ticks quantum done

theorem next_done {box result : Mailbox Value} (authorized : box.next? = some result) (ticks quantum : Nat)
    (done : (Runner.run (node "ErNext" [mailbox value box]) ticks quantum).phase = .done) :
    (Runner.run (node "ErNext" [mailbox value box]) ticks quantum).state = node "ErAdvanced" [mailbox value result] :=
  Runner.done_value (next Runner.base value authorized) (Admission.unary_canonical _ box)
    (Admission.next_sorted box) ticks quantum done

theorem remove_done {box result : Mailbox Value} (authorized : box.remove? = some result) (ticks quantum : Nat)
    (done : (Runner.run (node "ErRemove" [mailbox value box]) ticks quantum).phase = .done) :
    (Runner.run (node "ErRemove" [mailbox value box]) ticks quantum).state = node "ErRemoved" [mailbox value result] :=
  Runner.done_value (remove Runner.base value authorized) (Admission.unary_canonical _ box)
    (Admission.remove_sorted box) ticks quantum done

theorem deliver_done (message : Value) (box : Mailbox Value) (ticks quantum : Nat)
    (done : (Runner.run (node "ErDeliver" [value message, mailbox value box]) ticks quantum).phase = .done) :
    (Runner.run (node "ErDeliver" [value message, mailbox value box]) ticks quantum).state =
      node "ErDelivered" [mailbox value (box.deliver message)] :=
  Runner.done_value (deliver Runner.base value message box) (Admission.binary_canonical _ message box)
    (Admission.deliver_sorted message box) ticks quantum done

theorem wait_done (box : Mailbox Value) (ticks quantum : Nat)
    (done : (Runner.run (node "ErWait" [mailbox value box]) ticks quantum).phase = .done) :
    (Runner.run (node "ErWait" [mailbox value box]) ticks quantum).state = waitAnswer value box :=
  Runner.done_value (wait Runner.base value box) (Admission.unary_canonical _ box)
    (Admission.wait_sorted box) ticks quantum done

theorem waiting_done (box : Mailbox Value) (empty : box.unread = []) (ticks quantum : Nat)
    (done : (Runner.run (node "ErWait" [mailbox value box]) ticks quantum).phase = .done) :
    (Runner.run (node "ErWait" [mailbox value box]) ticks quantum).state = node "ErWaiting" [mailbox value box] := by
  simpa only [waitAnswer, empty, List.isEmpty_nil, ↓reduceIte] using wait_done box ticks quantum done

theorem wake_done (message : Value) (saved : List Value) (ticks quantum : Nat)
    (done : (Runner.run (node "ErWake" [value message, mailbox value ⟨saved, [], []⟩]) ticks quantum).phase = .done) :
    (Runner.run (node "ErWake" [value message, mailbox value ⟨saved, [], []⟩]) ticks quantum).state =
      node "ErReady" [mailbox value (Mailbox.deliver message ⟨saved, [], []⟩)] :=
  Runner.done_value (wake Runner.base value message saved) (Admission.binary_canonical _ message ⟨saved, [], []⟩)
    (Admission.wake_sorted message ⟨saved, [], []⟩) ticks quantum done

end Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangMailbox.Execution.SourceValues
