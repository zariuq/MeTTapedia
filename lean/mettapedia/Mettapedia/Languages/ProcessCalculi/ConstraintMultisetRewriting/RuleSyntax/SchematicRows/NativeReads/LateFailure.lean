import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.CursorProtocol
import Mettapedia.Machines.Cursor.Fold

/-!
# Failure after a producer pull: retain a loan or abort the private reader

Registration can fail after the occurrence cursor advances. A resumable
boundary retains the item before trying again; a terminal decision may close
its private reader and report failure. The latter preserves the public row
store, not the internal cursor position or the work already requested.
Neither profile reports successful exhaustion. Allocation and callback fault
realization in C remain native obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.LateFailure

open Mettapedia.Machines.Cursor
open Fold.OwnedSequence

variable {Item Accumulator Value : Type}

theorem registration_refusal_keeps_the_item
    (register : Accumulator → Item → Option Accumulator) (item : Item) (rest : List Item)
    (accumulator : Accumulator) (accepted requested allowance : Nat)
    (refused : register accumulator item = none) :
    undelivered (sequence register (allowance + 1)
      ⟨item :: rest, none, accumulator, accepted, requested⟩).2 = item :: rest :=
  rejected_fresh_return_preserves_residual register rest item accumulator accepted requested allowance refused

theorem resumption_does_not_pull_twice (register : Accumulator → Item → Accumulator)
    (item : Item) (rest : List Item) (accumulator : Accumulator) (accepted requested : Nat) :
    sequence (fun acc value => some (register acc value)) 1
        ⟨rest, some item, accumulator, accepted, requested⟩ =
      (.paused, ⟨rest, none, register accumulator item, accepted + 1, requested⟩) :=
  pending_resume_does_not_pull_again register rest item accumulator accepted requested

def abortAfterPull (machine : CursorProtocol.Native Value) (reader : Nat) : CursorProtocol.Native Value :=
  let pulled := StampedSnapshots.apply machine.val (.read reader)
  let closed := StampedSnapshots.apply pulled.1 (.close reader)
  ⟨closed.1, StampedSnapshots.valid_apply pulled.1
    (StampedSnapshots.valid_apply machine.val machine.property (.read reader)) (.close reader)⟩

theorem abort_preserves_public_rows (machine : CursorProtocol.Native Value) (reader : Nat) :
    (abortAfterPull machine reader).val.store = machine.val.store := by
  have pulled := StampedSnapshots.apply_store machine.val (.read reader)
  have closed := StampedSnapshots.apply_store (StampedSnapshots.apply machine.val (.read reader)).1 (.close reader)
  exact closed.trans pulled

theorem abort_closes_private_reader (machine : CursorProtocol.Native Value) (reader : Nat) :
    (abortAfterPull machine reader).val.readers reader = none := by
  change (StampedSnapshots.setReader (StampedSnapshots.apply machine.val (.read reader)).1 reader none).readers reader = none
  simp only [StampedSnapshots.setReader, Function.update_self]

theorem abort_preserves_other_readers (machine : CursorProtocol.Native Value) (reader other : Nat)
    (different : other ≠ reader) :
    (abortAfterPull machine reader).val.readers other = machine.val.readers other := by
  cases found : machine.val.readers reader <;>
    simp [abortAfterPull, StampedSnapshots.apply, StampedSnapshots.setReader, found, different]

theorem dropped_pending_loses_a_return :
    (sequence (fun (out : List Nat) (value : Nat) => some (out ++ [value])) 3
      ⟨[8], none, [], 0, 1⟩).2.accumulator = [8] ∧
      (sequence (fun (out : List Nat) (value : Nat) => some (out ++ [value])) 3
        ⟨[8], some 7, [], 0, 1⟩).2.accumulator = [7, 8] := by decide

theorem late_refusal_is_not_an_unchanged_cursor :
    sequence (fun (_ : List Nat) (_ : Nat) => none) 1 ⟨[7, 8], none, [], 0, 0⟩ =
      (.paused, ⟨[8], some 7, [], 0, 1⟩) := by decide

#print axioms registration_refusal_keeps_the_item
#print axioms abort_preserves_public_rows
#print axioms abort_closes_private_reader
#print axioms dropped_pending_loses_a_return

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.LateFailure
