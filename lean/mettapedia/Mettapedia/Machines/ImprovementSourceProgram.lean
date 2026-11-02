import Mettapedia.Machines.ImprovementInformation
import Mettapedia.Machines.Cursor.Protocol

/-!
# A primitive-program bridge for keyed improvement

The source block reads a slot, conditionally erases the old row, inserts the
candidate, and returns either one key or an empty answer packet. The target
performs one keyed upsert. Both are programs of the existing primitive syntax,
executed by its independent bounded interpreter and cursor correspondence.

The source debit counts primitive calls, not evaluator instructions or physical
CPU work. A completed block and any sequential continuation agree under this
debit, while primitive-by-primitive pause boundaries do not. The handler is
total and isolated during the block; concurrent publication and allocation
failure require additional contracts.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.KeyedImprovement.SourceProgram

open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open Cursor.PrimitiveProgram Information

inductive Op
  | read
  | erase (expected : Nat)
  | put (candidate : Nat)
  | upsert (candidate : Nat)

abbrev Ret : Op → Type
  | .read => Option Nat
  | .erase _ => Bool
  | .put _ => Unit
  | .upsert _ => Bool

variable {Key : Type} [DecidableEq Key]

def step (key : Key) (store : Store Key Nat) : (op : Op) → Store Key Nat × Except Empty (Ret op)
  | .read => (store, .ok (store key))
  | .erase expected =>
      if store key = some expected then (Function.update store key none, .ok true)
      else (store, .ok false)
  | .put candidate => (Function.update store key (some candidate), .ok ())
  | .upsert candidate => let result := improve store key candidate; (result.1, .ok result.2)

/-- Each packet is a list of source answers; `[]` really means no answer. -/
def source (key : Key) (candidate : Nat) : Prog Op Ret (List Key) :=
  .call .read fun old => match old with
    | none => .call (.put candidate) fun _ => .ret [key]
    | some previous => if candidate < previous then
        .call (.erase previous) fun _ => .call (.put candidate) fun _ => .ret [key]
      else .ret []

def native (key : Key) (candidate : Nat) : Prog Op Ret (List Key) :=
  .call (.upsert candidate) fun changed => .ret (if changed then [key] else [])

def answers (key : Key) (changed : Bool) : List Key := if changed then [key] else []

/-- Semantic source debit can differ from the target's physical call count. -/
def sourceCharge (key : Key) (store : Store Key Nat) : Op → Nat
  | .upsert candidate => (sourcePlan candidate (store key)).debit
  | _ => 1

theorem source_completed (store : Store Key Nat) (key : Key) (candidate : Nat) :
    direct (step key) (sourceCharge key) 4 (.ok (source key candidate)) store =
      ((sourcePlan candidate (store key)).debit,
        (.inl (.ok (answers key (improve store key candidate).2)), (improve store key candidate).1)) := by
  cases old : store key with
  | none => simp [direct, source, step, sourceCharge, sourcePlan, SourcePlan.debit, improve, old, answers]
  | some previous =>
    by_cases better : candidate < previous <;>
      simp [direct, source, step, sourceCharge, sourcePlan, SourcePlan.debit, improve,
        old, better, answers]

theorem native_completed (store : Store Key Nat) (key : Key) (candidate : Nat) :
    direct (step key) (sourceCharge key) 2 (.ok (native key candidate)) store =
      ((sourcePlan candidate (store key)).debit,
        (.inl (.ok (answers key (improve store key candidate).2)), (improve store key candidate).1)) := by
  simp [direct, native, step, sourceCharge, answers]

theorem completed_source_native (store : Store Key Nat) (key : Key) (candidate : Nat) :
    direct (step key) (sourceCharge key) 4 (.ok (source key candidate)) store =
      direct (step key) (sourceCharge key) 2 (.ok (native key candidate)) store := by
  rw [source_completed, native_completed]

/-- The arbitrary continuation retains actual answers, faults and residual
control. It can include the outer driver's source-visible round counter. -/
theorem source_continuation {Answer : Type} (store : Store Key Nat) (key : Key) (candidate fuel : Nat)
    (next : List Key → Prog Op Ret Answer) :
    direct (step key) (sourceCharge key) ((sourcePlan candidate (store key)).debit + fuel)
      (.ok ((source key candidate).bind next)) store =
    let rest := direct (step key) (sourceCharge key) fuel
      (.ok (next (answers key (improve store key candidate).2))) (improve store key candidate).1
    ((sourcePlan candidate (store key)).debit + rest.1, rest.2) := by
  cases old : store key with
  | none =>
    simp [source, Prog.bind, sourcePlan, SourcePlan.debit, old, Nat.add_comm 2 fuel,
      direct, step, sourceCharge, improve, answers]
    omega
  | some previous =>
    by_cases better : candidate < previous <;>
      simp [source, Prog.bind, sourcePlan, SourcePlan.debit, old, better,
        Nat.add_comm 3 fuel, Nat.add_comm 1 fuel, direct, step, sourceCharge,
        improve, answers]
    all_goals omega

theorem native_continuation {Answer : Type} (store : Store Key Nat) (key : Key) (candidate fuel : Nat)
    (next : List Key → Prog Op Ret Answer) :
    direct (step key) (sourceCharge key) (fuel + 1) (.ok ((native key candidate).bind next)) store =
    let rest := direct (step key) (sourceCharge key) fuel
      (.ok (next (answers key (improve store key candidate).2))) (improve store key candidate).1
    ((sourcePlan candidate (store key)).debit + rest.1, rest.2) := by
  simp [native, Prog.bind, direct, step, sourceCharge, answers]

theorem composed_source_native {Answer : Type} (store : Store Key Nat) (key : Key)
    (candidate fuel : Nat) (next : List Key → Prog Op Ret Answer) :
    direct (step key) (sourceCharge key) ((sourcePlan candidate (store key)).debit + fuel)
      (.ok ((source key candidate).bind next)) store =
    direct (step key) (sourceCharge key) (fuel + 1) (.ok ((native key candidate).bind next)) store := by
  rw [source_continuation, native_continuation]

/-- A real cursor execution, not just the direct interpreter, completes with
the same answer packet, source debit and final store. -/
theorem native_cursor_completed (store : Store Key Nat) (key : Key) (candidate : Nat) :
    let result := Cursor.advance (provider (step key)) (client Op Ret (List Key) Empty)
      (charge (sourceCharge key) (step key)) 2 ⟨PUnit.unit, .ok (native key candidate), store⟩
    (result.1, readOutcome (step key) result.2) =
      ((sourcePlan candidate (store key)).debit,
        (.inl (.ok (answers key (improve store key candidate).2)), (improve store key candidate).1)) := by
  dsimp only
  rw [advance_is_direct, native_completed]

namespace Controls

def ten : Store Unit Nat := fun _ => some 10

theorem intermediate_absence_distinguishes :
    (direct (step ()) (sourceCharge ()) 2 (.ok (source () 7)) ten).2.2 () = none ∧
    (direct (step ()) (sourceCharge ()) 2 (.ok (native () 7)) ten).2.2 () = some 7 := by
  decide

theorem physical_calls_are_not_source_debit :
    (direct (step ()) (fun _ _ => 1) 4 (.ok (source () 7)) ten).1 = 3 ∧
    (direct (step ()) (fun _ _ => 1) 2 (.ok (native () 7)) ten).1 = 1 := by decide

theorem no_improvement_is_empty_packet :
    answers () (improve ten () 12).2 = [] := by decide

end Controls
end Mettapedia.Machines.KeyedImprovement.SourceProgram
