import Mathlib.Tactic

/-!
# A final receipt at the native process boundary

The optional controller runs outside the interpreter. A declared query count
may precede the final receipt, but cannot replace it. The final receipt must
agree with both that count and the operating-system exit status. A raw host
exit without finalization is therefore an incomplete framed run, even when
its operating-system status is zero. Correlation is not authentication.

This finite protocol models complete packets. Native pipe bytes, interrupted
system calls, child ownership and report publication require native checks.
-/
set_option autoImplicit false
namespace Mettapedia.Machines.RunContracts.ProcessReceipt

inductive Packet where
  | declared (queries : Nat)
  | final (status queries : Nat)
  deriving DecidableEq, Repr

def decode : List Packet → Option (Nat × Nat)
  | [.final status queries] => if status < 256 then some (status, queries) else none
  | [.declared count, .final status queries] =>
      if count = queries ∧ status < 256 then some (status, queries) else none
  | _ => none

def exitCode (packets : List Packet) (osStatus : Nat) : Nat :=
  match decode packets with
  | none => 1
  | some (status, _) => if status = osStatus then status else 1

theorem complete_receipt (status queries : Nat) (bounded : status < 256) :
    exitCode [.final status queries] status = status := by
  simp [exitCode, decode, bounded]

theorem declared_complete_receipt (status queries : Nat) (bounded : status < 256) :
    exitCode [.declared queries, .final status queries] status = status := by
  simp [exitCode, decode, bounded]

theorem missing_receipt (queries osStatus : Nat) :
    exitCode [.declared queries] osStatus = 1 := rfl

theorem duplicate_receipt (status queries osStatus : Nat) :
    exitCode [.final status queries, .final status queries] osStatus = 1 := rfl

theorem changed_catalogue (count queries status osStatus : Nat)
    (different : count ≠ queries) :
    exitCode [.declared count, .final status queries] osStatus = 1 := by
  simp [exitCode, decode, different]

theorem changed_os_status (status queries osStatus : Nat)
    (bounded : status < 256) (different : status ≠ osStatus) :
    exitCode [.final status queries] osStatus = 1 := by
  simp [exitCode, decode, bounded, different]

theorem invalid_status (status queries osStatus : Nat) (invalid : 256 ≤ status) :
    exitCode [.final status queries] osStatus = 1 := by
  simp [exitCode, decode, Nat.not_lt.mpr invalid]

theorem successful_requires_receipt (packets : List Packet) (osStatus : Nat) :
    exitCode packets osStatus = 0 ↔
      osStatus = 0 ∧ ∃ queries, decode packets = some (0, queries) := by
  cases h : decode packets with
  | none => simp [exitCode, h]
  | some pair =>
      rcases pair with ⟨status, queries⟩
      by_cases same : status = osStatus
      · subst osStatus
        simp [exitCode, h]
      · constructor
        · intro impossible
          simp [exitCode, h, same] at impossible
        · rintro ⟨osZero, count, packet⟩
          have statusZero : status = 0 :=
            congrArg Prod.fst (Option.some.inj packet)
          exact False.elim (same (statusZero.trans osZero.symm))

example : exitCode [.declared 2] 0 = 1 := rfl
example : exitCode [.declared 2, .final 0 2] 0 = 0 := by decide
example : exitCode [.declared 2, .final 0 1] 0 = 1 := by decide
end Mettapedia.Machines.RunContracts.ProcessReceipt
