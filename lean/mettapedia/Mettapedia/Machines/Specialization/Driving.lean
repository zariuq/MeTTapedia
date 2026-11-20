import Mettapedia.Machines.ResumableRegion

/-!
# Certified driving and handback at the reached state

A transformation can take several source steps as one segment. Its
certificate identifies the endpoint and the source debit. Guards and
resource limits preserve the reached state and its accumulated debit.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Specialization.Driving

variable {Term : Type}

structure Advance (core : MachineCore Term) (start : core.State) where
  target : core.State
  debit : Nat
  positive : 0 < debit
  follows : core.runSlice debit start = (target, debit)

inductive Reason where
  | limit | refusal | credit
  deriving DecidableEq

structure Prefix (core : MachineCore Term) (start : core.State) (allowance : Nat) where
  target : core.State
  used : Nat
  bounded : used ≤ allowance
  exactSteps : core.runSlice used start = (target, used)
  reason : Reason

def Prefix.stop (core : MachineCore Term) (start : core.State) (allowance : Nat) (reason : Reason) :
    Prefix core start allowance :=
  ⟨start, 0, Nat.zero_le _, rfl, reason⟩

def Prefix.prepend {core : MachineCore Term} {start : core.State}
    (advance : Advance core start) {allowance : Nat} (fits : advance.debit ≤ allowance)
    (later : Prefix core advance.target (allowance - advance.debit)) : Prefix core start allowance where
  target := later.target
  used := advance.debit + later.used
  bounded := by have := later.bounded; omega
  exactSteps := by
    rw [core.runSlice_add, advance.follows]
    dsimp only
    rw [later.exactSteps]
  reason := later.reason

def run (core : MachineCore Term) (prepare : (start : core.State) → Option (Advance core start)) :
    Nat → (allowance : Nat) → (start : core.State) → Prefix core start allowance
  | 0, allowance, start => .stop core start allowance .limit
  | rounds + 1, allowance, start =>
    match prepare start with
    | none => .stop core start allowance .refusal
    | some segment =>
      if fits : segment.debit ≤ allowance then
        (run core prepare rounds (allowance - segment.debit) segment.target).prepend segment fits
      else .stop core start allowance .credit

theorem Prefix.continue_exact {core : MachineCore Term} {start : core.State} {allowance : Nat}
    (driven : Prefix core start allowance) :
    let ordinary := core.runSlice (allowance - driven.used) driven.target
    (ordinary.1, driven.used + ordinary.2) = core.runSlice allowance start := by
  have split := core.runSlice_add driven.used (allowance - driven.used) start
  rw [show driven.used + (allowance - driven.used) = allowance by have := driven.bounded; omega,
    driven.exactSteps] at split
  exact split.symm

theorem refusal_keeps_the_next_call (core : MachineCore Term)
    (prepare : (start : core.State) → Option (Advance core start))
    (start : core.State) (rounds allowance : Nat) (refused : prepare start = none) :
    (run core prepare (rounds + 1) allowance start).target = start ∧
    (run core prepare (rounds + 1) allowance start).reason = .refusal := by
  simp [run, refused, Prefix.stop]

theorem insufficient_credit_keeps_the_next_call (core : MachineCore Term)
    (prepare : (start : core.State) → Option (Advance core start))
    (start : core.State) (rounds allowance : Nat) (segment : Advance core start)
    (ready : prepare start = some segment) (short : allowance < segment.debit) :
    (run core prepare (rounds + 1) allowance start).target = start ∧
    (run core prepare (rounds + 1) allowance start).reason = .credit := by
  simp [run, ready, Prefix.stop, show ¬ segment.debit ≤ allowance by omega]

namespace Controls

private abbrev successor : MachineCore Nat := ⟨Nat, id, fun value => some (value + 1)⟩

private def segment (start : successor.State) : Advance successor start :=
  ⟨start + 2, 2, by decide, rfl⟩

private def prepare (start : successor.State) : Option (Advance successor start) :=
  if start < 2 then some (segment start) else none

theorem refusal_preserves_the_steps_already_taken :
    let driven := run successor prepare 10 5 0
    driven.target = 2 ∧ driven.used = 2 ∧ driven.reason = .refusal ∧
      successor.runSlice (5 - driven.used) driven.target = (5, 3) := by decide +kernel

theorem exhausted_credit_leaves_the_reached_configuration :
    let driven := run successor (fun start => some (segment start)) 10 3 0
    driven.target = 2 ∧ driven.used = 2 ∧ driven.reason = .credit := by decide +kernel

end Controls

end Mettapedia.Machines.Specialization.Driving
