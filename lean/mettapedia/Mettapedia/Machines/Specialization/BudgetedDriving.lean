import Mettapedia.Machines.Specialization.Driving

/-!
# Charged driving with a single handback

An admitted segment is priced against the source slice it discharges.
The provider can also spend a bounded allowance discovering a refusal,
including a refusal of source credit. The driver stops trying at the
first refusal. The ordinary suffix is metered by the existing attempt
observer, including its possible final unsuccessful probe.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Specialization.BudgetedDriving

open Mettapedia.Machines (MachineCore)
open MachineCore (sliceCost)
open Mettapedia.Machines.Specialization.Driving

variable {Term : Type} (core : MachineCore Term) (price : core.State → Nat) (rate refusalCap : Nat)

/-- One local quotation. Success carries the exact source endpoint and
may spend only its source debit at the common rate. Refusal spends only
the separate attempt allowance. -/
structure Trial (allowance : Nat) (state : core.State) where
  segment : Option (Advance core state)
  elapsed : Nat
  pays : match segment with
    | none => elapsed ≤ refusalCap
    | some advance => advance.debit ≤ allowance ∧
        elapsed ≤ rate * sliceCost core price advance.debit state

structure Result (allowance : Nat) (state : core.State) where
  executed : Prefix core state allowance
  elapsed : Nat
  bound : elapsed ≤ rate * sliceCost core price executed.used state + refusalCap

variable (offer : (allowance : Nat) → (state : core.State) → Trial core price rate refusalCap allowance state)

def run : Nat → (allowance : Nat) → (state : core.State) → Result core price rate refusalCap allowance state
  | 0, allowance, state => ⟨Prefix.stop core state allowance .limit, 0, Nat.zero_le _⟩
  | rounds + 1, allowance, state =>
    match offer allowance state with
    | ⟨none, elapsed, pays⟩ =>
      ⟨Prefix.stop core state allowance .refusal, elapsed, pays.trans (Nat.le_add_left _ _)⟩
    | ⟨some segment, elapsed, paid⟩ =>
      let later := run rounds (allowance - segment.debit) segment.target
      let combined := later.executed.prepend segment paid.1
      ⟨combined, elapsed + later.elapsed, by
        change elapsed + later.elapsed ≤
          rate * sliceCost core price (segment.debit + later.executed.used) state + refusalCap
        rw [MachineCore.sliceCost_add, segment.follows, Nat.mul_add, Nat.add_assoc]
        exact Nat.add_le_add paid.2 later.bound⟩

theorem continuation_exact (rounds allowance : Nat) (state : core.State) :
    let advanced := (run core price rate refusalCap offer rounds allowance state).executed
    let ordinary := core.runSlice (allowance - advanced.used) advanced.target
    (ordinary.1, advanced.used + ordinary.2) = core.runSlice allowance state :=
  (run core price rate refusalCap offer rounds allowance state).executed.continue_exact

/-- The compiled prefix and the ordinary suffix together cost at most
one common multiplier times the full source attempt ledger plus one
refusal allowance. The source prefix cannot contain a terminal probe. -/
theorem continuation_bound (rounds allowance : Nat) (state : core.State) :
    let result := run core price rate refusalCap offer rounds allowance state
    result.elapsed +
        rate * MachineCore.Attempts.cost core price (allowance - result.executed.used) result.executed.target ≤
      rate * MachineCore.Attempts.cost core price allowance state + refusalCap := by
  let result := run core price rate refusalCap offer rounds allowance state
  let front := result.executed
  let rear := allowance - front.used
  have split := MachineCore.Attempts.cost_split core price front.used rear state
  rw [front.exactSteps, show front.used + rear = allowance by have := front.bounded; omega] at split
  have equal : sliceCost core price front.used state + MachineCore.Attempts.cost core price rear front.target =
      MachineCore.Attempts.cost core price allowance state := by
    have lead := MachineCore.Attempts.cost_exact core price front.used state
    rw [front.exactSteps] at lead
    simpa [lead] using split
  change result.elapsed + rate * MachineCore.Attempts.cost core price rear front.target ≤ _
  rw [← equal, Nat.mul_add]
  have spent := result.bound
  change result.elapsed ≤ rate * sliceCost core price front.used state + refusalCap at spent
  omega

namespace Controls

private abbrev counter : MachineCore Nat := ⟨Nat, id, fun value => some (value + 1)⟩

private def offerCounter (allowance : Nat) (state : Nat) : Trial counter (fun _ => 1) 2 2 allowance state :=
  if within : 2 ≤ allowance ∧ state < 2 then
    ⟨some ⟨state + 2, 2, by decide, rfl⟩, 4, ⟨within.1, by rfl⟩⟩
  else ⟨none, 2, Nat.le_refl _⟩

theorem charged_work_includes_the_first_refusal_only :
    let result := run counter (fun _ => 1) 2 2 offerCounter 8 10 0
    result.executed.target = 2 ∧ result.executed.used = 2 ∧ result.elapsed = 6 := ⟨rfl, rfl, rfl⟩

theorem narrow_credit_refuses_before_any_progress :
    let result := run counter (fun _ => 1) 2 2 offerCounter 8 1 0
    result.executed.target = 0 ∧ result.executed.used = 0 ∧ result.elapsed = 2 := ⟨rfl, rfl, rfl⟩

end Controls

end Mettapedia.Machines.Specialization.BudgetedDriving
