import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Preparation.DispatchCost
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Preparation.BindingSimulation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Preparation.Meter
import Mettapedia.Machines.Specialization.BudgetedDriving

/-!
# The charged boundary between a prepared prefix and ordinary execution

The source's agenda charges and the selected services use the same
attempt account on both sides of the handback. A successful region uses
only its discharged source debit. The first refused offer spends a
separate allowance before the ordinary machine takes control.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Preparation.HybridCost

open Mettapedia.OSLF.Binding
open Mettapedia.Machines
open Mettapedia.Machines.Specialization
open Mettapedia.Machines.MachineCore
open Evaluation (Evaluator)
open Machine (State Scheduler)
open Meter (Ledger core)

variable {S : Signature} {κ : Keys S} {Γ : Ctx S} {star : S.Srt}
  {Storage : Type} {D : Discipline S Γ star}

private theorem attempts_succ {T : Type} (ordinary : MachineCore T) (quote : ordinary.State → Nat)
    (fuel : Nat) (state : ordinary.State) :
    Attempts.cost ordinary quote (fuel + 1) state =
      quote state + match ordinary.step state with
      | none => 0
      | some next => Attempts.cost ordinary quote fuel next := by
  unfold Attempts.cost
  rw [MachineCore.sliceCost_succ]
  have observed : (Attempts.observer ordinary).step (false, state) =
      some (match ordinary.step state with
        | none => (true, state)
        | some next => (false, next)) := rfl
  rw [observed]
  cases attempted : ordinary.step state with
  | none =>
    change quote state + MachineCore.sliceCost (Attempts.observer ordinary)
      (fun packet => quote packet.2) fuel (true, state) = _
    rw [Attempts.cost_stopped]
  | some next =>
    change quote state + MachineCore.sliceCost (Attempts.observer ordinary)
      (fun packet => quote packet.2) fuel (false, next) = _
    rfl

variable (machine : Evaluator κ D Storage) (strategy : Strategy κ Γ star D.Ty)
  (schedule : Scheduler machine strategy) (prices : DispatchCost.Prices κ Γ star D.Ty Storage)
  (unavailable : State κ Γ star D.Ty Storage → Nat)

/-- The common source price includes the terminal quota whenever a
stop is observed, regardless of which tier reached that configuration. -/
def quote (ledger : Ledger κ Γ star D.Ty Storage) : Nat :=
  DispatchCost.debit machine strategy schedule unavailable ledger.current

theorem dispatch_debit_eq_attempts (fuel : Nat) (ledger : Ledger κ Γ star D.Ty Storage) :
    DispatchCost.totalDebit machine strategy schedule unavailable
        (DispatchCost.run machine strategy schedule prices fuel ledger.current) =
      Attempts.cost (core machine strategy schedule) (quote machine strategy schedule unavailable) fuel ledger := by
  induction fuel generalizing ledger with
  | zero => simp [DispatchCost.run, DispatchCost.totalDebit, units, Attempts.cost, MachineCore.sliceCost_zero]
  | succ fuel ih =>
    have step := DispatchCost.step_exact machine strategy schedule prices ledger.current
    simp only [attempts_succ, DispatchCost.run, step, Meter.core]
    cases moved : Machine.advance machine strategy schedule ledger.current with
    | none =>
      simp [DispatchCost.totalDebit, quote, units]
    | some answer =>
      have later := ih ⟨answer.next, answer.work :: ledger.reverseWork⟩
      have first : quote machine strategy schedule unavailable ledger = answer.work.units := by
        simp only [quote, DispatchCost.debit, moved]
      rw [first]
      change DispatchCost.totalDebit machine strategy schedule unavailable
        ⟨(DispatchCost.run machine strategy schedule prices fuel answer.next).state,
          answer.work :: (DispatchCost.run machine strategy schedule prices fuel answer.next).moves,
          _, (DispatchCost.run machine strategy schedule prices fuel answer.next).stopped⟩ = _
      change DispatchCost.totalDebit machine strategy schedule unavailable
        (DispatchCost.run machine strategy schedule prices fuel answer.next) = _ at later
      change _ = answer.work.units + Attempts.cost (core machine strategy schedule)
        (quote machine strategy schedule unavailable) fuel ⟨answer.next, answer.work :: ledger.reverseWork⟩
      rw [← later]
      simp only [DispatchCost.totalDebit, units, List.map_cons, List.sum_cons, Nat.add_assoc]

/-- A proved region endpoint supplies a segment of the shared source
account. The receipts here are the source trace associated to that
proof, irrespective of whether an execution retains receipts. -/
theorem certified_segment {moves : Nat} {ledger : Ledger κ Γ star D.Ty Storage}
    {target : State κ Γ star D.Ty Storage}
    (reached : BindingSimulation.Reaches schedule moves ledger.current target) (positive : 0 < moves) :
    ∃ segment : Driving.Advance (core machine strategy schedule) ledger,
      segment.target.current = target ∧ segment.debit = moves := by
  let trace := (Machine.run machine strategy schedule moves ledger.current).2
  let after : Ledger κ Γ star D.Ty Storage := ⟨target, trace.reverse ++ ledger.reverseWork⟩
  refine ⟨⟨after, moves, positive, ?_⟩, rfl, rfl⟩
  rw [Meter.runSlice_agrees]
  exact Prod.ext (congrArg (fun state => Ledger.mk state (trace.reverse ++ ledger.reverseWork)) reached.state)
    reached.debit

theorem hybrid_exact {multiplier refusalCap : Nat}
    (offer : (allowance : Nat) → (ledger : Ledger κ Γ star D.Ty Storage) →
      BudgetedDriving.Trial (core machine strategy schedule) (quote machine strategy schedule unavailable)
        multiplier refusalCap allowance ledger)
    (rounds credit : Nat) (ledger : Ledger κ Γ star D.Ty Storage) :
    let result := BudgetedDriving.run (core machine strategy schedule)
      (quote machine strategy schedule unavailable) multiplier refusalCap offer rounds credit ledger
    let later := DispatchCost.run machine strategy schedule prices
      (credit - result.executed.used) result.executed.target.current
    let ordinary := Machine.run machine strategy schedule credit ledger.current
    (later.state, result.executed.target.reverseWork.reverse ++ later.moves) =
      (ordinary.1, ledger.reverseWork.reverse ++ ordinary.2) := by
  let advanced := (BudgetedDriving.run (core machine strategy schedule)
    (quote machine strategy schedule unavailable) multiplier refusalCap offer rounds credit ledger).executed
  let remainder := credit - advanced.used
  have same := congrArg Prod.fst advanced.continue_exact
  change ((core machine strategy schedule).runSlice remainder advanced.target).1 =
    ((core machine strategy schedule).runSlice credit ledger).1 at same
  have before := congrArg Prod.fst (Meter.runSlice_agrees machine strategy schedule credit ledger)
  have after := congrArg Prod.fst (Meter.runSlice_agrees machine strategy schedule remainder advanced.target)
  have equal := congrArg (fun receipt : Ledger κ Γ star D.Ty Storage =>
    (receipt.current, receipt.reverseWork.reverse)) (after.symm.trans (same.trans before))
  simp only [List.reverse_append, List.reverse_reverse] at equal
  have observed := DispatchCost.run_exact machine strategy schedule prices remainder advanced.target.current
  let measured := DispatchCost.run machine strategy schedule prices remainder advanced.target.current
  change (measured.state, measured.moves) = _ at observed
  have sameState : measured.state = (Machine.run machine strategy schedule remainder advanced.target.current).1 :=
    congrArg Prod.fst observed
  have sameMoves : measured.moves = (Machine.run machine strategy schedule remainder advanced.target.current).2 :=
    congrArg Prod.snd observed
  change (measured.state, advanced.target.reverseWork.reverse ++ measured.moves) = _
  rw [sameState, sameMoves]
  exact equal

/-- The compiled provider has the same local rate as the ordinary
realization. This establishes the global bound across the switch,
including the one failed offer and the ordinary terminal probe. -/
theorem hybrid_bound {rate refusalCap : Nat}
    (adequate : DispatchCost.Adequate machine strategy schedule prices unavailable rate)
    (offer : (allowance : Nat) → (ledger : Ledger κ Γ star D.Ty Storage) →
      BudgetedDriving.Trial (core machine strategy schedule) (quote machine strategy schedule unavailable)
        (3 * rate + 3) refusalCap allowance ledger)
    (rounds credit : Nat) (ledger : Ledger κ Γ star D.Ty Storage) :
    let result := BudgetedDriving.run (core machine strategy schedule)
      (quote machine strategy schedule unavailable) (3 * rate + 3) refusalCap offer rounds credit ledger
    let later := DispatchCost.run machine strategy schedule prices
      (credit - result.executed.used) result.executed.target.current
    result.elapsed + later.elapsed ≤
      (3 * rate + 3) * Attempts.cost (core machine strategy schedule)
        (quote machine strategy schedule unavailable) credit ledger + refusalCap := by
  let result := BudgetedDriving.run (core machine strategy schedule)
    (quote machine strategy schedule unavailable) (3 * rate + 3) refusalCap offer rounds credit ledger
  let left := credit - result.executed.used
  let later := DispatchCost.run machine strategy schedule prices left result.executed.target.current
  have ordinary := DispatchCost.run_bound machine strategy schedule prices adequate 0 left result.executed.target.current
  change later.elapsed + 0 ≤ (3 * rate + 3) *
    DispatchCost.totalDebit machine strategy schedule unavailable later + 0 at ordinary
  have paid := dispatch_debit_eq_attempts machine strategy schedule prices unavailable left result.executed.target
  change DispatchCost.totalDebit machine strategy schedule unavailable later = _ at paid
  rw [paid] at ordinary
  refine (Nat.add_le_add_left (by simpa only [Nat.add_zero] using ordinary) result.elapsed).trans ?_
  exact BudgetedDriving.continuation_bound (core machine strategy schedule)
    (quote machine strategy schedule unavailable) (3 * rate + 3) refusalCap offer rounds credit ledger

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Preparation.HybridCost
