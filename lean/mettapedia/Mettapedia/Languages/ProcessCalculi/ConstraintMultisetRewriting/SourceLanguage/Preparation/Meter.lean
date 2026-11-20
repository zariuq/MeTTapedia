import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Preparation.Continuations
import Mettapedia.Machines.Specialization.Driving

/-!
# Metered execution and exact handback

Primitive steps retain the ordered agenda and record their source
charge. Guarded driving uses certificates for segments of this
machine. On refusal the ordinary suffix starts in the reached
world with all earlier charges still present.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Preparation.Meter

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Machines (MachineCore)
open Mettapedia.Machines.Specialization.Driving (Advance run)
open Evaluation (Evaluator)
open Machine (State Scheduler)

variable {S : Signature} {κ : Keys S} {Γ : Ctx S} {star : S.Srt}
  {Storage : Type} {D : Discipline S Γ star}
  (machine : Evaluator κ D Storage) (strategy : Strategy κ Γ star D.Ty)
  (schedule : Scheduler machine strategy)

structure Ledger (κ : Keys S) (Γ : Ctx S) (star : S.Srt) (Ty Storage : Type) where
  current : State κ Γ star Ty Storage
  reverseWork : List (Charge (Data κ Γ star))

def core : MachineCore (State κ Γ star D.Ty Storage) where
  State := Ledger κ Γ star D.Ty Storage
  load := fun state => ⟨state, []⟩
  step := fun ledger =>
    (Machine.advance machine strategy schedule ledger.current).map fun transition =>
      ⟨transition.next, transition.work :: ledger.reverseWork⟩

theorem runSlice_agrees (fuel : Nat) (ledger : Ledger κ Γ star D.Ty Storage) :
    (core machine strategy schedule).runSlice fuel ledger =
      let result := Machine.run machine strategy schedule fuel ledger.current
      (⟨result.1, result.2.reverse ++ ledger.reverseWork⟩, result.2.length) := by
  induction fuel generalizing ledger with
  | zero => rfl
  | succ fuel ih =>
    cases did : Machine.advance machine strategy schedule ledger.current with
    | none =>
      simp [MachineCore.runSlice, core, Machine.run, did]
    | some transition =>
      have outer : (core machine strategy schedule).step ledger =
          some ⟨transition.next, transition.work :: ledger.reverseWork⟩ := by
        simp [core, did]
      simp only [MachineCore.runSlice, Machine.run, did, outer]
      rw [ih ⟨transition.next, transition.work :: ledger.reverseWork⟩]
      simp [List.append_assoc]

theorem administrative_steps_le_source_work (fuel : Nat) (ledger : Ledger κ Γ star D.Ty Storage) :
    ((core machine strategy schedule).runSlice fuel ledger).2 ≤
      units (Machine.run machine strategy schedule fuel ledger.current).2 := by
  rw [runSlice_agrees]
  exact reductions_bounded_by_work _

/-- Starting at a retained boundary adds the new receipts in order.
This equation uses the supplied evaluator and strategy at the boundary,
so earlier receipts remain available even if the next evaluator differs. -/
theorem receipts_after_resume (fuel : Nat) (ledger : Ledger κ Γ star D.Ty Storage) :
    ((core machine strategy schedule).runSlice fuel ledger).1.reverseWork.reverse =
      ledger.reverseWork.reverse ++ (Machine.run machine strategy schedule fuel ledger.current).2 := by
  rw [runSlice_agrees]
  simp

/-- The fast provider supplies checked segments. A failed guard, an
unrepresentable result, or insufficient credit leaves the remaining
observation to the ordinary machine from the exact reached state. -/
theorem drive_then_ordinary
    (prepare : (ledger : Ledger κ Γ star D.Ty Storage) →
      Option (Advance (core machine strategy schedule) ledger))
    (rounds fuel : Nat) (initial : State κ Γ star D.Ty Storage) :
    let start := Ledger.mk initial []
    let driven := run (core machine strategy schedule) prepare rounds fuel start
    let ordinary := (core machine strategy schedule).runSlice (fuel - driven.used) driven.target
    (ordinary.1.current, ordinary.1.reverseWork.reverse) = Machine.run machine strategy schedule fuel initial := by
  let start : Ledger κ Γ star D.Ty Storage := ⟨initial, []⟩
  let driven := run (core machine strategy schedule) prepare rounds fuel start
  have sameEnd := congrArg Prod.fst driven.continue_exact
  change ((core machine strategy schedule).runSlice (fuel - driven.used) driven.target).1 =
    ((core machine strategy schedule).runSlice fuel start).1 at sameEnd
  change (((core machine strategy schedule).runSlice (fuel - driven.used) driven.target).1.current,
    ((core machine strategy schedule).runSlice (fuel - driven.used) driven.target).1.reverseWork.reverse) = _
  rw [sameEnd, runSlice_agrees]
  cases Machine.run machine strategy schedule fuel initial
  simp [start]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Preparation.Meter
