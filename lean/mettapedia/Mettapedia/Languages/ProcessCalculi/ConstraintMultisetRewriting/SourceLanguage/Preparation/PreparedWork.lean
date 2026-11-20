import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Preparation.BindingExpenses
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Preparation.HybridCost
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Preparation.PreparedBodies

/-!
# A prepared body with a work reservation

The instruction quote and the publication service quote are reserved
before entering a region. The source reduction credit is a separate
quantity. Publication uses the same checked boundary as ordinary
prepared execution. A credited successful attempt supplies a certified
segment of the existing source account.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Preparation.PreparedWork

open Mettapedia.OSLF.Binding
open Mettapedia.Machines
open Mettapedia.Machines.Specialization
open BindingPlans BindingTemplates BindingSimulation BindingExpenses
open Evaluation (Evaluator)
open Machine (Scheduler State)
open PreparedBodies (Publication)

variable {S : Signature} {κ : Keys S} {Γ : Ctx S} {star : S.Srt}
  {Storage Ty : Type} {D : Discipline S Γ star}

variable (templates : Templates κ Γ star) (prices : Prices κ Γ star)

/-- The publication quote covers the final consistency check, readback
and publication. That service is reached only if all templates return. -/
def activate (solver : Solver κ Γ star) (quoted : QuotedPlan prices)
    (around : Surrounding κ Γ star Ty) (world : ExecutionWorld Storage)
    (knowledge : List (Constraint κ Γ star)) (frames : List (Frame κ Γ star Ty))
    (cells : List (Data κ Γ star × Comp κ Γ star Ty)) (entry : List Nat) (table : templates.Table)
    (publicationWork work credit : Nat) : Charged (Publication κ Γ star Ty Storage) :=
  if quoted.plan.sourceDebit ≤ credit ∧ quoted.work + publicationWork ≤ work then
    let measured := measure templates prices quoted.plan world.scope entry 0 table
    ⟨PreparedBodies.publish templates solver quoted.plan around world knowledge frames cells measured.answer,
      measured.elapsed + if measured.answer.isOk then publicationWork else 0⟩
  else ⟨.error .credit, 0⟩

theorem activate_bound (solver : Solver κ Γ star) (quoted : QuotedPlan prices)
    (around : Surrounding κ Γ star Ty) (world : ExecutionWorld Storage)
    (knowledge : List (Constraint κ Γ star)) (frames : List (Frame κ Γ star Ty))
    (cells : List (Data κ Γ star × Comp κ Γ star Ty)) (entry : List Nat) (table : templates.Table)
    (publicationWork work credit : Nat) :
    (activate templates prices solver quoted around world knowledge frames cells entry table
      publicationWork work credit).elapsed ≤ work := by
  by_cases ready : quoted.plan.sourceDebit ≤ credit ∧ quoted.work + publicationWork ≤ work
  · rw [activate, if_pos ready]
    have templatesPay := (measured_plan templates prices quoted.plan world.scope entry 0 table).2
    rw [← quoted.exactWork] at templatesPay
    change _ + (if _ then _ else _) ≤ work
    split <;> omega
  · simp [activate, ready]

theorem activate_sound (solver : Solver κ Γ star) (quoted : QuotedPlan prices)
    (around : Surrounding κ Γ star Ty) (world : ExecutionWorld Storage)
    (knowledge : List (Constraint κ Γ star)) (frames : List (Frame κ Γ star Ty))
    (cells : List (Data κ Γ star × Comp κ Γ star Ty)) (entry : List Nat) (table : templates.Table)
    (publicationWork work credit : Nat) {result : Publication κ Γ star Ty Storage}
    (published : (activate templates prices solver quoted around world knowledge frames cells entry table
      publicationWork work credit).answer = .ok result) :
    PreparedBodies.activate templates solver quoted.plan around world knowledge frames cells entry table credit =
      .ok result := by
  by_cases ready : quoted.plan.sourceDebit ≤ credit ∧ quoted.work + publicationWork ≤ work
  · simp only [activate, if_pos ready] at published
    have exactTemplates := (measured_plan templates prices quoted.plan world.scope entry 0 table).1
    simpa only [PreparedBodies.activate, if_pos ready.1, exactTemplates] using published
  · simp [activate, ready] at published

private theorem slice_pays_moves {T : Type} (source : MachineCore T) (price : source.State → Nat)
    (positive : ∀ state, 1 ≤ price state) (fuel : Nat) (state : source.State) :
    (source.runSlice fuel state).2 ≤ source.sliceCost price fuel state := by
  induction fuel generalizing state with
  | zero => exact Nat.zero_le _
  | succ fuel ih =>
    rw [MachineCore.sliceCost_succ]
    cases stepped : source.step state with
    | none => simp [MachineCore.runSlice, stepped]
    | some next =>
      have paid := ih next
      have unit := positive state
      simp only [MachineCore.runSlice, stepped]
      omega

variable {machine : Evaluator κ D Storage} {strategy : Strategy κ Γ star D.Ty}
  {schedule : Scheduler machine strategy} {around : Surrounding κ Γ star D.Ty}

/-- An offer can be charged to successful source moves when its
reservation fits the common rate. The refusal cap is charged once by
the driver. This certificate uses the actual checked binder compiler. -/
theorem certified_attempt [DecidableEq κ.Key] (kept : Keeps machine strategy schedule around)
    (quoted : QuotedPlan prices) {code : Comp κ Γ star D.Ty} (compiled : compile code = some quoted.plan)
    (world : ExecutionWorld Storage) (knowledge : List (Constraint κ Γ star))
    (frames : List (Frame κ Γ star D.Ty)) (cells : List (Data κ Γ star × Comp κ Γ star D.Ty))
    (entry : List Nat) (table : templates.Table) (publicationWork work credit rate refusalCap : Nat)
    (price : (Meter.core machine strategy schedule).State → Nat) (positive : ∀ state, 1 ≤ price state)
    (progress : 0 < quoted.plan.sourceDebit) (successRate : work ≤ rate * quoted.plan.sourceDebit)
    (failureRate : work ≤ refusalCap) (earlier : List (Charge (Data κ Γ star))) :
    let before := PreparedBodies.entryState around world knowledge code frames cells entry
    let ledger : Meter.Ledger κ Γ star D.Ty Storage := ⟨before, earlier⟩
    let tried := activate templates prices machine.solver quoted around world knowledge frames cells entry table
      publicationWork work credit
    ∃ trial : BudgetedDriving.Trial (Meter.core machine strategy schedule) price rate refusalCap credit ledger,
      trial.elapsed = tried.elapsed ∧
      match tried.answer with
      | .error _ => trial.segment = none
      | .ok result => ∃ segment, trial.segment = some segment ∧
          segment.target.current = result.state ∧ segment.debit = result.debit := by
  let before := PreparedBodies.entryState around world knowledge code frames cells entry
  let ledger : Meter.Ledger κ Γ star D.Ty Storage := ⟨before, earlier⟩
  let tried := activate templates prices machine.solver quoted around world knowledge frames cells entry table
    publicationWork work credit
  have spent : tried.elapsed ≤ work := activate_bound templates prices machine.solver quoted around world
    knowledge frames cells entry table publicationWork work credit
  change ∃ trial : BudgetedDriving.Trial (Meter.core machine strategy schedule) price rate refusalCap credit ledger,
    trial.elapsed = tried.elapsed ∧ _
  cases outcome : tried.answer with
  | error why =>
    exact ⟨⟨none, tried.elapsed, spent.trans failureRate⟩, rfl, rfl⟩
  | ok result =>
    have published := activate_sound templates prices machine.solver quoted around world knowledge frames cells entry
      table publicationWork work credit outcome
    have ⟨fits, reached⟩ := PreparedBodies.activate_exact kept templates compiled world knowledge frames cells entry
      table credit published
    obtain ⟨_, _, _, _, _, _, view⟩ := PreparedBodies.activate_result templates machine.solver quoted.plan around world
      knowledge frames cells entry table credit published
    have debit : result.debit = quoted.plan.sourceDebit := congrArg Publication.debit view
    obtain ⟨segment, endpoint, used⟩ := HybridCost.certified_segment machine strategy schedule
      (ledger := ledger) reached (debit.symm ▸ progress)
    have covers := slice_pays_moves (Meter.core machine strategy schedule) price positive segment.debit ledger
    rw [segment.follows] at covers
    have paid : tried.elapsed ≤ rate * (Meter.core machine strategy schedule).sliceCost price segment.debit ledger := by
      apply (spent.trans successRate).trans
      apply Nat.mul_le_mul_left
      rw [← debit, ← used]
      exact covers
    exact ⟨⟨some segment, tried.elapsed, ⟨used.symm ▸ fits, paid⟩⟩, rfl, segment, rfl, endpoint, used⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Preparation.PreparedWork
