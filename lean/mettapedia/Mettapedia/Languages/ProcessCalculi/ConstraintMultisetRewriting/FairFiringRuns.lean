import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ReadinessPersistence

/-!
# Existing fairness owners applied to actual selected CMR firings

The LTS below packages the original Configuration, ConditionalSchedule.Firing,
Selection.Valid and Selection.result. The only idle completion is the existing
FairRuns withIdle construction. There is no new scheduler, parked queue,
whole-state token interpreter or assumed wake-index adequacy.

Tasks here identify one fixed selected firing. A process with changing schema
instances or selections requires a separate cover/transport argument. Fairness
is semantic readiness fairness; an actual parked queue must independently
establish that a ready task is awake and available for selection.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FairFiringRuns

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Liveness
open ReadinessPersistence

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]

def system (action : SubstitutionAction T S) (label : O → T) :
    LTS (Configuration T O) (ConditionalSchedule.Firing T O) where
  Allowed before firing := firing.2.Valid action label firing.1 before
  next before firing := firing.2.result label firing.1 before

def selectedTask (pending : ConditionalSchedule.Firing T O) :
    Option (ConditionalSchedule.Firing T O) → Prop :=
  LTS.liftTask (fun firing => firing = pending)

theorem task_enabled_iff (action : SubstitutionAction T S) (label : O → T)
    (pending : ConditionalSchedule.Firing T O) (before : Configuration T O) :
    (system action label).withIdle.TaskEnabled (selectedTask pending) before ↔
      pending.2.Valid action label pending.1 before := by
  unfold selectedTask
  rw [LTS.withIdle_taskEnabled_iff]
  constructor
  · rintro ⟨firing, rfl, valid⟩
    exact valid
  · intro valid
    exact ⟨pending, rfl, valid⟩

theorem run_refines (action : SubstitutionAction T S) (label : O → T)
    (run : Run (system action label).withIdle) (n : Nat) :
    action.Refines (run.state (n + 1)).equations (run.state n).equations := by
  rw [run.step n]
  have allowed := run.allowed n
  cases event : run.label n with
  | none => exact action.refines_refl _
  | some firing =>
      rw [event] at allowed
      exact Selection.Valid.refines allowed

/-- The stable, once-enabled route uses an entailed full port/tell problem.
The world need stay fixed only until this particular task fires. -/
theorem weak_fair_fires_of_entailed_added (action : SubstitutionAction T S)
    (label : O → T) (run : Run (system action label).withIdle)
    (pending : ConditionalSchedule.Firing T O) (start : Nat)
    (ready : pending.2.Valid action label pending.1 (run.state start))
    (noNewBinding : action.Refines (run.state start).equations
      (GuardFreeProcessOrders.added label pending.1 pending.2))
    (consistent : ∀ n ≥ start, action.Consistent (run.state n).equations)
    (sameUntil : ∀ n ≥ start,
      (∀ m, start ≤ m → m < n → ¬ selectedTask pending (run.label m)) →
        (run.state start).present = (run.state n).present)
    (fair : run.WeaklyFair (selectedTask pending)) :
    ∃ n ≥ start, selectedTask pending (run.label n) := by
  apply fair.fires start
  intro n later notYet
  apply (task_enabled_iff action label pending _).mpr
  exact valid_of_entailed_added action label ready
    (refinement_between action run.state (run_refines action label run) later)
    (sameUntil n later notYet) noNewBinding (consistent n later)

/-- Infinitely many ready moments of a fixed row need only weak fairness if
equations only refine and its world stays fixed until it fires. This does
not promote fixed-row readiness to an existential changing process task. -/
theorem weak_fair_fires_of_often_fixed_row (action : SubstitutionAction T S)
    (label : O → T) (run : Run (system action label).withIdle)
    (pending : ConditionalSchedule.Firing T O) (start : Nat)
    (often : InfinitelyOften fun n => pending.2.Valid action label pending.1 (run.state n))
    (sameUntil : ∀ n ≥ start,
      (∀ m, start ≤ m → m < n → ¬ selectedTask pending (run.label m)) →
        (run.state start).present = (run.state n).present)
    (fair : run.WeaklyFair (selectedTask pending)) :
    ∃ n ≥ start, selectedTask pending (run.label n) := by
  classical
  by_contra never
  push Not at never
  have same : ∀ early late, (run.state (start + early)).present = (run.state (start + late)).present := by
    intro early late
    exact (sameUntil _ (by omega) (fun m lower _ => never m lower)).symm.trans
      (sameUntil _ (by omega) (fun m lower _ => never m lower))
  have shifted : InfinitelyOften fun n =>
      pending.2.Valid action label pending.1 (run.state (start + n)) := by
    intro N
    obtain ⟨n, later, ready⟩ := often (start + N)
    refine ⟨n - start, by omega, ?_⟩
    simpa only [Nat.add_sub_of_le (by omega : start ≤ n)] using ready
  have eventuallyReady := often_ready_is_eventually_ready action label pending.1 pending.2
    (fun n => run.state (start + n))
    (fun n => by simpa only [Nat.add_assoc] using run_refines action label run (start + n)) same shifted
  obtain ⟨N, readyAfter⟩ := eventuallyReady
  have eventuallyEnabled : EventuallyAlways fun n =>
      (system action label).withIdle.TaskEnabled (selectedTask pending) (run.state n) := by
    refine ⟨start + N, ?_⟩
    intro n later
    apply (task_enabled_iff action label pending _).mpr
    have ready := readyAfter (n - start) (by omega)
    simpa only [Nat.add_sub_of_le (by omega : start ≤ n)] using ready
  obtain ⟨n, later, fired⟩ := fair eventuallyEnabled start
  exact never n later fired

/-- With changing physical worlds the stronger infinitely-often hypothesis
can use the original strong-fairness theorem directly. -/
theorem strong_fair_fires_of_often (action : SubstitutionAction T S) (label : O → T)
    (run : Run (system action label).withIdle)
    (pending : ConditionalSchedule.Firing T O) (start : Nat)
    (often : InfinitelyOften fun n => pending.2.Valid action label pending.1 (run.state n))
    (fair : run.StronglyFair (selectedTask pending)) :
    ∃ n ≥ start, selectedTask pending (run.label n) := by
  apply fair.fires _ start
  intro N
  obtain ⟨n, later, ready⟩ := often N
  exact ⟨n, later, (task_enabled_iff action label pending _).mpr ready⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FairFiringRuns
