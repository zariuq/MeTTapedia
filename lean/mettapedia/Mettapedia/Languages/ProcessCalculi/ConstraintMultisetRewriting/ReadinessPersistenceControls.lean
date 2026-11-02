import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FairFiringRuns
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Controls

/-!
# A consistent tell can kill a finite window of selected readiness

The examples use the original first-order action and source occurrence step.
A pending call can bind x to zero, while a separate actual tell fixes x to
one. Both stores are globally consistent, but the selected call cannot run
after the tell. A shared reflexive read has no new port binding and survives.
Strong fairness still does not guarantee service during a finite window.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ReadinessPersistenceControls

open Mettapedia.Logic.LP
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Liveness
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Controls

def bindOne : RuleInstance (Term signature) := ⟨[], [], [(.var 0, .const 1)], [], []⟩
def emptyPick : Selection Nat := ⟨[], [], []⟩
def boundState : Configuration (Term signature) Nat := emptyPick.result label bindOne initial

theorem bind_valid : emptyPick.Valid A label bindOne initial := by
  refine ⟨by decide, by decide, rfl, rfl, rfl, by decide, ?_, ?_⟩
  · refine ⟨one, ?_⟩
    intro equation member
    have same : equation = (Term.var (σ := signature) 0, Term.const (σ := signature) 1) := by
      simpa [Selection.problem, Selection.equations, emptyPick, bindOne, initial] using member
    subst equation
    rfl
  · simp [bindOne]

theorem actual_consistent_tell :
    Step A label bindOne initial boundState ∧
      initial.present = boundState.present ∧ A.Consistent boundState.equations :=
  ⟨⟨emptyPick, bind_valid, rfl⟩, by decide, bind_valid.consistent⟩

theorem pending_call_destroyed : ¬ callSelection.Valid A label callRule boundState := by
  intro valid
  obtain ⟨assignment, solved⟩ := valid.consistent
  have oldProblem := ReadinessPersistence.extended_problem_refines A label callRule callSelection
    (early := initial) (late := boundState) (fun _ _ => A.models_nil _) assignment solved
  have zeroValue := caller_binding_reaches_frame assignment oldProblem
  change assignment 0 = Term.const (σ := signature) 0 at zeroValue
  have oneValue := solved (Term.var (σ := signature) 0, Term.const (σ := signature) 1) (by
    simp [Selection.problem, Selection.result, Selection.equations, boundState,
      emptyPick, bindOne, initial])
  change assignment 0 = Term.const (σ := signature) 1 at oneValue
  have impossible := zeroValue.symm.trans oneValue
  cases impossible

theorem entailed_port_condition_is_not_automatic :
    ¬ A.Refines initial.equations (GuardFreeProcessOrders.added label callRule callSelection) := by
  intro entailed
  apply caller_value_cannot_stay_arbitrary
  rw [GuardFreeProcessOrders.result_equations, A.models_append]
  exact ⟨A.models_nil one, entailed one (A.models_nil one)⟩

def readBoundState : Configuration (Term signature) Nat :=
  emptyPick.result label bindOne singletonStore

theorem reflexive_shared_read_survives :
    sharedRead.Valid A label readsRule readBoundState := by
  apply ReadinessPersistence.valid_of_entailed_added A label two_reads_share_one_occurrence
    (fun _ _ => A.models_nil _) (by decide)
  · intro assignment _ equation member
    have same : equation = (Term.var (σ := signature) 0, Term.var (σ := signature) 0) := by
      simpa [GuardFreeProcessOrders.added, Selection.equations, readsRule, sharedRead, label] using member
    subst equation
    rfl
  · refine ⟨one, ?_⟩
    intro equation member
    have same : equation = (Term.var (σ := signature) 0, Term.const (σ := signature) 1) := by
      simpa [Selection.result, Selection.problem, Selection.equations, readBoundState,
        emptyPick, bindOne, singletonStore] using member
    subst equation
    rfl

def pendingFiring : ConditionalSchedule.Firing (Term signature) Nat := (callRule, callSelection)
def bindingFiring : ConditionalSchedule.Firing (Term signature) Nat := (bindOne, emptyPick)

/-- One actual tell followed by the existing idle transition. -/
def finiteWindowRun : Run (FairFiringRuns.system A label).withIdle where
  state n := if n = 0 then initial else boundState
  label n := if n = 0 then some bindingFiring else none
  allowed n := by
    cases n with
    | zero => exact bind_valid
    | succ n => trivial
  step n := by cases n <;> rfl

theorem pending_ready_initially :
    pendingFiring.2.Valid A label pendingFiring.1 (finiteWindowRun.state 0) := call_valid

theorem pending_never_served (n : Nat) :
    ¬ FairFiringRuns.selectedTask pendingFiring (finiteWindowRun.label n) := by
  cases n with
  | zero =>
      intro same
      have rules := congrArg (fun firing : ConditionalSchedule.Firing (Term signature) Nat => firing.1.take) same
      cases rules
  | succ n => exact False.elim

/-- Even strong fairness cannot require firing during one finite enabling
window. Afterwards this actual selected problem is inconsistent. -/
theorem finite_window_run_is_strongly_fair :
    finiteWindowRun.StronglyFair (FairFiringRuns.selectedTask pendingFiring) := by
  intro often
  exfalso
  obtain ⟨n, later, enabled⟩ := often 1
  have valid := (FairFiringRuns.task_enabled_iff A label pendingFiring _).mp enabled
  have nonzero : n ≠ 0 := by omega
  have atBound : finiteWindowRun.state n = boundState := by simp [finiteWindowRun, nonzero]
  rw [atBound] at valid
  exact pending_call_destroyed valid

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ReadinessPersistenceControls
