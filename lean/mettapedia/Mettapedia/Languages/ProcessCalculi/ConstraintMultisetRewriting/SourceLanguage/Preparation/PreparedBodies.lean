import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Preparation.BindingSimulation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Preparation.BindingTemplates
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Preparation.PreparedCall

/-!
# Admission and handback for compiled equation bodies

A compiled body is a private finite region. The publish operation
exposes its result and scope changes together, after testing source
credit and consistency. The ordinary machine continues from that
boundary, or from the original state upon refusal.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Preparation.PreparedBodies

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.ContextualFamily
open BindingPlans
open BindingSimulation
open BindingTemplates (Templates Refusal)
open Evaluation (Evaluator)
open Machine (State Scheduler)

variable {S : Signature} {κ : Keys S} {Γ : Ctx S} {star : S.Srt}
  {Storage Ty : Type} {D : Discipline S Γ star}

structure Publication (κ : Keys S) (Γ : Ctx S) (star : S.Srt) (Ty Storage : Type) where
  state : State κ Γ star Ty Storage
  debit : Nat

def publish (templates : Templates κ Γ star) (solver : Solver κ Γ star)
    (plan : Plan κ Γ star) (around : Surrounding κ Γ star Ty)
    (world : ExecutionWorld Storage) (knowledge : List (Constraint κ Γ star))
    (frames : List (Frame κ Γ star Ty)) (cells : List (Data κ Γ star × Comp κ Γ star Ty)) :
    Except Refusal ((templates.Table × List (templates.Value × templates.Value)) × templates.Value) →
      Except Refusal (Publication κ Γ star Ty Storage)
  | .error why => .error why
  | .ok ((_, facts), value) =>
    let store := knowledge ++ facts.map templates.equation
    if solver.satisfiable store then
      .ok ⟨around.state (laterWorld world plan.code.length)
        ⟨store, ExitKind.focus (templates.view value) plan.ending, frames, cells⟩, plan.sourceDebit⟩
    else .error .inconsistent

def activate (templates : Templates κ Γ star) (solver : Solver κ Γ star)
    (plan : Plan κ Γ star) (around : Surrounding κ Γ star Ty)
    (world : ExecutionWorld Storage) (knowledge : List (Constraint κ Γ star))
    (frames : List (Frame κ Γ star Ty)) (cells : List (Data κ Γ star × Comp κ Γ star Ty))
    (entry : List Nat) (table : templates.Table) (credit : Nat) :
    Except Refusal (Publication κ Γ star Ty Storage) :=
  if plan.sourceDebit ≤ credit then
    publish templates solver plan around world knowledge frames cells
      (BindingTemplates.run templates plan world.scope entry 0 table)
  else .error .credit

def entryState (around : Surrounding κ Γ star Ty) (world : ExecutionWorld Storage)
    (knowledge : List (Constraint κ Γ star)) (code : Comp κ Γ star Ty)
    (frames : List (Frame κ Γ star Ty)) (cells : List (Data κ Γ star × Comp κ Γ star Ty))
    (entry : List Nat) : State κ Γ star Ty Storage :=
  around.state world ⟨knowledge, .eval (code.inst (relabel κ (fun name => entry ++ name.scopes))), frames, cells⟩

theorem activate_result (templates : Templates κ Γ star) (solver : Solver κ Γ star)
    (plan : Plan κ Γ star) (around : Surrounding κ Γ star Ty)
    (world : ExecutionWorld Storage) (knowledge : List (Constraint κ Γ star))
    (frames : List (Frame κ Γ star Ty)) (cells : List (Data κ Γ star × Comp κ Γ star Ty))
    (entry : List Nat) (table : templates.Table) (credit : Nat)
    {result : Publication κ Γ star Ty Storage}
    (published : activate templates solver plan around world knowledge frames cells entry table credit = .ok result) :
    ∃ after facts value,
      BindingTemplates.run templates plan world.scope entry 0 table = .ok ((after, facts), value) ∧
      Solvable (knowledge ++ facts.map templates.equation) ∧ plan.sourceDebit ≤ credit ∧
      result = ⟨around.state (laterWorld world plan.code.length)
        ⟨knowledge ++ facts.map templates.equation, ExitKind.focus (templates.view value) plan.ending,
          frames, cells⟩, plan.sourceDebit⟩ := by
  by_cases enough : plan.sourceDebit ≤ credit
  · cases ran : BindingTemplates.run templates plan world.scope entry 0 table with
    | error why => simp [activate, publish, enough, ran] at published
    | ok packed =>
      obtain ⟨⟨after, facts⟩, value⟩ := packed
      by_cases consistent : solver.satisfiable (knowledge ++ facts.map templates.equation) = true
      · simp only [activate, if_pos enough, ran, publish, if_pos consistent, Except.ok.injEq] at published
        exact ⟨after, facts, value, rfl, (solver.satisfiable_iff _).mp consistent, enough, published.symm⟩
      · simp [activate, publish, enough, ran, consistent] at published
  · simp [activate, enough] at published

variable {machine : Evaluator κ D Storage} {strategy : Strategy κ Γ star D.Ty}
  {schedule : Scheduler machine strategy} {around : Surrounding κ Γ star D.Ty}

/-- The published state is reached by exactly the charged number of
reductions of the derived machine, under the region's scheduling law. -/
theorem activate_exact [DecidableEq κ.Key] (kept : Keeps machine strategy schedule around)
    (templates : Templates κ Γ star) {code : Comp κ Γ star D.Ty} {plan : Plan κ Γ star}
    (compiled : compile code = some plan)
    (world : ExecutionWorld Storage) (knowledge : List (Constraint κ Γ star))
    (frames : List (Frame κ Γ star D.Ty)) (cells : List (Data κ Γ star × Comp κ Γ star D.Ty))
    (entry : List Nat) (table : templates.Table) (credit : Nat)
    {result : Publication κ Γ star D.Ty Storage}
    (published : activate templates machine.solver plan around world knowledge frames cells entry table credit =
      .ok result) :
    result.debit ≤ credit ∧
      Reaches schedule result.debit (entryState around world knowledge code frames cells entry) result.state := by
  obtain ⟨⟨ending, shape⟩, _, rfl⟩ := Option.map_eq_some_iff.mp compiled
  let plan := lower shape [] 0
  obtain ⟨after, facts, value, computed, consistent, enough, rfl⟩ :=
    activate_result templates machine.solver plan around world knowledge frames cells entry table credit published
  have readback := BindingTemplates.run_exact templates plan world.scope entry 0 table computed
  have live : Solvable (knowledge ++ (plan.execute world.scope entry 0 (templates.scopes table)).1.2) := by
    rw [← readback]
    exact consistent
  have execution := lower_refines shape kept [] world.scope 0 entry (templates.scopes table)
    world knowledge frames cells (by simp [Context.earlier]) (by simp) live
  change Reaches schedule shape.moves
    (entryState around world knowledge code frames cells entry)
    (around.state (laterWorld world shape.bindings)
      ⟨knowledge ++ (plan.execute world.scope entry 0 (templates.scopes table)).1.2,
        ExitKind.focus (plan.execute world.scope entry 0 (templates.scopes table)).2 ending,
        frames, cells⟩) at execution
  rw [← readback] at execution
  refine ⟨enough, ?_⟩
  change Reaches schedule (lower shape [] 0).sourceDebit
    (entryState around world knowledge code frames cells entry)
    (around.state (laterWorld world (lower shape [] 0).code.length)
      ⟨knowledge ++ facts.map templates.equation,
        ExitKind.focus (templates.view value) (lower shape [] 0).ending, frames, cells⟩)
  rw [lower_debit, lower_ending, lower_length]
  exact execution

def resume (schedule : Scheduler machine strategy) (credit : Nat)
    (before : State κ Γ star D.Ty Storage) (attempt : Except Refusal (Publication κ Γ star D.Ty Storage)) :
    State κ Γ star D.Ty Storage × Nat :=
  match attempt with
  | .error _ =>
    let result := Machine.run machine strategy schedule credit before
    (result.1, result.2.length)
  | .ok published =>
    let later := Machine.run machine strategy schedule (credit - published.debit) published.state
    (later.1, published.debit + later.2.length)

/-- Both immediate refusal and successful publication followed by
ordinary execution have the original state and reduction count.
The decision to publish is made before the state is exposed. -/
theorem activate_then_continue_exact [DecidableEq κ.Key]
    (kept : Keeps machine strategy schedule around)
    (templates : Templates κ Γ star) {code : Comp κ Γ star D.Ty} {plan : Plan κ Γ star}
    (compiled : compile code = some plan) (world : ExecutionWorld Storage)
    (knowledge : List (Constraint κ Γ star)) (frames : List (Frame κ Γ star D.Ty))
    (cells : List (Data κ Γ star × Comp κ Γ star D.Ty))
    (entry : List Nat) (table : templates.Table) (credit : Nat) :
    let before := entryState around world knowledge code frames cells entry
    let attempt := activate templates machine.solver plan around world knowledge frames cells entry table credit
    resume schedule credit before attempt =
      let result := Machine.run machine strategy schedule credit before
      (result.1, result.2.length) := by
  dsimp only
  let before := entryState around world knowledge code frames cells entry
  cases tried : activate templates machine.solver plan around world knowledge frames cells entry table credit with
  | error failed => rfl
  | ok published =>
    have ⟨enough, execution⟩ := activate_exact kept templates compiled world knowledge frames cells entry table credit tried
    have split := Machine.run_add machine strategy schedule published.debit (credit - published.debit) before
    rw [show published.debit + (credit - published.debit) = credit by omega] at split
    have reached : (Machine.run machine strategy schedule published.debit before).1 = published.state := execution.state
    have debit : (Machine.run machine strategy schedule published.debit before).2.length = published.debit :=
      execution.debit
    change resume schedule credit before (.ok published) = _
    rw [split]
    simp only [resume, reached, List.length_append, debit]

open Elaboration

/-- The same body plans serve a selected equation. Its copy-opening is
the common environment at entry, and its lexical openings start at the
next fresh scope. Equation selection and program validity remain the
source-level contracts of the enclosing call. -/
theorem after_prepared_entry {MD : Discipline MSig [] ()} (m : Evaluator mkeys MD Storage)
    (policy : Strategy mkeys [] () MD.Ty) (sched : Scheduler m policy)
    (surround : Surrounding mkeys [] () MD.Ty) (kept : Keeps m policy sched surround)
    {head : PreparedCall.Head} (dispatch : PreparedCall.Plan m.program head)
    (world : ExecutionWorld Storage) (knowledge : List (Constraint mkeys [] ())) (call : MData)
    (frames : List (Frame mkeys [] () MD.Ty)) (cells : List (MData × Comp mkeys [] () MD.Ty))
    (templates : Templates mkeys [] ()) {bodyPlan : Plan mkeys [] ()}
    (compiled : compile dispatch.selected.rhs = some bodyPlan)
    (table : templates.Table) (credit : Nat) :
    let entered := PreparedCall.enter dispatch (world.source m.spaces) knowledge call frames cells
    let before := surround.state world.fresh entered
    resume sched credit before
      (activate templates m.solver bodyPlan surround world.fresh entered.store frames cells [world.scope] table credit) =
      let result := Machine.run m policy sched credit before
      (result.1, result.2.length) :=
  activate_then_continue_exact kept templates compiled world.fresh
    (PreparedCall.enter dispatch (world.source m.spaces) knowledge call frames cells).store
    frames cells [world.scope] table credit

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Preparation.PreparedBodies
