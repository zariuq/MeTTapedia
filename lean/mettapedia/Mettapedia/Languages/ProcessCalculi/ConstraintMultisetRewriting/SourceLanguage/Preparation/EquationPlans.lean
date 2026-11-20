import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Preparation.PreparedBodies

/-!
# Cached equation plans

A cache entry combines one licensed equation selection with one
compiled body. It can be transported through unchanged candidate
observations. Both successful body execution and refusal refine the
original source call through the same ordinary continuation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Preparation.EquationPlans

open Mettapedia.OSLF.Binding
open Elaboration
open FunctionVariables (Along)
open BindingSimulation (Surrounding Keeps)
open BindingTemplates (Templates)
open Evaluation (Evaluator)
open Machine (Scheduler)
open Mettapedia.GSLT.Dynamics.CacheCoherence (Notifies execute)

variable {D : Discipline MSig [] ()} {Storage : Type}

structure Cached (program : Program mkeys [] () D.Ty) (head : PreparedCall.Head) (budget : Nat) where
  dispatch : PreparedCall.Plan program head
  body : BindingPlans.Plan mkeys [] ()
  compiled : BindingPlans.compile dispatch.selected.rhs = some body
  fits : body.size ≤ budget

def compile (program : Program mkeys [] () D.Ty) (head : PreparedCall.Head) (budget : Nat) :
    Option (Cached program head budget) := do
  let dispatch ← PreparedCall.compile program head
  match built : BindingPlans.compile dispatch.selected.rhs with
  | none => none
  | some body =>
    if room : body.size ≤ budget then some ⟨dispatch, body, built, room⟩ else none

def Cached.afterPublications {Edit : Type} {program : Program mkeys [] () D.Ty}
    {head : PreparedCall.Head} {budget : Nat} (cached : Cached program head budget)
    (publish : Program mkeys [] () D.Ty → Edit → Program mkeys [] () D.Ty)
    (valid : Program mkeys [] () D.Ty → Prop) (stamp : Program mkeys [] () D.Ty → PreparedCall.Head → Nat)
    (notifies : Notifies publish valid stamp PreparedCall.candidates) (started : valid program)
    (edits : List Edit) (same : stamp (execute publish program edits) head = stamp program head) :
    Cached (execute publish program edits) head budget where
  dispatch := cached.dispatch.afterPublications publish valid stamp notifies started edits same
  body := cached.body
  compiled := cached.compiled
  fits := cached.fits

/-- The cached body is reusable for every fresh scope of the equation.
The entry guard performs clause selection before this suffix is run. -/
def suffix (machine : Evaluator mkeys D Storage) (strategy : Strategy mkeys [] () D.Ty)
    (schedule : Scheduler machine strategy) (around : Surrounding mkeys [] () D.Ty)
    {head : PreparedCall.Head} {budget : Nat} (cached : Cached machine.program head budget)
    (world : ExecutionWorld Storage) (knowledge : List (Constraint mkeys [] ())) (call : MData)
    (frames : List (Frame mkeys [] () D.Ty)) (cells : List (MData × Comp mkeys [] () D.Ty))
    (templates : Templates mkeys [] ()) (table : templates.Table) (credit : Nat) :
    Machine.State mkeys [] () D.Ty Storage × Nat :=
  let entered := PreparedCall.enter cached.dispatch (world.source machine.spaces) knowledge call frames cells
  let attempt := PreparedBodies.activate templates machine.solver cached.body around world.fresh entered.store
    frames cells [world.scope] table credit
  PreparedBodies.resume schedule credit (around.state world.fresh entered) attempt

theorem suffix_exact (machine : Evaluator mkeys D Storage) (strategy : Strategy mkeys [] () D.Ty)
    (schedule : Scheduler machine strategy) (around : Surrounding mkeys [] () D.Ty)
    (kept : Keeps machine strategy schedule around)
    {head : PreparedCall.Head} {budget : Nat} (cached : Cached machine.program head budget)
    (world : ExecutionWorld Storage) (knowledge : List (Constraint mkeys [] ())) (call : MData)
    (frames : List (Frame mkeys [] () D.Ty)) (cells : List (MData × Comp mkeys [] () D.Ty))
    (templates : Templates mkeys [] ()) (table : templates.Table) (credit : Nat) :
    suffix machine strategy schedule around cached world knowledge call frames cells templates table credit =
      let entered := PreparedCall.enter cached.dispatch (world.source machine.spaces) knowledge call frames cells
      let ordinary := Machine.run machine strategy schedule credit (around.state world.fresh entered)
      (ordinary.1, ordinary.2.length) :=
  PreparedBodies.after_prepared_entry machine strategy schedule around kept cached.dispatch
    world knowledge call frames cells templates cached.compiled table credit

/-- For a selected entry with only dead alternatives omitted, the
compiled suffix followed by ordinary execution implements an actual
source run, including the caller's final observations and quiescence. -/
theorem admitted_call_refines (machine : Evaluator mkeys D Storage)
    (strategy : Strategy mkeys [] () D.Ty) (schedule : Scheduler machine strategy)
    (kept : Keeps machine strategy schedule ⟨[], []⟩)
    {head : PreparedCall.Head} {budget : Nat} (cached : Cached machine.program head budget)
    {start : Config mkeys [] () D.Ty} (world : ExecutionWorld Storage)
    (knowledge : List (Constraint mkeys [] ())) (call : MData)
    (frames : List (Frame mkeys [] () D.Ty)) (cells : List (MData × Comp mkeys [] () D.Ty))
    (along : Along D machine.program machine.supply start (world.source machine.spaces)
      ⟨knowledge, .eval (.apply call), frames, cells⟩)
    (representable fits : Branch mkeys [] () D.Ty → Bool) {entered : Branch mkeys [] () D.Ty}
    (admitted : PreparedCall.activate cached.dispatch machine.solver (world.source machine.spaces)
      knowledge call frames cells representable fits = .ok entered)
    (templates : Templates mkeys [] ()) (table : templates.Table) (credit : Nat) :
    let result := (suffix machine strategy schedule ⟨[], []⟩ cached world knowledge call frames cells
      templates table credit).1.source machine.spaces
    ∃ whole, Runs D machine.program machine.supply start whole ∧
      Observation.observe (D := D) whole = Observation.observe (D := D) result ∧
      (Config.Quiescent (D := D) machine.program machine.supply result →
        Config.Quiescent (D := D) machine.program machine.supply whole) := by
  obtain ⟨same, identified, solvable⟩ := PreparedCall.activate_conditions cached.dispatch machine.solver
    (world.source machine.spaces) knowledge call frames cells representable fits admitted
  subst entered
  have entered := PreparedCall.enter_refines cached.dispatch along identified
  dsimp only
  rw [suffix_exact machine strategy schedule _ kept]
  let selected := PreparedCall.enter cached.dispatch (world.source machine.spaces) knowledge call frames cells
  let initial : Machine.State mkeys [] () D.Ty Storage := ⟨world.fresh, [selected]⟩
  have trace := Machine.run_charged machine strategy schedule credit initial
  change ChargedRun D machine.program machine.supply strategy
    ⟨(world.source machine.spaces).fresh, {selected}⟩
    (Machine.run machine strategy schedule credit initial).2
    ((Machine.run machine strategy schedule credit initial).1.source machine.spaces) at trace
  exact PreparedCall.handback_refines entered solvable trace

/-- A prepared caller can stop at another application with the same
pending continuation. The next equation can enter under the usual
guard, with earlier dead alternatives still accounted for. -/
theorem admitted_tail_refines (machine : Evaluator mkeys D Storage)
    (strategy : Strategy mkeys [] () D.Ty) (schedule : Scheduler machine strategy)
    (kept : Keeps machine strategy schedule ⟨[], []⟩)
    {head : PreparedCall.Head} {budget : Nat} (cached : Cached machine.program head budget)
    (exit : cached.body.ending = .tailCall)
    {start : Config mkeys [] () D.Ty} (world : ExecutionWorld Storage)
    (knowledge : List (Constraint mkeys [] ())) (call : MData)
    (frames : List (Frame mkeys [] () D.Ty)) (cells : List (MData × Comp mkeys [] () D.Ty))
    (along : Along D machine.program machine.supply start (world.source machine.spaces)
      ⟨knowledge, .eval (.apply call), frames, cells⟩)
    (representable fits : Branch mkeys [] () D.Ty → Bool) {entered : Branch mkeys [] () D.Ty}
    (admitted : PreparedCall.activate cached.dispatch machine.solver (world.source machine.spaces)
      knowledge call frames cells representable fits = .ok entered)
    (templates : Templates mkeys [] ()) (table : templates.Table) (credit : Nat)
    {result : PreparedBodies.Publication mkeys [] () D.Ty Storage}
    (published : PreparedBodies.activate templates machine.solver cached.body ⟨[], []⟩ world.fresh entered.store
      frames cells [world.scope] table credit = .ok result) :
    ∃ nextKnowledge nextCall,
      let next : Branch mkeys [] () D.Ty := ⟨nextKnowledge, .eval (.apply nextCall), frames, cells⟩
      result.state.agenda = [next] ∧ Solvable nextKnowledge ∧
        Along D machine.program machine.supply start (result.state.world.source machine.spaces) next := by
  obtain ⟨same, identified, live⟩ := PreparedCall.activate_conditions cached.dispatch machine.solver
    (world.source machine.spaces) knowledge call frames cells representable fits admitted
  subst entered
  let selected := PreparedCall.enter cached.dispatch (world.source machine.spaces) knowledge call frames cells
  have entry := PreparedCall.enter_refines cached.dispatch along identified
  have reached := (PreparedBodies.activate_exact kept templates cached.compiled world.fresh selected.store
    frames cells [world.scope] table credit published).2
  obtain ⟨after, facts, value, _, consistent, _, shape⟩ := PreparedBodies.activate_result templates machine.solver
    cached.body ⟨[], []⟩ world.fresh selected.store frames cells [world.scope] table credit published
  let store := selected.store ++ facts.map templates.equation
  let next : Branch mkeys [] () D.Ty := ⟨store, .eval (.apply (templates.view value)), frames, cells⟩
  let later := BindingSimulation.laterWorld world.fresh cached.body.code.length
  have agenda : result.state = ⟨later, [next]⟩ := by
    rw [shape, exit]
    rfl
  obtain ⟨work, certified, _, _⟩ := reached.charged
  change ChargedRun D machine.program machine.supply strategy
    ⟨(world.source machine.spaces).fresh, {selected}⟩ work (result.state.source machine.spaces) at certified
  rw [agenda] at certified
  change ChargedRun D machine.program machine.supply strategy
    ⟨(world.source machine.spaces).fresh, {selected}⟩ work ⟨later.source machine.spaces, {next}⟩ at certified
  obtain ⟨dead, inert, ran⟩ := entry
  have extended := Runs.frame certified.source dead
  simp only [Multiset.singleton_add] at extended
  refine ⟨store, templates.view value, congrArg Machine.State.agenda agenda, consistent, ?_⟩
  rw [agenda]
  exact ⟨dead, inert, fun _ => (ran live).trans extended⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Preparation.EquationPlans
