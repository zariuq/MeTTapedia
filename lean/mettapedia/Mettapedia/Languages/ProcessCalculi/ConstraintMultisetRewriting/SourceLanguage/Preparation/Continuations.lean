import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Preparation.Evaluate
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Preparation.OrderedAgenda
import Mettapedia.Machines.ScopedCommit

/-!
# Continuation passing and its ordered machine

A lexical value resumes the source frame already carried by its
alternative. A move exposes zero or more new alternatives in the
world produced by that move. In continuation-passing form, each
alternative is sent to success along with the remaining search.
An empty reply invokes failure on the current world. The two
continuations defunctionalize to the ordered replacement of the
selected occurrence in the agenda.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Preparation.Machine

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.ContextualFamily
open Evaluation (Evaluator Reply)
open Mettapedia.Machines

variable {S : Signature} {κ : Keys S} {Γ : Ctx S} {star : S.Srt} {Storage Ty : Type}

structure State (κ : Keys S) (Γ : Ctx S) (star : S.Srt) (Ty Storage : Type) where
  world : ExecutionWorld Storage
  agenda : List (Branch κ Γ star Ty)

def State.source (spaces : Spaces κ Γ star Storage) (state : State κ Γ star Ty Storage) :
    Config κ Γ star Ty :=
  ⟨state.world.source spaces, state.agenda⟩

structure Transition (κ : Keys S) (Γ : Ctx S) (star : S.Srt) (Ty Storage : Type) where
  next : State κ Γ star Ty Storage
  work : Charge (Data κ Γ star)

variable {D : Discipline S Γ star}
  (machine : Evaluator κ D Storage) (strategy : Strategy κ Γ star D.Ty)

abbrev Scheduler := (state : State κ Γ star D.Ty Storage) →
  Option {position : Fin state.agenda.length //
    strategy.chooses (state.source machine.spaces) (state.agenda.get position)}

/-- Sequence the visible effect and the ordered choice in the independent
CPS algebra. Success receives the alternative together with the rest. -/
def sendCPS {Result : Type} (active : Branch κ Γ star Ty)
    (before after : ExecutionWorld Storage) (replies : List (Branch κ Γ star Ty))
    (success : ScopedCommit.Success (Branch κ Γ star Ty) (ExecutionWorld Storage) Result)
    (failure : ScopedCommit.Failure (ExecutionWorld Storage) Result) : Result :=
  let body : ScopedCommit.Body (Branch κ Γ star Ty) (ExecutionWorld Storage) :=
    .effect (fun branch _ => (branch, after)) (.choose (fun _ _ => replies) .done)
  ScopedCommit.eval body active success failure failure before

theorem sendCPS_defunctionalizes (active : Branch κ Γ star Ty)
    (before after : ExecutionWorld Storage) (replies pending : List (Branch κ Γ star Ty)) :
    sendCPS active before after replies ScopedCommit.collect (fun world => (pending, world)) =
      (replies ++ pending, after) := by
  induction replies with
  | nil => rfl
  | cons head rest ih =>
    simpa only [sendCPS, ScopedCommit.eval, List.foldr_cons, ScopedCommit.collect, List.cons_append] using
      congrArg (fun collected : List (Branch κ Γ star Ty) × ExecutionWorld Storage =>
        (head :: collected.1, collected.2)) ih

def advanceCPS (state : State κ Γ star D.Ty Storage) (chosen : Fin state.agenda.length) :
    Option (Transition κ Γ star D.Ty Storage) :=
  let branch := state.agenda.get chosen
  if machine.solver.satisfiable branch.store then
    (Evaluation.reduce machine state.world branch).map fun reply =>
      let pending := state.agenda.drop (chosen.val + 1)
      let emitted := sendCPS branch state.world reply.world' reply.branches
        ScopedCommit.collect (fun current => (pending, current))
      ⟨⟨emitted.2, state.agenda.take chosen.val ++ emitted.1⟩,
        charge strategy (state.source machine.spaces) branch reply.branches⟩
  else none

private def publish (state : State κ Γ star D.Ty Storage) (chosen : Fin state.agenda.length)
    (reply : Reply machine state.world (state.agenda.get chosen)) : Transition κ Γ star D.Ty Storage :=
  ⟨⟨reply.world', OrderedAgenda.replace state.agenda chosen reply.branches⟩,
    charge strategy (state.source machine.spaces) (state.agenda.get chosen) reply.branches⟩

/-- Reified continuations are the two sides of the selected position and the
ordered replacement. An unavailable reduction leaves the caller its state. -/
def advanceAt (state : State κ Γ star D.Ty Storage) (chosen : Fin state.agenda.length) :
    Option (Transition κ Γ star D.Ty Storage) :=
  let branch := state.agenda.get chosen
  if machine.solver.satisfiable branch.store then
    (Evaluation.reduce machine state.world branch).map (publish machine strategy state chosen)
  else none

theorem advanceCPS_eq (state : State κ Γ star D.Ty Storage) (chosen : Fin state.agenda.length) :
    advanceCPS machine strategy state chosen = advanceAt machine strategy state chosen := by
  dsimp only [advanceCPS, advanceAt]
  split
  · refine congrArg
      (fun k => Option.map k (Evaluation.reduce machine state.world (state.agenda.get chosen))) ?_
    funext reply
    simp only [sendCPS_defunctionalizes, publish, OrderedAgenda.replace, List.append_assoc]
  · rfl

theorem advanceAt_source {state : State κ Γ star D.Ty Storage} {chosen : Fin state.agenda.length}
    (scheduled : strategy.chooses (state.source machine.spaces) (state.agenda.get chosen))
    {transition : Transition κ Γ star D.Ty Storage}
    (step : advanceAt machine strategy state chosen = some transition) :
    ChargedStep D machine.program machine.supply strategy
      (state.source machine.spaces) transition.work (transition.next.source machine.spaces) := by
  by_cases alive : machine.solver.satisfiable (state.agenda.get chosen).store = true
  · simp only [advanceAt, alive, if_true] at step
    obtain ⟨reply, _, rfl⟩ := Option.map_eq_some_iff.mp step
    exact OrderedAgenda.charged_replacement strategy (state.world.source machine.spaces)
      (reply.world'.source machine.spaces) state.agenda chosen reply.branches scheduled
      ((machine.solver.satisfiable_iff _).mp alive) reply.sound
  · have stopped : advanceAt machine strategy state chosen = none := by
      dsimp only [advanceAt]
      rw [if_neg alive]
    rw [stopped] at step
    cases step

def advance (schedule : Scheduler machine strategy) (state : State κ Γ star D.Ty Storage) :
    Option (Transition κ Γ star D.Ty Storage) :=
  (schedule state).bind fun choice => advanceAt machine strategy state choice.val

theorem advance_source (schedule : Scheduler machine strategy)
    {state : State κ Γ star D.Ty Storage} {transition : Transition κ Γ star D.Ty Storage}
    (step : advance machine strategy schedule state = some transition) :
    ChargedStep D machine.program machine.supply strategy
      (state.source machine.spaces) transition.work (transition.next.source machine.spaces) := by
  obtain ⟨choice, _, advances⟩ := Option.bind_eq_some_iff.mp step
  exact advanceAt_source machine strategy choice.property advances

def run (schedule : Scheduler machine strategy) :
    Nat → State κ Γ star D.Ty Storage → State κ Γ star D.Ty Storage × List (Charge (Data κ Γ star))
  | 0, state => (state, [])
  | fuel + 1, state =>
    match advance machine strategy schedule state with
    | none => (state, [])
    | some transition =>
      let later := run schedule fuel transition.next
      (later.1, transition.work :: later.2)

theorem run_charged (schedule : Scheduler machine strategy) (fuel : Nat)
    (state : State κ Γ star D.Ty Storage) :
    let result := run machine strategy schedule fuel state
    ChargedRun D machine.program machine.supply strategy
      (state.source machine.spaces) result.2 (result.1.source machine.spaces) := by
  induction fuel generalizing state with
  | zero => exact .stop _
  | succ fuel ih =>
    unfold run
    cases got : advance machine strategy schedule state with
    | none => exact .stop _
    | some transition =>
      exact .advance (advance_source machine strategy schedule got) (ih transition.next)

theorem run_add (schedule : Scheduler machine strategy) (initial remaining : Nat)
    (state : State κ Γ star D.Ty Storage) :
    run machine strategy schedule (initial + remaining) state =
      let earlier := run machine strategy schedule initial state
      let later := run machine strategy schedule remaining earlier.1
      (later.1, earlier.2 ++ later.2) := by
  induction initial generalizing state with
  | zero => simp [run]
  | succ initial ih =>
    simp only [Nat.succ_add, run]
    cases got : advance machine strategy schedule state with
    | none =>
      have stays : run machine strategy schedule remaining state = (state, []) := by
        cases remaining <;> simp [run, got]
      simp [stays]
    | some transition => simp [ih transition.next]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Preparation.Machine
