import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaBodySourceEmbedding
import Mettapedia.Machines.Checkpoint

/-!
# Exact retained execution of the saved-frame body region

Both machines use their existing actual typed-overlay steps. They stop before
the enclosing terminal dispatch and expose the complete reached state. This
checkpoint is not a successful answer: resolution and the enclosing result
guard still belong to the next boundary operation. All earlier requests,
packets, effects and exhaustion states are preserved exactly.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaBodyRegionTransport

open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS.Destination
open PettaOccurrenceOverlay PettaBodyFrameEmbedding PettaBodySourceEmbedding

def carriedExit {User : Type} (source : State User) : Bool :=
  match source.2.scopes with
  | [] => false
  | current :: _ => match current.frontier with
      | [] => false
      | (control, inside, _) :: _ => match inside.calls with
          | [frame] => frame.phase == .body && control.goals.isEmpty && frame.scopeDepth == source.2.scopes.length
          | _ => false

theorem exit_check_commutes {User : Type} (saved : CallFrame) (source : State User)
    (phase : saved.phase = .body) : carriedExit (state saved source) = exitReady saved source := by
  cases scopes : source.2.scopes with
  | nil => simp [carriedExit, exitReady, state, scopes]
  | cons current parents =>
      cases frontier : current.frontier with
      | nil => simp [carriedExit, exitReady, state, scope, scopes, frontier]
      | cons item pending =>
          rcases item with ⟨control, inside, origins⟩
          cases calls : inside.calls with
          | nil => simp [carriedExit, exitReady, state, scope, context, work, scopes, frontier, calls, phase]
          | cons frame rest =>
              cases rest <;> simp [carriedExit, exitReady, state, scope, context, work, scopes, frontier, calls]

abbrev RegionRequest := Unit ⊕ Request
abbrev RegionStep (User : Type) := Transition (State User) CollectedAnswer (State User) RegionRequest

def step {User : Type} (stop : State User → Bool) (operations : Services User)
    (program : SpaceSemantics.Program) (source : State User) : RegionStep User :=
  if stop source then .call (.inl ()) source
  else (PettaOccurrenceOverlay.step operations .eagerValue program source).relabel id id Sum.inr

def machine {User : Type} (stop : State User → Bool) (operations : Services User)
    (program : SpaceSemantics.Program) : Machine (State User) CollectedAnswer (State User) RegionRequest :=
  Mettapedia.Machines.Checkpoint.machine (PettaOccurrenceOverlay.machine operations .eagerValue program) stop

@[simp] theorem machine_step {User : Type} (stop : State User → Bool) (operations : Services User)
    (program : SpaceSemantics.Program) (source : State User) :
    (machine stop operations program).step source = some (step stop operations program source) := by
  cases checked : stop source <;>
    simp only [machine, Mettapedia.Machines.Checkpoint.machine, PettaOccurrenceOverlay.machine, step,
      checked, Bool.false_eq_true, if_false, if_true, Option.map_some]

theorem action_relabel {User : Type} (saved : CallFrame) (reply : Step User) :
    action saved (reply.relabel id id (Sum.inr : Request → RegionRequest)) =
      (action saved reply).relabel id id (Sum.inr : Request → RegionRequest) := by
  cases reply <;> rfl

theorem step_transport {User : Type} (saved : CallFrame) (original : Services User)
    (program : SpaceSemantics.Program) (source : State User) (phase : saved.phase = .body) :
    step carriedExit original program (state saved source) =
      action saved (step (exitReady saved) (services saved original) program source) := by
  unfold step
  rw [exit_check_commutes saved source phase]
  cases checked : exitReady saved source with
  | true => rfl
  | false =>
      simp only [Bool.false_eq_true, if_false]
      rw [interior_step saved original program source phase checked, action_relabel]

def outcome {User : Type} (saved : CallFrame) :
    Outcome (State User) (State User) RegionRequest → Outcome (State User) (State User) RegionRequest
  | .finished final => .finished (state saved final)
  | .suspended request retained => .suspended request (state saved retained)
  | .stuck retained => .stuck (state saved retained)
  | .exhausted retained => .exhausted (state saved retained)
  | .faulted => .faulted

theorem run_transport {User : Type} (saved : CallFrame) (original : Services User)
    (program : SpaceSemantics.Program) (fuel : Nat) (source : State User) (phase : saved.phase = .body) :
    (machine carriedExit original program).run fuel (state saved source) =
      let result := (machine (exitReady saved) (services saved original) program).run fuel source
      (result.1, outcome saved result.2) := by
  induction fuel generalizing source with
  | zero => rfl
  | succ fuel ih =>
      simp only [Machine.run, machine_step, step_transport saved original program source phase]
      cases advanced : step (exitReady saved) (services saved original) program source with
      | silent next => simpa only [advanced, action] using ih next
      | publish events next =>
          simpa only [advanced, action] using congrArg
            (fun result : List CollectedAnswer × Outcome (State User) (State User) RegionRequest =>
              (events ++ result.1, result.2)) (ih next)
      | finish final | call request retained | fail events => rfl

/-- The correspondence is two-sided at the full ordered packet observation.
The same equation retains the exact reached state at every kind of pause. -/
theorem packet_prefix_exact {User : Type} (saved : CallFrame) (original : Services User)
    (program : SpaceSemantics.Program) (fuel : Nat) (source : State User) (phase : saved.phase = .body) :
    ((machine carriedExit original program).run fuel (state saved source)).1 =
      ((machine (exitReady saved) (services saved original) program).run fuel source).1 := by
  have prefixEquality := congrArg
    (fun result : List CollectedAnswer × Outcome (State User) (State User) RegionRequest => result.1)
    (run_transport saved original program fuel source phase)
  exact prefixEquality

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaBodyRegionTransport
