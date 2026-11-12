import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaBodyRegionTransport
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaTypedBodyRun

/-!
# Earned return information at the retained body checkpoint

The region can stop early, run forever, refuse, or suspend at an ordinary
service request. Only an actual checkpoint outcome earns the terminal view
below. The proof derives its return invariant from real preceding operations;
it assumes neither successful execution nor a body-result equation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaBodyCheckpoint

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS.Destination
open PettaOccurrenceOverlay PettaFrameScopes
open PettaBodyRegionTransport

theorem checkpoint_invariant {User : Type} (inputs : User → Atom) (stop : State User → Bool)
    (operations : Services User) (program : SpaceSemantics.Program) (fuel : Nat)
    (source final : State User) (valid : PettaCallerReturnMachine.Invariant inputs source)
    (bounded : Bounded source)
    (captured : ((PettaBodyRegionTransport.machine stop operations program).run fuel source).2 =
      .suspended (.inl ()) final) :
    stop final = true ∧ PettaCallerReturnMachine.Invariant inputs final ∧ Bounded final := by
  induction fuel generalizing source with
  | zero => cases captured
  | succ fuel ih =>
      cases stopped : stop source with
      | true =>
          simp only [Machine.run, PettaBodyRegionTransport.machine_step, PettaBodyRegionTransport.step,
            stopped, if_true] at captured
          have same : source = final := (Outcome.suspended.inj captured).2
          cases same
          exact ⟨stopped, valid, bounded⟩
      | false =>
          have returns := PettaCallerReturnMachine.step_invariant inputs operations program source valid
          have frames := PettaFrameScopeMachine.step_keeps operations program source bounded
          cases advanced : PettaOccurrenceOverlay.step operations .eagerValue program source with
          | silent next =>
              rw [advanced] at returns frames
              apply ih next (returns next (by simp [PettaOccurrenceBinding.retained]))
                (frames next (by simp [PettaOccurrenceBinding.retained]))
              simpa only [Machine.run, PettaBodyRegionTransport.machine_step, PettaBodyRegionTransport.step,
                stopped, Bool.false_eq_true, if_false, advanced, Transition.relabel] using captured
          | publish events next =>
              rw [advanced] at returns frames
              apply ih next (returns next (by simp [PettaOccurrenceBinding.retained]))
                (frames next (by simp [PettaOccurrenceBinding.retained]))
              simpa only [Machine.run, PettaBodyRegionTransport.machine_step, PettaBodyRegionTransport.step,
                stopped, Bool.false_eq_true, if_false, advanced, Transition.relabel] using captured
          | finish reached | call request reached | fail events =>
              simp [Machine.run, PettaBodyRegionTransport.machine_step, PettaBodyRegionTransport.step,
                stopped, advanced, Transition.relabel] at captured

structure ExitView {User : Type} (inputs : User → Atom) (source : State User) where
  current : Scope User
  control : DControl
  context : Context User
  origins : List Nat
  pending : List (Work User)
  root : source.2.scopes = [current]
  frontier : current.frontier = (control, context, origins) :: pending
  noCalls : context.calls = []
  terminal : control.goals = []
  reads : ∀ environment, resolve control.bindings = some environment →
    read environment control.destination = read environment (inputs context.user)

theorem exit_view {User : Type} (inputs : User → Atom) (saved : CallFrame) (source : State User)
    (depth : saved.scopeDepth = 1) (checked : PettaBodySourceEmbedding.exitReady saved source = true)
    (valid : PettaCallerReturnMachine.Invariant inputs source) : Nonempty (ExitView inputs source) := by
  cases scopes : source.2.scopes with
  | nil => simp [PettaBodySourceEmbedding.exitReady, scopes] at checked
  | cons current parents =>
      cases frontier : current.frontier with
      | nil => simp [PettaBodySourceEmbedding.exitReady, scopes, frontier] at checked
      | cons item pending =>
          rcases item with ⟨control, context, origins⟩
          have tests : context.calls = [] ∧ control.goals = [] ∧ saved.scopeDepth = parents.length + 1 := by
            simpa [PettaBodySourceEmbedding.exitReady, scopes, frontier, Bool.and_eq_true, and_assoc] using checked
          have noParents : parents = [] := List.eq_nil_of_length_eq_zero (by omega)
          subst parents
          have held := PettaCallerReturnView.root_work inputs source current scopes valid.2
            (control, context, origins) (frontier ▸ List.mem_cons_self)
          have actual : PettaCallerReturnFrames.Frames (inputs context.user) control [] := by
            simpa only [PettaCallerReturnPhases.WorkHolds, tests.1] using held
          refine ⟨⟨current, control, context, origins, pending, scopes, frontier, tests.1, tests.2.1, ?_⟩⟩
          intro environment resolved
          exact Bridges.ScopedReturnLocal.terminal_alias_observation (inputs context.user)
            (⟨source.2.world, control, context⟩ : Cursor (Context User)) actual.no_calls tests.2.1 environment resolved

theorem checked_checkpoint {User : Type} (operations : Services User) (program : SpaceSemantics.Program)
    (head : String) (index inspectionFuel : Nat)
    (checked : Bridges.ScopedReturnFunction.checksHead program head index inspectionFuel = true)
    (control : DControl) (arguments : List Atom) (argument destination : Atom)
    (actual : arguments[index]? = some argument) (target : control.destination = destination)
    (user : User) (origins : List Nat) (allocator : Allocator) (world : EagerDFS.World)
    (saved : CallFrame) (depth : saved.scopeDepth = 1) (fuel : Nat) (final : State User)
    (captured : ((PettaBodyRegionTransport.machine (PettaBodySourceEmbedding.exitReady saved) operations program).run fuel
      (PettaCallerReturnEntry.enter operations program control head arguments destination user origins allocator world)).2 =
        .suspended (.inl ()) final) : Nonempty (ExitView (fun _ : User => argument) final) := by
  have result := checkpoint_invariant (fun _ : User => argument) (PettaBodySourceEmbedding.exitReady saved)
    operations program fuel _ final
    (PettaCallerReturnEntry.checked_entry_invariant operations program head index inspectionFuel checked
      control arguments argument destination actual target user origins allocator world)
    (PettaTypedBodyRun.entered_frames_bounded operations program control head arguments destination user origins allocator world)
    captured
  exact exit_view (fun _ : User => argument) saved final depth result.1 result.2.1

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaBodyCheckpoint
