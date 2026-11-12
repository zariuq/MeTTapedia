import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaArgumentOperations
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaInheritedMachine

/-!
# Actual finite typed runs earn their ready-argument bounds

The driver uses the existing source and typed operations. No producer reply,
successful body or final answer is assumed. Every retained outcome preserves
the argument alignment of each live frame and saved collection caller.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaArgumentProgress

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS.Destination
open PettaOccurrenceOverlay

theorem step_keeps {User : Type} (operations : Services User) (program : SpaceSemantics.Program)
    (source : State User) (good : Safe source) :
    Keeps (PettaOccurrenceOverlay.step operations .eagerValue program source) := by
  cases scopes : source.2.scopes with
  | nil =>
      simp only [PettaOccurrenceOverlay.step, scopes]
      exact source_keeps .eagerValue program source good
  | cons current parents =>
      cases frontier : current.frontier with
      | nil =>
          simp only [PettaOccurrenceOverlay.step, scopes, frontier]
          exact source_keeps .eagerValue program source good
      | cons item pending =>
          rcases item with ⟨control, context, origins⟩
          cases calls : context.calls with
          | nil =>
              simp only [PettaOccurrenceOverlay.step, scopes, frontier, calls]
              exact delegate_keeps operations program source current parents control context origins pending good scopes frontier
          | cons frame outside =>
              by_cases depth : frame.scopeDepth = parents.length + 1
              · simp only [PettaOccurrenceOverlay.step, scopes, frontier, calls, List.length_cons, if_pos depth]
                cases phase : frame.phase with
                | nextArgument =>
                    exact next_argument_keeps operations source current parents control context origins pending
                      frame outside good scopes frontier calls phase
                | argument formal slot =>
                    by_cases terminal : control.goals.isEmpty = true
                    · simp only [terminal, if_true]
                      cases resolved : resolve control.bindings with
                      | none => exact call_keeps source _ good
                      | some environment =>
                          exact argument_guard_keeps operations source current parents control context origins pending
                            frame outside formal slot (read environment control.destination) good scopes frontier calls phase
                    · simp only [terminal]
                      exact delegate_keeps operations program source current parents control context origins pending
                        good scopes frontier
                | body =>
                    by_cases terminal : control.goals.isEmpty = true
                    · simp only [terminal, if_true]
                      cases resolved : resolve control.bindings with
                      | none => exact call_keeps source _ good
                      | some environment =>
                          exact result_guard_keeps operations source current parents control context origins pending
                            frame outside (read environment control.destination) good scopes frontier calls
                    · simp only [terminal]
                      exact delegate_keeps operations program source current parents control context origins pending
                        good scopes frontier
              · simp only [PettaOccurrenceOverlay.step, scopes, frontier, calls, List.length_cons, if_neg depth]
                exact delegate_keeps operations program source current parents control context origins pending good scopes frontier

theorem run_retained {User : Type} (operations : Services User) (program : SpaceSemantics.Program)
    (fuel : Nat) (source : State User) (good : Safe source) :
    ∀ final, PettaCallerReturnMachine.exitState
        ((PettaOccurrenceOverlay.machine operations .eagerValue program).run fuel source).2 = some final → Safe final := by
  induction fuel generalizing source with
  | zero =>
      intro final same
      cases Option.some.inj same
      exact good
  | succ fuel ih =>
      have kept := step_keeps operations program source good
      cases advanced : PettaOccurrenceOverlay.step operations .eagerValue program source with
      | silent next =>
          rw [advanced] at kept
          simpa only [Machine.run, PettaOccurrenceOverlay.machine, advanced] using
            ih next (kept next (by simp [PettaOccurrenceBinding.retained]))
      | publish events next =>
          rw [advanced] at kept
          simpa only [Machine.run, PettaOccurrenceOverlay.machine, advanced] using
            ih next (kept next (by simp [PettaOccurrenceBinding.retained]))
      | finish final | call request final =>
          rw [advanced] at kept
          intro reached same
          simp only [Machine.run, PettaOccurrenceOverlay.machine, advanced, PettaCallerReturnMachine.exitState] at same
          cases Option.some.inj same
          exact kept final (by simp [PettaOccurrenceBinding.retained])
      | fail events =>
          intro reached impossible
          simp [Machine.run, PettaOccurrenceOverlay.machine, advanced, PettaCallerReturnMachine.exitState] at impossible

theorem root_frontier_safe {User : Type} (allocator : Allocator) (world : EagerDFS.World)
    (frontier : List (Work User)) (noCalls : ∀ item ∈ frontier, item.2.1.calls = []) :
    Safe (allocator, ⟨world, [⟨frontier, [], none⟩]⟩) := by
  refine ⟨.root _ _, ?_⟩
  intro current member
  cases List.mem_singleton.mp member
  refine ⟨?_, ?_, ?_⟩
  · intro item present frame called
    rw [noCalls item present] at called
    cases called
  · intro answer impossible
    cases impossible
  · intro saved impossible
    cases impossible

theorem root_safe {User : Type} (allocator : Allocator) (world : EagerDFS.World) (control : DControl)
    (user : User) (origins : List Nat) :
    Safe (allocator, ⟨world, [⟨[(control, (⟨user, []⟩ : Context User), origins)], [], none⟩]⟩) := by
  apply root_frontier_safe
  intro item present
  cases List.mem_singleton.mp present
  rfl

theorem retained_body_argument {User : Type} (operations : Services User) (program : SpaceSemantics.Program)
    (fuel : Nat) (source final : State User) (good : Safe source)
    (retained : PettaCallerReturnMachine.exitState
      ((PettaOccurrenceOverlay.machine operations .eagerValue program).run fuel source).2 = some final)
    (current : Scope User) (member : current ∈ final.2.scopes) (item : Work User)
    (present : item ∈ current.frontier) (frame : CallFrame) (called : frame ∈ item.2.1.calls)
    (phase : frame.phase = .body) (index : Nat) (within : index < frame.row.parameters.length) :
    ∃ argument, frame.ready[index]? = some argument := by
  have finalGood := run_retained operations program fuel source good final retained
  have aligned : Aligned frame := (finalGood.2 current member).work item present frame called
  exact ready_index_available aligned phase index within

theorem controller_retained {User : Type} (operations : Services User) (program : SpaceSemantics.Program)
    (fuel : Nat) (source : PettaInheritedMachine.Mode User)
    (good : Safe (PettaInheritedMachine.decode source)) :
    ∀ final, PettaCallerReturnMachine.exitState
        (PettaInheritedMachine.outcome ((PettaInheritedMachine.machine operations program).run fuel source).2) =
          some final → Safe final := by
  have runs := congrArg Prod.snd (PettaInheritedMachine.run_refines operations program fuel source)
  dsimp only at runs
  intro final retained
  rw [runs] at retained
  exact run_retained operations program fuel (PettaInheritedMachine.decode source) good final retained

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaArgumentProgress
