import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallOrderOperations
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaFrameScopeMachine

/-!
# Finite actual runs earn scope-depth order and active-prefix depth

The invariant combines the existing scope bounds with ordered call stacks.
It starts before any typed frame is installed and survives every retained
outcome, including missing services and exhaustion. A selected mark at its
owning scope then determines the active top frame's depth.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallOrder

open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS.Destination
open PettaOccurrenceOverlay

def Invariant {User : Type} (source : State User) : Prop := Safe source ∧ PettaFrameScopes.Bounded source

theorem step_keeps {User : Type} (operations : Services User) (program : SpaceSemantics.Program)
    (source : State User) (good : Safe source) (bounded : PettaFrameScopes.Bounded source) :
    Keeps (PettaOccurrenceOverlay.step operations .eagerValue program source) := by
  cases scopes : source.2.scopes with
  | nil =>
      simp only [PettaOccurrenceOverlay.step, scopes]
      exact PettaContextFacts.source_keeps (@Ordered User) .eagerValue program source good
  | cons current parents =>
      cases frontier : current.frontier with
      | nil =>
          simp only [PettaOccurrenceOverlay.step, scopes, frontier]
          exact PettaContextFacts.source_keeps (@Ordered User) .eagerValue program source good
      | cons item pending =>
          rcases item with ⟨control, context, origins⟩
          cases calls : context.calls with
          | nil =>
              simp only [PettaOccurrenceOverlay.step, scopes, frontier, calls]
              exact delegate_keeps operations program source current parents control context origins pending good bounded scopes frontier
          | cons frame outside =>
              by_cases depth : frame.scopeDepth = parents.length + 1
              · simp only [PettaOccurrenceOverlay.step, scopes, frontier, calls, List.length_cons, if_pos depth]
                cases phase : frame.phase with
                | nextArgument =>
                    exact next_argument_keeps operations source current parents control context origins pending frame outside
                      good scopes frontier calls
                | argument formal slot =>
                    by_cases terminal : control.goals.isEmpty = true
                    · simp only [terminal, if_true]
                      cases resolved : resolve control.bindings with
                      | none => exact PettaContextFacts.call_keeps source _ good
                      | some environment =>
                          exact argument_guard_keeps operations source current parents control context origins pending frame outside
                            formal slot (read environment control.destination) good scopes frontier calls
                    · simp only [terminal]
                      exact delegate_keeps operations program source current parents control context origins pending good bounded scopes frontier
                | body =>
                    by_cases terminal : control.goals.isEmpty = true
                    · simp only [terminal, if_true]
                      cases resolved : resolve control.bindings with
                      | none => exact PettaContextFacts.call_keeps source _ good
                      | some environment =>
                          exact result_guard_keeps operations source current parents control context origins pending frame outside
                            (read environment control.destination) good scopes frontier calls
                    · simp only [terminal]
                      exact delegate_keeps operations program source current parents control context origins pending good bounded scopes frontier
              · simp only [PettaOccurrenceOverlay.step, scopes, frontier, calls, List.length_cons, if_neg depth]
                exact delegate_keeps operations program source current parents control context origins pending good bounded scopes frontier

theorem step_invariant {User : Type} (operations : Services User) (program : SpaceSemantics.Program)
    (source : State User) (good : Invariant source) :
    ∀ next ∈ PettaOccurrenceBinding.retained (PettaOccurrenceOverlay.step operations .eagerValue program source),
      Invariant next := by
  intro next retained
  exact ⟨step_keeps operations program source good.1 good.2 next retained,
    PettaFrameScopeMachine.step_keeps operations program source good.2 next retained⟩

theorem run_retained {User : Type} (operations : Services User) (program : SpaceSemantics.Program)
    (fuel : Nat) (source : State User) (good : Invariant source) :
    ∀ final, PettaCallerReturnMachine.exitState
        ((PettaOccurrenceOverlay.machine operations .eagerValue program).run fuel source).2 = some final → Invariant final := by
  induction fuel generalizing source with
  | zero =>
      intro final same
      cases Option.some.inj same
      exact good
  | succ fuel ih =>
      have kept := step_invariant operations program source good
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

theorem root_frontier {User : Type} (allocator : Allocator) (world : EagerDFS.World) (frontier : List (Work User))
    (emptyCalls : ∀ item ∈ frontier, item.2.1.calls = []) :
    Invariant (allocator, ⟨world, [⟨frontier, [], none⟩]⟩) := by
  constructor
  · apply PettaContextFacts.root_frontier_safe
    intro item present
    simpa only [Ordered, emptyCalls item present] using (List.Pairwise.nil :
      ([] : List CallFrame).Pairwise (fun inner outer => outer.scopeDepth ≤ inner.scopeDepth))
  · apply PettaFrameScopes.Scoped.root
    intro item present frame member
    rw [emptyCalls item present] at member
    cases member

theorem reached_selected_depth {User : Type} {saved : CallFrame} {argument : Mettapedia.Languages.MeTTa.OSLFCore.Atom}
    (operations : Services User) (program : SpaceSemantics.Program) (fuel : Nat) (source final : State User)
    (good : Invariant source)
    (retained : PettaCallerReturnMachine.exitState
      ((PettaOccurrenceOverlay.machine operations .eagerValue program).run fuel source).2 = some final)
    (current : Scope User) (parents : List (Scope User)) (control : DControl) (context : Context User)
    (origins : List Nat) (pending : List (Work User)) (index : Nat) (frame : CallFrame) (outside : List CallFrame)
    (scopes : final.2.scopes = current :: parents)
    (frontier : current.frontier = (control, context, origins) :: pending)
    (selected : PettaSelectedReturnWork.Holds saved argument index (control, context, origins))
    (owner : saved.scopeDepth = final.2.scopes.length) (calls : context.calls = frame :: outside) :
    frame.scopeDepth = final.2.scopes.length := by
  have kept := run_retained operations program fuel source good final retained
  exact selected_depth (PettaContextFacts.active final current parents control context origins pending kept.1 scopes frontier)
    (active_bounds final current parents control context origins pending kept.2 scopes frontier) selected owner calls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallOrder
