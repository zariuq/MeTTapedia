import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaBodyFrameEmbedding
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationContextTransport

/-!
# Actual saved-frame transport through source and typed body interiors

The owned scheduler's context transport and the typed-operation laws now
compose at the actual overlay step. The explicit exit check marks the saved
frame's terminal body boundary, where return checking belongs to the caller.
No body-execution equality is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaBodySourceEmbedding

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS.Destination
open PettaOccurrenceOverlay PettaBodyFrameEmbedding

theorem source_state {User : Type} (saved : CallFrame) (source : State User) :
    state saved source = Bridges.DestinationContextMap.state (context saved) source := rfl

theorem source_action {User : Type} (saved : CallFrame) (reply : Bridges.ScopedQuerySource.Action (Context User)) :
    liftSource (Bridges.DestinationContextMap.action (context saved) reply) =
      action saved (liftSource reply) := by cases reply <;> rfl

theorem source_owned {User : Type} (saved : CallFrame) (policy : Policy)
    (program : SpaceSemantics.Program) (source : State User) :
    liftSource (Bridges.ScopedQuerySource.ownedStep policy program (state saved source)) =
      action saved (liftSource (Bridges.ScopedQuerySource.ownedStep policy program source)) := by
  rw [source_state, Bridges.DestinationContextMap.owned_step, source_action]

theorem delegate_commutes {User : Type} (saved : CallFrame) (original : Services User)
    (program : SpaceSemantics.Program) (source : State User) (current : Scope User)
    (parents : List (Scope User)) (control : DControl) (inside : Context User)
    (origins : List Nat) (pending : List (Work User)) :
    delegate original .eagerValue program (state saved source) (scope saved current)
      (parents.map (scope saved)) control (context saved inside) origins (pending.map (work saved)) =
      action saved (delegate (services saved original) .eagerValue program source current parents
        control inside origins pending) := by
  have rows : original.rows (state saved source).2.world (context saved inside).user =
      (services saved original).rows source.2.world inside.user := rfl
  unfold delegate
  simp only [rows]
  repeat' first
    | exact source_owned saved .eagerValue program source
    | exact enter_rows_commutes saved original source current parents control inside origins pending _ _ _ _
    | split

/-- Only the completed saved body is a region exit. A terminal inner
collection or an inner typed call is not mistaken for that boundary. -/
def exitReady {User : Type} (saved : CallFrame) (source : State User) : Bool :=
  match source.2.scopes with
  | [] => false
  | current :: _ => match current.frontier with
      | [] => false
      | (control, inside, _) :: _ =>
          inside.calls.isEmpty && control.goals.isEmpty && saved.scopeDepth == source.2.scopes.length

/-- Every interior step uses the actual source or typed operation. Return
checking is deliberately left at the explicit exit boundary. -/
theorem interior_step {User : Type} (saved : CallFrame) (original : Services User)
    (program : SpaceSemantics.Program) (source : State User)
    (phase : saved.phase = .body) (interior : exitReady saved source = false) :
    PettaOccurrenceOverlay.step original .eagerValue program (state saved source) =
      action saved (PettaOccurrenceOverlay.step (services saved original) .eagerValue program source) := by
  cases scopes : source.2.scopes with
  | nil =>
      have mapped : (state saved source).2.scopes = [] := by simp [state, scopes]
      simp only [PettaOccurrenceOverlay.step, mapped, scopes]
      exact source_owned saved .eagerValue program source
  | cons current parents =>
      have mappedScopes : (state saved source).2.scopes = scope saved current :: parents.map (scope saved) := by
        simp [state, scopes]
      cases frontier : current.frontier with
      | nil =>
          have mappedFrontier : (scope saved current).frontier = [] := by simp [scope, frontier]
          simp only [PettaOccurrenceOverlay.step, mappedScopes, scopes, mappedFrontier, frontier]
          exact source_owned saved .eagerValue program source
      | cons item pending =>
          rcases item with ⟨control, inside, origins⟩
          have mappedFrontier : (scope saved current).frontier =
              (control, context saved inside, origins) :: pending.map (work saved) := by
            simp [scope, frontier, work]
          cases calls : inside.calls with
          | nil =>
              have mappedCalls : (context saved inside).calls = [saved] := by simp [context, calls]
              by_cases depth : saved.scopeDepth = parents.length + 1
              · have fullDepth : saved.scopeDepth = source.2.scopes.length := by simpa [scopes] using depth
                have active : control.goals.isEmpty = false := by
                  cases goals : control.goals with
                  | nil => simp [exitReady, scopes, frontier, calls, goals, fullDepth] at interior
                  | cons first rest => rfl
                simp only [PettaOccurrenceOverlay.step, mappedScopes, scopes, mappedFrontier, frontier,
                  calls, mappedCalls, List.length_cons, List.length_map, if_pos depth, phase, active]
                exact delegate_commutes saved original program source current parents control inside origins pending
              · simp only [PettaOccurrenceOverlay.step, mappedScopes, scopes, mappedFrontier, frontier,
                  calls, mappedCalls, List.length_cons, List.length_map, if_neg depth]
                exact delegate_commutes saved original program source current parents control inside origins pending
          | cons frame outside =>
              have mappedCalls : (context saved inside).calls = frame :: (outside ++ [saved]) := by simp [context, calls]
              by_cases depth : frame.scopeDepth = parents.length + 1
              · by_cases active : frame.phase = .nextArgument ∨ control.goals = []
                · exact active_typed_step_commutes saved original program source current parents control inside origins pending
                    frame outside scopes frontier calls (by simpa [scopes] using depth) active
                · have running : control.goals.isEmpty = false := by
                    cases goals : control.goals with
                    | nil => exact False.elim (active (.inr goals))
                    | cons first rest => rfl
                  simp only [PettaOccurrenceOverlay.step, mappedScopes, scopes, mappedFrontier, frontier,
                    calls, mappedCalls, List.length_cons, List.length_map, if_pos depth]
                  cases innerPhase : frame.phase with
                  | nextArgument => exact False.elim (active (.inl innerPhase))
                  | argument formal slot | body =>
                      simp only [running]
                      exact delegate_commutes saved original program source current parents control inside origins pending
              · simp only [PettaOccurrenceOverlay.step, mappedScopes, scopes, mappedFrontier, frontier,
                  calls, mappedCalls, List.length_cons, List.length_map, if_neg depth]
                exact delegate_commutes saved original program source current parents control inside origins pending

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaBodySourceEmbedding
