import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaInheritedOperations

/-!
# A region hands off at the first active inherited frame

All source and owned typed steps commute with context flattening. The only
new boundary is a frame held in the inherited context becoming active at its
own scope depth. This test does not assume a successful solver or guard.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaInheritedContext

open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS.Destination
open PettaOccurrenceOverlay

def boundary {User : Type} (source : LocalState User) : Bool :=
  match source.2.scopes with
  | [] => false
  | current :: _ => match current.frontier with
      | [] => false
      | (control, inside, _) :: _ => match inside.calls with
          | _ :: _ => false
          | [] => match inside.user.calls with
              | [] => false
              | frame :: _ =>
                  decide (frame.scopeDepth = source.2.scopes.length) &&
                    match frame.phase with
                    | .nextArgument => true
                    | .argument _ _ | .body => control.goals.isEmpty

theorem active_owned_step {User : Type} (original : Services User) (program : SpaceSemantics.Program)
    (source : LocalState User) (current : Scope (Context User)) (parents : List (Scope (Context User)))
    (control : DControl) (inside : Context (Context User)) (origins : List Nat)
    (pending : List (Work (Context User))) (frame : CallFrame) (outside : List CallFrame)
    (scopes : source.2.scopes = current :: parents)
    (frontier : current.frontier = (control, inside, origins) :: pending)
    (calls : inside.calls = frame :: outside) (depth : frame.scopeDepth = source.2.scopes.length)
    (active : frame.phase = .nextArgument ∨ control.goals = []) :
    PettaOccurrenceOverlay.step original .eagerValue program (state source) =
      action (PettaOccurrenceOverlay.step (services original) .eagerValue program source) := by
  have mappedScopes : (state source).2.scopes = scope current :: parents.map scope := by
    change source.2.scopes.map scope = _
    rw [scopes, List.map_cons]
  have mappedFrontier : (scope current).frontier =
      (control, flatten inside, origins) :: pending.map work := by
    change current.frontier.map work = _
    rw [frontier, List.map_cons]
    rfl
  have mappedCalls : (flatten inside).calls = frame :: (outside ++ inside.user.calls) := by
    simp [flatten, calls]
  have level : frame.scopeDepth = parents.length + 1 := by simpa only [scopes, List.length_cons] using depth
  simp only [PettaOccurrenceOverlay.step, mappedScopes, mappedFrontier, mappedCalls,
    scopes, frontier, calls, List.length_cons, List.length_map, if_pos level]
  cases phase : frame.phase with
  | nextArgument => exact next_argument_commutes original source current parents control inside origins pending frame outside
  | argument formal slot =>
      have terminal : control.goals = [] := active.resolve_left (by simp [phase])
      simp only [terminal, List.isEmpty_nil, if_true]
      cases resolved : resolve control.bindings with
      | none => rfl
      | some environment =>
          exact argument_guard_commutes original source current parents control inside origins
            pending frame outside formal slot (read environment control.destination)
  | body =>
      have terminal : control.goals = [] := active.resolve_left (by simp [phase])
      simp only [terminal, List.isEmpty_nil, if_true]
      cases resolved : resolve control.bindings with
      | none => rfl
      | some environment =>
          exact result_guard_commutes original source current parents control inside origins
            pending frame outside (read environment control.destination)

theorem interior_step {User : Type} (original : Services User) (program : SpaceSemantics.Program)
    (source : LocalState User) (interior : boundary source = false) :
    PettaOccurrenceOverlay.step original .eagerValue program (state source) =
      action (PettaOccurrenceOverlay.step (services original) .eagerValue program source) := by
  cases scopes : source.2.scopes with
  | nil =>
      have mapped : (state source).2.scopes = [] := by
        change source.2.scopes.map scope = []
        rw [scopes, List.map_nil]
      simp only [PettaOccurrenceOverlay.step, mapped, scopes]
      exact source_owned .eagerValue program source
  | cons current parents =>
      have mappedScopes : (state source).2.scopes = scope current :: parents.map scope := by
        change source.2.scopes.map scope = _
        rw [scopes, List.map_cons]
      cases frontier : current.frontier with
      | nil =>
          have mapped : (scope current).frontier = [] := by
            change current.frontier.map work = []
            rw [frontier, List.map_nil]
          simp only [PettaOccurrenceOverlay.step, mappedScopes, scopes, mapped, frontier]
          exact source_owned .eagerValue program source
      | cons item pending =>
          rcases item with ⟨control, inside, origins⟩
          have mappedFrontier : (scope current).frontier =
              (control, flatten inside, origins) :: pending.map work := by
            change current.frontier.map work = _
            rw [frontier, List.map_cons]
            rfl
          cases calls : inside.calls with
          | nil =>
              cases inherited : inside.user.calls with
              | nil =>
                  have empty : (flatten inside).calls = [] := by simp [flatten, calls, inherited]
                  simp only [PettaOccurrenceOverlay.step, mappedScopes, scopes, mappedFrontier, frontier, calls, empty]
                  exact delegate_commutes original program source current parents control inside origins pending
              | cons frame outside =>
                  have mappedCalls : (flatten inside).calls = frame :: outside := by simp [flatten, calls, inherited]
                  by_cases depth : frame.scopeDepth = parents.length + 1
                  · cases phase : frame.phase with
                    | nextArgument => simp [boundary, scopes, frontier, calls, inherited, depth, phase] at interior
                    | argument formal slot | body =>
                        have running : control.goals.isEmpty = false := by
                          cases goals : control.goals with
                          | nil => simp [boundary, scopes, frontier, calls, inherited, depth, phase, goals] at interior
                          | cons first rest => rfl
                        simp only [PettaOccurrenceOverlay.step, mappedScopes, scopes, mappedFrontier, frontier,
                          calls, mappedCalls, List.length_cons, List.length_map, if_pos depth, phase, running]
                        exact delegate_commutes original program source current parents control inside origins pending
                  · simp only [PettaOccurrenceOverlay.step, mappedScopes, scopes, mappedFrontier, frontier,
                      calls, mappedCalls, List.length_cons, List.length_map, if_neg depth]
                    exact delegate_commutes original program source current parents control inside origins pending
          | cons frame outside =>
              have mappedCalls : (flatten inside).calls = frame :: (outside ++ inside.user.calls) := by
                simp [flatten, calls]
              by_cases depth : frame.scopeDepth = parents.length + 1
              · by_cases active : frame.phase = .nextArgument ∨ control.goals = []
                · exact active_owned_step original program source current parents control inside origins pending frame outside
                    scopes frontier calls (by simpa [scopes] using depth) active
                · have running : control.goals.isEmpty = false := by
                    cases goals : control.goals with
                    | nil => exact False.elim (active (.inr goals))
                    | cons first rest => rfl
                  simp only [PettaOccurrenceOverlay.step, mappedScopes, scopes, mappedFrontier, frontier,
                    calls, mappedCalls, List.length_cons, List.length_map, if_pos depth]
                  cases phase : frame.phase with
                  | nextArgument => exact False.elim (active (.inl phase))
                  | argument formal slot | body =>
                      simp only [running]
                      exact delegate_commutes original program source current parents control inside origins pending
              · simp only [PettaOccurrenceOverlay.step, mappedScopes, scopes, mappedFrontier, frontier,
                  calls, mappedCalls, List.length_cons, List.length_map, if_neg depth]
                exact delegate_commutes original program source current parents control inside origins pending

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaInheritedContext
