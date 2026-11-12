import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCompoundReturnFrames
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSelectedReturnBoundary
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationDataReturnRun
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCompoundReturnScopes
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaReturnMarkDepth

/-!
# Earned compound returns enter the existing typed result boundary

At the actual terminal output slot, the compound source invariant supplies
the earlier selected-frame view. The actual host then runs its existing
solver and result guard, with the reached world, record and caller suffix.
No boundary protocol, frame layout or evaluator is replaced.

Source-prefix composition below is for the maintained owned source-body
region. It does not identify that region with native optimized execution or
with a host body that intercepts additional typed prefix calls.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCompoundReturnBoundary

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open EagerDFS.Destination
open PettaOccurrenceOverlay

/-- All fields refer to the same reached host. The variable names its actual
output slot, not a substitute for the matched compound input pattern. -/
def view {User : Type} (program : SpaceSemantics.Program) (saved : CallFrame) (argument : Atom) (source : State User)
    (current : Scope User) (parents : List (Scope User)) (control : DControl) (context : Context User)
    (origins : List Nat) (pending : List (Work User)) (outside : List CallFrame)
    (scopes : source.2.scopes = current :: parents)
    (frontier : current.frontier = (control, context, origins) :: pending)
    (calls : context.calls = saved :: outside) (depth : saved.scopeDepth = source.2.scopes.length)
    (phase : saved.phase = .body) (terminal : control.goals = []) (name : String)
    (slot : control.destination = .var name)
    (earned : Bridges.DestinationDataReturnState.AliasHolds program argument control) :
    PettaSelectedReturnBoundary.View saved argument source :=
  ⟨current, parents, control, context, origins, pending, outside, scopes, frontier, calls, depth, phase, terminal,
    PettaSelectedReturnWork.at_head saved argument (control, context, origins) outside calls
      (Bridges.DestinationDataReturnState.terminal_slot_alias earned terminal name slot)⟩

theorem dispatch {User : Type} (program : SpaceSemantics.Program) (saved : CallFrame) (argument : Atom)
    (operations : Services User) (source : State User) (current : Scope User) (parents : List (Scope User))
    (control : DControl) (context : Context User) (origins : List Nat) (pending : List (Work User)) (outside : List CallFrame)
    (scopes : source.2.scopes = current :: parents)
    (frontier : current.frontier = (control, context, origins) :: pending)
    (calls : context.calls = saved :: outside) (depth : saved.scopeDepth = source.2.scopes.length)
    (phase : saved.phase = .body) (terminal : control.goals = []) (name : String)
    (slot : control.destination = .var name)
    (earned : Bridges.DestinationDataReturnState.AliasHolds program argument control) :
    PettaOccurrenceOverlay.step operations .eagerValue program source =
      match resolve control.bindings with
      | none => .call (.source (.branch .invalidEnvironment)) source
      | some environment => consumeBody operations source current parents control context origins pending saved outside
          (read environment argument) :=
  PettaSelectedReturnBoundary.dispatch operations program source
    (view program saved argument source current parents control context origins pending outside scopes frontier calls
      depth phase terminal name slot earned)

theorem served_guard_exact {User : Type} (program : SpaceSemantics.Program) (saved : CallFrame) (argument : Atom)
    (operations : Services User) (source : State User) (current : Scope User) (parents : List (Scope User))
    (control : DControl) (context : Context User) (origins : List Nat) (pending : List (Work User)) (outside : List CallFrame)
    (scopes : source.2.scopes = current :: parents)
    (frontier : current.frontier = (control, context, origins) :: pending)
    (calls : context.calls = saved :: outside) (depth : saved.scopeDepth = source.2.scopes.length)
    (phase : saved.phase = .body) (terminal : control.goals = []) (name : String)
    (slot : control.destination = .var name)
    (earned : Bridges.DestinationDataReturnState.AliasHolds program argument control)
    (environment : Environment) (resolved : resolve control.bindings = some environment) (stores : List Store)
    (served : guardResult operations source.2.world saved saved.row.range (read environment argument)
      (decide (ResultGuarded saved.row.range)) = some stores) :
    let generated := PettaTypedReturnDelivery.continuations operations source control context origins saved outside stores
    PettaOccurrenceOverlay.step operations .eagerValue program source =
        .silent (install source current parents generated pending) ∧
      ((generated.map fun _ => read environment argument : List Atom) : Multiset Atom) =
        resultGuard (operations.declarations source.2.world) (operations.kind source.2.world)
          saved.index saved.row.range saved.store (read environment argument) ∧
      generated.map (fun item => (item.1.bindings, item.1.goals, item.1.destination, item.1.cutBoundary,
        item.2.1.calls, item.2.2)) =
      stores.zipIdx.map (fun (_, occurrence) =>
        (control.bindings, saved.callerGoals, saved.callerDestination, saved.callerCutBoundary,
          outside, origins ++ [occurrence])) :=
  PettaSelectedReturnBoundary.served_guard_exact operations program source
    (view program saved argument source current parents control context origins pending outside scopes frontier calls
      depth phase terminal name slot earned) environment resolved stores served

/-- The prefix is an observed finite source run, not a promised successful
body. Its retained source obligation follows from the all-budget theorem. -/
theorem source_prefix_alias {User : Type} (program : SpaceSemantics.Program) (argument : Atom)
    (fuel : Nat) (source final : State User)
    (initial : Bridges.DestinationDataReturnRun.CursorGood program (fun _ : Context User => argument) source)
    (reached : ((Bridges.ScopedQuerySource.ownedMachine .eagerValue program).run fuel source).2 = .exhausted final)
    (current : Scope User) (control : DControl) (context : Context User) (origins : List Nat) (pending : List (Work User))
    (scopes : final.2.scopes = [current]) (frontier : current.frontier = (control, context, origins) :: pending) :
    Bridges.DestinationDataReturnState.AliasHolds program argument control := by
  have retained := Bridges.DestinationDataReturnRun.run_retains_obligation (fun _ : Context User => argument)
    program fuel source initial
  rw [reached] at retained
  have root := (scopes ▸ retained.2).root_work (control, context, origins) (frontier ▸ List.mem_cons_self)
  exact root

theorem source_prefix_dispatch {User : Type} (program : SpaceSemantics.Program) (saved : CallFrame) (argument : Atom)
    (operations : Services User) (fuel : Nat) (source final : State User)
    (initial : Bridges.DestinationDataReturnRun.CursorGood program (fun _ : Context User => argument) source)
    (reached : ((Bridges.ScopedQuerySource.ownedMachine .eagerValue program).run fuel source).2 = .exhausted final)
    (current : Scope User) (control : DControl) (context : Context User) (origins : List Nat) (pending : List (Work User))
    (outside : List CallFrame) (scopes : final.2.scopes = [current])
    (frontier : current.frontier = (control, context, origins) :: pending)
    (calls : context.calls = saved :: outside) (depth : saved.scopeDepth = final.2.scopes.length)
    (phase : saved.phase = .body) (terminal : control.goals = []) (name : String)
    (slot : control.destination = .var name) :
    PettaOccurrenceOverlay.step operations .eagerValue program final =
      match resolve control.bindings with
      | none => .call (.source (.branch .invalidEnvironment)) final
      | some environment => consumeBody operations final current [] control context origins pending saved outside
          (read environment argument) :=
  dispatch program saved argument operations final current [] control context origins pending outside scopes frontier
    calls depth phase terminal name slot
    (source_prefix_alias program argument fuel source final initial reached current control context origins pending scopes frontier)

/-- A physical position-zero mark derives the actual owning depth and guard
input. The output destination may be any Atom; no variable surrogate or
ghost equation is required. Solver failure remains the original request. -/
theorem marked_dispatch {User : Type} (program : SpaceSemantics.Program) (saved : CallFrame) (argument : Atom)
    (operations : Services User) (source : State User) (current : Scope User) (parents : List (Scope User))
    (control : DControl) (context : Context User) (origins : List Nat) (pending : List (Work User))
    (pendingMarks : List (Option Nat)) (callerMark : Option Nat) (parentMarks : List PettaSelectedReturnScopes.Marks)
    (held : PettaCompoundReturnScopes.Stack program saved argument
      (⟨some 0 :: pendingMarks, callerMark⟩ :: parentMarks) source.2.scopes)
    (depths : PettaReturnMarkDepth.Depths saved.scopeDepth (⟨some 0 :: pendingMarks, callerMark⟩ :: parentMarks))
    (scopes : source.2.scopes = current :: parents)
    (frontier : current.frontier = (control, context, origins) :: pending)
    (phase : saved.phase = .body) (terminal : control.goals = []) :
    ∃ outside, context.calls = saved :: outside ∧
      PettaOccurrenceOverlay.step operations .eagerValue program source =
        match resolve control.bindings with
        | none => .call (.source (.branch .invalidEnvironment)) source
        | some environment => consumeBody operations source current parents control context origins pending saved outside
            (read environment argument) := by
  have depth := PettaReturnMarkDepth.source_owner_of_stack source _ parentMarks held depths 0 List.mem_cons_self
  have selected := PettaScopeMarks.active_work current control context origins pending 0 pendingMarks callerMark
    (List.forall₂_cons.mp (scopes ▸ held)).1 frontier
  obtain ⟨above, outside, length, calls, returning⟩ := selected
  have empty : above = [] := List.eq_nil_of_length_eq_zero length
  subst above
  change context.calls = saved :: outside at calls
  change Bridges.DestinationDataReturnState.AliasHolds program argument control at returning
  refine ⟨outside, calls, ?_⟩
  cases resolved : resolve control.bindings with
  | none =>
      have actualDepth : saved.scopeDepth = (current :: parents).length := by simpa only [scopes] using depth
      simp only [PettaOccurrenceOverlay.step, scopes, frontier, calls, if_pos actualDepth, phase, terminal,
        List.isEmpty_nil, ↓reduceIte, resolved]
  | some environment =>
      have value := Bridges.DestinationDataReturnState.terminal_alias_observation returning terminal environment resolved
      have actual := terminal_body_step operations .eagerValue program source current parents control context origins pending
        saved outside environment scopes frontier calls depth phase terminal resolved
      simpa only [value] using actual

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCompoundReturnBoundary
