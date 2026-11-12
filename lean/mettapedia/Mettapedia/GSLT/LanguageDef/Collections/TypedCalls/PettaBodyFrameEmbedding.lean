import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaTypedReturnDelivery

/-!
# Carrying a saved body frame through region-local typed operations

The body services reserve the saved frame's operands. The full machine instead
sees those operands in its bottom typed frame. These two actual protection
operations agree; dropping the frame without reserving its operands need not
preserve fresh-name choices. Context and collection maps below retain all
controls, binding records, effects and occurrence coordinates.

This module establishes the representation and typed-operation connection.
`PettaBodySourceEmbedding` supplies the owned-source part, and
`PettaBodyRegionTransport` composes actual execution up to the retained terminal
checkpoint. Enclosing call entry and execution after that checkpoint remain
separate connections.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaBodyFrameEmbedding

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS.Destination
open PettaOccurrenceOverlay

def context {User : Type} (saved : CallFrame) (original : Context User) : Context User :=
  {original with calls := original.calls ++ [saved]}

def work {User : Type} (saved : CallFrame) (item : Work User) : Work User :=
  (item.1, context saved item.2.1, item.2.2)

def caller {User : Type} (saved : CallFrame) (original : CollectionCaller (Context User)) :
    CollectionCaller (Context User) :=
  (original.1, original.2.1, context saved original.2.2.1, original.2.2.2)

def scope {User : Type} (saved : CallFrame) (original : Scope User) : Scope User :=
  {original with frontier := original.frontier.map (work saved), caller := original.caller.map (caller saved)}

def state {User : Type} (saved : CallFrame) (source : State User) : State User :=
  (source.1, {source.2 with scopes := source.2.scopes.map (scope saved)})

def services {User : Type} (saved : CallFrame) (original : Services User) : Services User :=
  {original with userSupport := fun user => original.userSupport user ∪ operandSupport saved.atoms}

def action {User Request : Type} (saved : CallFrame) :
    Transition (State User) CollectedAnswer (State User) Request →
    Transition (State User) CollectedAnswer (State User) Request
  | .silent next => .silent (state saved next)
  | .publish events next => .publish events (state saved next)
  | .finish final => .finish (state saved final)
  | .call request retained => .call request (state saved retained)
  | .fail events => .fail events

theorem context_injective {User : Type} (saved : CallFrame) : Function.Injective (context (User := User) saved) := by
  intro first second same
  have users := congrArg Context.user same
  have calls := congrArg Context.calls same
  dsimp only [context] at users calls
  have originalCalls := List.append_cancel_right calls
  cases first
  cases second
  cases users
  cases originalCalls
  rfl

theorem state_world {User : Type} (saved : CallFrame) (source : State User) :
    (state saved source).1 = source.1 ∧ (state saved source).2.world = source.2.world := ⟨rfl, rfl⟩

theorem state_depth {User : Type} (saved : CallFrame) (source : State User) :
    (state saved source).2.scopes.length = source.2.scopes.length := by simp [state]

theorem scope_support {User : Type} (saved : CallFrame) (original : Scope User) :
    CollectionScope.support (scope saved original) = CollectionScope.support original := by
  simp only [CollectionScope.support, scope, List.foldr_map]
  congr 1
  cases original.caller <;> rfl

theorem state_support {User : Type} (saved : CallFrame) (source : State User) :
    collectionSupport (state saved source).2 = collectionSupport source.2 := by
  simp only [collectionSupport, state, List.foldr_map]
  congr 1
  funext original accumulated
  rw [scope_support]

theorem operand_support_append (first second : List Atom) :
    operandSupport (first ++ second) = operandSupport first ∪ operandSupport second := by
  induction first with
  | nil => simp [operandSupport]
  | cons value rest ih =>
      simp only [operandSupport, List.cons_append, List.foldr_cons] at ih ⊢
      rw [ih, Finset.union_assoc]

theorem context_support {User : Type} (saved : CallFrame) (original : Services User)
    (inside : Context User) :
    contextSupport original (context saved inside) = contextSupport (services saved original) inside := by
  simp only [contextSupport, context, services, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, operand_support_append]
  ac_rfl

theorem protect_commutes {User : Type} (saved : CallFrame) (original : Services User)
    (source : State User) (control : DControl) (inside : Context User) :
    protect original (state saved source) control (context saved inside) =
      protect (services saved original) source control inside := by
  simp only [protect, context_support, state_support]

theorem row_work_commutes {User : Type} (saved : CallFrame) (control : DControl)
    (inside : Context User) (origins : List Nat) (depth : Nat) (head : String)
    (arguments : List Atom) (destination : Atom) (older : List EagerDFS.Destination.Goal)
    (row : Row) (occurrence : Nat) :
    rowWork control (context saved inside) origins depth head arguments destination older row occurrence =
      work saved (rowWork control inside origins depth head arguments destination older row occurrence) := by
  rfl

theorem protected_row_work_commutes {User : Type} (saved : CallFrame) (original : Services User)
    (source : State User) (control : DControl) (inside : Context User) (origins : List Nat)
    (depth : Nat) (head : String) (arguments : List Atom) (destination : Atom)
    (older : List EagerDFS.Destination.Goal) (row : Row) (occurrence : Nat) :
    let full := rowWork control (context saved inside) origins depth head arguments destination older row occurrence
    let localWork := rowWork control inside origins depth head arguments destination older row occurrence
    (protect original (state saved source) full.1 full.2.1, full.2) =
      work saved (protect (services saved original) source localWork.1 localWork.2.1, localWork.2) := by
  simp only [row_work_commutes, work, protect_commutes]

theorem install_commutes {User : Type} (saved : CallFrame) (source : State User)
    (current : Scope User) (parents : List (Scope User)) (generated pending : List (Work User)) :
    install (state saved source) (scope saved current) (parents.map (scope saved))
      (generated.map (work saved)) (pending.map (work saved)) =
      state saved (install source current parents generated pending) := by
  simp [install, state, scope, List.map_append]

theorem guard_result_unchanged {User : Type} (saved : CallFrame) (original : Services User)
    (world : EagerDFS.World) (frame : CallFrame) (formal : Ty String) (value : Atom) (checked : Bool) :
    guardResult (services saved original) world frame formal value checked =
      guardResult original world frame formal value checked := rfl

theorem enter_rows_commutes {User : Type} (saved : CallFrame) (original : Services User)
    (source : State User) (current : Scope User) (parents : List (Scope User))
    (control : DControl) (inside : Context User) (origins : List Nat) (pending : List (Work User))
    (head : String) (arguments : List Atom) (destination : Atom) (older : List EagerDFS.Destination.Goal) :
    enterRows original (state saved source) (scope saved current) (parents.map (scope saved))
      control (context saved inside) origins (pending.map (work saved)) head arguments destination older =
      action saved (enterRows (services saved original) source current parents control inside origins pending
        head arguments destination older) := by
  cases selected : original.rows source.2.world inside.user head arguments with
  | unserved => simp [enterRows, state, context, services, selected, action]
  | untyped => simp [enterRows, state, context, services, selected, action]
  | typed rows =>
      simp only [enterRows, state, context, services, selected]
      split
      · simp only [action, install, state, scope, List.map_cons, List.map_append, List.map_map, List.length_map]
        congr 2
        apply congrArg (fun generated : List (Work User) =>
          (install source (scope saved current) (parents.map (scope saved)) generated (pending.map (work saved))).2)
        apply List.map_congr_left
        intro entry _member
        rcases entry with ⟨row, occurrence⟩
        simpa only [state, context, services, work, Function.comp_apply] using protected_row_work_commutes saved original source control
          inside origins source.2.scopes.length head arguments destination older row occurrence
      · simp only [action]
        rfl

theorem next_argument_commutes {User : Type} (saved : CallFrame) (original : Services User)
    (source : State User) (current : Scope User) (parents : List (Scope User))
    (control : DControl) (inside : Context User) (origins : List Nat) (pending : List (Work User))
    (frame : CallFrame) (outside : List CallFrame) :
    nextArgument original (state saved source) (scope saved current) (parents.map (scope saved))
      control (context saved inside) origins (pending.map (work saved)) frame (outside ++ [saved]) =
      action saved (nextArgument (services saved original) source current parents control inside origins pending frame outside) := by
  cases remaining : frame.remaining with
  | nil =>
      simp [nextArgument, remaining, action, install, state, scope, work, context]
      simpa only [context, state, remaining, List.cons_append] using protect_commutes saved original source _
        {inside with calls := {frame with phase := .body} :: outside}
  | cons parameter rest =>
      rcases parameter with ⟨formal, argument⟩
      by_cases raw : demand formal = .raw
      · simp [nextArgument, remaining, raw, action, install, state, scope, work, context]
        simpa only [context, state, List.cons_append] using protect_commutes saved original source control
          {inside with calls := {frame with remaining := rest, ready := frame.ready ++ [argument], index := frame.index + 1} :: outside}
      · simp only [nextArgument, remaining, if_neg raw, protect_commutes]
        simp [action, install, state, scope, work, context]
        let slot := Atom.var (freshName (protect (services saved original) source control inside) 0)
        let advanced : CallFrame := {frame with remaining := rest, phase := .argument formal slot}
        simpa only [context, state, List.cons_append, advanced, slot] using
          protect_commutes saved original source _ {inside with calls := advanced :: outside}

theorem argument_continuations_commute {User : Type} (saved : CallFrame) (original : Services User)
    (source : State User) (control : DControl) (inside : Context User) (origins : List Nat)
    (frame : CallFrame) (outside : List CallFrame) (slot : Atom) (stores : List Store) :
    argumentContinuations original (state saved source) control (context saved inside) origins
      frame (outside ++ [saved]) slot stores =
      (argumentContinuations (services saved original) source control inside origins frame outside slot stores).map
        (work saved) := by
  simp [argumentContinuations, List.map_map, work, context]
  intro store occurrence _member
  let advanced : CallFrame := {frame with
    ready := frame.ready ++ [slot]
    store := store
    index := frame.index + 1
    phase := .nextArgument}
  simpa only [context, List.cons_append, advanced] using
    protect_commutes saved original source control {inside with calls := advanced :: outside}

theorem argument_guard_commutes {User : Type} (saved : CallFrame) (original : Services User)
    (source : State User) (current : Scope User) (parents : List (Scope User))
    (control : DControl) (inside : Context User) (origins : List Nat) (pending : List (Work User))
    (frame : CallFrame) (outside : List CallFrame) (formal : Ty String) (slot value : Atom) :
    consumeArgument original (state saved source) (scope saved current) (parents.map (scope saved))
      control (context saved inside) origins (pending.map (work saved)) frame (outside ++ [saved]) formal slot value =
      action saved (consumeArgument (services saved original) source current parents control inside
        origins pending frame outside formal slot value) := by
  simp only [consumeArgument, guard_result_unchanged]
  cases delivered : guardResult original source.2.world frame formal value (demand formal == .guarded) with
  | none => simp [state, delivered, action]
  | some stores =>
      simp only [state_world, delivered]
      rw [argument_continuations_commute]
      exact congrArg Transition.silent (install_commutes saved source current parents _ pending)

theorem result_guard_commutes {User : Type} (saved : CallFrame) (original : Services User)
    (source : State User) (current : Scope User) (parents : List (Scope User))
    (control : DControl) (inside : Context User) (origins : List Nat) (pending : List (Work User))
    (frame : CallFrame) (outside : List CallFrame) (value : Atom) :
    consumeBody original (state saved source) (scope saved current) (parents.map (scope saved))
      control (context saved inside) origins (pending.map (work saved)) frame (outside ++ [saved]) value =
      action saved (consumeBody (services saved original) source current parents control inside origins pending frame outside value) := by
  simp only [consumeBody, guard_result_unchanged]
  cases delivered : guardResult original source.2.world frame frame.row.range value (decide (ResultGuarded frame.row.range)) with
  | none => simp [state, delivered, action]
  | some stores =>
      simp [state, delivered, action, install, scope, List.map_map, List.map_append, work, context]
      intro _store _occurrence _member
      exact protect_commutes saved original source (resumeCaller control frame) {inside with calls := outside}

/-- This is equality of the actual overlay steps while an inner typed phase
owns the active control. The bottom frame remains present in the full machine.
Ordinary source delegation is deliberately not assumed to commute here. -/
theorem active_typed_step_commutes {User : Type} (saved : CallFrame) (original : Services User)
    (program : SpaceSemantics.Program) (source : State User)
    (current : Scope User) (parents : List (Scope User))
    (control : DControl) (inside : Context User) (origins : List Nat) (pending : List (Work User))
    (frame : CallFrame) (outside : List CallFrame)
    (scopes : source.2.scopes = current :: parents)
    (frontier : current.frontier = (control, inside, origins) :: pending)
    (calls : inside.calls = frame :: outside)
    (depth : frame.scopeDepth = source.2.scopes.length)
    (active : frame.phase = .nextArgument ∨ control.goals = []) :
    PettaOccurrenceOverlay.step original .eagerValue program (state saved source) =
      action saved (PettaOccurrenceOverlay.step (services saved original) .eagerValue program source) := by
  have mappedScopes : (state saved source).2.scopes = scope saved current :: parents.map (scope saved) := by
    simp [state, scopes]
  have mappedFrontier : (scope saved current).frontier =
      (control, context saved inside, origins) :: pending.map (work saved) := by
    simp [scope, frontier, work]
  have mappedCalls : (context saved inside).calls = frame :: (outside ++ [saved]) := by
    simp [context, calls]
  have level : frame.scopeDepth = parents.length + 1 := by simpa only [scopes, List.length_cons] using depth
  simp only [PettaOccurrenceOverlay.step, mappedScopes, mappedFrontier, mappedCalls,
    scopes, frontier, calls, List.length_cons, List.length_map, if_pos level]
  cases phase : frame.phase with
  | nextArgument => exact next_argument_commutes saved original source current parents control inside origins pending frame outside
  | argument formal slot =>
      have terminal : control.goals = [] := active.resolve_left (by simp [phase])
      simp only [terminal, List.isEmpty_nil, if_true]
      cases resolved : resolve control.bindings with
      | none => rfl
      | some environment =>
          exact argument_guard_commutes saved original source current parents control inside origins pending frame outside
            formal slot (read environment control.destination)
  | body =>
      have terminal : control.goals = [] := active.resolve_left (by simp [phase])
      simp only [terminal, List.isEmpty_nil, if_true]
      cases resolved : resolve control.bindings with
      | none => rfl
      | some environment =>
          exact result_guard_commutes saved original source current parents control inside origins pending frame outside
            (read environment control.destination)

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaBodyFrameEmbedding
