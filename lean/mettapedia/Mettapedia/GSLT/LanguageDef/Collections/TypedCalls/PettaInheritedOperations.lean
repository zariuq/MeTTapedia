import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaInheritedContext

/-!
# Actual typed operations under an inherited caller context

An owned frame is pushed or popped only in the local prefix. Flattening keeps
the inherited suffix, and the local protection service accounts for its
operands. Every operation below is the existing occurrence overlay operation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaInheritedContext

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS.Destination
open PettaOccurrenceOverlay

theorem row_work_commutes {User : Type} (control : DControl) (inside : Context (Context User))
    (origins : List Nat) (depth : Nat) (head : String) (arguments : List Atom)
    (destination : Atom) (older : List EagerDFS.Destination.Goal) (row : Row) (occurrence : Nat) :
    rowWork control (flatten inside) origins depth head arguments destination older row occurrence =
      work (rowWork control inside origins depth head arguments destination older row occurrence) := rfl

theorem protected_row_work_commutes {User : Type} (original : Services User) (source : LocalState User)
    (control : DControl) (inside : Context (Context User)) (origins : List Nat) (depth : Nat)
    (head : String) (arguments : List Atom) (destination : Atom) (older : List EagerDFS.Destination.Goal)
    (row : Row) (occurrence : Nat) :
    let full := rowWork control (flatten inside) origins depth head arguments destination older row occurrence
    let insideWork := rowWork control inside origins depth head arguments destination older row occurrence
    (protect original (state source) full.1 full.2.1, full.2) =
      work (protect (services original) source insideWork.1 insideWork.2.1, insideWork.2) := by
  simp only [row_work_commutes, work, Bridges.DestinationContextMap.work, protect_commutes]

theorem enter_rows_commutes {User : Type} (original : Services User) (source : LocalState User)
    (current : Scope (Context User)) (parents : List (Scope (Context User)))
    (control : DControl) (inside : Context (Context User)) (origins : List Nat)
    (pending : List (Work (Context User))) (head : String) (arguments : List Atom)
    (destination : Atom) (older : List EagerDFS.Destination.Goal) :
    enterRows original (state source) (scope current) (parents.map scope) control (flatten inside)
      origins (pending.map work) head arguments destination older =
      action (enterRows (services original) source current parents control inside origins pending
        head arguments destination older) := by
  cases selected : original.rows source.2.world inside.user.user head arguments with
  | unserved => simp [enterRows, state, Bridges.DestinationContextMap.state,
      Bridges.DestinationContextMap.configuration, flatten, services, selected, action]
  | untyped => simp [enterRows, state, Bridges.DestinationContextMap.state,
      Bridges.DestinationContextMap.configuration, flatten, services, selected, action]
  | typed rows =>
      simp only [enterRows, state_world, flatten, services, selected]
      split
      · rw [state_depth]
        simp only [action]
        rw [← install_commutes]
        apply congrArg (fun generated : List (Work User) =>
          Transition.silent (install (state source) (scope current) (parents.map scope) generated (pending.map work)))
        rw [List.map_map]
        apply List.map_congr_left
        intro entry _member
        rcases entry with ⟨row, occurrence⟩
        exact protected_row_work_commutes original source control inside origins
          source.2.scopes.length head arguments destination older row occurrence
      · rfl

theorem guard_result_unchanged {User : Type} (original : Services User)
    (world : EagerDFS.World) (frame : CallFrame) (formal : Ty String) (value : Atom) (checked : Bool) :
    guardResult (services original) world frame formal value checked =
      guardResult original world frame formal value checked := rfl

theorem next_argument_commutes {User : Type} (original : Services User) (source : LocalState User)
    (current : Scope (Context User)) (parents : List (Scope (Context User))) (control : DControl)
    (inside : Context (Context User)) (origins : List Nat) (pending : List (Work (Context User)))
    (frame : CallFrame) (outside : List CallFrame) :
    nextArgument original (state source) (scope current) (parents.map scope) control (flatten inside)
      origins (pending.map work) frame (outside ++ inside.user.calls) =
      action (nextArgument (services original) source current parents control inside origins pending frame outside) := by
  cases remaining : frame.remaining with
  | nil =>
      simp [nextArgument, remaining, action, install, state, scope, work, flatten,
        Bridges.DestinationContextMap.state, Bridges.DestinationContextMap.configuration,
        Bridges.DestinationContextMap.scope, Bridges.DestinationContextMap.work]
      simpa only [flatten, state, Bridges.DestinationContextMap.state,
        Bridges.DestinationContextMap.configuration, remaining, List.cons_append] using protect_commutes original source _
        {inside with calls := {frame with phase := .body} :: outside}
  | cons parameter rest =>
      rcases parameter with ⟨formal, argument⟩
      by_cases raw : demand formal = .raw
      · simp [nextArgument, remaining, raw, action, install, state, scope, work, flatten,
          Bridges.DestinationContextMap.state, Bridges.DestinationContextMap.configuration,
          Bridges.DestinationContextMap.scope, Bridges.DestinationContextMap.work]
        simpa only [flatten, state, Bridges.DestinationContextMap.state,
          Bridges.DestinationContextMap.configuration, List.cons_append] using protect_commutes original source control
          {inside with calls := {frame with remaining := rest, ready := frame.ready ++ [argument], index := frame.index + 1} :: outside}
      · simp only [nextArgument, remaining, if_neg raw, protect_commutes]
        simp [action, install, state, scope, work, flatten, Bridges.DestinationContextMap.state,
          Bridges.DestinationContextMap.configuration, Bridges.DestinationContextMap.scope,
          Bridges.DestinationContextMap.work]
        let slot := Atom.var (freshName (protect (services original) source control inside) 0)
        let advanced : CallFrame := {frame with remaining := rest, phase := .argument formal slot}
        simpa only [flatten, state, Bridges.DestinationContextMap.state,
          Bridges.DestinationContextMap.configuration, List.cons_append, advanced, slot] using
          protect_commutes original source _ {inside with calls := advanced :: outside}

theorem argument_continuations_commute {User : Type} (original : Services User) (source : LocalState User)
    (control : DControl) (inside : Context (Context User)) (origins : List Nat)
    (frame : CallFrame) (outside : List CallFrame) (slot : Atom) (stores : List Store) :
    argumentContinuations original (state source) control (flatten inside) origins
      frame (outside ++ inside.user.calls) slot stores =
      (argumentContinuations (services original) source control inside origins frame outside slot stores).map work := by
  simp [argumentContinuations, List.map_map, work, Bridges.DestinationContextMap.work, flatten]
  intro store occurrence _member
  let advanced : CallFrame := {frame with
    ready := frame.ready ++ [slot]
    store := store
    index := frame.index + 1
    phase := .nextArgument}
  simpa only [flatten, List.cons_append, advanced] using
    protect_commutes original source control {inside with calls := advanced :: outside}

theorem argument_guard_commutes {User : Type} (original : Services User) (source : LocalState User)
    (current : Scope (Context User)) (parents : List (Scope (Context User))) (control : DControl)
    (inside : Context (Context User)) (origins : List Nat) (pending : List (Work (Context User)))
    (frame : CallFrame) (outside : List CallFrame) (formal : Ty String) (slot value : Atom) :
    consumeArgument original (state source) (scope current) (parents.map scope) control (flatten inside)
      origins (pending.map work) frame (outside ++ inside.user.calls) formal slot value =
      action (consumeArgument (services original) source current parents control inside origins pending
        frame outside formal slot value) := by
  simp only [consumeArgument, guard_result_unchanged]
  cases delivered : guardResult original source.2.world frame formal value (demand formal == .guarded) with
  | none => simp [state, Bridges.DestinationContextMap.state,
      Bridges.DestinationContextMap.configuration, delivered, action]
  | some stores =>
      simp only [state_world, delivered]
      rw [argument_continuations_commute]
      exact congrArg Transition.silent (install_commutes source current parents _ pending)

theorem result_guard_commutes {User : Type} (original : Services User) (source : LocalState User)
    (current : Scope (Context User)) (parents : List (Scope (Context User))) (control : DControl)
    (inside : Context (Context User)) (origins : List Nat) (pending : List (Work (Context User)))
    (frame : CallFrame) (outside : List CallFrame) (value : Atom) :
    consumeBody original (state source) (scope current) (parents.map scope) control (flatten inside)
      origins (pending.map work) frame (outside ++ inside.user.calls) value =
      action (consumeBody (services original) source current parents control inside origins pending frame outside value) := by
  simp only [consumeBody, guard_result_unchanged]
  cases delivered : guardResult original source.2.world frame frame.row.range value
      (decide (ResultGuarded frame.row.range)) with
  | none => simp [state, Bridges.DestinationContextMap.state,
      Bridges.DestinationContextMap.configuration, delivered, action]
  | some stores =>
      simp [state, Bridges.DestinationContextMap.state, Bridges.DestinationContextMap.configuration,
        delivered, action, install, scope, Bridges.DestinationContextMap.scope, List.map_map,
        List.map_append, work, Bridges.DestinationContextMap.work, flatten]
      intro _store _occurrence _member
      exact protect_commutes original source (resumeCaller control frame) {inside with calls := outside}

theorem delegate_commutes {User : Type} (original : Services User) (program : SpaceSemantics.Program)
    (source : LocalState User) (current : Scope (Context User)) (parents : List (Scope (Context User)))
    (control : DControl) (inside : Context (Context User)) (origins : List Nat)
    (pending : List (Work (Context User))) :
    delegate original .eagerValue program (state source) (scope current) (parents.map scope)
      control (flatten inside) origins (pending.map work) =
      action (delegate (services original) .eagerValue program source current parents control inside origins pending) := by
  have rows : original.rows (state source).2.world (flatten inside).user =
      (services original).rows source.2.world inside.user := rfl
  unfold delegate
  simp only [rows]
  repeat' first
    | exact source_owned .eagerValue program source
    | exact enter_rows_commutes original source current parents control inside origins pending _ _ _ _
    | split

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaInheritedContext
