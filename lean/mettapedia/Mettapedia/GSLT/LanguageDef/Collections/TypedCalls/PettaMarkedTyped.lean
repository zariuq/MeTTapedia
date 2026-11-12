import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaMarkedTransitions
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSelectedFrameTransport

/-!
# Actual typed operations preserve computed positional marks

The work invariant is a parameter with independently discharged frame laws.
Row capture pushes a selected position, argument phases keep it, inner
returns pop it, and a returned selected frame retires its mark. The guard
and generated continuations are the existing host operations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaMarkedTyped

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open EagerDFS.Destination
open PettaOccurrenceOverlay
open PettaSelectedReturnScopes (Marks)
open PettaScopeMarks (WorkMarked Stack)
open PettaReturnMarkUpdate
open PettaMarkedTransitions (Preserves install_keeps call_keeps same_count_generated)

theorem protect_marked {User : Type} {Held : Nat → Work User → Prop} (laws : PettaSelectedFrameTransport.Laws Held)
    {mark : Option Nat} {item : Work User} (held : WorkMarked Held mark item)
    (operations : Services User) (source : State User) :
    WorkMarked Held mark (protect operations source item.1 item.2.1, item.2) :=
  fun index selected => laws.protect (held index selected) operations source

theorem origins_marked {User : Type} {Held : Nat → Work User → Prop} (laws : PettaSelectedFrameTransport.Laws Held)
    {mark : Option Nat} {control : DControl} {context : Context User} {origins : List Nat}
    (held : WorkMarked Held mark (control, context, origins)) (suffix : List Nat) :
    WorkMarked Held mark (control, context, origins ++ suffix) :=
  fun index selected => laws.extendOrigins (held index selected) suffix

theorem updated_frame_marked {User : Type} {Held : Nat → Work User → Prop} (laws : PettaSelectedFrameTransport.Laws Held)
    {mark : Option Nat} (control : DControl) (context : Context User) (origins : List Nat)
    (frame : CallFrame) (outside : List CallFrame) (held : WorkMarked Held mark (control, context, origins))
    (notSelected : mark ≠ some 0) (calls : context.calls = frame :: outside) (after : DControl) (updated : CallFrame)
    (extended : RefinementTransport.Extends control.bindings after.bindings)
    (goals : updated.callerGoals = frame.callerGoals) (destination : updated.callerDestination = frame.callerDestination) :
    WorkMarked Held mark (after, {context with calls := updated :: outside}, origins) := by
  intro index selected
  cases index with
  | zero => exact (notSelected selected).elim
  | succ index =>
      exact laws.update control context origins frame outside (held (index + 1) selected)
        calls after updated extended goals destination

theorem rows_keeps {User : Type} {Held : Nat → Work User → Prop} (laws : PettaSelectedFrameTransport.Laws Held)
    (operations : Services User) (source : State User) (current : Scope User) (parents : List (Scope User))
    (control : DControl) (context : Context User) (origins : List Nat) (pending : List (Work User))
    (mark : Option Nat) (pendingMarks : List (Option Nat)) (callerMark : Option Nat) (parentMarks : List Marks)
    (head : String) (arguments : List Atom) (destination : Atom) (older : List EagerDFS.Destination.Goal)
    (held : Stack Held (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks) source.2.scopes)
    (scopes : source.2.scopes = current :: parents) (front : current.frontier = (control, context, origins) :: pending)
    (atCall : control.goals = .evaluate (.expression (.symbol head :: arguments)) destination :: older)
    (capture : ∀ index, Held index (control, context, origins) → ∀ row occurrence,
      Held (index + 1) (rowWork control context origins source.2.scopes.length head arguments destination older row occurrence)) :
    Preserves Held (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks) source
      (enterRows operations source current parents control context origins pending head arguments destination older) := by
  unfold enterRows
  split
  · exact call_keeps _ source _ held
  · exact call_keeps _ source _ held
  · dsimp only
    split
    · apply install_keeps source current parents (control, context, origins) pending _ mark pendingMarks callerMark parentMarks
        held scopes front (.inr (by intro tail same; rw [atCall] at same; cases same))
      intro active item member
      obtain ⟨⟨row, occurrence⟩, present, rfl⟩ := List.mem_map.mp member
      intro index selected
      cases mark with
      | none => cases selected
      | some position =>
          have shifted := shift_push context.calls.length position
          change shift context.calls.length (context.calls.length + 1) (some position) = some index at selected
          have same := Option.some.inj (shifted.symm.trans selected)
          subst index
          exact laws.protect (capture position (active position rfl) row occurrence) operations source
    · exact call_keeps _ source _ held

theorem next_argument_keeps {User : Type} {Held : Nat → Work User → Prop} (laws : PettaSelectedFrameTransport.Laws Held)
    (operations : Services User) (source : State User) (current : Scope User) (parents : List (Scope User))
    (control : DControl) (context : Context User) (origins : List Nat) (pending : List (Work User))
    (mark : Option Nat) (pendingMarks : List (Option Nat)) (callerMark : Option Nat) (parentMarks : List Marks)
    (frame : CallFrame) (outside : List CallFrame)
    (held : Stack Held (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks) source.2.scopes)
    (scopes : source.2.scopes = current :: parents) (front : current.frontier = (control, context, origins) :: pending)
    (calls : context.calls = frame :: outside) (depth : frame.scopeDepth = source.2.scopes.length)
    (phase : frame.phase = .nextArgument) (notSelected : mark ≠ some 0) :
    Preserves Held (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks) source
      (nextArgument operations source current parents control context origins pending frame outside) := by
  have activeFrame := frame_active_at source current parents control context origins pending frame outside
    scopes front calls depth (.inl phase)
  cases remaining : frame.remaining with
  | nil =>
      simp only [nextArgument, remaining]
      apply install_keeps source current parents (control, context, origins) pending _ mark pendingMarks callerMark parentMarks
        held scopes front (.inl activeFrame)
      intro active
      apply same_count_generated (Held := Held) (control, context, origins) [(_, _, _)] mark
      · intro item member; cases List.mem_singleton.mp member; simp only [calls, List.length_cons]
      · intro index selected item member
        cases List.mem_singleton.mp member
        exact protect_marked laws (updated_frame_marked laws control context origins frame outside active notSelected calls
          {control with goals := [.invoke frame.head frame.ready frame.callDestination], destination := frame.callDestination}
          {frame with remaining := [], phase := .body} (.refl _) rfl rfl) operations source index selected
  | cons parameter rest =>
      rcases parameter with ⟨formal, value⟩
      by_cases raw : demand formal = .raw
      · simp only [nextArgument, remaining, if_pos raw]
        apply install_keeps source current parents (control, context, origins) pending _ mark pendingMarks callerMark parentMarks
          held scopes front (.inl activeFrame)
        intro active
        apply same_count_generated (Held := Held) (control, context, origins) [(_, _, _)] mark
        · intro item member; cases List.mem_singleton.mp member; simp only [calls, List.length_cons]
        · intro index selected item member
          cases List.mem_singleton.mp member
          exact protect_marked laws (updated_frame_marked laws control context origins frame outside active notSelected calls control
            {frame with remaining := rest, ready := frame.ready ++ [value], index := frame.index + 1}
            (.refl _) rfl rfl) operations source index selected
      · simp only [nextArgument, remaining, if_neg raw]
        apply install_keeps source current parents (control, context, origins) pending _ mark pendingMarks callerMark parentMarks
          held scopes front (.inl activeFrame)
        intro active
        apply same_count_generated (Held := Held) (control, context, origins) [(_, _, _)] mark
        · intro item member; cases List.mem_singleton.mp member; simp only [calls, List.length_cons]
        · intro index selected item member
          cases List.mem_singleton.mp member
          let prepared := protect operations source control context
          let slot := Atom.var (freshName prepared 0)
          exact protect_marked laws (updated_frame_marked laws control context origins frame outside active notSelected calls
            {prepared with goals := [.evaluate value slot], destination := slot}
            {frame with remaining := rest, phase := .argument formal slot} (.refl _) rfl rfl) operations source index selected

theorem argument_guard_keeps {User : Type} {Held : Nat → Work User → Prop} (laws : PettaSelectedFrameTransport.Laws Held)
    (operations : Services User) (source : State User) (current : Scope User) (parents : List (Scope User))
    (control : DControl) (context : Context User) (origins : List Nat) (pending : List (Work User))
    (mark : Option Nat) (pendingMarks : List (Option Nat)) (callerMark : Option Nat) (parentMarks : List Marks)
    (frame : CallFrame) (outside : List CallFrame) (formal : Ty String) (slot value : Atom)
    (held : Stack Held (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks) source.2.scopes)
    (scopes : source.2.scopes = current :: parents) (front : current.frontier = (control, context, origins) :: pending)
    (calls : context.calls = frame :: outside) (depth : frame.scopeDepth = source.2.scopes.length)
    (terminal : control.goals = []) (notSelected : mark ≠ some 0) :
    Preserves Held (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks) source
      (consumeArgument operations source current parents control context origins pending frame outside formal slot value) := by
  have activeFrame := frame_active_at source current parents control context origins pending frame outside
    scopes front calls depth (.inr terminal)
  unfold consumeArgument
  split
  · exact call_keeps _ source _ held
  · apply install_keeps source current parents (control, context, origins) pending _ mark pendingMarks callerMark parentMarks
      held scopes front (.inl activeFrame)
    intro active
    apply same_count_generated (Held := Held) (control, context, origins) _ mark
    · intro item member
      obtain ⟨⟨store, occurrence⟩, present, rfl⟩ := List.mem_map.mp member
      simp only [calls, List.length_cons]
    · intro index selected item member
      obtain ⟨⟨store, occurrence⟩, present, rfl⟩ := List.mem_map.mp member
      exact protect_marked laws (updated_frame_marked laws control context (origins ++ [occurrence]) frame outside
        (origins_marked laws active [occurrence]) notSelected calls control
        {frame with ready := frame.ready ++ [slot], store := store, index := frame.index + 1, phase := .nextArgument}
        (.refl _) rfl rfl) operations source index selected

theorem body_guard_keeps {User : Type} {Held : Nat → Work User → Prop} (laws : PettaSelectedFrameTransport.Laws Held)
    (operations : Services User) (source : State User) (current : Scope User) (parents : List (Scope User))
    (control : DControl) (context : Context User) (origins : List Nat) (pending : List (Work User))
    (mark : Option Nat) (pendingMarks : List (Option Nat)) (callerMark : Option Nat) (parentMarks : List Marks)
    (frame : CallFrame) (outside : List CallFrame) (value : Atom)
    (held : Stack Held (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks) source.2.scopes)
    (scopes : source.2.scopes = current :: parents) (front : current.frontier = (control, context, origins) :: pending)
    (calls : context.calls = frame :: outside) (depth : frame.scopeDepth = source.2.scopes.length) (terminal : control.goals = []) :
    Preserves Held (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks) source
      (consumeBody operations source current parents control context origins pending frame outside value) := by
  have activeFrame := frame_active_at source current parents control context origins pending frame outside
    scopes front calls depth (.inr terminal)
  unfold consumeBody
  split
  · exact call_keeps _ source _ held
  · apply install_keeps source current parents (control, context, origins) pending _ mark pendingMarks callerMark parentMarks
      held scopes front (.inl activeFrame)
    intro active item member
    obtain ⟨⟨store, occurrence⟩, present, rfl⟩ := List.mem_map.mp member
    intro index selected
    cases mark with
    | none => cases selected
    | some position =>
        change shift context.calls.length outside.length (some position) = some index at selected
        rw [calls] at selected
        simp only [List.length_cons] at selected
        cases position with
        | zero => rw [shift_retires_zero] at selected; cases selected
        | succ position =>
            rw [shift_pop] at selected
            have same := Option.some.inj selected
            subst index
            exact laws.protect (laws.pop control context (origins ++ [occurrence]) frame outside
              (laws.extendOrigins (active (position + 1) rfl) [occurrence]) calls) operations source

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaMarkedTyped
