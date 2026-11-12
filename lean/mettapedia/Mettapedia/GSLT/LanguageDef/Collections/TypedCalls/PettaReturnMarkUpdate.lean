import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaScopeMarks
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaInheritedStep

/-!
# Positional mark updates read actual transition results

The update neither evaluates source expressions nor calls semantic services.
It reads the reached frontiers and frame counts. Ordinary work keeps its
position; an owned row pushes it; an inner return pops it. Removing the
selected position retires its mark. Separate semantic laws must justify the
retirement as the actual selected return boundary.

Collection push/pop and cut filtering keep the physical occurrence layout.
This metadata function is not, by itself, a correctness certificate for a
source or native transition.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaReturnMarkUpdate

open Mettapedia.Languages.MeTTa.PeTTa
open EagerDFS.Destination
open PettaOccurrenceOverlay
open PettaSelectedReturnScopes (Marks)

def shift (oldCount newCount : Nat) : Option Nat → Option Nat
  | none => none
  | some index => if index + newCount < oldCount then none else some (index + newCount - oldCount)

theorem shift_none (oldCount newCount : Nat) : shift oldCount newCount none = none := rfl

theorem shift_keeps (count index : Nat) : shift count count (some index) = some index := by
  simp only [shift]
  split
  · omega
  · congr 1; omega

theorem shift_push (count index : Nat) : shift count (count + 1) (some index) = some (index + 1) := by
  simp only [shift]
  split
  · omega
  · congr 1; omega

theorem shift_pop (count index : Nat) : shift (count + 1) count (some (index + 1)) = some index := by
  simp only [shift]
  split
  · omega
  · congr 1; omega

theorem shift_retires_zero (count : Nat) : shift (count + 1) count (some 0) = none := by
  simp [shift]

theorem shift_same (count : Nat) (mark : Option Nat) : shift count count mark = mark := by
  cases mark with
  | none => rfl
  | some index => exact shift_keeps count index

theorem shift_has_origin {oldCount newCount : Nat} {before : Option Nat} {after : Nat}
    (marked : shift oldCount newCount before = some after) :
    ∃ index, before = some index ∧ oldCount ≤ index + newCount ∧ after = index + newCount - oldCount := by
  cases before with
  | none => cases marked
  | some index =>
      simp only [shift] at marked
      split at marked
      · cases marked
      · exact ⟨index, rfl, by omega, (Option.some.inj marked).symm⟩

theorem retirement_requires_removed_position {oldCount newCount index : Nat}
    (retired : shift oldCount newCount (some index) = none) : index + newCount < oldCount := by
  simp only [shift] at retired
  split at retired
  · assumption
  · cases retired

def frameActive {User : Type} (source : State User) : Bool :=
  PettaInheritedContext.boundary (PettaInheritedContext.nest source)

theorem frame_active_view {User : Type} (source : State User) (current : Scope User) (parents : List (Scope User))
    (control : DControl) (context : Context User) (origins : List Nat) (pending : List (Work User))
    (scopes : source.2.scopes = current :: parents)
    (front : current.frontier = (control, context, origins) :: pending) :
    frameActive source = match context.calls with
      | [] => false
      | frame :: _ => decide (frame.scopeDepth = source.2.scopes.length) &&
          match frame.phase with
          | .nextArgument => true
          | .argument _ _ | .body => control.goals.isEmpty := by
  cases calls : context.calls <;>
    simp [frameActive, PettaInheritedContext.nest, PettaInheritedContext.boundary,
      Bridges.DestinationContextMap.state, Bridges.DestinationContextMap.configuration,
      Bridges.DestinationContextMap.scope, Bridges.DestinationContextMap.work,
      PettaInheritedContext.inherit, scopes, front, calls]
  rfl

theorem frame_active_at {User : Type} (source : State User) (current : Scope User) (parents : List (Scope User))
    (control : DControl) (context : Context User) (origins : List Nat) (pending : List (Work User))
    (frame : CallFrame) (outside : List CallFrame)
    (scopes : source.2.scopes = current :: parents)
    (front : current.frontier = (control, context, origins) :: pending)
    (calls : context.calls = frame :: outside) (depth : frame.scopeDepth = source.2.scopes.length)
    (active : frame.phase = .nextArgument ∨ control.goals = []) : frameActive source = true := by
  have level : frame.scopeDepth = parents.length + 1 := by simpa only [scopes, List.length_cons] using depth
  rcases active with phase | terminal
  · simp [frameActive, PettaInheritedContext.nest, PettaInheritedContext.boundary,
      Bridges.DestinationContextMap.state, Bridges.DestinationContextMap.configuration,
      Bridges.DestinationContextMap.scope, Bridges.DestinationContextMap.work,
      PettaInheritedContext.inherit, scopes, front, calls, level, phase]
  · cases phase : frame.phase <;>
      simp [frameActive, PettaInheritedContext.nest, PettaInheritedContext.boundary,
        Bridges.DestinationContextMap.state, Bridges.DestinationContextMap.configuration,
        Bridges.DestinationContextMap.scope, Bridges.DestinationContextMap.work,
        PettaInheritedContext.inherit, scopes, front, calls, level, phase, terminal]

def frontier {User : Type} (before : Work User) (mark : Option Nat) (pending : List (Work User))
    (pendingMarks : List (Option Nat)) (after : Scope User) : List (Option Nat) :=
  let generated := after.frontier.take (after.frontier.length - pending.length)
  generated.map (fun item => shift before.2.1.calls.length item.2.1.calls.length mark) ++ pendingMarks

def sameScope {User : Type} (source : State User) (current : Scope User) (marks : Marks) (after : Scope User) :
    Option Marks :=
  match current.frontier, marks.frontier with
  | [], [] => some marks
  | before :: pending, mark :: pendingMarks =>
      if frameActive source then
        some ⟨frontier before mark pending pendingMarks after, marks.caller⟩
      else match before.1.goals with
        | .commit :: _ =>
            let removed := pending.length - (after.frontier.length - 1)
            some ⟨mark :: pendingMarks.drop removed, marks.caller⟩
        | _ => some ⟨frontier before mark pending pendingMarks after, marks.caller⟩
  | _, _ => none

def advance {User : Type} (marks : List Marks) (source after : State User) : Option (List Marks) :=
  match source.2.scopes, marks, after.2.scopes with
  | current :: parents, label :: labels, reached :: reachedParents =>
      if reachedParents.length = parents.length then
        (sameScope source current label reached).map (· :: labels)
      else if reachedParents.length = parents.length + 1 then
        match current.frontier, label.frontier with
        | _ :: _, mark :: pendingMarks =>
            some (⟨List.replicate reached.frontier.length none, mark⟩ :: ⟨pendingMarks, label.caller⟩ :: labels)
        | _, _ => none
      else if parents.length = reachedParents.length + 1 then
        match parents, labels with
        | _ :: _, parentLabel :: outsideLabels =>
            some (⟨label.caller :: parentLabel.frontier, parentLabel.caller⟩ :: outsideLabels)
        | _, _ => none
      else none
  | [], [], [] => some []
  | _, _, _ => none

theorem frontier_replacement {User : Type} (before : Work User) (mark : Option Nat)
    (pending generated : List (Work User)) (pendingMarks : List (Option Nat)) (current : Scope User) :
    frontier before mark pending pendingMarks {current with frontier := generated ++ pending} =
      generated.map (fun item => shift before.2.1.calls.length item.2.1.calls.length mark) ++ pendingMarks := by
  simp [frontier]

theorem frontier_identity {User : Type} (before : Work User) (mark : Option Nat)
    (pending : List (Work User)) (pendingMarks : List (Option Nat)) (current : Scope User)
    (front : current.frontier = before :: pending) :
    frontier before mark pending pendingMarks current = mark :: pendingMarks := by
  simp [frontier, front, shift_same]

theorem same_scope_identity {User : Type} (source : State User) (current : Scope User) (marks : Marks)
    (aligned : marks.frontier.length = current.frontier.length) : sameScope source current marks current = some marks := by
  cases marks with
  | mk frontMarks callerMark =>
    cases front : current.frontier with
    | nil =>
        have empty : frontMarks = [] := List.eq_nil_of_length_eq_zero (by simpa only [front, List.length_nil] using aligned)
        simp only [sameScope, front, empty]
    | cons before pending =>
        cases tags : frontMarks with
        | nil => simp only [tags, front, List.length_nil, List.length_cons] at aligned; omega
        | cons mark pendingMarks =>
            simp only [sameScope, front]
            have unchanged := frontier_identity before mark pending pendingMarks current front
            cases active : frameActive source with
            | true => simp only [if_true, unchanged]
            | false =>
                simp only [Bool.false_eq_true, if_false]
                cases goals : before.1.goals with
                | nil => simp only [unchanged]
                | cons first older => cases first <;> simp_all

theorem advance_stack_identity {User : Type} {Held : Nat → Work User → Prop}
    (marks : List Marks) (source : State User) (held : PettaScopeMarks.Stack Held marks source.2.scopes) :
    advance marks source source = some marks := by
  cases scopes : source.2.scopes with
  | nil =>
      have empty : marks = [] := List.eq_nil_of_length_eq_zero (by simpa only [scopes, List.length_nil] using List.Forall₂.length_eq held)
      simp only [advance, scopes, empty]
  | cons current parents =>
      cases marks with
      | nil => simp only [PettaScopeMarks.Stack, scopes] at held; cases held
      | cons label labels =>
          have owner := (List.forall₂_cons.mp (scopes ▸ held)).1
          simp only [advance, scopes, if_true]
          rw [same_scope_identity source current label (PettaScopeMarks.Frontier.length owner.1)]
          rfl

theorem advance_replacement {User : Type} (source : State User) (current : Scope User) (parents : List (Scope User))
    (before : Work User) (pending generated : List (Work User)) (mark : Option Nat)
    (pendingMarks : List (Option Nat)) (callerMark : Option Nat) (parentMarks : List Marks)
    (scopes : source.2.scopes = current :: parents) (front : current.frontier = before :: pending)
    (ordinary : frameActive source = true ∨ ∀ older, before.1.goals ≠ .commit :: older) :
    advance (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks) source (install source current parents generated pending) =
      some (⟨generated.map (fun item => shift before.2.1.calls.length item.2.1.calls.length mark) ++ pendingMarks,
        callerMark⟩ :: parentMarks) := by
  have atScope : sameScope source current ⟨mark :: pendingMarks, callerMark⟩
      {current with frontier := generated ++ pending} =
        some ⟨generated.map (fun item => shift before.2.1.calls.length item.2.1.calls.length mark) ++ pendingMarks,
          callerMark⟩ := by
    simp only [sameScope, front]
    cases active : frameActive source with
    | true =>
        simp only [if_true]
        rw [frontier_replacement]
    | false =>
        simp only [Bool.false_eq_true, if_false]
        have notCommit := ordinary.resolve_left (by simp [active])
        split
        next older atCommit => exact (notCommit older atCommit).elim
        next => rw [frontier_replacement]
  simp only [advance, scopes, install, atScope, Option.map_some, if_true]

theorem advance_push {User : Type} (source : State User) (current : Scope User) (parents : List (Scope User))
    (before : Work User) (pending : List (Work User)) (child : Scope User)
    (mark : Option Nat) (pendingMarks : List (Option Nat)) (callerMark : Option Nat) (parentMarks : List Marks)
    (scopes : source.2.scopes = current :: parents) (front : current.frontier = before :: pending)
    (allocator : Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared.Allocator) (world : EagerDFS.World) :
    advance (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks) source
      (allocator, ⟨world, child :: {current with frontier := pending} :: parents⟩) =
      some (⟨List.replicate child.frontier.length none, mark⟩ :: ⟨pendingMarks, callerMark⟩ :: parentMarks) := by
  simp [advance, scopes, List.length_cons, front]

theorem advance_pop {User : Type} (source : State User) (child parent : Scope User) (parents : List (Scope User))
    (childMarks parentMarks : Marks) (outsideMarks : List Marks) (reached : Scope User)
    (scopes : source.2.scopes = child :: parent :: parents)
    (allocator : Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared.Allocator) (world : EagerDFS.World) :
    advance (childMarks :: parentMarks :: outsideMarks) source (allocator, ⟨world, reached :: parents⟩) =
      some (⟨childMarks.caller :: parentMarks.frontier, parentMarks.caller⟩ :: outsideMarks) := by
  have two : parents.length ≠ parents.length + 1 + 1 := by omega
  simp [advance, scopes, List.length_cons, two]

theorem advance_commit {User : Type} (source : State User) (current : Scope User) (parents : List (Scope User))
    (control : DControl) (context : Context User) (origins : List Nat) (pending younger kept : List (Work User))
    (older : List EagerDFS.Destination.Goal)
    (mark : Option Nat) (pendingMarks : List (Option Nat)) (callerMark : Option Nat) (parentMarks : List Marks)
    (scopes : source.2.scopes = current :: parents)
    (front : current.frontier = (control, context, origins) :: pending)
    (goals : control.goals = .commit :: older) (partition : pending = younger ++ kept)
    (sourceLane : frameActive source = false) :
    advance (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks) source
      (source.1, ⟨source.2.world, {current with frontier := ({control with goals := older}, context, origins) :: kept} :: parents⟩) =
      some (⟨mark :: pendingMarks.drop younger.length, callerMark⟩ :: parentMarks) := by
  simp [advance, scopes, sameScope, front, sourceLane, goals, partition]

theorem unchanged_frame_counts_keep_marks {User : Type} (before : Work User) (mark : Option Nat)
    (generated : List (Work User))
    (same : ∀ item ∈ generated, item.2.1.calls.length = before.2.1.calls.length) :
    generated.map (fun item => shift before.2.1.calls.length item.2.1.calls.length mark) =
      List.replicate generated.length mark := by
  apply List.map_eq_replicate_iff.mpr
  intro item member
  rw [same item member]
  cases mark with
  | none => rfl
  | some index => exact shift_keeps _ index

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaReturnMarkUpdate
