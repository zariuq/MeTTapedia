import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaOccurrenceOverlay

/-!
# One physical scope-mark layout with parameterized work obligations

Frontier positions and saved collection callers use the existing mark data.
The work obligation is independent of this bookkeeping. Collection children
are unmarked; local capture and restore laws carry the caller's obligation
through the actual saved caller and copied-answer continuation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSelectedReturnScopes

structure Marks where
  frontier : List (Option Nat)
  caller : Option Nat

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSelectedReturnScopes

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaScopeMarks

open Mettapedia.Languages.MeTTa.PeTTa
open EagerDFS.Destination
open PettaOccurrenceOverlay
open PettaSelectedReturnScopes (Marks)

def WorkMarked {User : Type} (Held : Nat → Work User → Prop) (mark : Option Nat) (item : Work User) : Prop :=
  ∀ index, mark = some index → Held index item

def Frontier {User : Type} (Held : Nat → Work User → Prop) (marks : List (Option Nat))
    (items : List (Work User)) : Prop := List.Forall₂ (WorkMarked Held) marks items

def CallerMarked {User : Type} (Held : Nat → Work User → Prop) (mark : Option Nat)
    (caller : Option (CollectionCaller (Context User))) : Prop :=
  ∀ index, mark = some index → ∃ actual, caller = some actual ∧ Held index (actual.1, actual.2.2.1, actual.2.2.2)

def ScopeHolds {User : Type} (Held : Nat → Work User → Prop) (marks : Marks) (current : Scope User) : Prop :=
  Frontier Held marks.frontier current.frontier ∧ CallerMarked Held marks.caller current.caller

def Stack {User : Type} (Held : Nat → Work User → Prop) (marks : List Marks) (scopes : List (Scope User)) : Prop :=
  List.Forall₂ (ScopeHolds Held) marks scopes

def untracked {User : Type} (current : Scope User) : Marks := ⟨List.replicate current.frontier.length none, none⟩

theorem active_work {User : Type} {Held : Nat → Work User → Prop}
    (current : Scope User) (control : DControl) (context : Context User) (origins : List Nat)
    (pending : List (Work User)) (index : Nat) (pendingMarks : List (Option Nat)) (callerMark : Option Nat)
    (held : ScopeHolds Held ⟨some index :: pendingMarks, callerMark⟩ current)
    (frontier : current.frontier = (control, context, origins) :: pending) : Held index (control, context, origins) := by
  have focused : List.Forall₂ (WorkMarked Held) (some index :: pendingMarks) ((control, context, origins) :: pending) :=
    frontier ▸ held.1
  exact (List.forall₂_cons.mp focused).1 index rfl

theorem Frontier.length {User : Type} {Held : Nat → Work User → Prop} {marks : List (Option Nat)}
    {items : List (Work User)} (good : Frontier Held marks items) : marks.length = items.length :=
  List.Forall₂.length_eq good

theorem Frontier.append {User : Type} {Held : Nat → Work User → Prop}
    {firstMarks secondMarks : List (Option Nat)} {first second : List (Work User)}
    (one : Frontier Held firstMarks first) (two : Frontier Held secondMarks second) :
    Frontier Held (firstMarks ++ secondMarks) (first ++ second) := by
  induction one with
  | nil => exact two
  | cons marked rest ih => exact .cons marked ih

theorem untracked_frontier {User : Type} (Held : Nat → Work User → Prop) (items : List (Work User)) :
    Frontier Held (List.replicate items.length none) items := by
  induction items with
  | nil => exact .nil
  | cons item items ih => exact .cons (by intro index impossible; cases impossible) ih

theorem marked_frontier {User : Type} (Held : Nat → Work User → Prop) (index : Nat)
    (items : List (Work User)) (held : ∀ item ∈ items, Held index item) :
    Frontier Held (List.replicate items.length (some index)) items := by
  induction items with
  | nil => exact .nil
  | cons item items ih =>
      refine .cons ?_ (ih (by intro other member; exact held other (List.mem_cons_of_mem _ member)))
      intro selected same
      cases Option.some.inj same
      exact held item List.mem_cons_self

theorem untracked_scope {User : Type} (Held : Nat → Work User → Prop) (current : Scope User) :
    ScopeHolds Held (untracked current) current :=
  ⟨untracked_frontier Held current.frontier, by intro index impossible; cases impossible⟩

theorem untracked_stack {User : Type} (Held : Nat → Work User → Prop) (scopes : List (Scope User)) :
    Stack Held (scopes.map untracked) scopes := by
  induction scopes with
  | nil => exact .nil
  | cons current parents ih => exact .cons (untracked_scope Held current) ih

theorem scope_install {User : Type} {Held : Nat → Work User → Prop}
    (current : Scope User) (control : DControl) (context : Context User) (origins : List Nat)
    (pending : List (Work User)) (mark : Option Nat) (pendingMarks : List (Option Nat)) (callerMark : Option Nat)
    (held : ScopeHolds Held ⟨mark :: pendingMarks, callerMark⟩ current)
    (frontier : current.frontier = (control, context, origins) :: pending)
    (generated : List (Work User)) (newMarks : List (Option Nat))
    (produced : WorkMarked Held mark (control, context, origins) → Frontier Held newMarks generated) :
    ScopeHolds Held ⟨newMarks ++ pendingMarks, callerMark⟩ {current with frontier := generated ++ pending} := by
  have focused : List.Forall₂ (WorkMarked Held) (mark :: pendingMarks) ((control, context, origins) :: pending) :=
    frontier ▸ held.1
  obtain ⟨active, older⟩ := List.forall₂_cons.mp focused
  exact ⟨Frontier.append (produced active) older, held.2⟩

theorem install_selected {User : Type} (Held : Nat → Work User → Prop)
    (current : Scope User) (parents : List (Scope User)) (pending generated : List (Work User))
    (earned : ∀ item ∈ generated, Held 0 item) :
    Stack Held (⟨List.replicate generated.length (some 0) ++ List.replicate pending.length none, none⟩ :: parents.map untracked)
      ({current with frontier := generated ++ pending} :: parents) := by
  refine .cons ⟨?_, ?_⟩ (untracked_stack Held parents)
  · exact Frontier.append (marked_frontier Held 0 generated earned) (untracked_frontier Held pending)
  · intro index impossible; cases impossible

theorem collection_push {User : Type} {Held : Nat → Work User → Prop}
    (current : Scope User) (parents : List (Scope User)) (parentMarks : List Marks)
    (control : DControl) (context : Context User) (origins : List Nat) (pending : List (Work User))
    (mark : Option Nat) (pendingMarks : List (Option Nat)) (callerMark : Option Nat)
    (held : Stack Held (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks) (current :: parents))
    (frontier : current.frontier = (control, context, origins) :: pending)
    (older : List EagerDFS.Destination.Goal) (destination : Mettapedia.Languages.MeTTa.OSLFCore.Atom)
    (capture : ∀ index, Held index (control, context, origins) → Held index ({control with goals := older}, context, origins))
    (child : Scope User)
    (savedCaller : child.caller = some ({control with goals := older}, destination, context, origins)) :
    Stack Held (⟨List.replicate child.frontier.length none, mark⟩ :: ⟨pendingMarks, callerMark⟩ :: parentMarks)
      (child :: {current with frontier := pending} :: parents) := by
  obtain ⟨owner, rest⟩ := List.forall₂_cons.mp held
  have focused : List.Forall₂ (WorkMarked Held) (mark :: pendingMarks) ((control, context, origins) :: pending) :=
    frontier ▸ owner.1
  obtain ⟨active, previous⟩ := List.forall₂_cons.mp focused
  refine .cons ⟨untracked_frontier Held child.frontier, ?_⟩ (.cons ⟨previous, owner.2⟩ rest)
  intro index marked
  exact ⟨_, savedCaller, capture index (active index marked)⟩

theorem collection_resume {User : Type} {Held : Nat → Work User → Prop}
    (child parent : Scope User) (parents : List (Scope User))
    (childMarks parentMarks : Marks) (outsideMarks : List Marks)
    (held : Stack Held (childMarks :: parentMarks :: outsideMarks) (child :: parent :: parents))
    (caller : CollectionCaller (Context User)) (actualCaller : child.caller = some caller)
    (copies : List (Mettapedia.Languages.MeTTa.OSLFCore.Atom × List Mettapedia.Languages.MeTTa.OSLFCore.Atom))
    (restore : ∀ index, Held index (caller.1, caller.2.2.1, caller.2.2.2) → Held index (Source.resumeCopies copies caller)) :
    Stack Held (⟨childMarks.caller :: parentMarks.frontier, parentMarks.caller⟩ :: outsideMarks)
      ({parent with frontier := Source.resumeCopies copies caller :: parent.frontier} :: parents) := by
  obtain ⟨childGood, rest⟩ := List.forall₂_cons.mp held
  obtain ⟨parentGood, outsideGood⟩ := List.forall₂_cons.mp rest
  refine .cons ⟨.cons ?_ parentGood.1, parentGood.2⟩ outsideGood
  intro index marked
  obtain ⟨actual, same, returning⟩ := childGood.2 index marked
  cases Option.some.inj (actualCaller.symm.trans same)
  exact restore index returning

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaScopeMarks
