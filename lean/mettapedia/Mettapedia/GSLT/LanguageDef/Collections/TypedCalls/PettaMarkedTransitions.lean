import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaReturnMarkUpdate

/-!
# The actual mark update transports parameterized scope obligations

The returned annotation is exactly the existing `advance` result. It is not
chosen afterwards to erase obligations. Semantic operation laws must earn
the obligation on every actual generated occurrence.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaMarkedTransitions

open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open EagerDFS.Destination
open PettaOccurrenceOverlay
open PettaSelectedReturnScopes (Marks)
open PettaScopeMarks (WorkMarked Frontier Stack)
open PettaReturnMarkUpdate

theorem evaluate_not_commit {control : DControl} {expression destination : Mettapedia.Languages.MeTTa.OSLFCore.Atom}
    {older : List EagerDFS.Destination.Goal} (scheduled : control.goals = .evaluate expression destination :: older) :
    ∀ tail, control.goals ≠ .commit :: tail := by
  intro tail same; rw [scheduled] at same; cases same

theorem invoke_not_commit {control : DControl} {head : String} {arguments : List Mettapedia.Languages.MeTTa.OSLFCore.Atom}
    {destination : Mettapedia.Languages.MeTTa.OSLFCore.Atom} {older : List EagerDFS.Destination.Goal}
    (scheduled : control.goals = .invoke head arguments destination :: older) :
    ∀ tail, control.goals ≠ .commit :: tail := by
  intro tail same; rw [scheduled] at same; cases same

theorem silent_not_commit {User : Type} {program : SpaceSemantics.Program} {before after : Cursor (Context User)}
    (source : Source.Step .eagerValue program before (.silent after)) :
    ∀ older, before.control.goals ≠ .commit :: older := by
  intro older atGoal
  have actual := source.execution
  have requested := (Source.Step.committing (policy := .eagerValue) (program := program) (cursor := before) older atGoal).execution
  rw [requested] at actual
  cases actual

theorem finish_not_commit {User : Type} {program : SpaceSemantics.Program} {before after : Cursor (Context User)} {result : Result}
    (source : Source.Step .eagerValue program before (.finish (result, after))) :
    ∀ older, before.control.goals ≠ .commit :: older := by
  intro older atGoal
  have actual := source.execution
  have requested := (Source.Step.committing (policy := .eagerValue) (program := program) (cursor := before) older atGoal).execution
  rw [requested] at actual
  cases actual

theorem query_not_commit {control : DControl} {space pattern body destination : Mettapedia.Languages.MeTTa.OSLFCore.Atom}
    {older : List EagerDFS.Destination.Goal} (scheduled : control.goals = .query space pattern body destination :: older) :
    ∀ tail, control.goals ≠ .commit :: tail := by
  intro tail same; rw [scheduled] at same; cases same

def Preserves {User : Type} (Held : Nat → Work User → Prop) (marks : List Marks)
    (source : State User) (reply : Step User) : Prop :=
  ∀ after ∈ PettaOccurrenceBinding.retained reply,
    ∃ next, advance marks source after = some next ∧ Stack Held next after.2.scopes

theorem call_keeps {User : Type} {Held : Nat → Work User → Prop}
    (marks : List Marks) (source : State User) (request : Request) (held : Stack Held marks source.2.scopes) :
    Preserves Held marks source (.call request source) := by
  intro after member
  cases List.mem_singleton.mp member
  exact ⟨marks, advance_stack_identity marks source held, held⟩

theorem constrained_keeps {User : Type} {Held : Nat → Work User → Prop}
    (marks : List Marks) (source : State User) (action : Bridges.ScopedQuerySource.Action (Context User))
    (computed : Bridges.ScopedQuerySource.constrainedCall source = some action) (held : Stack Held marks source.2.scopes) :
    Preserves Held marks source (liftSource action) := by
  unfold Bridges.ScopedQuerySource.constrainedCall at computed
  repeat' first
    | (cases Option.some.inj computed; exact call_keeps marks source _ held)
    | contradiction
    | (split at computed <;> try dsimp only [bind, Option.bind] at computed)

theorem mutation_keeps {User : Type} {Held : Nat → Work User → Prop}
    (marks : List Marks) (source : State User) (action : Bridges.ScopedQuerySource.Action (Context User))
    (computed : Bridges.ScopedQuerySource.mutationCall source = some action) (held : Stack Held marks source.2.scopes) :
    Preserves Held marks source (liftSource action) := by
  unfold Bridges.ScopedQuerySource.mutationCall at computed
  repeat' first
    | (cases Option.some.inj computed; exact call_keeps marks source _ held)
    | contradiction
    | (split at computed <;> try dsimp only [bind, Option.bind] at computed)

theorem ownership_keeps {User : Type} {Held : Nat → Work User → Prop}
    (marks : List Marks) (source : State User) (program : SpaceSemantics.Program)
    (action : Bridges.ScopedQuerySource.Action (Context User))
    (computed : Bridges.ScopedQuerySource.ownershipStep program source = some action)
    (held : Stack Held marks source.2.scopes) : Preserves Held marks source (liftSource action) := by
  unfold Bridges.ScopedQuerySource.ownershipStep at computed
  repeat' first
    | (cases Option.some.inj computed; exact call_keeps marks source _ held)
    | contradiction
    | (split at computed <;> try dsimp only [bind, Option.bind] at computed)

theorem annotated_frontier {User : Type} (Held : Nat → Work User → Prop) (mark : Option Nat)
    (before : Work User) (generated : List (Work User))
    (held : ∀ item ∈ generated, WorkMarked Held (shift before.2.1.calls.length item.2.1.calls.length mark) item) :
    Frontier Held (generated.map (fun item => shift before.2.1.calls.length item.2.1.calls.length mark)) generated := by
  induction generated with
  | nil => exact .nil
  | cons item generated ih =>
      exact .cons (held item List.mem_cons_self) (ih (fun other member => held other (List.mem_cons_of_mem _ member)))

theorem install_keeps {User : Type} {Held : Nat → Work User → Prop}
    (source : State User) (current : Scope User) (parents : List (Scope User)) (before : Work User)
    (pending generated : List (Work User)) (mark : Option Nat) (pendingMarks : List (Option Nat))
    (callerMark : Option Nat) (parentMarks : List Marks)
    (held : Stack Held (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks) source.2.scopes)
    (scopes : source.2.scopes = current :: parents) (front : current.frontier = before :: pending)
    (ordinary : frameActive source = true ∨ ∀ older, before.1.goals ≠ .commit :: older)
    (produced : WorkMarked Held mark before →
      ∀ item ∈ generated, WorkMarked Held (shift before.2.1.calls.length item.2.1.calls.length mark) item) :
    Preserves Held (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks) source
      (.silent (install source current parents generated pending)) := by
  intro after member
  cases List.mem_singleton.mp member
  refine ⟨_, advance_replacement source current parents before pending generated mark pendingMarks callerMark parentMarks
    scopes front ordinary, ?_⟩
  obtain ⟨owner, outside⟩ := List.forall₂_cons.mp (scopes ▸ held)
  apply List.Forall₂.cons _ outside
  exact PettaScopeMarks.scope_install current before.1 before.2.1 before.2.2 pending mark pendingMarks callerMark owner front
    generated _ (fun active => annotated_frontier Held mark before generated (produced active))

theorem same_count_generated {User : Type} {Held : Nat → Work User → Prop}
    (before : Work User) (generated : List (Work User)) (mark : Option Nat)
    (counts : ∀ item ∈ generated, item.2.1.calls.length = before.2.1.calls.length)
    (held : ∀ index, mark = some index → ∀ item ∈ generated, Held index item) :
    ∀ item ∈ generated, WorkMarked Held (shift before.2.1.calls.length item.2.1.calls.length mark) item := by
  intro item member index marked
  rw [counts item member, shift_same] at marked
  exact held index marked item member

theorem installed_data_irrelevant {User : Type} (marks : List Marks) (source : State User)
    (current : Scope User) (parents : List (Scope User)) (generated pending : List (Work User))
    (allocator : Allocator) (world : EagerDFS.World) (collected : List CollectedAnswer) :
    advance marks source (allocator, ⟨world, {current with frontier := generated ++ pending, collected} :: parents⟩) =
      advance marks source (install source current parents generated pending) := by
  cases scopes : source.2.scopes <;> cases marks <;>
    simp only [advance, install, sameScope, PettaReturnMarkUpdate.frontier, scopes]

theorem installed_scope_keeps {User : Type} {Held : Nat → Work User → Prop}
    (source : State User) (current : Scope User) (parents : List (Scope User)) (before : Work User)
    (pending generated : List (Work User)) (mark : Option Nat) (pendingMarks : List (Option Nat))
    (callerMark : Option Nat) (parentMarks : List Marks)
    (held : Stack Held (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks) source.2.scopes)
    (scopes : source.2.scopes = current :: parents) (front : current.frontier = before :: pending)
    (ordinary : frameActive source = true ∨ ∀ older, before.1.goals ≠ .commit :: older)
    (produced : WorkMarked Held mark before →
      ∀ item ∈ generated, WorkMarked Held (shift before.2.1.calls.length item.2.1.calls.length mark) item)
    (allocator : Allocator) (world : EagerDFS.World) (collected : List CollectedAnswer) :
    Preserves Held (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks) source
      (.silent (allocator, ⟨world, {current with frontier := generated ++ pending, collected} :: parents⟩)) := by
  intro after member
  cases List.mem_singleton.mp member
  let next : List Marks :=
    ⟨generated.map (fun item => shift before.2.1.calls.length item.2.1.calls.length mark) ++ pendingMarks, callerMark⟩ :: parentMarks
  refine ⟨next, ?_, ?_⟩
  · rw [installed_data_irrelevant]
    exact advance_replacement source current parents before pending generated mark pendingMarks callerMark parentMarks scopes front ordinary
  · obtain ⟨owner, outside⟩ := List.forall₂_cons.mp (scopes ▸ held)
    apply List.Forall₂.cons _ outside
    exact PettaScopeMarks.scope_install current before.1 before.2.1 before.2.2 pending mark pendingMarks callerMark owner front
      generated _ (fun active => annotated_frontier Held mark before generated (produced active))

theorem collapse_keeps {User : Type} {Held : Nat → Work User → Prop}
    (source : State User) (current : Scope User) (parents : List (Scope User))
    (control : DControl) (context : Context User) (origins : List Nat) (pending : List (Work User))
    (mark : Option Nat) (pendingMarks : List (Option Nat)) (callerMark : Option Nat) (parentMarks : List Marks)
    (held : Stack Held (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks) source.2.scopes)
    (scopes : source.2.scopes = current :: parents) (front : current.frontier = (control, context, origins) :: pending)
    (older : List EagerDFS.Destination.Goal) (destination : Mettapedia.Languages.MeTTa.OSLFCore.Atom)
    (capture : ∀ index, Held index (control, context, origins) → Held index ({control with goals := older}, context, origins))
    (child : Scope User) (atCaller : child.caller = some ({control with goals := older}, destination, context, origins))
    (allocator : Allocator) (world : EagerDFS.World) :
    Preserves Held (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks) source
      (.silent (allocator, ⟨world, child :: {current with frontier := pending} :: parents⟩)) := by
  intro after member
  cases List.mem_singleton.mp member
  exact ⟨_, advance_push source current parents (control, context, origins) pending child mark pendingMarks callerMark
      parentMarks scopes front allocator world,
    PettaScopeMarks.collection_push current parents parentMarks control context origins pending mark pendingMarks callerMark
      (scopes ▸ held) front older destination capture child atCaller⟩

theorem collection_keeps {User : Type} {Held : Nat → Work User → Prop}
    (source : State User) (child parent : Scope User) (parents : List (Scope User))
    (childMarks parentMarks : Marks) (outsideMarks : List Marks)
    (held : Stack Held (childMarks :: parentMarks :: outsideMarks) source.2.scopes)
    (scopes : source.2.scopes = child :: parent :: parents)
    (caller : CollectionCaller (Context User)) (atCaller : child.caller = some caller)
    (copies : List (Mettapedia.Languages.MeTTa.OSLFCore.Atom × List Mettapedia.Languages.MeTTa.OSLFCore.Atom))
    (restore : ∀ index, Held index (caller.1, caller.2.2.1, caller.2.2.2) → Held index (Source.resumeCopies copies caller))
    (allocator : Allocator) (world : EagerDFS.World) :
    Preserves Held (childMarks :: parentMarks :: outsideMarks) source
      (.silent (allocator, ⟨world, {parent with frontier := Source.resumeCopies copies caller :: parent.frontier} :: parents⟩)) := by
  intro after member
  cases List.mem_singleton.mp member
  exact ⟨_, advance_pop source child parent parents childMarks parentMarks outsideMarks _ scopes allocator world,
    PettaScopeMarks.collection_resume child parent parents childMarks parentMarks outsideMarks (scopes ▸ held) caller atCaller
      copies restore⟩

theorem commit_keeps {User : Type} {Held : Nat → Work User → Prop}
    (source : State User) (current : Scope User) (parents : List (Scope User))
    (control : DControl) (context : Context User) (origins : List Nat) (pending younger kept : List (Work User))
    (mark : Option Nat) (pendingMarks : List (Option Nat)) (callerMark : Option Nat) (parentMarks : List Marks)
    (older : List EagerDFS.Destination.Goal)
    (held : Stack Held (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks) source.2.scopes)
    (scopes : source.2.scopes = current :: parents) (front : current.frontier = (control, context, origins) :: pending)
    (goals : control.goals = .commit :: older) (partition : pending = younger ++ kept) (sourceLane : frameActive source = false)
    (capture : ∀ index, Held index (control, context, origins) → Held index ({control with goals := older}, context, origins)) :
    Preserves Held (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks) source
      (.silent (source.1, ⟨source.2.world,
        {current with frontier := ({control with goals := older}, context, origins) :: kept} :: parents⟩)) := by
  intro after member
  cases List.mem_singleton.mp member
  refine ⟨_, advance_commit source current parents control context origins pending younger kept older mark pendingMarks callerMark
    parentMarks scopes front goals partition sourceLane, ?_⟩
  obtain ⟨owner, outside⟩ := List.forall₂_cons.mp (scopes ▸ held)
  have active : List.Forall₂ (WorkMarked Held) (mark :: pendingMarks) ((control, context, origins) :: pending) := front ▸ owner.1
  obtain ⟨returning, pendingGood⟩ := List.forall₂_cons.mp active
  have retained := List.forall₂_drop younger.length pendingGood
  have suffix : pending.drop younger.length = kept := by simp [partition]
  rw [suffix] at retained
  apply List.Forall₂.cons _ outside
  refine ⟨.cons ?_ retained, owner.2⟩
  intro index selected
  exact capture index (returning index selected)

theorem source_collection_keeps {User : Type} {Held : Nat → Work User → Prop}
    {source after : State User} {marks : List Marks}
    (step : Source.CollectionReturn Source.FreshOperations.owned source after) (held : Stack Held marks source.2.scopes)
    (restore : ∀ (copies : List (Mettapedia.Languages.MeTTa.OSLFCore.Atom × List Mettapedia.Languages.MeTTa.OSLFCore.Atom))
      (caller : CollectionCaller (Context User)) (index : Nat),
      Held index (caller.1, caller.2.2.1, caller.2.2.2) → Held index (Source.resumeCopies copies caller)) :
    Preserves Held marks source (.silent after) := by
  cases step with
  | complete allocator next world answers caller parent parents copied ready returned copies =>
      cases marks with
      | nil => cases held
      | cons childMarks outerMarks =>
        cases outerMarks with
        | nil => cases List.forall₂_cons.mp held |>.2
        | cons parentMarks outsideMarks =>
            exact collection_keeps _ _ parent parents childMarks parentMarks outsideMarks held rfl caller rfl copied
              (restore copied caller) next world

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaMarkedTransitions
