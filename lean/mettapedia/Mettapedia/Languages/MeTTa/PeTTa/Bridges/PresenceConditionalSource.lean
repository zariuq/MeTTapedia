import Mettapedia.Languages.MeTTa.PeTTa.Bridges.PresenceGuardSource

/-!
# Literal presence conditionals with retained source continuations

The condition runs once. Its reached equations select one authored branch;
the other branch is retained during the condition but is never evaluated.
The source collection's allocation boundary remains observable.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.PresenceConditionalSource

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS (World)
open EagerDFS.Destination
open LiteralQuerySource (Request)
open ClosedOnceQueryFrame (FreshFor placed)

def source (request : Request) (yes no : Atom) : Atom :=
  .expression [.symbol "if", PresenceGuardSource.source request, yes, no]

def entry (caller : Control) (destination : Atom) (request : Request) (yes no : Atom) : Control :=
  {caller with goals := .evaluate (source request yes no) destination :: caller.goals}

def slot (caller : Control) (destination : Atom) (request : Request) (yes no : Atom) : String :=
  freshName (entry caller destination request yes no) 0

def waiting (caller : Control) (destination : Atom) (request : Request) (yes no : Atom) : Control :=
  {caller with goals := .branch (.var (slot caller destination request yes no)) yes no destination :: caller.goals}

theorem entry_step {Context : Type} (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (caller : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context)) (destination : Atom)
    (request : Request) (yes no : Atom) :
    scopeStep .relational program
      (placed allocator world scope parents (entry caller destination request yes no) context origins pending) =
      .silent (placed allocator world scope parents
        (PresenceGuardSource.start (waiting caller destination request yes no)
          (.var (slot caller destination request yes no)) request) context origins pending) := by
  simp [placed, entry, source, scopeStep, enterCollapse?, enterSuperpose?, EagerDFS.Destination.machine,
    prepare, replace, installChild, retainChild, PresenceGuardSource.start, waiting, slot]

private theorem name_in_support (control : Control) (name : String)
    (used : .var name ∈ control.goals.flatMap Goal.atoms) : name ∈ control.support := by
  apply Finset.mem_union_right
  apply (ClosedOnceQueryFrame.fold_support_iff _ _ name).mpr
  exact Or.inr ⟨.var name, List.mem_cons_of_mem _ (List.mem_append_right _ used),
    by simp [encode, Mettapedia.Logic.LP.Term.freeVars]⟩

private theorem name_apart_fresh (control : Control) (name : String) (index : Nat)
    (used : name ∈ control.support) : name ≠ freshName control index := by
  intro same
  apply freshName_not_mem control index
  rw [← same]
  exact used

set_option maxHeartbeats 1200000 in
theorem slot_apart (caller : Control) (destination : Atom) (request : Request) (yes no : Atom) :
    let name := slot caller destination request yes no
    let kept := waiting caller destination request yes no
    name ≠ PresenceGuardSource.notSlot kept (.var name) request ∧
      name ≠ PresenceGuardSource.leftSlot kept (.var name) request ∧
      name ≠ PresenceGuardSource.rightSlot kept (.var name) request := by
  dsimp only
  have first := name_in_support
    (PresenceGuardSource.start (waiting caller destination request yes no)
      (.var (slot caller destination request yes no)) request)
    (slot caller destination request yes no) (by simp [PresenceGuardSource.start, Goal.atoms])
  have later := name_in_support
    (PresenceGuardSource.equalityControl (waiting caller destination request yes no)
      (.var (slot caller destination request yes no)) request)
    (slot caller destination request yes no) (by simp [PresenceGuardSource.equalityControl, Goal.atoms])
  exact ⟨name_apart_fresh _ _ 0 first, name_apart_fresh _ _ 0 later, name_apart_fresh _ _ 1 later⟩

theorem slot_fresh (caller : Control) (destination : Atom) (request : Request) (yes no : Atom) (present : Bool) :
    FreshFor (slot caller destination request yes no)
      (PresenceGuardSource.comparisonBindings (waiting caller destination request yes no)
        (.var (slot caller destination request yes no)) request present) := by
  obtain ⟨notApart, leftApart, rightApart⟩ := slot_apart caller destination request yes no
  apply PresenceGuardSource.fresh_append_closed
  · apply PresenceGuardSource.fresh_append_closed
    · apply PresenceGuardSource.fresh_append_closed
      · exact ClosedOnceQueryFrame.fresh_for_bindings (entry caller destination request yes no) _ (freshName_not_mem _ _)
      · exact leftApart
      · exact PresenceGuardSource.tuple_freeVars request present
    · exact rightApart
    · decide +kernel
  · exact notApart
  · simp [Effects.boolean, encode, Mettapedia.Logic.LP.Term.freeVars]

def returned (caller : Control) (destination : Atom) (request : Request) (yes no : Atom) (present : Bool) : Control :=
  let kept := waiting caller destination request yes no
  let bindings := PresenceGuardSource.comparisonBindings kept
    (.var (slot caller destination request yes no)) request present ++
      [(Effects.boolean present, .var (slot caller destination request yes no))]
  {kept with bindings}

def reached (caller : Control) (destination : Atom) (request : Request) (yes no : Atom) (present : Bool) : Control :=
  {returned caller destination request yes no present with
    goals := .evaluate (if present then yes else no) destination :: caller.goals}

theorem returned_refined (caller : Control) (destination : Atom) (request : Request) (yes no : Atom) (present : Bool)
    (consistent : ∃ environment, Solves environment caller.bindings) :
    refine (PresenceGuardSource.comparisonBindings (waiting caller destination request yes no)
      (.var (slot caller destination request yes no)) request present)
      (Effects.boolean present) (.var (slot caller destination request yes no)) =
      some (returned caller destination request yes no present).bindings := by
  exact ClosedOnceQueryFrame.refine_fresh_closed _ _ _ (slot_fresh caller destination request yes no present)
    (ClosedOnceQueryFrame.refined_consistent _ _ _
      (PresenceGuardSource.comparison_refined (waiting caller destination request yes no)
        (.var (slot caller destination request yes no)) request present consistent))
    (PresenceGuardSource.read_boolean present)

theorem branch_step {Context : Type} (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (condition yes no destination : Atom) (older : List Goal) (environment : Environment)
    (atGoal : control.goals = .branch condition yes no destination :: older)
    (resolved : resolve control.bindings = some environment) :
    scopeStep .relational program (placed allocator world scope parents control context origins pending) =
      .silent (placed allocator world scope parents
        {control with goals := (.evaluate (if read environment condition == Effects.boolean true then yes else no)
          destination :: older)} context origins pending) := by
  simp [placed, scopeStep, enterCollapse?, enterSuperpose?, EagerDFS.Destination.machine,
    atGoal, resolved, replace, installChild, retainChild]

set_option maxHeartbeats 1200000 in
theorem select_prefix {Context : Type} (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (caller : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context)) (destination : Atom)
    (request : Request) (yes no : Atom) (present : Bool)
    (consistent : ∃ environment, Solves environment caller.bindings) :
    (EagerDFSStreaming.machine program (.scopedDestination Context .relational)).run 2
      (placed allocator world scope parents
        (PresenceGuardSource.delivered (waiting caller destination request yes no)
          (.var (slot caller destination request yes no)) request present) context origins pending) =
      ([], .exhausted (placed allocator world scope parents (reached caller destination request yes no present)
        context origins pending)) := by
  have refined := returned_refined caller destination request yes no present consistent
  obtain ⟨environment, resolved⟩ := resolve_complete (ClosedOnceQueryFrame.refined_consistent _ _ _ refined)
  have value := PresenceGuardSource.bound_closed_value _ (Effects.boolean present)
    (slot caller destination request yes no) environment resolved
    (by simp) (PresenceGuardSource.read_boolean present environment)
  have first : scopeStep .relational program
      (placed allocator world scope parents
        (PresenceGuardSource.delivered (waiting caller destination request yes no)
          (.var (slot caller destination request yes no)) request present) context origins pending) =
      .silent (placed allocator world scope parents (returned caller destination request yes no present)
        context origins pending) := by
    simp only [placed, PresenceGuardSource.delivered, scopeStep, enterCollapse?, enterSuperpose?,
      EagerDFS.Destination.machine, refined, installChild, retainChild]
    rfl
  have second : scopeStep .relational program
      (placed allocator world scope parents (returned caller destination request yes no present) context origins pending) =
      .silent (placed allocator world scope parents (reached caller destination request yes no present)
        context origins pending) := by
    have selected := branch_step program allocator world scope parents
      (returned caller destination request yes no present) context origins pending
      (.var (slot caller destination request yes no)) yes no destination caller.goals environment rfl resolved
    rw [value] at selected
    cases present <;> exact selected
  have firstStep := EagerDFSStreaming.Scoped.step_scope .relational program
    (placed allocator world scope parents
      (PresenceGuardSource.delivered (waiting caller destination request yes no)
        (.var (slot caller destination request yes no)) request present) context origins pending)
  have secondStep := EagerDFSStreaming.Scoped.step_scope .relational program
    (placed allocator world scope parents (returned caller destination request yes no present) context origins pending)
  rw [first] at firstStep
  rw [second] at secondStep
  rw [Machine.run_succ_silent _ firstStep, Machine.run_succ_silent _ secondStep]
  rfl

theorem source_prefix {Context : Type} (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (caller : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context)) (destination : Atom)
    (request : Request) (yes no : Atom)
    (consistent : ∃ environment, Solves environment caller.bindings)
    (rows : List Atom) (snapshot : world.state.read request.handle = some rows) :
    let present := decide (request.pattern ∈ rows)
    let kept := waiting caller destination request yes no
    let joined := Atom.var (slot caller destination request yes no)
    (EagerDFSStreaming.machine program (.scopedDestination Context .relational)).run
      (1 + (CollectedOnceQuerySource.childBudget present + 10) + 2)
      (placed allocator world scope parents (entry caller destination request yes no) context origins pending) =
      ([], match PresenceGuardSource.copyAllocator allocator present with
        | some next => .exhausted (placed next world scope parents (reached caller destination request yes no present)
            context (origins ++ [0, 0]) pending)
        | none => .suspended .allocation (PresenceGuardSource.collectionEnd allocator world scope parents
            kept context origins pending joined request present)) := by
  dsimp only
  let machine := EagerDFSStreaming.machine program (.scopedDestination Context .relational)
  have firstStep := EagerDFSStreaming.Scoped.step_scope .relational program
    (placed allocator world scope parents (entry caller destination request yes no) context origins pending)
  rw [entry_step] at firstStep
  have firstRun : machine.run 1
      (placed allocator world scope parents (entry caller destination request yes no) context origins pending) =
      ([], .exhausted (placed allocator world scope parents
        (PresenceGuardSource.start (waiting caller destination request yes no)
          (.var (slot caller destination request yes no)) request) context origins pending)) := by
    rw [Machine.run_succ_silent _ firstStep]
    rfl
  have guardRun := PresenceGuardSource.source_guard_prefix program allocator world scope parents
    (waiting caller destination request yes no) context origins pending
    (.var (slot caller destination request yes no)) request consistent rows snapshot
  dsimp only at guardRun
  have first := machine.established_and_pending 1
    (CollectedOnceQuerySource.childBudget (decide (request.pattern ∈ rows)) + 10) _ _ [] firstRun
  rw [guardRun] at first
  simp only [List.nil_append] at first
  cases copied : PresenceGuardSource.copyAllocator allocator (decide (request.pattern ∈ rows)) with
  | none =>
      rw [copied] at first
      have stable := machine.run_stable _ 2 _ (fun residual => by rw [first]; simp)
      rw [first] at stable
      exact stable
  | some next =>
      rw [copied] at first
      have last := machine.established_and_pending _ 2 _ _ [] first
      rw [select_prefix program next world scope parents caller context (origins ++ [0, 0]) pending
        destination request yes no _ consistent] at last
      exact last

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.PresenceConditionalSource
