import Mettapedia.Languages.MeTTa.PeTTa.Bridges.PresenceGuardSource

/-!
# Presence guards followed by source work

A relational `let` tests the guard against a required Boolean and enters its
body only on agreement. The prefix retains the reached equations, caller,
older alternatives and allocation boundary. No body effect is performed by
guard preparation, including when allocation suspends.

This is the source `let` spelling, not an implementation theorem for `if`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.PresenceGuardContinuation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS (World)
open EagerDFS.Destination
open LiteralQuerySource (Request)
open ClosedOnceQueryFrame (placed)

def source (required : Bool) (request : Request) (body : Atom) : Atom :=
  .expression [.symbol "let", Effects.boolean required, PresenceGuardSource.source request, body]

def entry (caller : Control) (destination : Atom) (required : Bool) (request : Request) (body : Atom) : Control :=
  {caller with goals := .evaluate (source required request body) destination :: caller.goals}

def slot (caller : Control) (destination : Atom) (required : Bool) (request : Request) (body : Atom) : String :=
  freshName (entry caller destination required request body) 0

def waiting (caller : Control) (destination : Atom) (required : Bool) (request : Request) (body : Atom) : Control :=
  {caller with
    bindings := caller.bindings ++ [(Effects.boolean required, .var (slot caller destination required request body))]
    goals := .evaluate body destination :: caller.goals}

theorem waiting_refined (caller : Control) (destination : Atom) (required : Bool) (request : Request) (body : Atom)
    (consistent : ∃ environment, Solves environment caller.bindings) :
    refine caller.bindings (Effects.boolean required) (.var (slot caller destination required request body)) =
      some (waiting caller destination required request body).bindings := by
  exact ClosedOnceQueryFrame.refine_fresh_closed _ _ _
    (ClosedOnceQueryFrame.fresh_for_bindings (entry caller destination required request body) _
      (freshName_not_mem _ _)) consistent (PresenceGuardSource.read_boolean required)

theorem waiting_consistent (caller : Control) (destination : Atom) (required : Bool) (request : Request) (body : Atom)
    (consistent : ∃ environment, Solves environment caller.bindings) :
    ∃ environment, Solves environment (waiting caller destination required request body).bindings :=
  ClosedOnceQueryFrame.refined_consistent _ _ _ (waiting_refined caller destination required request body consistent)

set_option maxHeartbeats 1200000 in
theorem entry_prefix {Context : Type} (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (caller : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context)) (destination : Atom)
    (required : Bool) (request : Request) (body : Atom)
    (consistent : ∃ environment, Solves environment caller.bindings) :
    (EagerDFSStreaming.machine program (.scopedDestination Context .relational)).run 3
      (placed allocator world scope parents (entry caller destination required request body) context origins pending) =
      ([], .exhausted (placed allocator world scope parents
        (PresenceGuardSource.start (waiting caller destination required request body)
          (.var (slot caller destination required request body)) request) context origins pending)) := by
  have refined := waiting_refined caller destination required request body consistent
  simp [Machine.run, EagerDFSStreaming.machine, placed, entry, source,
    scopeStep, enterCollapse?, enterSuperpose?, EagerDFS.Destination.machine, prepare, replace,
    letGoals, rigid, callable, StdLib.known, Eval.ioHead, Effects.boolean,
    PresenceGuardSource.source, PresenceGuardSource.start, installChild, retainChild, waiting, slot] at refined ⊢
  simp [refined]

/-- A previously constrained Boolean slot accepts precisely the same Boolean.
The consistency premise concerns the inherited equations, not a source result. -/
theorem refine_boolean_slot (bindings : Equations) (name : String) (required observed : Bool)
    (member : (Effects.boolean required, .var name) ∈ bindings)
    (consistent : ∃ environment, Solves environment bindings) :
    refine bindings (Effects.boolean observed) (.var name) =
      if observed = required then some (bindings ++ [(Effects.boolean observed, .var name)]) else none := by
  by_cases same : observed = required
  · subst observed
    rw [if_pos rfl]
    obtain ⟨environment, solved⟩ := consistent
    exact (refine_iff _ _ _ _).mpr ⟨rfl, environment, solved, solved _ member⟩
  · rw [if_neg same]
    cases refined : refine bindings (Effects.boolean observed) (.var name) with
    | none => rfl
    | some result =>
        obtain ⟨_, environment, solved, equal⟩ := (refine_iff _ _ _ _).mp refined
        have old := solved _ member
        rw [PresenceGuardSource.read_boolean] at old equal
        have impossible : observed = required := by
          simpa [Effects.boolean] using equal.trans old.symm
        exact (same impossible).elim

def reached (caller : Control) (destination : Atom) (required : Bool) (request : Request) (body : Atom)
    (present : Bool) : Control :=
  let kept := waiting caller destination required request body
  let bindings := PresenceGuardSource.comparisonBindings kept
    (.var (slot caller destination required request body)) request present ++
      [(Effects.boolean present, .var (slot caller destination required request body))]
  {kept with bindings}

set_option maxHeartbeats 1200000 in
theorem delivered_step {Context : Type} (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (caller : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context)) (destination : Atom)
    (required present : Bool) (request : Request) (body : Atom)
    (consistent : ∃ environment, Solves environment caller.bindings) :
    scopeStep .relational program (placed allocator world scope parents
      (PresenceGuardSource.delivered (waiting caller destination required request body)
        (.var (slot caller destination required request body)) request present) context origins pending) =
      .silent (if present = required then
        placed allocator world scope parents (reached caller destination required request body present)
          context origins pending
      else (allocator, ⟨world, {scope with frontier := pending} :: parents⟩)) := by
  have consistentWaiting := waiting_consistent caller destination required request body consistent
  have consistentReadout := ClosedOnceQueryFrame.refined_consistent _ _ _
    (PresenceGuardSource.comparison_refined (waiting caller destination required request body)
      (.var (slot caller destination required request body)) request present consistentWaiting)
  have refined := refine_boolean_slot
    (PresenceGuardSource.comparisonBindings (waiting caller destination required request body)
      (.var (slot caller destination required request body)) request present)
    (slot caller destination required request body) required present
    (by simp [PresenceGuardSource.comparisonBindings, PresenceGuardSource.emptyBindings,
      PresenceGuardSource.tupleBindings, waiting]) consistentReadout
  simp only [placed, PresenceGuardSource.delivered, scopeStep, enterCollapse?, enterSuperpose?,
    EagerDFS.Destination.machine, refined]
  by_cases same : present = required <;> simp [same, installChild, retainChild, reached]

/-- Complete source guard prefix, including Boolean refusal and the live
collection-allocation residual. The body is still pending in the result. -/
theorem source_prefix {Context : Type} (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (caller : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context)) (destination : Atom)
    (required : Bool) (request : Request) (body : Atom)
    (consistent : ∃ environment, Solves environment caller.bindings)
    (rows : List Atom) (snapshot : world.state.read request.handle = some rows) :
    let present := decide (request.pattern ∈ rows)
    let kept := waiting caller destination required request body
    let joined := Atom.var (slot caller destination required request body)
    (EagerDFSStreaming.machine program (.scopedDestination Context .relational)).run
      (3 + (CollectedOnceQuerySource.childBudget present + 10) + 1)
      (placed allocator world scope parents (entry caller destination required request body) context origins pending) =
      ([], match PresenceGuardSource.copyAllocator allocator present with
        | some next => .exhausted (if present = required then
            placed next world scope parents (reached caller destination required request body present)
              context (origins ++ [0, 0]) pending
          else (next, ⟨world, {scope with frontier := pending} :: parents⟩))
        | none => .suspended .allocation (PresenceGuardSource.collectionEnd allocator world scope parents
            kept context origins pending joined request present)) := by
  dsimp only
  let machine := EagerDFSStreaming.machine program (.scopedDestination Context .relational)
  have entryRun := entry_prefix program allocator world scope parents caller context origins pending
    destination required request body consistent
  have guardRun := PresenceGuardSource.source_guard_prefix program allocator world scope parents
    (waiting caller destination required request body) context origins pending
    (.var (slot caller destination required request body)) request
    (waiting_consistent caller destination required request body consistent) rows snapshot
  dsimp only at guardRun
  have first := machine.established_and_pending 3
    (CollectedOnceQuerySource.childBudget (decide (request.pattern ∈ rows)) + 10) _ _ [] entryRun
  rw [guardRun] at first
  simp only [List.nil_append] at first
  cases copied : PresenceGuardSource.copyAllocator allocator (decide (request.pattern ∈ rows)) with
  | none =>
      rw [copied] at first
      have stable := machine.run_stable _ 1 _ (fun residual => by rw [first]; simp)
      rw [first] at stable
      exact stable
  | some next =>
      rw [copied] at first
      have tail := machine.established_and_pending _ 1 _ _ [] first
      have last := delivered_step program next world scope parents caller context
        (origins ++ [0, 0]) pending destination required (decide (request.pattern ∈ rows)) request body consistent
      have step := EagerDFSStreaming.Scoped.step_scope .relational program
        (placed next world scope parents
          (PresenceGuardSource.delivered (waiting caller destination required request body)
            (.var (slot caller destination required request body)) request (decide (request.pattern ∈ rows)))
          context (origins ++ [0, 0]) pending)
      rw [last] at step
      rw [Machine.run_succ_silent _ step] at tail
      exact tail

/-- Guard elimination composes with arbitrary subsequent execution. The
continuation may mutate, fail, publish, suspend or encounter an unavailable
operation; it resumes from the exact reached source control, not its entrance. -/
theorem accepted_continuation {Context : Type} (program : SpaceSemantics.Program)
    (allocator next : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (caller : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context)) (destination : Atom)
    (required : Bool) (request : Request) (body : Atom)
    (consistent : ∃ environment, Solves environment caller.bindings)
    (rows : List Atom) (snapshot : world.state.read request.handle = some rows)
    (agrees : decide (request.pattern ∈ rows) = required)
    (allocated : PresenceGuardSource.copyAllocator allocator required = some next) (fuel : Nat) :
    (EagerDFSStreaming.machine program (.scopedDestination Context .relational)).run
      (3 + (CollectedOnceQuerySource.childBudget required + 10) + 1 + fuel)
      (placed allocator world scope parents (entry caller destination required request body) context origins pending) =
    (EagerDFSStreaming.machine program (.scopedDestination Context .relational)).run fuel
      (placed next world scope parents (reached caller destination required request body required)
        context (origins ++ [0, 0]) pending) := by
  have guarded := source_prefix program allocator world scope parents caller context origins pending
    destination required request body consistent rows snapshot
  dsimp only at guarded
  simp only [agrees, allocated, ↓reduceIte] at guarded
  have composed := (EagerDFSStreaming.machine program (.scopedDestination Context .relational)).established_and_pending
    _ fuel _ _ [] guarded
  simpa only [List.nil_append, Prod.mk.eta] using composed

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.PresenceGuardContinuation
