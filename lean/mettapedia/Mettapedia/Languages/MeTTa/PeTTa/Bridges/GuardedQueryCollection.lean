import Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedQueryPackets
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedQueryGrowth

/-!
# Actual copied return of completed guarded-query collectors

Ready Boolean packets are copied by the existing generative allocator. A
successful return retains the actual new allocator and original caller;
allocation refusal retains the entire reached cursor, including body writes.
No successful copy result is invented from the packet count.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedQueryCollection

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator Token)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS (World)
open EagerDFS.Destination

theorem owned_true_values {allocator next : Allocator} {raw : List (Atom × List Atom)}
    {copies : List (Token × (Atom × List Atom))}
    (trace : EagerDFS.Collection.OwnedCopies allocator raw next copies)
    (ready : ∀ row ∈ raw, row.1 = Effects.boolean true ∧ row.2 = []) :
    copies.map (fun row => row.2.1) = List.replicate raw.length (Effects.boolean true) := by
  induction trace with
  | nil => rfl
  | @cons allocator middle next token handle value associated rest copies allocated later ih =>
    obtain ⟨rfl, rfl⟩ := ready (value, associated) List.mem_cons_self
    have tail := ih (fun row member => ready row (List.mem_cons_of_mem _ member))
    simp [EagerDFS.Collection.copyAllocated, HE.Spec.Type.RuntimeRefinement.renameTypeVars, Effects.boolean, tail, List.replicate_succ]

theorem copied_true_values (allocator next : Allocator) (protectedNames : Finset String)
    (packets : List CollectedAnswer) (copies : List (Token × (Atom × List Atom)))
    (ready : ∀ packet ∈ packets, GuardedQueryPackets.Ready packet)
    (copied : EagerDFS.Collection.copyOwnedAnswers? allocator protectedNames
      (packets.map (fun packet => (packet.value, packet.associated))) = some (next, copies)) :
    copies.map (fun row => row.2.1) = List.replicate packets.length (Effects.boolean true) := by
  have actual := owned_true_values (EagerDFS.Collection.copyOwnedAnswers_trace copied) (by
    intro row member
    obtain ⟨packet, included, rfl⟩ := List.mem_map.mp member
    exact ready packet included)
  simpa only [List.length_map] using actual

def tuple (count : Nat) : Atom := .expression (List.replicate count (Effects.boolean true))

def returned {Context : Type} (count : Nat) (caller : CollectionCaller Context) : CollectionWork Context :=
  ({caller.1 with goals := .equate (tuple count) caller.2.1 :: caller.1.goals}, caller.2.2.1, caller.2.2.2)

def boundary {Context : Type} (allocator : Allocator) (world : World) (packets : List CollectedAnswer)
    (caller : CollectionCaller Context) (parent : CollectionScope Context) (parents : List (CollectionScope Context)) :
    ScopedCursor Context :=
  (allocator, ⟨world, ⟨[], packets, some caller⟩ :: parent :: parents⟩)

theorem allocated_work {Context : Type} (allocator next : Allocator) (protectedNames : Finset String)
    (packets : List CollectedAnswer) (copies : List (Token × (Atom × List Atom))) (caller : CollectionCaller Context)
    (ready : ∀ packet ∈ packets, GuardedQueryPackets.Ready packet)
    (copied : EagerDFS.Collection.copyOwnedAnswers? allocator protectedNames
      (packets.map (fun packet => (packet.value, packet.associated))) = some (next, copies)) :
    allocatedWork copies caller = returned packets.length caller := by
  unfold allocatedWork returned tuple
  rw [copied_true_values allocator next protectedNames packets copies ready copied]

theorem boundary_step {Context : Type} (program : SpaceSemantics.Program) (allocator : Allocator)
    (world : World) (packets : List CollectedAnswer) (caller : CollectionCaller Context)
    (parent : CollectionScope Context) (parents : List (CollectionScope Context))
    (ready : ∀ packet ∈ packets, GuardedQueryPackets.Ready packet) :
    let before := boundary allocator world packets caller parent parents
    (ScopedQuerySource.machine .relational program).step before =
      some (match finishAllocated? before with
        | some next => .silent next
        | none => .call .allocation before) := by
  have allReady : ∀ packet ∈ packets, packet.associated = [] := fun packet member => (ready packet member).2
  simp [boundary, ScopedQuerySource.machine, ScopedQuerySource.step, ScopedQuerySource.syntaxStep,
    ScopedQuerySource.constrainedCall, ScopedQuerySource.mutationCall, ScopedQuerySource.queryStep,
    scopeStep]
  rw [if_pos allReady]
  rfl

/-- Both actual copy outcomes are retained. Failure does not roll back body
effects or fabricate an empty result; success returns the exact Boolean tuple. -/
theorem return_boundary {Context : Type} (program : SpaceSemantics.Program) (allocator : Allocator)
    (world : World) (packets : List CollectedAnswer) (caller : CollectionCaller Context)
    (parent : CollectionScope Context) (parents : List (CollectionScope Context))
    (ready : ∀ packet ∈ packets, GuardedQueryPackets.Ready packet) :
    let before := boundary allocator world packets caller parent parents
    (ScopedQuerySource.machine .relational program).run 1 before =
      ([], match EagerDFS.Collection.copyOwnedAnswers? allocator (collectionSupport before.2)
        (packets.map (fun packet => (packet.value, packet.associated))) with
        | none => .suspended .allocation before
        | some (next, _) => .exhausted (next, ⟨world,
            {parent with frontier := returned packets.length caller :: parent.frontier} :: parents⟩)) := by
  dsimp only
  let before := boundary allocator world packets caller parent parents
  have step := boundary_step program allocator world packets caller parent parents ready
  dsimp only at step
  cases copied : EagerDFS.Collection.copyOwnedAnswers? allocator (collectionSupport before.2)
      (packets.map (fun packet => (packet.value, packet.associated))) with
  | none =>
    have failed : finishAllocated? before = none := by
      dsimp only [before, boundary] at copied
      simp [before, boundary, finishAllocated?, copied]
    change finishAllocated? (boundary allocator world packets caller parent parents) = none at failed
    simp only [Machine.run, step, failed]
  | some result =>
    obtain ⟨next, copies⟩ := result
    have finished := finishAllocated_completed allocator next world packets caller parent parents copies
      (fun packet member => (ready packet member).2) copied
    rw [allocated_work allocator next (collectionSupport before.2) packets copies caller ready copied] at finished
    change finishAllocated? (boundary allocator world packets caller parent parents) =
      some (next, ⟨world, {parent with frontier := returned packets.length caller :: parent.frontier} :: parents⟩) at finished
    simp only [Machine.run, step, finished]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedQueryCollection
