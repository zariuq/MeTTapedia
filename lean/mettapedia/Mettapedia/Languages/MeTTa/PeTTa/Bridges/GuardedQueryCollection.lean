import Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedQueryPackets
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedQueryGrowth

/-!
# Actual copied return of completed guarded-query collectors

Boolean packets are copied by the existing generative allocator, and the
returned tuple carries their values in order. Ready guarded-query packets
carry only `True`. A successful return retains the actual new allocator and
original caller; allocation refusal retains the entire reached cursor,
including body writes. No successful copy result is invented from the packet
count.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedQueryCollection

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator Token)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS (World)
open EagerDFS.Destination

/-- Collected packets carrying exactly the Boolean values `flags`, in order,
with no associated syntax. -/
def Flagged (packets : List CollectedAnswer) (flags : List Bool) : Prop :=
  packets.map CollectedAnswer.value = flags.map Effects.boolean ∧ ∀ packet ∈ packets, packet.associated = []

theorem ready_flagged {packets : List CollectedAnswer}
    (ready : ∀ packet ∈ packets, GuardedQueryPackets.Ready packet) :
    Flagged packets (List.replicate packets.length true) := by
  refine ⟨?_, fun packet member => (ready packet member).2⟩
  rw [List.map_replicate, List.eq_replicate_iff]
  refine ⟨by simp, fun value member => ?_⟩
  obtain ⟨packet, included, rfl⟩ := List.mem_map.mp member
  exact (ready packet included).1

theorem Flagged.scalar {packets : List CollectedAnswer} {flags : List Bool} (flagged : Flagged packets flags) :
    ∀ packet ∈ packets, ConstantQuerySource.Scalar packet.value ∧ packet.associated = [] := by
  intro packet member
  obtain ⟨flag, _, same⟩ := List.mem_map.mp (flagged.1 ▸ List.mem_map_of_mem member :
    packet.value ∈ flags.map Effects.boolean)
  exact ⟨same ▸ .grounded _, flagged.2 packet member⟩

theorem owned_values {allocator next : Allocator} {raw : List (Atom × List Atom)}
    {copies : List (Token × (Atom × List Atom))}
    (trace : EagerDFS.Collection.OwnedCopies allocator raw next copies)
    (flagged : ∀ row ∈ raw, (∃ flag, row.1 = Effects.boolean flag) ∧ row.2 = []) :
    copies.map (fun row => row.2.1) = raw.map Prod.fst := by
  induction trace with
  | nil => rfl
  | @cons allocator middle next token handle value associated rest copies allocated later ih =>
    obtain ⟨⟨flag, rfl⟩, rfl⟩ := flagged (value, associated) List.mem_cons_self
    have tail := ih (fun row member => flagged row (List.mem_cons_of_mem _ member))
    simp [EagerDFS.Collection.copyAllocated, HE.Spec.Type.RuntimeRefinement.renameTypeVars, Effects.boolean, tail]

theorem copied_values (allocator next : Allocator) (protectedNames : Finset String)
    (packets : List CollectedAnswer) (flags : List Bool) (copies : List (Token × (Atom × List Atom)))
    (flagged : Flagged packets flags)
    (copied : EagerDFS.Collection.copyOwnedAnswers? allocator protectedNames
      (packets.map (fun packet => (packet.value, packet.associated))) = some (next, copies)) :
    copies.map (fun row => row.2.1) = flags.map Effects.boolean := by
  have actual := owned_values (EagerDFS.Collection.copyOwnedAnswers_trace copied) (by
    intro row member
    obtain ⟨packet, included, rfl⟩ := List.mem_map.mp member
    obtain ⟨flag, _, same⟩ := List.mem_map.mp (flagged.1 ▸ List.mem_map_of_mem included :
      packet.value ∈ flags.map Effects.boolean)
    exact ⟨⟨flag, same.symm⟩, flagged.2 packet included⟩)
  rw [actual, ← flagged.1, List.map_map]
  rfl

/-- The tuple returned for collected Boolean values. -/
def flagTuple (flags : List Bool) : Atom := .expression (flags.map Effects.boolean)

/-- The tuple returned for `count` ready packets. -/
def tuple (count : Nat) : Atom := .expression (List.replicate count (Effects.boolean true))

theorem tuple_eq_flagTuple (count : Nat) : tuple count = flagTuple (List.replicate count true) := by
  simp [tuple, flagTuple, List.map_replicate]

def returnedFlags {Context : Type} (flags : List Bool) (caller : CollectionCaller Context) : CollectionWork Context :=
  ({caller.1 with goals := .equate (flagTuple flags) caller.2.1 :: caller.1.goals}, caller.2.2.1, caller.2.2.2)

def returned {Context : Type} (count : Nat) (caller : CollectionCaller Context) : CollectionWork Context :=
  ({caller.1 with goals := .equate (tuple count) caller.2.1 :: caller.1.goals}, caller.2.2.1, caller.2.2.2)

theorem returned_eq_returnedFlags {Context : Type} (count : Nat) (caller : CollectionCaller Context) :
    returned count caller = returnedFlags (List.replicate count true) caller := by
  simp only [returned, returnedFlags, tuple_eq_flagTuple]

def boundary {Context : Type} (allocator : Allocator) (world : World) (packets : List CollectedAnswer)
    (caller : CollectionCaller Context) (parent : CollectionScope Context) (parents : List (CollectionScope Context)) :
    ScopedCursor Context :=
  (allocator, ⟨world, ⟨[], packets, some caller⟩ :: parent :: parents⟩)

theorem allocated_work {Context : Type} (allocator next : Allocator) (protectedNames : Finset String)
    (packets : List CollectedAnswer) (flags : List Bool) (copies : List (Token × (Atom × List Atom)))
    (caller : CollectionCaller Context) (flagged : Flagged packets flags)
    (copied : EagerDFS.Collection.copyOwnedAnswers? allocator protectedNames
      (packets.map (fun packet => (packet.value, packet.associated))) = some (next, copies)) :
    allocatedWork copies caller = returnedFlags flags caller := by
  unfold allocatedWork returnedFlags flagTuple
  rw [copied_values allocator next protectedNames packets flags copies flagged copied]

theorem boundary_step {Context : Type} (program : SpaceSemantics.Program) (allocator : Allocator)
    (world : World) (packets : List CollectedAnswer) (caller : CollectionCaller Context)
    (parent : CollectionScope Context) (parents : List (CollectionScope Context))
    (flat : ∀ packet ∈ packets, packet.associated = []) :
    let before := boundary allocator world packets caller parent parents
    (ScopedQuerySource.machine .relational program).step before =
      some (match finishAllocated? before with
        | some next => .silent next
        | none => .call .allocation before) := by
  simp [boundary, ScopedQuerySource.machine, ScopedQuerySource.step, ScopedQuerySource.syntaxStep,
    ScopedQuerySource.constrainedCall, ScopedQuerySource.mutationCall, ScopedQuerySource.queryStep,
    scopeStep]
  rw [if_pos flat]
  rfl

/-- Both actual copy outcomes are retained. Failure does not roll back body
effects or fabricate an empty result; success returns the exact tuple of the
collected Boolean values. -/
theorem return_boundary_flags {Context : Type} (program : SpaceSemantics.Program) (allocator : Allocator)
    (world : World) (packets : List CollectedAnswer) (flags : List Bool) (caller : CollectionCaller Context)
    (parent : CollectionScope Context) (parents : List (CollectionScope Context))
    (flagged : Flagged packets flags) :
    let before := boundary allocator world packets caller parent parents
    (ScopedQuerySource.machine .relational program).run 1 before =
      ([], match EagerDFS.Collection.copyOwnedAnswers? allocator (collectionSupport before.2)
        (packets.map (fun packet => (packet.value, packet.associated))) with
        | none => .suspended .allocation before
        | some (next, _) => .exhausted (next, ⟨world,
            {parent with frontier := returnedFlags flags caller :: parent.frontier} :: parents⟩)) := by
  dsimp only
  let before := boundary allocator world packets caller parent parents
  have step := boundary_step program allocator world packets caller parent parents flagged.2
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
      flagged.2 copied
    rw [allocated_work allocator next (collectionSupport before.2) packets flags copies caller flagged copied] at finished
    change finishAllocated? (boundary allocator world packets caller parent parents) =
      some (next, ⟨world, {parent with frontier := returnedFlags flags caller :: parent.frontier} :: parents⟩) at finished
    simp only [Machine.run, step, finished]

/-- Ready packets return the all-`True` tuple of their count. -/
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
  simp only [returned_eq_returnedFlags]
  exact return_boundary_flags program allocator world packets _ caller parent parents (ready_flagged ready)

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedQueryCollection
