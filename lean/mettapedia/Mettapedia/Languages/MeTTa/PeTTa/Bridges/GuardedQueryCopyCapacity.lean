import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScalarCopyCapacity
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedQueryCollection

/-!
# Sufficient usable identities for the actual collector copy

Every scalar packet without associated syntax needs one usable identity for
its copy, independently of protected names. Boolean packets, in particular
ready ones, are scalar. The theorem constructs success of the existing copying
operation rather than assuming a receipt. It does not cover arbitrary
variable-bearing packets.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedQueryCopyCapacity

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator Token)
open EagerDFS.Destination
open GuardedQueryCollection (boundary returned returnedFlags Flagged)

theorem copy_scalar (allocator : Allocator) (protectedNames : Finset String) (packets : List CollectedAnswer)
    (scalar : ∀ packet ∈ packets, ConstantQuerySource.Scalar packet.value ∧ packet.associated = [])
    (capacity : packets.length ≤ allocator.usableCount) :
    ∃ next copies,
      EagerDFS.Collection.copyOwnedAnswers? allocator protectedNames
        (packets.map (fun packet => (packet.value, packet.associated))) = some (next, copies) ∧
      next.usableCount + packets.length = allocator.usableCount := by
  induction packets generalizing allocator with
  | nil => exact ⟨allocator, [], rfl, by simp⟩
  | cons packet packets ih =>
    obtain ⟨value, associated⟩ := scalar packet List.mem_cons_self
    have positive : 0 < allocator.usableCount := by
      simp only [List.length_cons] at capacity
      omega
    obtain ⟨middle, token, allocated⟩ := (ScalarCopyCapacity.allocateCopy_exists_iff value allocator protectedNames).mpr positive
    have spent := ScalarCopyCapacity.allocateCopy_usableCount value allocated
    have tailCapacity : packets.length ≤ middle.usableCount := by
      simp only [List.length_cons] at capacity
      omega
    obtain ⟨next, copies, copied, remaining⟩ := ih middle
      (fun answer member => scalar answer (List.mem_cons_of_mem packet member)) tailCapacity
    refine ⟨next, (token, EagerDFS.Collection.copyAllocated token packet.value []) :: copies, ?_, ?_⟩
    · simp only [List.map_cons, EagerDFS.Collection.copyOwnedAnswers?, associated, allocated]
      change (EagerDFS.Collection.copyOwnedAnswers? middle protectedNames
        (packets.map (fun packet => (packet.value, packet.associated))) >>= fun result =>
        some (result.1, (token, EagerDFS.Collection.copyAllocated token packet.value []) :: result.2)) = _
      rw [copied]
      rfl
    · simp only [List.length_cons]
      omega

theorem copy_ready (allocator : Allocator) (protectedNames : Finset String) (packets : List CollectedAnswer)
    (ready : ∀ packet ∈ packets, GuardedQueryPackets.Ready packet)
    (capacity : packets.length ≤ allocator.usableCount) :
    ∃ next copies,
      EagerDFS.Collection.copyOwnedAnswers? allocator protectedNames
        (packets.map (fun packet => (packet.value, packet.associated))) = some (next, copies) ∧
      next.usableCount + packets.length = allocator.usableCount :=
  copy_scalar allocator protectedNames packets (GuardedQueryCollection.ready_flagged ready).scalar capacity

/-- Under the explicit Boolean-packet and capacity conditions, collector exit
returns the tuple of the collected values to the retained caller and
preserves the reached world. There is no post-hoc allocation-success premise. -/
theorem return_with_capacity_flags {Context : Type} (program : SpaceSemantics.Program) (allocator : Allocator)
    (world : EagerDFS.World) (packets : List CollectedAnswer) (flags : List Bool) (caller : CollectionCaller Context)
    (parent : CollectionScope Context) (parents : List (CollectionScope Context))
    (flagged : Flagged packets flags) (capacity : packets.length ≤ allocator.usableCount) :
    ∃ next,
      (ScopedQuerySource.machine .relational program).run 1 (boundary allocator world packets caller parent parents) =
        ([], .exhausted (next, ⟨world,
          {parent with frontier := returnedFlags flags caller :: parent.frontier} :: parents⟩)) ∧
      next.usableCount + packets.length = allocator.usableCount := by
  obtain ⟨next, copies, copied, remaining⟩ := copy_scalar allocator
    (collectionSupport (boundary allocator world packets caller parent parents).2) packets flagged.scalar capacity
  refine ⟨next, ?_, remaining⟩
  have returned := GuardedQueryCollection.return_boundary_flags program allocator world packets flags caller parent
    parents flagged
  dsimp only at returned
  rw [copied] at returned
  exact returned

/-- Ready packets return the all-`True` tuple of their count. -/
theorem return_with_capacity {Context : Type} (program : SpaceSemantics.Program) (allocator : Allocator)
    (world : EagerDFS.World) (packets : List CollectedAnswer) (caller : CollectionCaller Context)
    (parent : CollectionScope Context) (parents : List (CollectionScope Context))
    (ready : ∀ packet ∈ packets, GuardedQueryPackets.Ready packet)
    (capacity : packets.length ≤ allocator.usableCount) :
    ∃ next,
      (ScopedQuerySource.machine .relational program).run 1 (boundary allocator world packets caller parent parents) =
        ([], .exhausted (next, ⟨world,
          {parent with frontier := returned packets.length caller :: parent.frontier} :: parents⟩)) ∧
      next.usableCount + packets.length = allocator.usableCount := by
  simp only [GuardedQueryCollection.returned_eq_returnedFlags]
  exact return_with_capacity_flags program allocator world packets _ caller parent parents
    (GuardedQueryCollection.ready_flagged ready) capacity

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedQueryCopyCapacity
