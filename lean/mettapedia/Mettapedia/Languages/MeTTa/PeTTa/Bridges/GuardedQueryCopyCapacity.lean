import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScalarCopyCapacity
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedQueryCollection

/-!
# Sufficient usable identities for the actual collector copy

Every ready packet contains a scalar Boolean and no associated syntax. Its
copy therefore needs one usable identity, independently of protected names.
The theorem constructs success of the existing copying operation rather than
assuming a receipt. It does not cover arbitrary variable-bearing packets.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedQueryCopyCapacity

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator Token)
open EagerDFS.Destination
open GuardedQueryCollection (boundary returned)

theorem copy_ready (allocator : Allocator) (protectedNames : Finset String) (packets : List CollectedAnswer)
    (ready : ∀ packet ∈ packets, GuardedQueryPackets.Ready packet)
    (capacity : packets.length ≤ allocator.usableCount) :
    ∃ next copies,
      EagerDFS.Collection.copyOwnedAnswers? allocator protectedNames
        (packets.map (fun packet => (packet.value, packet.associated))) = some (next, copies) ∧
      next.usableCount + packets.length = allocator.usableCount := by
  induction packets generalizing allocator with
  | nil => exact ⟨allocator, [], rfl, by simp⟩
  | cons packet packets ih =>
    obtain ⟨value, associated⟩ := ready packet List.mem_cons_self
    have scalar : ConstantQuerySource.Scalar packet.value := by
      rw [value]
      exact .grounded _
    have positive : 0 < allocator.usableCount := by
      simp only [List.length_cons] at capacity
      omega
    obtain ⟨middle, token, allocated⟩ := (ScalarCopyCapacity.allocateCopy_exists_iff scalar allocator protectedNames).mpr positive
    have spent := ScalarCopyCapacity.allocateCopy_usableCount scalar allocated
    have tailCapacity : packets.length ≤ middle.usableCount := by
      simp only [List.length_cons] at capacity
      omega
    obtain ⟨next, copies, copied, remaining⟩ := ih middle
      (fun answer member => ready answer (List.mem_cons_of_mem packet member)) tailCapacity
    refine ⟨next, (token, EagerDFS.Collection.copyAllocated token packet.value []) :: copies, ?_, ?_⟩
    · simp only [List.map_cons, EagerDFS.Collection.copyOwnedAnswers?, associated, allocated]
      change (EagerDFS.Collection.copyOwnedAnswers? middle protectedNames
        (packets.map (fun packet => (packet.value, packet.associated))) >>= fun result =>
        some (result.1, (token, EagerDFS.Collection.copyAllocated token packet.value []) :: result.2)) = _
      rw [copied]
      rfl
    · simp only [List.length_cons]
      omega

/-- Under the explicit scalar-packet and capacity conditions, collector exit
returns the true tuple to the retained caller and preserves the reached
world. There is no post-hoc allocation-success premise. -/
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
  obtain ⟨next, copies, copied, remaining⟩ := copy_ready allocator
    (collectionSupport (boundary allocator world packets caller parent parents).2) packets ready capacity
  refine ⟨next, ?_, remaining⟩
  have returned := GuardedQueryCollection.return_boundary program allocator world packets caller parent parents ready
  dsimp only at returned
  rw [copied] at returned
  exact returned

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedQueryCopyCapacity
