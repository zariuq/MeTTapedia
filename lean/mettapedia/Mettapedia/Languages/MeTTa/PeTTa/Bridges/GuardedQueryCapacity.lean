import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScalarCopyCapacity
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedNestedQuerySource

/-!
# One identity of consumed or reserved capacity per guarded candidate

A held witness consumes one scalar-copy identity and emits no packet.
A fresh publication consumes no copy identity yet and emits one packet.
The exact balance follows from the executed publication receipt. Existing
collected packets are counted without assuming their later copy can succeed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedQueryCapacity

open EagerDFS.Destination
open NamedPresenceConditional (Input)
open NamedGuardedInsertionSource (Body)
open NamedGuardedCandidateExecution (Advance Publication execute)
open NamedGuardedCandidateBatch (State)

variable {Context : Type}

theorem publication_conservation (input : Input Context) (body : Body) (after : Advance)
    (published : Publication input body after) :
    after.allocator.usableCount + 1 = input.allocator.usableCount + after.answers.length := by
  cases published with
  | held rows snapshot present copied unchanged noPacket =>
    rw [noPacket, List.length_nil, Nat.add_zero]
    exact ScalarCopyCapacity.copyAllocator_true_usableCount copied
  | fresh guard evidence rows middle snapshot absent first second allocator packet =>
    rw [allocator, packet]
    rfl

theorem execute_conservation (input : Input Context) (body : Body) (after : Advance)
    (completed : (execute input body).result = .advanced after) :
    after.allocator.usableCount + 1 = input.allocator.usableCount + after.answers.length :=
  publication_conservation input body after (NamedGuardedCandidateExecution.execute_publication input body after completed)

theorem invoke_conservation (program : SpaceSemantics.Program) (template : GuardedNestedQuerySource.Template)
    (caller : Control) (before : State Context) (context : Context) (origins : List Nat)
    (pending : List (CollectionWork Context)) (after : State Context)
    (completed : (GuardedNestedQuerySource.invoke program template caller before context origins pending).execution.stop =
      .complete after) :
    after.allocator.usableCount + 1 + before.scope.collected.length =
      before.allocator.usableCount + after.scope.collected.length := by
  obtain ⟨principal, request, advance, resolved, requested, advanced, rfl⟩ :=
    GuardedNestedQuerySource.completed_origin program template caller before context origins pending after completed
  have balance := execute_conservation
    ((template.candidate caller context origins request).input program before pending) template.body advance advanced
  change advance.allocator.usableCount + 1 = before.allocator.usableCount + advance.answers.length at balance
  simp only [State.advance, List.length_append]
  omega

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedQueryCapacity
