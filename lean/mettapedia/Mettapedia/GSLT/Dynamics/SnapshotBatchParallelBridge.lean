import Mettapedia.Machines.SnapshotBatch
import Mettapedia.GSLT.Dynamics.CertifiedBatchParallelBridge

/-!
# Snapshot/private-write kernels as certified parallel execution

The concrete indexed-store updates in `Machines.SnapshotBatch` supply a
literal commuting square. This module transports that proved square into the
existing parallel authority interface and lifts whole-batch permutation
invariance into `CertifiedBatch`.

The destination check grants semantic separation only for the kernel API:
immutable shared reads, private writes, and stable logical seeds. An account
receipt still has to fund the actual batch. Neither resource affordability nor
a favorable cost estimate proves the square.
-/

namespace Mettapedia.GSLT.Dynamics.SnapshotBatchParallelBridge

open Mettapedia.Machines.SnapshotBatch
open Mettapedia.GSLT.Core.ObservationControlContract
open Mettapedia.GSLT.Core.ResourceAwareControl
open Mettapedia.GSLT.Dynamics.QueryRevision
open Mettapedia.GSLT.Dynamics.EventValuation
open Mettapedia.GSLT.Dynamics.CertifiedBatchParallelBridge

universe uSnapshot uItem uSeed uId uValue uView uGuard uCandidate uAccount

variable {Snapshot : Type uSnapshot} {Item : Type uItem}
  {Seed : Type uSeed} {Id : Type uId} {Value : Type uValue}
  {View : Type uView} [DecidableEq Id]

variable (kernel : Kernel Snapshot Item Seed Id Value)
  (snapshot : Snapshot) (seeds : Item → Seed) (observe : (Id → Value) → View)

/-- Both orders reach exactly the same store. The square is constructed from
the kernel's update law, not supplied as an admission assumption. -/
def privateWriteSquare (state : Id → Value) (first second : Item)
    (distinct : kernel.destination first ≠ kernel.destination second) :
    (deterministicTheory (kernel.step snapshot seeds) observe).StrongSquare
      first second state where
  afterFirst := kernel.step snapshot seeds state first
  afterSecond := kernel.step snapshot seeds state second
  joined := kernel.step snapshot seeds (kernel.step snapshot seeds state first) second
  firstFromSource := rfl
  secondFromSource := rfl
  secondAfterFirst := rfl
  firstAfterSecond := kernel.step_commute snapshot seeds state first second distinct

/-- The executable destination inequality is conservative semantic admission
for the full state observer, hence for any projection of that observer. -/
def privateWriteBackend :
    ParallelBackend (deterministicTheory (kernel.step snapshot seeds) observe) where
  valuation := eventCount (deterministicTheory (kernel.step snapshot seeds) observe)
  Admits first second _state := kernel.destination first ≠ kernel.destination second
  sound := by
    intro first second state distinct
    exact ⟨⟨(privateWriteSquare kernel snapshot seeds observe state
      first second distinct).toQuerySquare⟩,
      additive_compatible (fun _item => 1) first second⟩

/-- Full-batch serializability is derived from indexed-store locality and
destination uniqueness. The candidate and result observers remain separate. -/
theorem privateBatch_serializes (initial : Id → Value) (items : List Item)
    (disjoint : kernel.Disjoint items) :
    (deterministicSemantics (kernel.step snapshot seeds) observe).SerializesTo
      initial items (kernel.run snapshot seeds initial items) := by
  refine ⟨rfl, ?_⟩
  intro ordering permutation
  refine ⟨kernel.run snapshot seeds initial ordering, rfl, ?_⟩
  exact congrArg observe
    (kernel.run_perm snapshot seeds initial permutation.symm disjoint).symm

/-- Assemble semantic permission with the independently supplied candidate
observation and exact resource decomposition. A cost estimate is not used. -/
def certifyPrivateBatch {Guard : Type uGuard} {Candidate : Type uCandidate}
    {Account : Type uAccount} [AddMonoid Account]
    (contract : Contract Item Guard Candidate)
    (initial : Id → Value) (items : List Item)
    (nonempty : items ≠ []) (disjoint : kernel.Disjoint items)
    (candidateInvariant : PermutationInvariantAt contract.observer.observe items)
    (demand : Item → Account) (inventory : Account)
    (resources : BatchSeparation Account demand inventory items) :
    CertifiedBatch contract
      (deterministicSemantics (kernel.step snapshot seeds) observe)
      initial (kernel.run snapshot seeds initial items)
      Account demand inventory items where
  nonempty := nonempty
  candidateInvariant := candidateInvariant
  executionSerializable := privateBatch_serializes kernel snapshot seeds observe
    initial items disjoint
  resources := resources

/-- A partitioned realization produces precisely the certified reference
store, so every declared state observer agrees without a further quotient. -/
theorem partitioned_observation (initial : Id → Value) (parts : List (List Item))
    (items : List Item) (coverage : parts.flatten.Perm items)
    (disjoint : kernel.Disjoint items) :
    observe (kernel.partitioned snapshot seeds initial parts) =
      observe (kernel.run snapshot seeds initial items) :=
  congrArg observe
    (kernel.partitioned_eq_run snapshot seeds initial parts items coverage disjoint)

namespace Controls

open Mettapedia.Machines.SnapshotBatch.Controls

theorem distinct_private_owners_admitted :
    (privateWriteBackend privateKernel 10 (fun item => item.val + 1) id).Admits
      (0 : Fin 3) (1 : Fin 3) (fun _ => 0) := by
  change (0 : Fin 3) ≠ 1
  decide

theorem aliased_owners_declined :
    ¬ (privateWriteBackend aliasedKernel () (fun _ => ()) id).Admits
      true false (fun _ => 1) := by
  change ¬ (() ≠ ())
  decide

end Controls

end Mettapedia.GSLT.Dynamics.SnapshotBatchParallelBridge
