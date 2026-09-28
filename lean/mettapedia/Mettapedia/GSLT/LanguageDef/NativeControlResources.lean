import Mettapedia.Machines.ResourceOwnership
import Mettapedia.Machines.ResourceOwnershipOpenExtension
import Mettapedia.Machines.ResourceOwnershipOptimality
import Mettapedia.Machines.ExclusiveSequenceMutation
import Mettapedia.Machines.Cursor.OwnedLifecycle
import Mettapedia.Machines.Cursor.AdaptiveBudget
import Mettapedia.Machines.Cursor.RelationalTransfer
import Mettapedia.GSLT.LanguageDef.NativeControlBoundedCursor
import Mettapedia.GSLT.LanguageDef.NativeControlTwoStackCut
import Mettapedia.GSLT.LanguageDef.NativeControlOwnedCursor
import Mettapedia.GSLT.LanguageDef.NativeControlOwnedCollection

/-!
# Owned, resumable native control

These modules connect bounded answer observation to resource ownership and
delimited cancellation using the existing cursor protocol.

* `NativeControlBoundedCursor` separates answer allowance, scheduling budget,
  and exhaustion while preserving the actual residual and world.
* `NativeControlTwoStackCut` decodes the interleaved tier and host stacks,
  accounts for each native frame once, and refines the scoped `once` step.
* `NativeControlOwnedCollection` pins answer graphs between provider polls;
  `NativeControlOwnedCursor` exports them to an enclosing owner before a cut.
* `ResourceOwnership` traces shared, cyclic graphs. Its open-extension laws
  permit fresh resources and roots; its byte bounds require transitive
  footprint and cell-size bounds in addition to a bound on root count.
  `ResourceOwnershipOptimality` proves minimal cell count and declared bytes
  among heaps preserving fixed-address, complete root-path observations.
* `ExclusiveSequenceMutation` compares in-place extension with fresh allocation
  under a transitive exclusivity condition.
* `AdaptiveBudget` preserves execution under history-dependent budget choices;
  `RelationalTransfer` permits representation changes without a canonical
  state decoder, subject to a local protocol bisimulation.

The heap model is a specification of reachable storage, not an executable
collector. The stack model is a refinement target, not a proof about C memory.
Concrete root enumeration, delimiter lifetime authority, answer export before
rollback, relocation, concurrency, and effectful cleanup require corresponding
implementation proofs. Semantic preservation supplies no profitability claim
for a representation switch or policy.
-/
