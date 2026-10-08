import Mettapedia.Machines.CMemory.Block
import Mettapedia.Machines.CMemory.Primitives
import Mettapedia.Machines.CMemory.Assertions
import Mettapedia.Machines.CMemory.Values
import Mettapedia.Machines.CMemory.Array
import Mettapedia.Machines.CMemory.Examples
import Mettapedia.Machines.CMemory.Fractional
import Mettapedia.Machines.CMemory.Lift
import Mettapedia.Machines.CMemory.Concurrency

/-!
# A C memory model on Mettapedia's separation logic

Three layers connect proofs about C programs over idealized split heaps to
physical C memory.

**Layer 1: block memory as a separation algebra.**

* `CMemory.Block`: blocks with a size, a liveness bit and cells; pointers with
  provenance; the heap as a separation algebra built from `instPi`, `Excl`
  and the product instance; cell permissions as an interface with exclusive
  cells as one instance.
* `CMemory.Primitives`: load, store, malloc, free, realloc, pointer
  comparison and undefined behaviour as local actions; the frame rule for every
  C program, from `AbstractSeparationLogic`; memory stays well formed.
* `CMemory.Assertions`: points-to, cell ranges, live and dead blocks, and the
  small axiom of every primitive.
* `CMemory.Values`, `CMemory.Array`: scalar values and typed loads; dynamic
  arrays and the specification of CeTTa's `space_module_link_reserve`.
* `CMemory.Examples`, `CMemory.Fractional`: positive and negative controls;
  fractional permissions for shared reading.

**Layer 2: lifting to split heaps** (`CMemory.Lift`): the representation of
Co5's counted arrays and spaces, and refinement of `PostIndex.store`,
`writeLink` and `writeBatch` by the publisher's stores on block memory.

**Layer 3: concurrency** (`CMemory.Concurrency`, with the generic
`DisjointConcurrency` and `LockInvariant`): disjoint parallel composition, one
lock with a resource invariant, and data-race freedom of every reachable
interleaving.
-/
