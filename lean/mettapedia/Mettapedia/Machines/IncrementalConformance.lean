import Mettapedia.Machines.IncrementalConformance.ForeignState
import Mettapedia.Machines.IncrementalConformance.ForeignStateHandles
import Mettapedia.Machines.IncrementalConformance.ForeignStateTrace
import Mettapedia.Machines.IncrementalConformance.ForeignStateRenaming
import Mettapedia.Machines.IncrementalConformance.ForeignQueryLifecycle
import Mettapedia.Machines.IncrementalConformance.ForeignRegionSlots
import Mettapedia.Machines.IncrementalConformance.ForeignRegionCheckpoints
import Mettapedia.Machines.IncrementalConformance.DependencyInvalidation
import Mettapedia.Machines.IncrementalConformance.LiveResources
import Mettapedia.Machines.IncrementalConformance.TransferAccounting
import Mettapedia.Machines.IncrementalConformance.BindingPublication
import Mettapedia.Machines.IncrementalConformance.BatchedTransfer
import Mettapedia.Machines.IncrementalConformance.NominalCallables
import Mettapedia.Machines.IncrementalConformance.CallableObservationBoundary
import Mettapedia.Machines.IncrementalConformance.CallableMatchingBoundary
import Mettapedia.Machines.IncrementalConformance.CallableForeignBoundary
import Mettapedia.Machines.IncrementalConformance.CallableNameSeparation

/-!
# Incremental execution: state, dependencies, resources and transport

These component contracts address four distinct obligations of an incremental
runtime. Foreign-state retention must preserve branch observations; candidate
reuse must respect dependency changes; cancelled ownership must cease retaining
unreachable resources; reduced transport must have explicit cost accounting.

Each component states its admitted fragment and its native integration boundary.
The collection is not a whole-language conformance theorem, a proof of a C
allocator or Prolog FFI, or a wall-clock performance theorem.
-/
