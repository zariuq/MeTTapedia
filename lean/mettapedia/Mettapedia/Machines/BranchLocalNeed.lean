import Mettapedia.Machines.BranchLocalNeed.AllocationBound
import Mettapedia.Machines.BranchLocalNeed.CacheLaws
import Mettapedia.Machines.BranchLocalNeed.DependentService
import Mettapedia.Machines.BranchLocalNeed.ExecutionMachine
import Mettapedia.Machines.BranchLocalNeed.HeapIndex
import Mettapedia.Machines.BranchLocalNeed.InferenceControl
import Mettapedia.Machines.BranchLocalNeed.InteractionAuthority
import Mettapedia.Machines.BranchLocalNeed.InteractionValuation
import Mettapedia.Machines.BranchLocalNeed.LocalStepPaths
import Mettapedia.Machines.BranchLocalNeed.LocalSteps
import Mettapedia.Machines.BranchLocalNeed.ProtocolBridge
import Mettapedia.Machines.BranchLocalNeed.ReferenceSemantics
import Mettapedia.Machines.BranchLocalNeed.Representation
import Mettapedia.Machines.BranchLocalNeed.Worlds

/-!
# Branch-local call-by-need machines

Subject-level import inventory, including explicit instances and boundary
controls. Individual foundational modules do not import this inventory.
Language-specific adapters are intentionally excluded.
-/
