import Mettapedia.Machines.Kernel.SingleAddressSpace
import Mettapedia.Machines.Kernel.SingleAddressSpaceAsWritten
import Mettapedia.Machines.Kernel.Delegation
import Mettapedia.Machines.Kernel.SexOSGenesis
import Mettapedia.Machines.Kernel.TraceReplay
import Mettapedia.Machines.Kernel.AgentCoordination
import Mettapedia.Machines.Kernel.CorrelatedReplies
import Mettapedia.Machines.Kernel.BootAuthority
import Mettapedia.Machines.Kernel.DelegationPolicy
import Mettapedia.Machines.Kernel.SharedCalls
import Mettapedia.Machines.Kernel.EpochTransition
import Mettapedia.Machines.Kernel.EpochLedger
import Mettapedia.Machines.Kernel.EpochMemory
import Mettapedia.Machines.Kernel.FrameLease
import Mettapedia.Machines.Kernel.EpochHandover
import Mettapedia.Machines.Kernel.EpochActivation
import Mettapedia.Machines.Kernel.EpochDevice
import Mettapedia.Machines.Kernel.EpochWriterLease
import Mettapedia.Machines.Kernel.DmaLease
import Mettapedia.Machines.Kernel.EpochDeviceReset
import Mettapedia.Machines.Kernel.PartitionedFrameAllocation
import Mettapedia.Machines.Kernel.ParkedCoreReplay
import Mettapedia.Machines.Kernel.Arm64Phase3
import Mettapedia.Machines.Kernel.Arm64Phase4
import Mettapedia.Machines.Kernel.Arm64Phase5
import Mettapedia.Machines.Kernel.NvmeMsix
import Mettapedia.Machines.Kernel.FpuContext

/-!
# Kernels of authority

Abstract cores of capability operating systems, and the instances that check concrete systems:

- `Delegation`: authority passed between subjects and revoked along its derivation; confinement within the
  closure of the genesis, and that closure realized by runs.
- `AgentCoordination`: the delegation core read as a coordination layer for agents sharing a mailbox;
  delegation and cascading revocation down a chain, and confinement of an outside agent.
- `SingleAddressSpace`: protection domains sharing one address space under protection keys; integrity of
  memory, rings, tables and reply slots, a fixed communication graph, authenticated replies, and memory
  reachable only along lent frames.
- `SingleAddressSpaceAsWritten`: the same kernel as SexOS writes it, the properties it loses, and the
  simulation showing both agree on every request the first accepts.
- `SexOSGenesis`: the SexOS boot genesis, generated from the table the Cesta kernel compiles.
- `EpochTransition`: the sealed snapshot-transform-swap-commit transition used by the first
  current-kernel ring integration; abort preserves the published bank and commit advances exactly once.
- `EpochLedger`: a bounded committed causal prefix with deterministic replay and the first
  adjacent-event erasure law for independently commuting inputs.
-/
