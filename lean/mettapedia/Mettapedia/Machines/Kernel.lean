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
-/
