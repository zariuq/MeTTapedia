import Mettapedia.Machines.SourceSnapshot
import Mettapedia.Machines.LevinSearch
import Mettapedia.Machines.ReadCertifiedQueryReuse
import Mettapedia.Machines.ValidatedCommit
import Mettapedia.Machines.Cursor.ReadOnlyQuery
import Mettapedia.Machines.Cursor.ProducerOccurrenceLog
import Mettapedia.Machines.Cursor.SharedFactorCost
import Mettapedia.Machines.Cursor.SharedFactorMachine
import Mettapedia.Machines.Cursor.SuffixForwarding
import Mettapedia.Machines.Cursor.ForwardedTableStore
import Mettapedia.Machines.Cursor.TermPathPostingRefinement
import Mettapedia.Machines.Cursor.KeyedPostingChains
import Mettapedia.Machines.Cursor.SharedFactor
import Mettapedia.Machines.ConeDuality
import Mettapedia.Machines.BranchLocalNeed
import Mettapedia.Machines.DepthFirstStack
import Mettapedia.Machines.RevisionedOccurrenceStore
import Mettapedia.Machines.RevisionDependencySet
import Mettapedia.Machines.NestedQuerySchedule
import Mettapedia.Machines.FunctionalCorrespondence
import Mettapedia.Machines.MachineSubstrate
import Mettapedia.Machines.MachineRefinement
import Mettapedia.Machines.ProductiveCoreAdapters
import Mettapedia.Machines.SourceProducerCardinality
import Mettapedia.Machines.ExecutionHints
import Mettapedia.Machines.ProductiveFunctionalMachines
import Mettapedia.Machines.ProductiveCoreOrdered
import Mettapedia.Machines.Refocusing
import Mettapedia.Machines.CategoricalAbstractMachine
import Mettapedia.Machines.CategoricalAbstractMachineGraph
import Mettapedia.Machines.OccurrenceMachine
import Mettapedia.Machines.OccurrenceCone
import Mettapedia.Machines.ReceiptReachability
import Mettapedia.Machines.RunObservation
import Mettapedia.Machines.IdentityPressureSchedule
import Mettapedia.Machines.RefusalObservation
import Mettapedia.Machines.TraceObservationBoundary
import Mettapedia.Machines.OSLFConeBridge
import Mettapedia.Machines.SpaceServiceChecks
import Mettapedia.Machines.NativeStoreTransactions
import Mettapedia.Machines.NativeStoreScopes
import Mettapedia.Machines.NativeStoreResources
import Mettapedia.Machines.NativeDiskIndex
import Mettapedia.Machines.NativeProviderIndex
import Mettapedia.Machines.NativeStoreMaximum
import Mettapedia.Machines.NativeScalarText
import Mettapedia.Machines.NativeProviderConstraints
import Mettapedia.Machines.NativeProviderDomain
import Mettapedia.Machines.NativeProviderAdmission
import Mettapedia.Machines.NativeProviderPolicy
import Mettapedia.Machines.NativeProviderClaims
import Mettapedia.Machines.Kernel
import Mettapedia.Machines.VersionedValidation

/-!
# Abstract-machine foundations

Shared term substrates, distinct evaluation controls, reachability cones,
refinement contracts for deterministic abstract machines, and
occurrence-preserving finite branching with explicit completion and
interruption observations for nondeterministic answer streams, together with
constructive boundaries on what flattened traces can reconstruct and exact
guards for causal-receipt reachability.

Finite source-resolved collection producers use shared body and call cursors.
Their direct, optional and producer workers preserve ordered occurrences,
captured append contexts, invocation-local commitment and retained stop phases.
The total supported cursor and every bounded prefix agree with the independent
source interpreter; native lowering has its own correspondence boundary.

Adaptive reads use the shared cursor protocol. Their retained read certificates
support validated resumption and certified reuse without introducing another
binding store or identifying a logical observation with mutable native memory.
The common resumable trajectory applies to retained adaptive reads, scheduled
premise states, PeTTa program jobs and owned effect sessions. Snapshot runners
keep their selected world; changing a pure query's world requires validating
its performed reads. Effect sessions interpret only fresh events, and
cancellation keeps the committed world and history. Writes computed from reads
of a shared store commit only after their read certificate is validated against
the current store; accepted commitments are serializable, refused ones change
nothing, and the owned host publishes each accepted write list once.

A nested query whose bodies may write the store it reads has a source schedule:
each level is read once when its branch is reached, and branches run in the
order of that read.  Fusing levels into one join over the initial store is that
schedule exactly where no body changes the store, and differs where one does.

Deterministic control cores instantiate the common event-machine interface
through ordered operational occurrences. Bare missing transitions remain
stuck; answer cores use their checked answer observer. Exact finite traces,
residuals and work accounts connect those instances to the existing CEK and
Krivine machines without assuming source termination.

Kinded refocusing uses paths of licensed frames and an explicit focus. Its
source-step observer preserves residuals and instruction costs; local search
credits exclude endless administration while allowing computational divergence.
Authored MeTTaIL frames connect its stacks to the existing context representation.

The historical categorical abstract machine supplies a compiled-code instance
with independent source evaluation, instruction transitions and executable
readback. Its strict and neutral profiles retain their distinct instruction
rules; compiled answers require both an empty code sequence and an empty stack.
Its value-graph form keeps values in a heap of cells: recursion closes a cyclic
environment by updating one couple in place, delayed bodies are forced on demand
and re-run on each use, and finite observations of the graph agree with the
source values that compiled code computes.
-/
