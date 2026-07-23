import Mettapedia.Machines.ConeDuality
import Mettapedia.Machines.DepthFirstStack
import Mettapedia.Machines.RevisionedOccurrenceStore
import Mettapedia.Machines.FunctionalCorrespondence
import Mettapedia.Machines.MachineSubstrate
import Mettapedia.Machines.MachineRefinement
import Mettapedia.Machines.OccurrenceMachine
import Mettapedia.Machines.OccurrenceCone
import Mettapedia.Machines.ReceiptReachability
import Mettapedia.Machines.RunObservation
import Mettapedia.Machines.TraceObservationBoundary
import Mettapedia.Machines.OSLFConeBridge

/-!
# Abstract-machine foundations

Shared term substrates, distinct evaluation controls, reachability cones,
refinement contracts for deterministic abstract machines, and
occurrence-preserving finite branching with explicit completion and
interruption observations for nondeterministic answer streams, together with
constructive boundaries on what flattened traces can reconstruct and exact
guards for causal-receipt reachability.
-/
