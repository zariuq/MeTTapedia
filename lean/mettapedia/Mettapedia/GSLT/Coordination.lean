import Mettapedia.GSLT.Coordination.ExactlyOnceTake
import Mettapedia.GSLT.Coordination.CoordinatedAttack
import Mettapedia.GSLT.Coordination.CrashConsensusImpossibility
import Mettapedia.GSLT.Coordination.ReplicaMerge
import Mettapedia.GSLT.Coordination.InvariantConfluence
import Mettapedia.GSLT.Coordination.HomeLocation
import Mettapedia.GSLT.Coordination.FencedLeases
import Mettapedia.GSLT.Coordination.Escrow
import Mettapedia.GSLT.Coordination.Deduplication
import Mettapedia.GSLT.Coordination.MajorityEpochs
import Mettapedia.GSLT.Coordination.AtomicCommitBlocking
import Mettapedia.GSLT.Coordination.AuthorityRoles
import Mettapedia.GSLT.Coordination.Declarations
import Mettapedia.GSLT.Coordination.AtomicCommitClass
import Mettapedia.GSLT.Coordination.Colocation
import Mettapedia.GSLT.Coordination.DeterministicOrdering
import Mettapedia.GSLT.Coordination.ExactClassifier
import Mettapedia.GSLT.Coordination.LeaseHandover
import Mettapedia.GSLT.Coordination.LocatedIdentities
import Mettapedia.GSLT.Coordination.OwnerFailover
import Mettapedia.GSLT.Coordination.OwnerFailoverFairness
import Mettapedia.GSLT.Coordination.OwnerFailoverLiveness
import Mettapedia.GSLT.Coordination.Sagas
import Mettapedia.GSLT.Coordination.Liveness.EscrowProgress
import Mettapedia.GSLT.Coordination.Liveness.FairLeaseService
import Mettapedia.GSLT.Coordination.ConsensusNumbers

/-!
# Coordination across locations

Occurrences live at locations; commits are the atomic commits of
`Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits`. These modules say when coordination
cannot be avoided, exactly when it is needed, which mechanisms provide it and what each refines,
and how a region declares the coordination it needs.

## What cannot be avoided

* `ExactlyOnceTake`: exactly-once take is not monotone, so replicas that only merge cannot compute
  it (from the converse of CALM); under a partition no system is both available and exactly once.
* `CoordinatedAttack`: no deterministic protocol over lossy links reaches agreement on attack, and
  attack is never common knowledge.
* `CrashConsensusImpossibility`: no deterministic protocol solves consensus in an asynchronous
  system in which one process may crash (Fischer, Lynch and Paterson).
* `MajorityEpochs`: owners replaced by majorities are unique per epoch; winner rules need a delay
  bound.
* `AtomicCommitBlocking`: an uncertain participant of two-phase commit cannot decide.

## Exactly when

* `ReplicaMerge`: two commits made concurrently at replicas merge to a legal serial run exactly
  when they do not clash and at most one spoils the other; monotone commits always do.
* `InvariantConfluence`: coordination-free execution keeps an invariant exactly when the
  transactions are invariant confluent; owned scopes need no coordination.
* `Declarations`: the verdict needs the invariant, not only the footprint; count bounds have an
  exact decidable table.

## Mechanisms, each a refinement

* `HomeLocation`: with one home per occurrence and closed predicate queries, every network run is an
  atomic run.
* `FencedLeases`: claim, lease expiry and fenced effect at the owner refine the atomic take; each
  owner step is a commit; no stuck claims; a timely worker completes.
* `Escrow`: shares spent locally refine the central budget; rebalancing by deduplicated transfers.
* `Deduplication`: at-least-once delivery with identifiers is exactly once; unknown activities are
  never rerun; content identity is not occurrence identity.
* `AuthorityRoles`: escrow shares are counting permissions, the owner holds the consume right, a
  fencing epoch is a versioned capability (`current_iff_valid`).

## Across owners, and owners that fail

* `AtomicCommitClass`: every atomic commit protocol blocks, over the whole class of protocols.
* `ExactClassifier`: the coordination classifier is exact, and every verdict it gives is
  sufficient.
* `Colocation`: how much must move together for commits across owners to be local; runs with moves
  are atomic runs.
* `DeterministicOrdering`: commits across owners by a deterministic order refine the atomic run.
* `Sagas`: what compensation restores (labels) and what it does not (isolation, identities).
* `LocatedIdentities`: identities qualified by the location that allocates them are fresh without
  coordination.
* `OwnerFailover`, `OwnerFailoverLiveness`, `OwnerFailoverFairness`: majority epochs, state
  transfer and fencing; the chosen log is an executable run; liveness with a stable candidate, and
  from weak fairness.
* `LeaseHandover`: what a new owner does with the leases it inherits.
* `Liveness.FairLeaseService`, `Liveness.EscrowProgress`: every task is eventually done; escrow
  rebalancing makes progress.

The refinements here end in an `Executable` sequence of `OccurrenceCommits.Waves`, or for leases
in an atomic take; `OccurrenceCommits.CommitProtocol` lists the runtime models that do.
-/
