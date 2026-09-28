import Mettapedia.Machines.Cursor
import Mettapedia.GSLT.Dynamics.GuardedWork
import Mettapedia.GSLT.Dynamics.GuardedCursor
import Mettapedia.GSLT.Dynamics.ValuedAgenda
import Mettapedia.GSLT.Core.ResumableGivenClause

/-!
# Guarded, valued, resumable inference work

This entry point connects existing protocols rather than defining a dedicated
GCL machine or a second execution loop.

* `GuardedWork.Decision` authorizes, refutes, or defers a candidate's guard.
  The charged `attempt` preserves store and receipt on rejection or waiting.
  `GuardedCursor.dispatch` applies it to the live cursor and accounts for
  guard work separately from the cumulative provider-operation account.
* `ContextualCandidateValuation.ValuedOccurrence` retains arbitrary values.
  `ValuedAgenda.select` returns an occurrence and all retained alternatives.
* `Cursor.Fold.client` consumes an arbitrary pull provider incrementally.
  The retained accumulator can be a private update, count, or collection.
* `Cursor.Scheduling.execute` advances retained independently owned packets;
  it can split/fuse quanta without replay or refunding their charges.
* `ResumableGivenClause.realization_complete` instantiates those cursor laws
  for the existing snapshot/batch GCL. Other algorithms can supply different
  clients, providers, selection policies, and publication boundaries.

Scheduling priority and authored semantic values need no common algebra.
Pure guard hoisting has an exact cost theorem; shared-state reordering does
not receive an unconditional license. Native implementations still discharge
their local realization and ownership obligations. Neither this import nor
the reference instance certifies a textual MeTTa compiler or a C ABI.
-/
