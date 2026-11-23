import Mettapedia.Machines.GracePeriodPins

set_option autoImplicit false

/-!
# retract/1 and clause garbage collection: the access generations

SWI-Prolog's clause garbage collector is a grace-period reclamation scheme
(`Mettapedia.Machines.GracePeriodPins`).  This module maps that model onto
the C sources of SWI-Prolog master `cf6960c` (stock) and of the fix on top of
it, and names the consequences for retract/1.  Revision 1 of the fix moved
the first access object; revision 2 keeps it and adds a second one.

## Source map

| Model | SWI-Prolog C |
|---|---|
| generation `gen` | `GD->_generation`, read by `global_generation()` |
| object | a `Clause`, or a clause index (`ClauseIndex`) that `ctx->chp` walks |
| `born`, `died` of a clause | `generation.created`, `generation.erased` |
| `born`, `died` of an index | its creation; one after the generation that `linger_always()` stamps when `replaceIndex()` replaces it |
| `tick` | an assert, which gives the clause the next generation |
| `erase` | `retract_clause()`: `erased = GD->_generation+1` under `L_GENERATION`, then the generation advances; for an index, its replacement |
| reader | a thread (`PL_local_data_t`) |
| reader's pins | the `definition_ref` access objects of the thread for the predicate (`LD->predicate_references`), and the generations of frames running the predicate |
| `pin` | `pushPredicateAccessObj(def)`, which re-reads the generation until it is stable: `dref` in the first call of retract/1; on a lost race, a second access object (`retract_move_generation()`); on a further lost race, a third |
| `acquire` | `firstClause()` at `dref`'s generation (the index it chooses, and the candidates), and `nextClause()` at the frame generation; the walk runs under `acquire_def()`, so `gcClauseRefs()` frees no clause reference of the predicate during it |
| held objects | the candidate `clause` during `decompile()`/`retractClauseDefinition()`, the clause of `ctx->chp.cref` (the next candidate, kept for backtracking), and the index that `ctx->chp` walks |
| `repin` | a further lost race: under `LD->thread.scan_lock`, the second access object takes the generation of the third, which is popped: the pins `[G0, G1, G2]` become `[G0, G2]` |
| `release` | `free_retract_context()`: pops the second access object if there is one, then `dref` |
| `start` | `pl_garbage_collect_clauses()`: `start_gen = global_generation()`, `ddi_reset()` |
| `scan` | `markPredicatesInEnvironments()` for the collecting thread, and for every other thread through `forThreadLocalDataUnsuspended()`, which holds that thread's `scan_lock` while it marks its frames and access objects (`markAccessedPredicates()`) |
| `Garbage` | a clause: `ddi_is_garbage()`; an index: `free_lingering(&def->lingering, active)` in `cleanDefinition()`, with `active` the older of `start_gen` and the oldest marked generation |
| `finish` | `cleanDefinition()` unlinks garbage clauses and frees lingering indexes; `lingerClauseRef()`, then `gcClauseRefs()` frees a clause reference once no thread walks the predicate |

The frame of retract/1 runs `system:retract/1`, never the dynamic predicate,
so for that predicate the only pins of a thread inside retract/1 are its
access objects.  An index that `firstClause()` chooses is visible at `dref`'s
generation: `replaceIndex()` stamps the replaced index with the generation at
the replacement, which is not older than `dref`'s.

## Consequences

* Stock (`cf6960c`): when `retractClauseDefinition()` fails on the first call
  (another thread erased the candidate first, or an update event refused),
  retract/1 calls `setGenerationFrame(environment_frame)`: the frame moves to
  the current generation, `dref` does not, and `nextClause()` selects at the
  frame generation.  That is a read at an unpinned generation:
  `unpinned_view_unsafe` gives a run in which the held clause is freed.
* Revision 1 of the fix moved `dref` itself to the new generation, after a
  second access object had published it: a `repin` from `[G0, G1]` to
  `[G1]`.  Its precondition fails when a resize replaced the index that
  `ctx->chp` walks between the two generations: the index is then visible
  only at `G0`.  `unchecked_repin_unsafe` gives the run in which clause GC
  frees the index while retract/1 still walks it (a heap-use-after-free in
  `next_clause_primary_index()` on backtracking).
* Revision 2 keeps `dref` at `G0` until retract/1 is done: a lost race adds a
  second access object (`pin`), and a further one a third, followed by the
  `repin` above, whose precondition holds: the index is visible at `G0`, and
  the candidates were selected at the newest generation.
  `GracePeriodPins.safe_of_reach` applies.
* Moving an access object in place before the scan is
  `unchecked_repin_unsafe` too: the saved candidate may be visible only at
  the old generation.
* Without `scan_lock` the collector may read the access objects at different
  times, around the move: `slotwise_scan_unsafe`.
* That retract/1 erases nothing more once an update event has raised an
  exception is a separate, semantic requirement; it is tested, not part of
  this reclamation model.

## Assumptions that hold at the source boundary, not in the model

* Sequential consistency.  The publication loops of `pushPredicateAccessObj()`
  and `setGenerationFrame()`, and the barriers of the call-port fix (PR 6),
  are what make a published generation visible to a collector that starts
  later; the model takes that for granted.
* The walk returns only clauses whose memory is still valid: `acquire_def()`
  and the `activePredicate()` test of `gcClauseRefs()`.
* Transactions use their own generation space (`GEN_TRANSACTION_BASE`,
  `tr_starts`) and are not modelled; nor are address reuse, `erase/1` through
  clause references (protected by the reference count of the clause blob),
  or the update-event and constraint goals that run Prolog inside retract/1
  (the model lets any other step interleave at any point, which covers their
  database effects).
-/

namespace Mettapedia.Languages.Prolog.SWI.RetractAccess

open Mettapedia.Machines.GracePeriodPins

/-- The fixed protocol keeps every clause and index a thread uses unfreed,
for every interleaving of threads, writers and collector. -/
theorem fixed_safe {R O : Type} [DecidableEq R] [DecidableEq O] {s t : St R O}
    (hs : Inv s) (h : Reach s t) : ∀ r o, o ∈ t.held r → o ∉ t.freed :=
  safe_of_reach hs h

/-- Stock retract/1 reads at a frame generation it has not pinned; a clause
it holds can be freed. -/
theorem stock_unsafe :
    ∃ t, Relation.ReflTransGen (StepWith UnpinnedAcquire) (mk 0 lives ∅ [0] [] .idle) t ∧
      true ∈ t.held () ∧ true ∈ t.freed :=
  unpinned_view_unsafe.2

/-- Revision 1 moved `dref` to the new generation while `ctx->chp` walked an
index that a resize had replaced since: clause GC frees the index that
retract/1 still walks. -/
theorem moved_start_pin_unsafe :
    ∃ t, Relation.ReflTransGen (StepWith UncheckedRepin) (mk 0 lives ∅ [0] [] .idle) t ∧
      false ∈ t.held () ∧ false ∈ t.freed :=
  unchecked_repin_unsafe.2

/-- Moving an access generation in place before the scan frees a clause
retract/1 still keeps. -/
theorem move_before_scan_unsafe :
    ∃ t, Relation.ReflTransGen (StepWith UncheckedRepin) (mk 0 lives ∅ [0] [] .idle) t ∧
      false ∈ t.held () ∧ false ∈ t.freed :=
  unchecked_repin_unsafe.2

/-- Moving an access generation without `scan_lock`: a collector that reads
the access objects at different times frees a held clause. -/
theorem unlocked_move_unsafe :
    ∃ t, Relation.ReflTransGen (StepWith SlotwiseScan) (mk 0 lives ∅ [0] [] .idle) t ∧
      true ∈ t.held () ∧ true ∈ t.freed :=
  slotwise_scan_unsafe.2

end Mettapedia.Languages.Prolog.SWI.RetractAccess
