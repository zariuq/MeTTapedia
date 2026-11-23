# Models of the SWI-Prolog clause GC protocols

Part of MeTTapedia's main Lean project. The original protocol models use core
Lean; the separate `RetractAccess` instantiation and generic reclamation library
use Mathlib.
Build from `lean/mettapedia` with
`lake build Mettapedia.Languages.Prolog.SWI`; every theorem
depends only on a subset of `propext`, `Quot.sound` and
`Classical.choice`.

Each model is a transition system over the interleavings of its actors.
Selected protocol orderings are flags. The publication models prove
their fixed protocols safe for every schedule. `SupervisorV1` refutes the
earlier three-fix supervisor safety claim even with its fixes enabled. Each
removed fix also has an explicit counterexample.

The ownership-aware model in `Supervisor.lean` proves memory safety and the
erasure side of the logical update view for every reachable fixed-protocol
state. Six removed-fix traces distinguish memory faults from erasure violations.
A seventh trace documents the remaining birth-side limitation. The legacy
counterexample remains under `Supervisor.V1`.

The theorem count measures checked statements, not the fraction of C verified.
There is no end-to-end C refinement proof. The coverage table below separates
proved protocols from source and platform obligations.

Import `Mettapedia.Languages.Prolog.SWI` for all models. Build
`Mettapedia.Languages.Prolog.SWI.Audit` for the axiom output of every explicitly
declared theorem. The models use this repository's existing toolchain and cache.

## Publish.lean: the call port and clause GC

| model | C |
|---|---|
| `call`: the frame takes `G` while still at lTop | `setGenerationFrame()` in `depart_or_retry_continue` (normal_call leaves lTop at the new frame) |
| `publish`: lTop above the frame, via the store buffer | `lTop = argFrameP(fr, arity)` in `publishGenerationFrame()` / `S_STATIC` |
| `retake`/`confirm`: re-read `G` until equal | the loop in `publishGenerationFrame()` |
| `readerFence` | its `MEMORY_BARRIER()` |
| `gcStart`, `gcFence`, `scan` | `start_gen = global_generation(); MEMORY_BARRIER();` and `markPredicatesInEnvironments()` (frames below lTop, under scan_lock) |
| `reclaim` | `ddi_is_garbage()`: erased before start, invisible in every registered generation (list mode; interval mode reclaims less) |
| `erase` | `retract_clause()`: under L_GENERATION, `erased := G+1; MEMORY_RELEASE(); G := G+1` |

Results:
- `fixed_safe`: re-validation plus both barriers is safe for any number of readers, clauses, writers and GC runs.
- `stock_unsafe`: without re-validation (the stock call port, and `S_STATIC` today) the frame selects a reclaimed clause.
- `no_reader_fence_unsafe`: without the reader's barrier the lTop store is still buffered when the frame re-reads.
- `no_gc_fence_unsafe`: without clause GC's barrier the scan can precede the start read (load-load reordering).

The same shape covers `pushPredicateAccessObj()` (clause/2, retract/1, retractall/1).

## PublishAsym.lean: asymmetric barrier

The reader uses no hardware barrier. Clause GC issues one process-wide barrier after reading its start generation (`membarrier(MEMBARRIER_CMD_PRIVATE_EXPEDITED)`, `FlushProcessWriteBuffers()`). `asym_safe`: safe.

## Handoff.lean: snapshot to frame

Part A covers a `db_snapshot/1` handle. The goal frame is stamped without a lock, so the stamp may still be buffered. Close runs under `L_MISC`. Clause GC marks the open snapshots (`markDBSnapshots()`) before scanning frames.
- `handle_safe`.
- `handle_frames_first_unsafe`: frames scanned first. This is the surviving mutant `r_gc_order`.
- `handle_close_unsynced_unsafe`: a close that does not order the stamp before it.

Part B covers the `db_snapshot_scope/2` frame, stamped under the thread's scan lock.
- `scope_safe`.
- `scope_split_unsafe`: the generation read and the flag store split around a scan.

## CallPort.lean: the code of PR 6 revision 3

This model follows the code step by step. A frame protects what it reads only once clause GC can see it, so the call port moves lTop above the frame before `setGenerationFrame()`. That function's loop re-reads the generation after a barrier, and all of this happens before `DEF->codes` is read.

| model | C (PR 6 revision 3) |
|---|---|
| `call` | `normal_call`: the new frame, at lTop |
| `publish` | `lTop = FR+1` in `depart_or_retry_continue` |
| `grab` | `gen = global_generation()` in `setGenerationFrameAt()` |
| `put` (into the store buffer) | `setGenerationFrameVal(fr, gen)` |
| `check` | the barrier, `} while(gen != global_generation());` then `MEMORY_ACQUIRE()` |
| `fence` | `MEMORY_BARRIER()`: the first commit; `GENERATION_BARRIER()` and `depart_alerted` without a process-wide barrier |
| `cross`, per thread, while the others run | `processBarrier()` after `start_gen`: `membarrier(MEMBARRIER_CMD_PRIVATE_EXPEDITED)` (Linux, FreeBSD), `FlushProcessWriteBuffers()` (Windows), `thread_get_register_pointer_values()` on every thread (macOS); the loop has a compiler barrier |
| `toScan`, only once every thread has crossed | clause GC scans only if `processBarrier()` returned true; otherwise it skips the run (`gcAbort`) and waits until more clauses are erased (revision 3b). On macOS a thread counts as crossed only if its registers were read or the error says that it is gone or is the hidden exception thread of Rosetta 2; `KERN_ABORTED` is retried |
| `light` | `setGenerationCallPort()`: the loop with a compiler barrier; without a process-wide barrier `ALERT_FENCE` sends the call to `depart_alerted`, which runs the loop with `MEMORY_BARRIER()` |
| `dispatch` | `PC = DEF->codes` |
| `replace` | `freeCodesDefinition()` -> `linger_always()` (`c->generation = global_generation()`) |
| `freeCode` | `free_lingering(&def->lingering, min(oldest registered, start))` in `cleanDefinition()` |
| `freeClause` | `ddi_is_garbage()` |
| `drainGen`, `drainTop` | in order per address, any order across (ARM store reordering; contains TSO) |

Results:
- `safe`, `symmetric_safe`, `asymmetric_safe`: no frame ever holds a reclaimed clause or a freed supervisor.
- `fallback_safe`: the same without a process-wide barrier, with `light` rounds before the fenced one. `asymmetricLight_safe`: a thread that still has `ALERT_FENCE` while clause GC uses `membarrier()`.
- `early_codes_unsafe`: validating after `DEF->codes` was read, inside the supervisor. This is the S_TRUSTME use-after-free.
- `no_recheck_unsafe`: storing without loading again after the barrier.
- `neither_unsafe`: no fence and no crossing.

Still assumed here:
- Loads happen in program order. This is `MEMORY_ACQUIRE()` after the loop: free on x86, `dmb ishld` on ARM.
- `processBarrier()` returns true only if every thread that runs Prolog crossed. On macOS this assumes that the errors it accepts (`KERN_TERMINATED`, `KERN_INVALID_ARGUMENT`, `MACH_SEND_INVALID_DEST`) come only from a thread that has exited or from Rosetta's exception thread, which runs no Prolog.
- One predicate here; see `CallPortPred` for several predicates and last calls.
- The scan reads lTop and the generation field in one step. A frame that matters has no pending stores at that point.
- The erase is one step.

## CallPortPred.lean: predicates and last calls

The same protocol, with three additions. Each clause and each supervisor version belongs to a predicate. The frame's predicate field is a third buffered store. Clause GC keys what it registers by that field, as `markPredicatesInEnvironments()` adds a generation to the `DirtyDefInfo` of `fr->predicate`.

The step `depart` is `I_DEPART`: a running frame that clause GC can see already is reused for another predicate. It stores the new predicate and passes the call port again.

`safe` (`symmetric_safe`, `asymmetric_safe`, `fallback_safe`, `asymmetricLight_safe`): no frame ever holds a reclaimed clause or a freed supervisor of its predicate, also when a visible frame changes its predicate. This removes the "one predicate" assumption of `CallPort`.

## SupervisorV1.lean: pre-ownership static supervisor lifetime, `3f6bfd9`

`fixed_unsafe` is a machine-checked counterexample to the earlier
`fixed_safe` claim. All three fixes are enabled, including the creator's
predicate hold. `not_fixed_safe` explicitly negates universal safety from
`Init`. This is the counterexample outcome of the supervisor verification;
there is no `fixed_safe` theorem.

These historical results are in the namespace
`Mettapedia.Languages.Prolog.SWI.Supervisor.V1`. The reference-owning protocol
is developed separately in `Supervisor.lean`, under
`Mettapedia.Languages.Prolog.SWI.Supervisor`.

The missing condition is the **birth** side of visibility. A reader can
stamp an old generation, then load a newly created supervisor whose clause
was born later. Detaching before publishing an erasure does not prevent
this. `S_TRUSTME` and `S_LIST` do not test visibility, while clause GC
protects the clause only in generations where it is visible.

`fixed_birth_gap` certifies this 23-step execution with two clauses and one
reader. The slot starts at `S_VIRGIN`; the predicate can already be defined.

| action | global generation | reader generation | replacement clause |
|---|---:|---:|---|
| reader stamps, before its slot load | 0 | 0 | not yet visible; born at 1 |
| first writer marks the old clause, detaches, publishes | 1 | 0 | now visible |
| creator scans the replacement, validates under the lock, CAS installs version 0, releases its hold | 1 | 0 | live |
| reader loads version 0 | 1 | 0 | embedded, although born after the reader's stamp |
| second writer marks the replacement, detaches and lingers version 0 at 1, publishes | 2 | 0 | erased at 2 |
| another generation is published; GC starts and records the reader's 0 | 3 | 0 | invisible at 0 because born at 1 |
| GC frees the replacement; reader runs the embedded operand | 3 | 0 | freed |

The witness also certifies `dup = false`, `vfreed 0 = false`, and
`lingered 0 = some 1`. The supervisor need not be reclaimed for its embedded
clause to be unsafe. The first writer actually erases an existing clause;
the last publication can represent an update that erases no further clause
of this predicate.

| model | C at `3f6bfd9` |
|---|---|
| `G`, `born`, `erased`, `cl_erased`, `cfreed` | global generation; clause creation/erasure generations, `CL_ERASED`, physical reclamation |
| `embeds v`, fresh `next`, `vfreed`, `slot` | allocated supervisor versions and their fixed clause operands; `DEF->codes`, with `none` representing the static `S_VIRGIN` code |
| `stamp`, `readSlot`, `wait`, `run`, `exit` | the CallPort guarantee, then the slot load; `S_VIRGIN`; `S_TRUSTME` / `S_LIST` trusting the embedded reference |
| `writerLock`, repeated `mark`, `writerDetach`, `publish` | `removeClausesPredicate()` / `reconsultFinalizePredicate()`: hold `L_GENERATION`, mark `CL_ERASED` and `erased = G+1`, `detachErasedSupervisor()`, publish and unlock |
| prescribed future `born` | pending reconsult additions: `reconsultFinalizePredicate()` sets their creation generation to the update generation before publishing it |
| `creatorRead`, repeated `scanClause`, `allocate` | `setDefaultSupervisor()` reads the old slot; `getClauses()` tests each candidate at the current global generation; `singleClauseSupervisor()` / `listSupervisor()` embed the collected references |
| `cr.holds` | the outer `acquire_def2()` through creation, validation and lingering; `release_def2()` afterwards |
| `creatorLock`, `install`, `retry` | `installSupervisor()`: `embedsErasedClause()` and CAS under `L_GENERATION`; retry on failed validation or CAS |
| `creatorLinger` | `freeSupervisor(old, true)` after `installSupervisor()` unlocks; the linger generation is the global generation at this later step |
| `detacherRead`, `detacherCas`, `detacherRetry`, `detacherLinger` | unlocked `freeCodesDefinition()` from consult, `fix_metapredicate()` or `resetProcedure()`; only the CAS winner lingers |
| `lingered`, `dup`, `St.linger` | `linger_always()`: record the generation at insertion and detect a second insertion of the same version; the model retains insertion history after free |
| `gcStart`, `gcScan`, `freeClause`, `gcEnd` | clause GC start generation, frame generation registration, `ddi_is_garbage()` and `gcClauseRefs()`; erased before start, invisible at every registered generation, no creator holding the predicate |
| `freeVersion` | `cleanDefinition()` → `free_lingering(min(start, oldest registered))`: linger generation strictly below both start and every registered generation |

The wrapped supervisor slot uses the same update protocol:
`setWrappedSupervisor()` uses `installSupervisor()`, and
`resetWrappedSupervisor()` retries its CAS and only lingers after success.
The one-slot abstraction covers either slot's updates. Its reader rule
assumes the stamp precedes the slot load. In the pinned C, `S_WRAP` loads
the wrapped code before calling `setGenerationFrame()`; applying the reader
rule to that VM path requires a separate ordering argument.

The five removed-fix results are explicit `Reach.tail` traces,
all starting from `unitInit`, with the sole clause born at 0:

- `no_detach_unsafe`: the unchanged-mode meta-predicate case retains an erased operand.
- `late_detach_unsafe`: a reader loads the old supervisor after publication and before detachment.
- `unvalidated_install_unsafe`: the creator installs an operand erased after its scan, despite holding the predicate.
- `plain_swap_unsafe`: two unlocked detachers read the same version; both linger it, setting `dup`.
- `no_hold_unsafe`: GC frees a collected operand before the creator enters its validation phase; taking `L_GENERATION` does not revive it.

`initial_init`, `init_init`, `unitInit_init` and `prepared_reach` establish
the initial states and the shared creation prefix. `#print axioms` checks
every theorem in this module: the initial-state and prefix lemmas and
`plain_swap_unsafe` use no axioms; the others use only `propext` and
`Quot.sound`.

Assumptions and limits:

- Sequential consistency. The store-buffer stretch is not attempted after
  the fixed protocol's counterexample.
- The reader's stamp already satisfies the guarantee proved in `CallPort`:
  a later GC scan sees its generation until exit. No visibility or liveness
  premise is added to `readSlot` or `run`.
- One predicate and one slot; arbitrary reader and unlocked-detacher index
  types; one creator serialized by `L_PREDICATE` and writers serialized by
  `L_GENERATION`. Fresh version numbers abstract allocations without address reuse.
- Clause births are prescribed, possibly after the initial generation, as
  also allowed by `CallPort.Init`. A future birth abstracts a pending
  addition becoming visible at publication. The fixed counterexample uses
  one such addition. Assuming every clause was born before every reader
  stamps would exclude this reconsult case.
- Scans may collect several operands over several steps. Writer detachment
  and lingering inside its generation critical section are combined into
  one step; the counterexample therefore needs no race inside that operation.
- `Safe` includes the liveness of operands in the creator's `checking`
  phase, immediately before `embedsErasedClause()` dereferences them.
  Reclamation is modeled once per object; lingering history is retained
  for duplicate detection. The clause rule uses generation-list GC;
  interval GC can conservatively retain more clauses.
- This is a Lean protocol result with a source mapping, not a compiled-C
  refinement proof or an executed SWI reproducer. The pinned ordinary
  defined-predicate `S_VIRGIN` path calls `setDefaultSupervisor()` and then
  loads `DEF->codes` without refreshing the frame's generation, consistent
  with the birth gap above.

## Supervisor.lean: ownership and erasure safety, `65455ce`–`8f7019a`

The protocol is pinned to the four commits on `pr/static-supervisor-v3`,
based on `cf6960c`. Namespace:
`Mettapedia.Languages.Prolog.SWI.Supervisor`.

| Commit | C behavior | Model |
|---|---|---|
| `65455ce` | `ownClause()` calls `newClauseRef()` / `acquire_clause()` for `S_TRUSTME` and `S_LIST` while `singleClauseSupervisor()` / `listSupervisor()` hold `acquire_def2()`; `freeCodes()` calls `releaseSupervisorClauses()` → `freeClauseRef()` → `release_clause()` | `Proto.own`, `allocate`, `owned`, `embeds`, `vfreed`; each unfreed owning version retains every embedded operand |
| `dc6b978` | Supervisor slots use CAS; only a successful replacement retires the old version, including default, wrapped and reset paths | `Proto.cas`, `install`, `detacherCas`, `detacherRetry`; reservations move between slot, prototype and pending linger locations; `dup` detects double retirement |
| `c445fee` | `detachErasedSupervisor()` runs under `L_GENERATION` before publishing the erasure generation in `removeClausesPredicate()` / `reconsultFinalizePredicate()` | `writerLock`, `mark`, `writerDetach`, `publish`; `Proto.detach = inSection` |
| `8f7019a` | `installSupervisor()` checks `CL_ERASED` and CAS under `L_GENERATION`; validation uses owned references, without an outer hold in `setDefaultSupervisor()`; `S_WRAP` takes its generation before reading the wrapped slot | `creatorLock`, `install`, `retry`, `Proto.validate`; `stamp` precedes `readSlot`; `allocate` releases the acquisition hold before validation |

The creator's scan has the inner `getClauses()` hold in every protocol.
`finishScan` distinguishes the subsequent build window: `Proto.hold` keeps
the predicate held until `allocate` acquires the supervisor's own references.
The `noHold` mutant drops protection in this window, before ownership exists.
This does not impose the removed outer hold around `setDefaultSupervisor()`.

`linked k` represents the clause-list reference. `unlink` implements the
list-generation `ddi_is_garbage()` test, requiring no creator hold; it drops
only that reference. `hasOwner k` asks whether any allocated, unfreed owning
version embeds `k`. The clause is physically free exactly when both the list
reference and all such owners are absent. `freeVersion` therefore releases
its operands as well as the code. Reference multiplicity within one version
is abstracted to presence, which is enough for these lifetime properties.

Results (all checked by `SWI.Audit`):

| Theorem | Statement |
|---|---|
| `fixed_mem_safe` | From any `Init` state, every state reachable under `fixed` satisfies `Mem` |
| `fixed_lud_safe` | The same states satisfy `LudErase`: a running clause's erasure is strictly after the reader's generation |
| `mem_safe` | Memory safety needs CAS, ownership and the acquisition hold; it holds independently of detachment timing and install validation |
| `no_own_unsafe` | The birth-gap trace frees a running operand after list unlink while its supervisor version remains allocated |
| `plain_swap_unsafe` | Two detachers retire the same version, setting `dup` |
| `no_hold_unsafe` | GC unlinks and frees an operand retained by the creator between scan completion and acquiring ownership |
| `no_detach_lud` | An erased clause remains callable in the erasing generation; `Mem` still holds |
| `late_detach_lud` | A reader loads the stale version between publication and detachment; `Mem` still holds |
| `unvalidated_install_lud` | A prototype collected before erasure is installed afterwards; `Mem` still holds |
| `birth_side_open` | The fixed protocol reaches a memory-safe state running a clause born after the reader's generation |

`Mem` covers the reader's code and selected operand, creator operands during
both borrowing and prototype ownership, absence of duplicate retirement,
and absence of lingering or freed code in an installed slot. `LudErase`
is separate: ownership can preserve memory even when erasure visibility is
wrong. Neither theorem claims the birth side of the logical update view.

The proofs induct over `Reach`. The resource invariant tracks unique clean
reservations, immutable allocated operands, the acquisition hold, owning
references, readers' code and retirement bounds, and the GC scan cutoff.
The erasure invariant additionally connects the generation lock, detached
slot, validated installs and reader generations. These invariants are
proved from `Init`; they are not extra transition preconditions. In
particular, `readSlot` and `run` do not test clause visibility or liveness.

Assumptions and limits:

- Sequentially consistent interleavings; the reader stamp already has the
  publication guarantee modeled separately in `CallPort`. This module does
  not re-prove that store-buffer protocol or compose the two models formally.
- One predicate and one slot, arbitrary reader and detacher index types, one
  creator serialized by `L_PREDICATE`, and writers serialized by `L_GENERATION`.
  The slot abstracts either the ordinary or wrapped slot; the corrected
  `S_WRAP` ordering now matches the reader rule.
- Fresh unbounded version identifiers, with no address reuse, integer overflow,
  or allocation failure. Clause births are prescribed and may be in a future
  generation, abstracting additions made visible by reconsult publication.
- Reference acquisition is one step while the creator is protected. GC list
  unlink and dropping its reference are combined; separating them can retain
  an extra reference longer. Writer detachment and its linger are combined
  inside the generation critical section; unlocked detachers and creator
  lingering remain separate steps.
- GC records active generations and frees a retired version only below both
  its start generation and every recorded generation. The list-generation
  clause test is modeled; interval GC may retain more. No fairness or eventual
  reclamation theorem is claimed.
- These are protocol proofs with a source mapping, rather than a C refinement
  proof, weak-memory proof, or a new executed SWI experiment. The older
  `SupervisorV1` counterexample is preserved as a result about the earlier
  protocol.

## Retract.lean: constraints before destructive retraction, `6b14930`

This model concerns the proposed `retract/1` and `retractall/1` constraint
fix in `6b14930` on `cf6960c`. It distinguishes an erase request from this
operation and database edits made by a wakeup itself. Namespace:
`Mettapedia.Languages.Prolog.SWI.Retract`.

| C behavior | Model |
|---|---|
| SSU flags plus `decompile()`, or `decompileHead()` | `Candidate.unifies`: ordinary structural success; failure short-circuits before the constraint hook |
| `CONSTRAINTS_HOLD()` tests only `ALERT_WAKEUP` | `Candidate.wake = none` takes the successful fast path; `otherAlerts` has no effect |
| `clause_constraints_run()`: propagate a caught exception, then `rc && !PL_exception(0)` | `guardResult`: acceptance requires a true query result and no pending exception |
| `foreignWakeup()`: `PL_next_solution()`, then `PL_cut_query()` | `Wake` records the first observed result and effects; discarded `alternatives` are never evaluated |
| Patched condition before `retractClauseDefinition()` | `candidateTrace true`: an accepted check immediately precedes every outer erase request |
| Old ordering with a pending hook | `candidateTrace false`: erase before checking; one pending rejected or throwing candidate witnesses either predicate's bug |
| Hook-driven assert/retract operations | `Event.callback` edits, distinct from `Event.erase` requests issued by the outer operation; `replay` applies both |
| `allVars()`: distinct plain variable cells, excluding attributed cells | `allVars`, `allVars_plain`, `allVars_nonsharing`, `attributed_argument_slow` |
| `pushPredicateAccessObj()` protects the access generation while callbacks run | `predicate_access_visible_live`, derived from the existing `Publish` invariant, protects any clause visible in an active access generation |

The main theorem `fixed_scan_guarded` proves the ordering for every candidate
list in both traversal modes and for arbitrary callback edits. Rejected
and throwing candidates issue no outer erase (`rejected_candidate_no_request`,
`throwing_candidate_no_request`). `fixed_all_filter` identifies exactly
the accepted requests in the prefix before the first exception;
`fixed_first_requests` selects the first of those requests. `exception_stops_scan`
and `exception_preserves_prefix` prove that a throwing prefix stops all
suffix work and keeps the effects already performed. Repeated plain failure
continues to the next candidate.

`structural_failure_short_circuits`, `no_wakeup_fast_path`,
`unrelated_alerts_ignored`, `guard_result_accepted_iff` and
`foreign_wakeup_cuts_alternatives` check the guard's smaller boundaries.
In particular, acceptance of the first wakeup solution does not retain
choicepoints that could issue another erase for the same candidate.

Checked witnesses under `Retract.Examples` include:

- `stock_rejection_unsafe`, `stock_exception_unsafe`: the old order has
  already removed a rejected or throwing candidate, for either mode.
- `first_authorized_skips_rejections`, `all_authorized_filters_rejections`:
  reject `p(a)`, accept `p(b)`, reject `p(c)`; only `p(b)` is requested for
  deletion by the fixed traversal. The old first-accepted traversal also
  removes `p(a)`.
- `no_accepted_candidate_no_deletions`: all candidates are rejected.
- `exception_keeps_prior_deletions`: a prior accepted deletion persists;
  the throwing and subsequent clauses remain.
- `failed_wakeup_can_modify_database`: a rejecting hook itself deletes
  another clause, although the outer operation makes no erase request.
  A theorem promising whole-database rollback on failure would be false.
- `failed_structure_never_runs_hook` and the plain, shared and attributed
  fast-path witnesses.

Scope and assumptions:

- Constraint solving and candidate selection are abstract inputs. `Wake`
  describes a completed observation after the first-query search, not an
  implementation of attributed-variable hooks or their scheduler. Its
  effects include effects produced during that search, including failed
  branches; cut discards only future alternatives.
- The traversals specify **authorized erase requests**, rather than full
  `retract/1` return values. A removal listener may veto an erase or throw;
  a wakeup may already have removed the current candidate. On a first call,
  that latter case can refresh `setGenerationFrame()` and continue. Redo
  can return an already-erased clause under the logical update view.
  Candidate enumeration across those cases is not proved here. The
  multi-candidate examples use successful, unopposed removals.
- A rejected candidate's bindings and temporary terms must be rewound before
  the next candidate, as `PL_rewind_foreign_frame(fid)` does in C. The model
  assumes those independent attempts; it does not prove trail restoration,
  foreign-frame allocation bounds, stack relocation, or raw pointer safety.
  Decompilation/resource errors before the guard and removal-event errors
  after it are outside the scan abstraction.
- The visible-clause lifetime lemma reuses the sequential publication model
  conditionally on an active protected generation. It is not a formal
  composition with the callback scanner or a refinement of the C predicate
  access stack. A generation refresh requires establishing visibility in
  the refreshed generation again.
- No C build or runtime experiment is part of this formalization. The
  source mapping and checked protocol properties complement the patch's
  regression tests; they do not certify the complete SWI implementation.

## RetractAccess.lean and the generic grace-period library

`Mettapedia.Machines.GracePeriodPins` proves safe reclamation with pinned
generations, including pin replacement and atomic scanning of one reader's
pins. Its three counterexamples remove pinned selection, safe replacement or
atomic scanning. `RetractAccess` instantiates those results for stock
`cf6960c` and the retract access-generation fix, with a C source map and
explicit assumptions. The clause index that retract/1 walks is a held object
there: revision 1 (`bf81af4`) moved the first access object to the new
generation, so clause GC could free an index that a resize had replaced
(`moved_start_pin_unsafe`); revision 2 (`66e35f0`) keeps it and adds a second
access object for the new generation. It is imported separately by the Prolog
umbrella; `SWI.Audit` also checks it and the generic library.

The instantiation assumes the publication ordering, valid memory during an
index/list walk, and sequentially consistent reader-pin scans. It excludes
transactions and address reuse. This is meaningful checked protocol coverage
plus an explicit source map; the C implementation and its weak-memory/platform
primitives are not mechanically refined into the model.

## Mutation.lean: post-publication lifetime and erase-generation guards

`Mutation.Lifetime` splits operation preparation, publication, postwork and
finish from list unlink and list-node disposal. `clauseLive` is derived from
the list reference or an owned local Clause reference. Invalid dereferences
are recorded when they occur; the read transitions do not require liveness.
GC may interleave arbitrarily once publication permits list disposal.

- `fixed_safe`: a local Clause reference held through the last access, with
  no reads through the borrowed list node, preserves safety for every modeled
  schedule.
- `no_hold_unsafe`: the unprotected post-publication read reaches freed memory.
- `clause_pin_does_not_pin_node`: a local Clause reference keeps the Clause
  alive while its list ClauseRef is already dead; reading that node is unsafe.
- `early_release_unsafe`: releasing before the last metadata/callback access
  leaves a reclamation window.
- `fixed_survives_node_disposal`, `fixed_can_release_last_owner`: the list
  node may disappear during protected postwork, and the last reference may be
  released once that postwork finishes.

This is the lifetime obligation relevant to PR 1 revision 2 (`ee182ae`) and
the post-unlock `retract_clause()` issue reported on `cf6960c`. This local
reference discipline is separate from the conditional access-pin handover
proof in `RetractAccess`.
For each C path, the reference must be acquired while the pointer is valid,
retained across every remaining access and callback, then released on its
success and error exits. Alternatively, all later dereferences may be removed.
Caching only the generation does not justify a remaining callback that reads
the Clause. A Clause reference does not preserve a borrowed ClauseRef node.
The model permits list disposal after publication independently of generation
roots. A maintained access generation could protect the same pointer instead;
this model does not establish why C clause GC missed that protection. It omits
address reuse and extra owners, and has no fairness, leak-freedom or
shutdown-liveness theorem.

`Mutation.EraseGeneration` models the serialized comparison changed from
`>=` to `>` by `1ba322c`, in either the ordinary or local transaction generation
space. `already_erased_stable`, `fixed_idempotent` and
`fixed_no_resurrection` prove that a retry preserves an existing erasure and
cannot make a clause visible again. `stock_retry_resurrects` checks the bad
`erased == current` case. Special discard modes, generation-space exhaustion,
overflow, transaction rollback and the surrounding C control flow are outside
this arithmetic fragment.

`refresh_does_not_preserve_saved_visibility` separately shows that advancing a
frame generation can invalidate a saved next clause's visibility assertion,
even while an older access generation still sees it. This is not a proof of
physical reclamation or of a release-build cursor defect. Mapping the cursor,
frame generation and predicate-access generation together remains necessary.

`frame_refresh_can_outgrow_access_pin` shows the other direction of the gap:
a clause born at 1 and erased at 2 is visible to a refreshed selector at 1,
invisible to an unchanged predicate-access pin at 0, and older than GC start
3. At `d743487`, `pl_retract1_va` initializes the frame from
`pushPredicateAccessObj(def)->generation`, but on a lost first-call erase it
calls `setGenerationFrame(environment_frame)` without updating that access
record. `markAccessedPredicates()` scans the record's generation for the target
predicate. This is a source-mapping concern, not a machine-checked C trace or
a proven explanation of the reported ASan event. Whether cursor enumeration
can reach the newer clause and whether any other root protects it must be
established. Advancing a pin while keeping an old cursor can instead expose
old saved nodes; a repair must handle both sides, and publish any changed pin
with the ordering that the collector requires.

## SnapshotContracts.lean and EmptyCutoff.lean: earlier index/snapshot laws

These historical review models are now part of the public build and axiom
audit. `SnapshotContracts` proves occurrence-preserving filtering under a
coverage premise, a sufficient generation cutoff, least safe retention roots,
frozen-frame preservation, and local insertion/retirement laws. It also gives
counterexamples for unlocked index-array retirement and a fill/retirement wait
cycle. These are list and state laws; they do not implement index filling or
prove that current C locks and caches realize those laws.

`EmptyCutoff.upper_bound_suffices` proves the timestamp condition required by
an empty-predicate shortcut. Its counterexamples show that publishing a stale
stamp, or a late older plain store, can lose a visible clause. Taking a maximum
commutes after both writes complete, but does not close a publication gap
before a write completes. The current implementation must establish the upper
bound at the point the shortcut reads its metadata.

## ReadyFixes.lean: source obligations for the reviewed fix branches

`ReadyFixes.lean` gives each November 15 ready branch a compact positive
protocol theorem and a counterexample with the repaired condition removed.
It is intended to be read beside the larger models above and beside the C diff.

| C branch | Lean namespace | Checked obligation |
|---|---|---|
| `pr/mqual-cyclic-error`, `b61d9f7` | `ReadyFixes.MetaQualification` | Moving `lTop` over the frame arguments before `PL_error()` allocates makes the error path stack-safe; the old lower top is an explicit invalid-access witness. |
| `pr/assertz-clause-reference-v3`, `36f53d5` | `ReadyFixes.AssertionReference`, `Mutation.Lifetime` | The returned clause reference exists before publication, the original clause is owned, and the borrowed `where` node is not read after unlock. Removing any of these conditions is unsafe. |
| `pr/index-fill-race-v6`, `18ad39f` | `ReadyFixes.IndexFill` | Predicate locking admits only mutation-before-fill or mutation-after-fill schedules. The transition invariant proves one linked and indexed occurrence at every completed run; old schedules exhibit duplicate and missing entries. Completion publication is paired with acquire observation. |
| `pr/retract-constraints`, `d743487` | `Retract` | Constraint wakeups authorize deletion before the destructive request, exceptions stop the suffix, rejected candidates issue no outer erase, and wakeup alternatives are cut. |
| `pr/retract-access-generation-v2`, `64db76f` | `RetractAccess`, `ReadyFixes.RetractContinuation` | The original pin continues to cover the walked index, generation handover is atomic to clause GC, and a lost candidate is found again before continuing. Falling back to the complete clause list preserves appended matching clauses. |
| `pr/transaction-start-generation`, `ec7d838` | `ReadyFixes.TransactionStart` | A start generation is accepted only after the published sample equals the re-read global generation. The old stale announcement can miss a clause visible in the refreshed view. |
| `pr/static-reload-view`, `0f7a274` | `ReadyFixes.StaticReload` | Reload records `last_modified` and dirty registration under the predicate lock. Clause GC repeats the generation condition under that lock, so an older running goal prevents unregister. The split old precheck has a concrete lost-registration trace. |
| `pr/clause-publication-order`, `fb1a108` | `ReadyFixes.Publication` | A release-linked node exposes initialized payload, and release publication of the global generation exposes its prior birth stamp. Plain publication has witnesses for both failures. |
| `pr/transaction-isolation-v11`, `96a0875` | `ReadyFixes.Publication` | Release/acquire publication of `good_from` makes completed entries visible. The x86 assembly path is safe only under its stated compiler and machine ordering premise; the theorem takes that premise explicitly and the unordered path is refuted. |

The same module records design obligations for three unresolved source items.
`WrapperOwnership` requires atomic wrapper-slot update, retirement and drainage
of closure-owned lingering versions, and ownership of embedded clauses (C2).
`PostUnlock` requires a Clause owner across every post-unlock Clause read and
forbids reads through a borrowed ClauseRef node (C8.2). `SplitGeneration` shows
that a split 32-bit frame-generation read can produce a value equal to neither
the old nor new generation (C7a). These positive theorems describe a design for
the C fix; they do not claim the current source implements it.

The models also delimit what formalization can establish. In particular,
`x86_path_safe_of_ordered` proves the desired property from the x86 load-order
premise; it does not prove that a volatile inline-assembly access is a C11
atomic acquire. Source review or a switch to the portable acquire path must
discharge that premise. The same source-boundary rule applies to allocation,
reference counts, lock coverage, error exits and every platform barrier.

## Verification coverage and remaining source obligations

This table is an audit of the pinned revisions, not a submission certificate.
A safe abstract protocol does not establish that every C path refines it.

| Patch or feature | Checked coverage | Still outside the proof |
|---|---|---|
| Assert reference rev 3, `36f53d5` | `AssertionReference` and `Mutation.Lifetime` cover pre-publication result ownership, original-clause ownership, and rejection of post-unlock borrowed-node access | Mapping every assert/reload/VM/event/error path to acquisition, publication and final release; actual refcount, atom handle and allocator behavior |
| Index fill rev 6, `18ad39f` | `IndexFill` proves the lock/wait transition invariant and exactly-once terminal indexing; `SnapshotContracts` supplies retirement and wait-cycle laws | Exact source-path coverage of all mutators, invalid-index retirement, mutex/atomic semantics and retry progress |
| Transaction isolation rev 11, `96a0875` | `Publication` proves the release/acquire `good_from` contract and refutes unordered observation; filtering/cutoff laws cover retained clauses | The x86 assembly path's C atomicity and compiler contract, `last_erased` publication across all writers, cache invalidation and multi-argument C6d |
| PR 4, `feb0f16` | Test-only thread-support guard; no dedicated protocol theorem | Threaded and unthreaded test builds, rather than a bespoke Lean proof |
| PR 5, `1ba322c` | Exact natural-number guard fragment: idempotent erasure and no resurrection | Generation limits, discard/rollback modes and surrounding implementation paths |
| PR 6 rev 3, `7a56de8` + `f98cbb3` | `CallPort` / `CallPortPred`: buffering, barriers, light rounds and frame reuse under stated assumptions | Real platform barrier success/failure contracts, numeric lTop/argument preservation, C path completeness and platform CI; pending review corrections are not discharged by these models |
| Cyclic meta qualification, `b61d9f7` | `MetaQualification` proves the raised local top covers error allocation and refutes the old lower top | `PL_error()` and term-reference stack footprint, relocation and all architecture-specific frame layouts |
| Transaction start publication, `ec7d838` | `TransactionStart` proves stable sample publication and exhibits a stale announcement that misses the refreshed view | Weak-memory realization of `GENERATION_BARRIER`, transaction nesting and all reset/error paths |
| Static reload view, `0f7a274` | `StaticReload` proves an older goal prevents unregister with the locked repeated test and exhibits the old split race | C lock discipline at every registration/unregistration site and composition with static supervisors |
| Clause publication, `fb1a108` | `Publication` proves release-link payload visibility and birth-stamp-before-generation visibility, with removed-order witnesses | Every list/bucket publication site, non-GNU atomic implementation and reader acquire/data-dependency behavior |
| Supervisor ownership, `65455ce`–`8f7019a` | `Supervisor.fixed_mem_safe`, `fixed_lud_safe`, six removed-fix witnesses and the birth-side limitation | Composition with weak-memory publication and actual C reclamation/refcounts; current source review |
| Retract constraints, C body of `d743487` | `Retract`: accepted-before-erase, exception stopping, cut alternatives, fast-path restrictions and callback effects | Native unification/trail restoration, foreign-frame allocation, stack relocation, erase-event vetoes/errors, cursor refresh and C refinement |
| Retract access and continuation, `64db76f` (`66e35f0` lifetime core; revision 1 `bf81af4` refuted) | `GracePeriodPins` and `RetractAccess` prove safety of the kept start pin and current pin; `RetractContinuation` proves current-index coverage or full-list fallback preserves appended candidates | Source review must establish scan atomicity, publication ordering, current-index coverage, argument reconstruction after stack shifts and all error paths; transactions and weak-memory composition remain open |
| `db_snapshot` v15 (`642c1f8` / `21cebc7` / `10ee5dc`) | Generic retention/frozen-frame laws and `Handoff` publication/close ordering | Current scope/handle identity and lifetime, transaction rollback, nested query requests, stack/atom GC, API errors, and the pending v16 rebase |

Additional cross-cutting gaps include shutdown/thread teardown, the Debug
protected-ClauseRef registry, finite machine arithmetic, C data races and
memory accesses, and composition of separately proved protocols. The
`CallPort` models assume that relevant frame fields are scanned coherently;
`Supervisor` assumes the reader publication guarantee; `Retract` assumes
independent rewound attempts. Those assumptions must be justified at the source
boundary, not inferred from the existence of a theorem named `safe`.

The appropriate review package pins the exact source revision and its claimed
property, supplies baseline/fixed reproductions and regression controls,
records platform and performance evidence, and states the remaining model
assumptions. Independent stock failures do not by themselves prove that a
particular patched failure is unrelated. Each patch should claim only the
property its evidence establishes.

## Assumptions of the earlier models (Publish, PublishAsym, Handoff)

1. A frame's generation store is visible together with the step that makes it. In C it is a store, so a scan could see the previous value between the reader's load and its store. Informally the loop covers this: the frame exits only on a read that follows its last store and a barrier. The next refinement puts generation stores through the store buffer.
2. Stores of one thread become visible in order (TSO). On ARM, the call-port generation store and the lTop store need a store-store barrier between them; there is none today.
3. A reader reads clause fields after its final generation read. On ARM this needs an acquire, for example `global_generation()` as an acquire load. The stock code has none, and the writer's `MEMORY_RELEASE()` has nothing to pair with.
4. The erase is one step (L_GENERATION serializes writers; the release orders `erased` before `G`).

## Experiments that match the counterexamples

- `stock_unsafe` on a dynamic predicate is the v12 race experiment (delay hooks): heap-use-after-free, 3 of 3 runs before PR 6, 0 of 3 after.
- `stock_unsafe` on a static predicate under reconsult, with PR 6 applied: heap-use-after-free in `next_clause_unindexed()`, 3 of 3 runs. PR 6 does not cover `S_STATIC` or the static supervisors.
