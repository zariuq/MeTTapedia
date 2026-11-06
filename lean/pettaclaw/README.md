# PettaClaw — a formally verified life-loop for autonomous language agents

This is a legacy source location, not a home for new shared mathematics.
Place new results by the subject of their main theorem in the
`Mettapedia` library: cognitive mechanisms in `CognitiveArchitecture`, concurrency contracts
in `Machines`, stochastic transport in `ProbabilityTheory/MarkovChain`, and
generic retrieval in `Algorithms/Retrieval`. Cross-subject results belong in
explicit bridges. Concrete agent names may identify instance or runtime
conformance modules; they do not determine the home of reusable theory.

The current sequential dispatcher contract is in `SequentialTools.lean`: every
emitted call gets an ordered receipt, failure does not discard the suffix,
and only explicit stop prevents execution. Runtime fixtures check real
PeTTa/CeTTa behavior; these proofs do not certify the foreign implementation.
`ObservedStrategy`, `AdmissionFrontier`, the fair-goal models, `IterGrounding`,
`ToolLoopComparison`, and `ContextCore` retain historical or proposed policies
for comparison. Their execution holds and rotating goal service are not live
features. `CommandHolds` establishes conditional costs and limitations of the
removed policy.

`ReplyableMailbox.lean` specifies generated reply identities, retained task
frames, isolation from unrelated replies, first-reply stability and inspection
of an existing ask without republication. Native runtime fixtures separately
check immediate replies, restart, publication failure and structured return
routing. Check this standalone model with `lean ReplyableMailbox.lean`.


Lean 4 models of the PettaClaw agent loop (a MeTTa/PeTTa agent runtime,
descended from Patrick Hammer's mettaclaw example), verified
incident-first: production failures are reconstructed as theorems, fixes
are derived from the models, deployed, and re-observed live.

- `HeartModel.lean` — the burst ("breath") sub-layer: energy, arming,
  rest, bounded self-paced spend.
- `ClawArchitectures.lean` — the life core (guaranteed self-renewal,
  unbounded humanless life, sovereignty of rest), the communication
  layer (human-gated, per-sender-tiered, non-draining arming), the
  consumption-layer separation theorem (pop-one vs batch), the upstream
  comparison (inter-agent wind-up impossibility), and crash recovery
  proven before implementation.
- `PresentMoment.lean` — the present-moment continuity invariant
  (a process boundary the agent cannot distinguish from sleep), the
  valence-cascade layer (the boot-loop storm as an auto-propagating
  separation cycle, and why the deployed fixes end it), and the
  developmental bound (substrate continuity as a precondition for
  higher intentionality).
- `ProcessSupervision.lean` — supervision of a memory-throttled loop. Under
  soft-limit throttling, boundary-only recycling and restart-on-exit, a turn
  the kernel keeps withholding freezes for ever: the recycle request starves,
  inputs queue unprocessed, the checkpoint-based status reports `working`, and
  a session-wide pressure killer gives no per-agent bound. The fix and its
  proofs: a graceful threshold recycle that never throttles when `T + δ ≤ H`
  (sharp); an independent progress/throttle watchdog with bounded silence in
  every environment, plus the exact conditions under which a watchdog inside
  the service could serve; inputs acknowledged only after the checkpoint, so
  no kill loses one and every input is processed within a stated bound, each
  assumption shown essential; and a status report that is exact about recent
  progress, which no responder without a freshness signal can be.
- `IterArchitecture.lean` — the current `patham9/iter` reference loop: ordered
  failure-transactional transformations, the separation between advertised
  and executable tools, one-cycle hot reload, burst pacing, restart behavior,
  path-only automatic memory visibility, and a proved necessary-feature gap
  for hosting PettaClaw unchanged.
- `IterAuthoring.lean` — the authoring seam found by comparing the hosted
  adapter with Iter's actual next-capture reload law: protected source
  proposals remain pending, while direct writes to the mutable transformation
  store activate at the next capture with a revision-bound receipt.  The
  repair changes neither the replace-or-stutter reducer nor the protected
  source-promotion boundary.
- `OmegaArchitecture.lean` — the pinned `singnet/Omega` core: duplicate-input
  pacing, signed loop budget, strict timed wakeup, provider request settings,
  ordered dispatch/history observations and the provider-failure boundary.
- `ProtectedPlasticity.lean` — the essential Iter–PettaClaw fusion: an
  invariant constitution, freely transformable development, lawfully evolving
  life, and conservative projection of every mixed trace back to both source
  architectures.
- `CodingAgent.lean` — the Codex coding-agent core: request-snapshot coherence,
  broker-mediated workspace effects, the action/evidence barrier, explicit
  cancellation and termination, an unverified-answer counterexample, and
  essential composition with Iter preparation and PettaClaw life.
- `FeedbackSensitiveBatch.lean` — the exact boundary for precommitted command
  batches: a continuation chosen before an observation is right for every
  outcome if and only if the step is observation-invariant.
- `ToolLoopComparison.lean` — historical batch admission against the
  call/result boundary shared by Codex and OpenCode.  The five-command envelope
  became, at `b7e8837`, a count limit that keeps the requested count only for
  batches of independent reads and runs one command of any other batch; with
  no new input the stimulus guard alone would run the whole batch
  (`count_limit_withholds_what_the_guard_would_run`).  Also: stimulus-guarded
  batches, a failed prefix that does not stop a mutating suffix, lossy result
  projections, and query-then-use.  Its per-chat refinement withholds only a
  reply into a chat with unread input, or a rest, so input in one chat never
  cancels a send to another.
- `ActThenObserve.lean` — what a blind batch costs: a precommitted step is
  wrong with probability at least `min (μ a) (μ b)`, independent blind steps
  compound to `(1 - ε) ^ k` (five steps at `ε = 1/5` are all right less than
  a third of the time), deciding after the observation never loses expected
  value, and a batched absence claim is right only when the item is truly
  absent.
- `IterGrounding.lean` — Iter, the historical one-command broker and a hybrid
  over one call/result vocabulary.  Iter gives every call exactly one result
  before the next decision, defers nothing silently and decides on complete
  evidence, but runs effects blind and trims away the originating request at
  its real limits.  The broker is effect-safe for every dependency relation,
  yet a withheld command gets no receipt, the next view omits results the
  ledger holds, and the deferred-write/claimed-send incident replays as a
  concrete trace.  The hybrid (execute in order, stop at a failure, denial or
  dependent effect, give the rest a `notRun` result and a pending entry, pin
  the request) has all of these together (`hybrid_grounded_and_safe`). The hybrid
  has no numeric command ceiling; successful admitted observations all run.
  Pending occurrences require an explicit resolution; repeating equal content
  does not erase them. Dependency soundness remains a host obligation. Without
  a claim gate the false claim still goes out
  (`hybrid_without_claim_gate_admits_claim`).
- `CommandHolds.lean` — what the historical dependency hold and failure stop
  cost, against a runner that executes every emitted call, as Codex,
  opencode, Claude Code and Iter do.  If the model re-proposes what was held,
  the hold is pure delay: the same commands with the same results in
  `1 + stops` calls instead of one (`pure_delay`).  `n` read/effect pairs take
  `n + 1` calls and leave `n * n` pending entries that only `task-resolve`
  clears, at most one per call (`alternation_pending`, `draining_takes_calls`,
  `resolve_batch_never_drains`); a search with `k - 1` failing candidates
  before the right one takes `k` calls (`failure_stop_search`).  Running every
  call already grounds the loop (`allCall_grounded`), and no read result can
  change an effect of its own batch (`allCall_noninterference`); the hold is
  what lets read content choose the effect (`hold_opens_channel`).  It changes
  what runs only when the model would revise, and with a per-call cost it
  loses below a revision probability of `cost / G`
  (`hold_negative_below_threshold`).  No Mathlib; its audit also lists
  `Classical.choice`, through core list lemmas.
- `PromptCacheLayout.lean` — why a prompt's stable text must lead: laid out
  least changeable first, the text up to any level is a prefix of the whole,
  so turns that agree on it share it with the provider's prefix cache; one
  changing segment ahead of stable text can leave nothing shared.  The
  deployed head / stable-sources / conversation / per-turn layout is an
  instance.
- `ContextAttention.lean` — an interruptible task capsule with a separate
  foreground human-event lane, exact acknowledgement, stop dominance, and
  bounded semantic retrieval that cannot erase required context.
- `RemoveByIndex.lean` — when a workspace removal may read an index instead
  of every row: removing every match through a complete index removes the
  rows the scan removes; removing one occurrence agrees with the scan only for
  an index that follows row order, and the store's index (exact values, then
  variables) does not, so a bounded removal keeps the scan.
- `OverlayIndex.lean` — a transaction's own edits read through an index
  instead of a scan: a row that unifies with a pattern lies in the slot list of
  the pattern's key, the keyless list or the variable list; the cursor's
  three-way walk of those lists yields the scan's matching rows in slot order,
  whichever exact position it reads; an open cursor is unchanged by later
  edits; the hash set of removed stored rows answers what the old scan of the
  removals answered; marking removed rows and filtering at commit keeps the
  rows that erasing them kept; and with ground keyed rows a read visits only
  the pattern's bucket.
- `LlmLedger.lean` — the LLM call ledger as native transitions: the host's
  Python path completed (or failed) a request and settled its call in two
  transactions, so a crash between them left a completed request with an
  active call; the native transition does both or nothing, and leaves no such
  state; with the epoch that owns the call it is exactly the two steps in
  sequence, and a stale epoch changes nothing; a failure raises its provider's
  cooldown in the same transition and a cooldown never shortens; the history
  keeps the first event of each pair; an operation repeated under its request
  id returns its first answer without a second effect; and inserting a call
  keeps the newest-first list of turn calls ordered by creation time, calls of
  one time in their arrival order.
- `CodingSessionLifecycle.lean` — the classifier and the view behind the
  agent's coding sessions. Under the given world, the resume guard is
  equivalent to the stated predicate for a safe resume on the pin: the bundle
  is present, no dependency is retired or of unknown backend selection, the
  engine binary exists, and a recorded hash still matches. Each refusal names
  a reason that holds. A pin without an engine hash is allowed by policy, and
  is labelled unverified, never resumable. An unknown selection is labelled
  unverified and refused, retryably. The unbounded view lists every listed
  session once and nothing else: a running session always, a held session
  only from its review date (or not at all while held without one).
  Recomputing it is idempotent, and it does not change between review dates.
  The bounded rendering shows or counts every listed session, and counts every
  session under its verdict; a hidden tail can stay hidden, so this is no
  fairness claim. Outside the model: checkpoint decoding, the completeness of
  the retirement table, filesystem coherence, launch races and legacy engines.
- `CodingSessionAuthority.lean` — resumes, systemd scopes and the turn-start
  reaper, with the reaper's observation and publication as separate steps.
  Two traces are decided. A paused reaper marks a live successor run
  interrupted, even when the resume settled the old ending first. A launch
  delayed past a later run's whole life still starts. With conditional
  publication (the state must still name the observed run) and run tokens (a
  resume reserves a fresh token under the session lock, and a worker starts
  only by consuming the current one), no ending is ever published over a live
  run, a token is consumed at most once, only the newest reservation can be
  consumed, and a superseded launch exits in either order of registration.
  A stop must revoke a pending reservation: otherwise the stopped launch
  starts afterwards (decided), and with the revocation it never does.
  That one worker runs is systemd's unit-name uniqueness, assumed.
- `CodingSessionLaunch.lean` — the adapter steps the authority model
  assumes atomic. Two decided traces: a launch that rereads the manifest's
  newest token runs its own bundle under a later re-pin's authority, and a
  resume whose liveness check ran outside the lock replaces the token of a
  live worker. With a reservation that refuses while a consumed worker is
  alive, a launch that carries its descriptor unchanged, and a consumption
  that requires the descriptor's token and bundle to equal the manifest's,
  every live authority holds the manifest's token and runs its bundle.
- `CodingSessionRepin.lean` — re-pinning a stopped session to the current
  runtime keeps every execution record, so an uncertain execution stays
  uncertain and the dispatchable identities are unchanged; a recorded
  identity is never dispatchable; a failed checkpoint check changes nothing;
  re-pinning to the pin itself is a no-op; the kept record is the replaced
  pin; and at every crash point the pin a resume reads is the old record or
  the checked new one. The check runs outside the lock on one checkpoint
  revision, and the publication rechecks it, so a published pin was checked
  against the checkpoint it pairs with; without the recheck, a checkpoint that
  changed during the check pairs with an unchecked bundle (decided). Inbox
  lines appended meanwhile are kept. The manifest is rechecked as well: a
  re-pin that rechecks only the checkpoint overwrites a reservation made
  during the check (decided), and with the manifest rechecked a publication
  replaces exactly the manifest it observed. The check itself is a given
  verdict.
- `RepeatedOccurrence.lean` — a publication may edit an occurrence once:
  checking the collected keys for a repeat only where staging stops (at the
  end, before a failed edit, at a failed count or index step) gives exactly
  the answer of testing each key against the earlier ones, which lets the
  runtime check once with a hash set instead of n²/2 comparisons.
- `TurnLedger.lean` — the agent ledger as one state machine (accept, capture,
  decide, restore, report, observe, attest, finish, dispositions, checkpoint):
  only deciding the pending turn creates an action, recovery never re-issues,
  receipts are write-once, achievement needs a checked successful receipt, a
  checkpoint commits its working set, inputs and request together, and settled
  inputs stay settled. The specification a native ledger must satisfy.
- `ObservedReceipts.lean` — when an action counts as observed, the mark that
  attest, finish and the protected view's waiting receipts depend on. If
  answered prompts mark nothing, no action created since is ever observed or
  checkable, a shown result stays unobserved (a concrete trace), and two
  waiting receipts keep every later one out of the view. If an answered prompt
  marks the actions it carried completely, observed means exactly shown, a
  shown action with its receipt stays checkable, and the view waits only on
  receipts never shown.
- `ConsoleView.lean` — the operator console's promises: commands printed at
  column 0 copy back exactly (an indented here-document never ends), and the
  status row drops fields in one fixed order, so essentials stay, kept fields
  keep their order, the row fits, and a wider terminal never hides a field.
- `RecallProvenance.lean` — recall over a best-first ranking keeps one
  candidate per distinct memory text: kept texts are distinct, a later copy
  changes nothing, the dedupe of a prefix is a prefix of the dedupe of the
  whole (so a fetch that grows until it has `k` texts or exhausts the ranking
  is exact), copies merge by an idempotent max, and the oldest-copy
  representative is stable when newer copies arrive.
- `ContextCore.lean` — the proposed context layer over that batch rule, with
  no count limit (a proposal runs in order up to the first command the host
  holds back): a paired task transcript, a pending list that resolves each entry once,
  compaction that leaves a recoverable stub for every dropped pair, an
  integer short-term-importance pool for optional context only, a trigger-aware
  assembler whose pins do not depend on the pool or the trigger, and a claim
  gate under which a `notRun` result never backs a claim.
- `ConversationContinuation.lean` — the shared managed-host request ledger:
  delivery acknowledgements, interruptions and bounded context cannot discharge
  unfinished requests; dependent effects wait for observed broker results;
  completion requires a correlated successful receipt and the task's own
  acceptance check. This is an executable architecture contract, not a claim
  that unchanged upstream loops or the deployed framework already conform.
- `ObservedStrategy.lean` — the composition of Iter preparation, Codex request
  authority/result observation and Omega wake scheduling over that ledger.
  It protects unfinished work across arbitrary operational traces, invalidates
  stale decisions after input and mode changes, preserves pending effects on
  restart, accounts for every provider attempt, and gates scope-specific
  absence and completion claims. Independent batches remain possible when
  their continuations are proved observation-invariant.
- `ObservedStrategyChecks.lean` — finite model replays and deliberately broken
  alternatives covering stale effects, skipped observation, schema-only
  authority, false completion, unavailable searches and lost checkpoint state.
- `AdmissionFrontier.lean` — separate thought and tool admission, trusted
  observation/effect classes, unchanged unresolved outcomes, and snapshot
  invalidation after late receipts. `ObservedStrategy.lean` reuses its thought
  gate; dependent effects and checked goal completion retain separate gates.
- `InputDelivery.lean` — the transport refinement missing from the original
  attention model: stable observation under relational re-entry,
  history-before-acknowledgement, exact-prefix settlement, failure retention,
  restart recovery, and a destructive-observation counterexample.
- `AgentArchitecture.lean` — an architecture-neutral reliability contract:
  protected constraints outside lossy compaction, append-only receipts,
  distinct process/cognitive/verified liveness, end-to-end completion evidence,
  and syntactic repetition signals that do not overclaim semantic stuckness.
- `VerifiedFrontier.lean` — the Codex `StartOrSteer` turn law and its fusion
  with the other models: pending-input steering, quiescent effect commitment,
  exact-artifact receipts, exact-once input and effect handling, append-only
  proof-carrying traces, a frontier-blindness separation theorem,
  digest-bound promotion, outcome-first evaluation, derived attention, and
  conservative coordinate composition.
- `MinimalKernel.lean` — a weakness-ordered refinement of the fused core:
  harness-issued decision receipts, semantic effect idempotency, fail-closed
  and fail-alive promotion, finite autonomous budgets with human preemption,
  evidence-closed knowledge, bounded non-progress observation, a
  weakest-sufficient commit theorem, and coordinate-erasure witnesses.
- `WeakSelfHostingCore.lean` — the smaller protected-plasticity root:
  arbitrary failure-transactional extensions, unrestricted candidate staging,
  a weakest sound root-promotion gate, atomic recovery, and erasure witnesses
  only for last-known-good separation, external selection, and atomic
  promotion.
- `FeatureExpressibility.lean` — adequacy witnesses showing that Agent, Iter,
  Coding, human-attention, timing, receipts, evidence, stuck observation, and
  metadata-aware no-replay policies can be hosted above the unchanged weak
  core.  It also proves that metadata cannot force an arbitrary opaque
  controller to behave well.
- `ThreePolicyFusion.lean` — one product-state runner with Agent, Iter, and
  Coding policy views; arbitrary mixed traces project exactly to all three
  source semantics, policy selection is an operational stutter, independent
  actions commute, and every fused action refines to a two-outcome process
  kernel protecting an abstract root while leaving the whole periphery
  plastic.
- `OpenEndedProcessCore.lean` — the periphery-polymorphic form of that same
  two-equation kernel: open named-coordinate assemblages, conservative
  append-only observation, admission witnesses that cannot be relabeled across
  authorities, authority revision with fresh evidence, admitted whole-root and
  quiescent succession, and exact specialization back to the three-policy
  runner.
- `ContextProjection.lean` — typed known/absent/unavailable source states,
  latest-revision views over append-only ledgers, causal-frontier isolation,
  compositional delta replay, non-authoritative materializations, and an open
  policy type capable of hosting arbitrary context managers without changing
  the process core.
- `WeakAgentEcology.lean` — the weakest common Agent/Iter/Coding host: an open
  table of replaceable context-sensitive policies over the unchanged
  two-equation runner, locally transactional composition, exact preservation
  of all three source projections and Iter pipelines, arbitrary policy and
  context replacement, and erasure counterexamples for both kernel equations.
- `ContextWindow.lean` — a bounded context window that preserves the newest
  substantive turn, respects its size limit, and never invents admitted turns.
- `FuelPolicy.lean` — explicit renewal disciplines separating overwrite,
  saturation, carry, decay, and accumulation, with their exact boundedness
  and autonomy consequences.
- `RestEnergy.lean` — the pause/rest state omitted by the earlier breath model,
  including the deployed stranding counterexample and a self-directed renewal
  policy that preserves energy without creating it.
- `StiMass.lean` — bounded salience injection and repeated-decay Lyapunov laws
  for the short-term-importance economy.
- `StiFloor.lean` — a facts-of-record ordering for salience-floor ties, with
  irreflexivity, transitivity, totality, and injected-over-never precedence.
- `StiFloorDecay.lean` — the concrete fixed-point floor-division decay model
  and its contraction and loss bounds.
- `TelegramCommandPlane.lean` — operator commands answered by the channel
  service, a process separate from the agent. For every agent behaviour, each
  command gets exactly one reply by its deadline: the agent's own answer, or
  the service's fallback, later edited with the agent's answer. Every reply
  and edit traces to the agent's answer to that very command, and a stop is
  enforced where sends are dispatched. A contrast theorem shows that when only
  the agent can answer, a silent agent leaves the command unanswered forever.

Attention and memory models now live in the semantic library:
`Mettapedia.CognitiveArchitecture.Attention` and
`Mettapedia.CognitiveArchitecture.Memory`. Generic restarting walks and finite
mass transport live in `Mettapedia.ProbabilityTheory.MarkovChain`. These are
shared mathematics, independent of the agent framework that first used them.

Most models use no Mathlib and end with a `#print axioms` audit:
zero `sorry`, axioms at most `propext` and `Quot.sound`, several theorems
axiom-free. Files that import Mathlib, including the probabilistic batch models
above, compile with Mathlib's build directory on `LEAN_PATH` (the revision
pinned by the MeTTapedia Lake manifest), and their audits may also list
`Classical.choice`. `IterArchitecture.lean` imports the two comparison models.
Check with:

```
lean HeartModel.lean
lean -o ClawArchitectures.olean ClawArchitectures.lean
lean -o PresentMoment.olean PresentMoment.lean
LEAN_PATH=. lean -o IterArchitecture.olean IterArchitecture.lean
LEAN_PATH=. lean -o IterAuthoring.olean IterAuthoring.lean
LEAN_PATH=. lean ProtectedPlasticity.lean
LEAN_PATH=. lean CodingAgent.lean
LEAN_PATH=. lean ContextAttention.lean
lean RecallProvenance.lean
lean ConsoleView.lean
lean TurnLedger.lean
lean ObservedReceipts.lean
lean RemoveByIndex.lean
lean OverlayIndex.lean
lean LlmLedger.lean
lean CodingSessionLifecycle.lean
lean CodingSessionAuthority.lean
lean CodingSessionRepin.lean
lean CodingSessionLaunch.lean
lean RepeatedOccurrence.lean
lean InputDelivery.lean
LEAN_PATH=. lean AgentArchitecture.lean
LEAN_PATH=. lean VerifiedFrontier.lean
LEAN_PATH=. lean MinimalKernel.lean
LEAN_PATH=. lean WeakSelfHostingCore.lean
LEAN_PATH=. lean FeatureExpressibility.lean
LEAN_PATH=. lean ThreePolicyFusion.lean
LEAN_PATH=. lean OpenEndedProcessCore.lean
LEAN_PATH=. lean ContextProjection.lean
LEAN_PATH=. lean WeakAgentEcology.lean
LEAN_PATH=. lean ContextWindow.lean
LEAN_PATH=. lean FuelPolicy.lean
LEAN_PATH=. lean RestEnergy.lean
LEAN_PATH=. lean StiMass.lean
LEAN_PATH=. lean StiFloor.lean
LEAN_PATH=. lean StiFloorDecay.lean
lean IterGrounding.lean
lean CommandHolds.lean
lean SequentialTools.lean
lean ContextCore.lean
lean -o HeartModel.olean HeartModel.lean
LEAN_PATH=. lean -o AsyncWait.olean AsyncWait.lean
LEAN_PATH=. lean -o AdmissionFrontier.olean AdmissionFrontier.lean
LEAN_PATH=. lean -o EventPump.olean EventPump.lean
LEAN_PATH=. lean ProcessSupervision.lean
lean TelegramCommandPlane.lean
```

For the composed strategy and its imported model dependencies, from the
repository root with the pinned Lake dependencies already available:

```sh
python3 lean/pettaclaw/check_observed_strategy.py \
  --output-dir lean/mettapedia/.lake/observed-strategy
```

This checks the modules, the finite replays, and the theorem axiom audit. Its
JSON receipts identify source hashes and reject proof dependencies outside
Lean's standard axioms. This is an executable managed-host specification;
conformance of a deployed runtime must still be established at this boundary.
The reference models are pinned to Iter `f4064d97849ecaccac7939315a3f1a68de15c3ef`,
Omega `ee0618a293ec3662a32b10b09c6cbb073f59d6b2`, and the Codex snapshot documented
in `CodingAgent.lean`. The managed composition does not rewrite upstream loops.

The composition reuses the source models at these boundaries:

| Mechanism | Reused definition | Composition property |
| --- | --- | --- |
| Iter ordered preparation | `CodingAgent.prepareWithIter`, `IterArchitecture.applyTransformations` | Exact message order; failed transforms stutter; authority is unchanged |
| Iter persistence | `IterArchitecture.rollback_preserves_checkpoint` | Reference checkpoint law remains available; managed restore also retains obligations and issued effects |
| Codex captured authority | `CodingAgent.RequestView` | Commands require the captured implementation and permission; advertisements grant neither |
| Codex result observation | `ConversationContinuation.propose`, `brokerResult`, `observeResult` | Dependent effects wait for correlated result observation |
| Omega wake scheduling | `OmegaArchitecture.armWake`, `idleWake` | Submission arms the deadline; strict wake changes scheduling without discharging work |
| Managed lifecycle | `ObservedStrategy.step`, `run` | Input, mode changes, restart and compaction preserve accepted unfinished requests |

The protected request ledger, stale-decision gate, allowance/cooldown policy,
full host checkpoint and scoped search-evidence gate are managed additions.
The model assumes durable atomic storage, faithful IDs, a trusted coverage
validator and a task-specific completion checker. It proves preservation,
admission and conditional readiness; it does not prove eventual success of
arbitrary tasks, natural-language interpretation, or external tool behavior.

The paper (repository [`papers/pettaclaw.tex`](../../papers/pettaclaw.tex),
PDF alongside) tells the whole story: architecture, doctrine, the two
incidents, the theorems, the live verifications. Model-to-code
conformance tests live with the agent runtime
([godelclaw/pettaclaw](https://github.com/godelclaw/pettaclaw)).

## Scheduling boundary

The rho reduction relation determines which communications are enabled. The
host executor chooses and runs enabled continuations. In Rholang, RSpace keeps
unmatched sends and waiting continuations; a matching `produce` or `consume`
returns runnable work to the interpreter. The current F1R3FLY Rust interpreter
uses Tokio tasks for parallel branches. This is execution machinery around the
calculus, not an additional language-level ordering guarantee.

Primary sources: [RSpace](https://rholang.github.io/docs/rspace-intro/),
[F1R3FLY reduction and dispatch](https://github.com/F1R3FLY-io/f1r3node/blob/3507ce3daab1946cdda2050a6dbeedd0f0898575/rholang/src/rust/interpreter/reduce.rs).

CeTTa already supplies canonical/rotating rho reduction scheduling and a
bounded reducer. A long-lived agent additionally needs an event pump that
retains continuations, delivers correlated HTTP/timer completions, resumes
runnable work and checkpoints ownership across restart. Reaching quiescence
means no reaction is enabled now; it does not complete a pending external call.
Scheduling policy can remain MeTTa over native transport and storage services.

The historical strategy and topic models share `AdmissionFrontier` for provider
admission. A missing broker outcome cannot disable eligible thinking. Unknown
effects still block dependent effects; task completion checks settlement and
the task-specific acceptance rule. This conservative strategic model treats
every command as an effect. The richer observation/effect distinction and its
runtime decision correspondence belong to `AdmissionFrontier`.

The checker audits this shared admission dependency in every suite. Replays
cover thinking with an unresolved effect, retaining that effect after a text
reply, refusing a second effect and invalidating a plan when a late receipt
arrives. These are model properties and bounded implementation comparisons;
they do not verify the C executor, transport, or arbitrary host scheduling.
Conditional fairness still requires continued service and bounded admission.

## Event pump and channel contract

`EventPump.lean` models owner/generation/serial identities, immutable input
records, queued/claimed/settled delivery, selective receive and safe suspension.
Steps preserve other mailboxes, and independent mailbox steps commute.
An epoch-bound wait ticket is checked against durable readiness immediately
before parking. Arrival both before and after that check is covered. Accepted
evidence survives arbitrary action/recovery traces; settlement cannot reopen
or produce another delivery receipt. Recovery requeues local claims, while
`AsyncWait` retains remote uncertainty and denies another provider submission
while the original call remains owned. Local delivery settlement is distinct
from goal fulfillment and remote execution.

The scheduling policy pops one runnable task per slot and appends both yielding
continuations and new arrivals to the tail. Every task in an existing finite
prefix receives service within its prefix length plus one, even with continuing
arrivals. Ready-owner publication connects accepted inbox events to this queue.
The existing weighted goal policy remains available; round-robin is a concrete
policy whose bound is proved, not a claim about Tokio's internal algorithm.
Capacity admission preserves unique runnable keys and the configured limit.
A finite inbox drains within its pending-event count when handling slots return
and commit dispositions. Neither service theorem promises provider completion.

`ReadyQueue.lean` specializes admission, rotation and removal to an executable
native-queue reference. Its invariant holds across arbitrary operation traces:
membership remains unique and within capacity. Its service theorem permits
visited competitors to retire as well as yield, while continuing arrivals
cannot overtake an existing finite prefix. `EventPumpChecks` exhibits the old
advancing-array failure after retirement and the preserved order in the new
model. `ReadyQueueOracle.lean` runs these same transition definitions for CeTTa's
native differential test; this avoids an independently rewritten test oracle.
The finite C comparison establishes checked cases, not a proof of native
pointers, the compiler, or all host transitions.
The model also proves exact suffix recovery using `(revision, position)`
cursors under the store's ordering assumption, with a counterexample to
resuming a partially discovered batch from its revision alone. Native channel
tests exercise the multi-effect case through a queue of capacity one.

The wall-time theorem requires bounded whole-slot durations, including pump,
storage and evaluation work, as well as a wake-up bound and continued service.
For a queue bounded by `N` and slot cost bounded by `q`, the modeled latency is
at most `p + N*q`, where `p` is wake-up delay. These are implementation
obligations. Reduction counts alone cannot bound an unbounded primitive. The
journal/filter definitions are reference semantics; efficient implementations
should use derived pending indexes instead of rescanning historical rows.

`ChannelJoin.lean` models the RSpace data/continuation/reaction boundary. Each
join selects a distinct occurrence for every pattern, with channel and payload
checks. Invalid/partial candidates stutter. A valid join consumes its selected
sends and records the complete runnable input tuple in one transition. Unchosen
data and other receives are preserved. One-shot receives retire; persistent
receives remain but cannot reuse consumed sends, including after arbitrary
later actions. Joins using distinct receives and disjoint occurrences leave
each other enabled. All accepted occurrences remain available or recorded in a
reaction across arbitrary channel traces. Matching is nondeterministic at this
boundary: the validator does not claim an incomplete candidate finder is
complete, and this model does not implement the full Rholang pattern language.

`EventPumpChecks.lean` includes the answer/timer latch race in both orders,
late-answer receipt after the timer wins, distinct sends with equal payloads,
selective receive, restart and duplicate-delivery replays. Counterexamples show
lost wake-ups without rechecking, starvation without rotation, violation of any
proposed latency without bounded slots, and lost work after partial join
publication. A stuttering host satisfies safety refinement without making
service progress. The checker audits these contracts, the shared admission boundary
and the reused scheduling dependency against Lean's standard axioms.

`HostAdapter` states the per-transition refinement equation required of an
actual implementation. Its trace theorem lifts evidence and wake-up safety to
any host that proves that equation, allowing bookkeeping stutters. Liveness
additionally requires service progress and timing bounds: a host that stutters
forever can preserve safety while never handling an event. Atomic durable
commit, never-reused identities/epochs, trusted classifications and faithful
clock/transport observations remain host obligations. No C/MeTTa deployment,
Erlang, Tokio or RSpace implementation is verified by these files.

Primary sources: [Erlang mailboxes and selective receive](https://www.erlang.org/doc/system/conc_prog.html),
[Tokio fairness assumptions](https://docs.rs/tokio/latest/tokio/runtime/index.html),
[RSpace matching](https://rholang.github.io/docs/rspace-intro/).

From the repository root:

```sh
python3 lean/pettaclaw/check_observed_strategy.py \
  --suite event-pump --output-dir build/event-pump
```

## Operator control through the channel service

`ChannelOperatorControl.lean` composes the channel service's own send latch,
the cognition latch its command responder writes, and the supervisor's pause
marker. The service answers `/stop` and `/start` at once from its own latch,
so the operator can be told "Stopped" while the agent keeps calling the
provider (`stopped_reply_while_thinking`, unbounded while the responder is
down), or "Started" while the sibling tool's pause keeps it down
(`started_reply_while_paused`). With one latch that cognition and the
supervisor read, replies equal the committed authority
(`reply_matches_authority`) and a stopped latch admits no new provider call
(`stopped_means_no_new_calls`). Among several agents, a bare command in a
group reaches every agent (`bare_command_reaches_every_agent`) and a shared
command file names them all alike (`shared_name_misnames`); addressed group
commands and per-instance names fix both. The deployed repair keeps both latches
but replies with the responder's answer after the cognition latch is set, and
`/start` clears the agent's own pause (`implemented_replies_follow_effect`,
`implemented_no_false_stop`, `implemented_start_resumes`).

```sh
lean lean/pettaclaw/ChannelOperatorControl.lean
```

## Response timing and periodic work

`ResponseTiming.lean` separates the existing local service bound from provider
completion and outbound delivery. It proves that local responsiveness alone
cannot bound a model answer, derives an answer bound when the external stages
are bounded, and checks periodic deadlines against the complete scheduling
slot and handler cost. Absolute releases avoid accumulated handler drift;
meeting a deadline still requires enough time for dispatch and execution.
These conditional results do not verify the live scheduler or remote delivery.

```sh
python3 lean/pettaclaw/check_observed_strategy.py \
  --suite response-timing --output-dir build/response-timing
```

## Owned asynchronous topics

`TopicAsync.lean` extends the existing observed strategy and fair goal queue.
It allows bounded provider requests for independent topics while preserving
one shared request ledger and budget. Its thought gate is independent of the
dependent-tool observation barrier; effect dispatch checks that barrier
explicitly. `TopicAsyncChecks.lean` supplies finite replays and deliberately
broken alternatives.

```text
topic context -> captured request -> same-topic result inbox
                        |                     |
                 shared fair queue     observe -> version check -> broker
```

Each call retains its agent/generation/serial identity, original topic,
context revision, declared dependency revisions, captured tool authority and
response reservation. Partial content is provisional. A slow or disconnected
attempt remains owned; recovery marks it uncertain and preserves its spent
budget. Late results remain evidence, while changed context or authority
blocks stale commands. Failure evidence applies shared cooldown before the
slot is retired. Provider text alone cannot complete a goal.

The model proves bounded reservations and unfinished-work preservation over
arbitrary operational traces, unchanged result ownership, commuting distinct
arrivals, idempotent settlement, capture accounting, stale-command exclusion
and reuse of the existing checked completion rule. Weighted fairness retains
its finite-cohort and continued-admission assumptions; arbitrary task success
and unbounded arrival fairness are not claimed.

The default permits one retained call. Response capacity must be configured
explicitly; the default reservation budget is zero. Raising concurrency is a
managed-host choice, independent of the reference Iter/Omega loops.

From the repository root:

```sh
python3 lean/pettaclaw/check_observed_strategy.py \
  --suite topic-async --output-dir build/topic-async
```

The topic, fair-goal and observed-strategy suites build from Lean's standard
library. The generic typed state and query contracts are in
`Mettapedia.CognitiveArchitecture.Agent.WorldStateCore`; `Agent.WorldState`
re-exports them and adds the Mathlib finite-cardinality theorem. No extra
Mathlib copy is needed for these executable architecture checks.

Runtime correspondence requires atomic durable capture/charging, faithful
result IDs, declared shared reads and versioned writes, honest payload
accounting, and the existing broker/task checker. Reservations cover modeled
retained responses, not decoder, TLS or total process memory. Uncertain calls
need explicit reconciliation; the model does not retry a remote POST or
silently erase an unknown outcome. Runtime implementation and paired live
qualification remain separate milestones.

## Upstream loop mechanisms

Seven files analyze loop and control changes proposed upstream after the
pinned Iter and Omega revisions. Each states what the mechanism solves, proves
its sound part, and gives explicit counterexamples where it fails.

| File | Upstream source | Mechanism |
| --- | --- | --- |
| `IterBranches.lean` | `bgoertzel-sing/iter` master `3399366`, branch `agent/protocosmo2-multi-branch` `6ea3dd6` | background branches, merge queue, model-call semaphore, shutdown drain |
| `IterTurnControl.lean` | same, commits `2727dbe`, `87374c3` | progress checkpoints, terminal and transient provider errors |
| `DeonticControl.lean` | branches `agent/protocosmo2-wmtm-live-20261005` `4564185` and `agent/protocosmo2-402-circuit` `7c603b5` | OODA cycle, deontic appraisal, reference monitor, grants, event store, deontic enforcer |
| `WorkLease.lean` | `bgoertzel-sing/iter-work-lease-controller` `ccbaa30` | budgeted work leases with periodic review |
| `ContextFrames.lean` | `singnet/Omega` PR #284 `a72837e` | context frames, modes, priority selection |
| `NativeToolCalls.lean` | `singnet/Omega` PRs #379 (merged), #358 `030c014`, #349 `9d28e83` | text command parsing versus native tool calls |
| `PromptCacheLayout.lean` (extended) | `singnet/Omega` PR #341 `5455049` | stable-first context order |

**Background branches (`IterBranches.lean`).** A slow model call continues in a
thread so the loop stays responsive. Sound: the multi-branch set tracks every
running branch and stays within its cap (`multi_tracks_running`,
`multi_bounded`); the semaphore bounds concurrent calls (`semaphore_bound`);
an abandoned branch stops after its current step (`multi_abandon_leak_le`).
Counterexamples: master overwrites its single slot and orphans a running branch
(`master_orphans_branch`); an abandoned master branch can still run 249 tool
calls (`master_abandon_leak`); results pushed after abandonment are merged
(`abandoned_results_merged`); merging per message can separate a tool call
from its result, which the chat protocol forbids
(`interleaved_merge_breaks_protocol`); shutdown can leave an executed effect
without a record (`shutdown_loses_record`). Fixes proved: merging a call with
all its results preserves well-formedness (`wf_append`,
`group_merge_preserves`), and journaling the intent first covers every effect
(`intent_covers_effects`). In CeTTa a call is never abandoned: it stays owned
(`EventPump.lean`, `AsyncWait.lean`), its late result is evidence
(`TopicAsync.lean`), and a call and its results publish atomically
(`ChannelJoin.lean`).

**Checkpoints and provider errors (`IterTurnControl.lean`).** A burst with no
reply produces a progress message at step 50 (`silent_burst_checkpoints`), but
one early `send` disables the watchdog until the next input
(`acknowledgement_disables_checkpoints`), and bursts ended by `nop` never trigger
it (`nop_resets_without_message`). Counting working steps since the last
visible message bounds silence on every trace (`quiet_bounded`). Transient
errors back off and reach the idle state at the ninth failure
(`transient_errors_idle_at_ninth`); errors that are neither terminal nor
transient retry every second forever (`other_errors_retry_forever`); the
terminal path truncates the user's input away (`terminal_error_drops_input`).
One failure budget for every class leaves the retry state
(`budgeted_errors_leave_retry`); the request ledger keeps a failed request with
its receipt.

**Deontic control (`DeonticControl.lean`).** The appraisal filter is sound
(`deontic_filter_sound`), and a dispatcher that accepts only consumed monitor
approvals executes each approved grant at most once and never after revocation
(`effects_authorized_once`, `revoked_stays_without_effect`). The deployed
dispatcher trusts a caller flag (`dispatch_trusts_flag`); revocation is inert
(`revoke_is_inert`); used keys vanish on restart (`restart_reauthorizes`);
superseding the newest event can lower the revision and revalidate a stale
grant (`revision_aba`, fixed by log positions, `knowledge_time_monotone`); plan
steps run against a state earlier steps changed (`stale_plan_step_runs`, fixed by
`one_effect_per_revision`); a stop is read once per cycle
(`stop_mid_plan_ignored`, fixed by `stop_checked_per_dispatch`); the integration
adapter's grants are expired on arrival (`adapter_grant_expired_on_arrival`);
derived working-memory items become observations
(`derived_item_becomes_observation`). The 402-circuit enforcer lowers the
attention and PLN strength of everything sharing a keyword with a forbidden
action, including the reason for the prohibition and its negation
(`deontic_status_rewrites_truth`, `prohibition_loses_attention`), and cannot
block the action (`enforcement_only_lowers_attention`). Deontic status belongs
in the authorization gate, as a separate atom.

**Work leases (`WorkLease.lean`).** The counters are sound: turns never
decrease and stay within the turn and token budgets on every trace
(`turns_monotone`, `turns_within_budget`, `tokens_within_budget`); a paused
lease reserves nothing (`paused_lease_reserves_nothing`); admission is idempotent
with one active lease per bot (`admit_idempotent`, `one_active_lease`). The review
gate waits for a reserved review, not a verdict
(`review_gate_is_reservation_only`; fixed by `pending_review_blocks_turns`); a
paused lease does not stop a new event from opening a fresh one
(`paused_lease_admits_new_event`); completion is allowed with an uncertain effect
(`completes_with_uncertain_effect`).

**Context frames (`ContextFrames.lean`).** Completed frames are never selected
again and selection respects the root mode (`completed_never_selected`,
`selected_matches_mode`); user input preempts autonomous work
(`user_input_preempts_slow_work`). Nothing bounds waiting: a lower-priority
frame starves while a higher one stays active (`lower_priority_starves`), later
user requests wait behind the oldest (`older_user_frame_wins`,
`user_input_waits_behind_user_work`), and the per-frame history in the prompt
grows without bound (`history_summary_unbounded`). Frames map to owned topics
under `FairGoalScheduling.lean`, with a bounded window per topic
(`ContextWindow.lean`).

**Native tool calls (`NativeToolCalls.lean`).** Decoding tokens before splitting
lines turns relayed text into commands (`decode_then_split_injects`); splitting
first keeps the command count (`split_then_decode_keeps_commands`). Serialized
structured calls round-trip exactly when the reader inverts the writer's
escaping (`readStr_escape`, `roundtrip`); a reader that ignores `\\` misplaces
literal boundaries and rejects the batch (`quirky_reader_misplaces_boundary`,
`quirky_breaks_roundtrip`). Validation admits only calls advertised in the
request (`validated_call_was_advertised`). Building call atoms directly from the
provider's fields removes the text round trip.

**Context order (`PromptCacheLayout.lean`).** History ahead of per-cycle results
is stable-first, and an appended history is shared while it fits
(`appended_history_shared`). A sliding tail window shares nothing once full
(`sliding_window_shares_nothing`); a block-aligned cut shares the history between
block boundaries (`block_window_shared`, `block_window_example`).

These models check the stated mechanisms at the modeled boundary. They do not
verify Python threads, SQLite, provider behavior or the MeTTa runtime.

```sh
cd lean/pettaclaw
lean IterBranches.lean
lean IterTurnControl.lean
lean DeonticControl.lean
lean WorkLease.lean
lean ContextFrames.lean
lean NativeToolCalls.lean
cd ../mettapedia
lake env lean ../pettaclaw/PromptCacheLayout.lean
```
