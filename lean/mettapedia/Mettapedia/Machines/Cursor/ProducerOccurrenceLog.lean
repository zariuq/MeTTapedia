import Mettapedia.Machines.OwnedPullDriverCost
import Mettapedia.Machines.Cursor.SharedOccurrenceOwnership
import Mettapedia.Machines.Cursor.SharedFactorMachine
import Mettapedia.Machines.ExecutionHistoryReadout
import Mettapedia.GSLT.Core.InferenceRecordingPrefix
import Mettapedia.GSLT.Contracts.RunAccounts
import Mettapedia.Machines.Cursor.Amortized

/-!
# One selected producer feeding an owned occurrence log

The composition stages an actual producer return together with its complete
post-transition residual. Capture and log admission occur before another
producer transition. A full log, a refused capture or refused admission retains
the pending return and the complete residual. Administrative progress, yields,
effect requests, handoffs, interruption and genuine completion stay distinct.
Repeated barrier notices inspect the same retained request; they execute no
host action and do not add answer occurrences.

No active consumer means no producer demand; this leaves execution and log
open rather than certifying exhaustion. Known terminal or retained request
barriers are inspected before row fullness because they execute no producer.

The scheduler below counts composition microsteps, including staging and
admission. This is different from an allowance counting admitted returns and
does not bound callback work or latency. For the owned-driver instance, the
notice projection also recovers the exact number of driver transitions and the
complete residual of the unrecorded common runner. Admission and refusal do not
execute the producer again. Capturing a borrowed return is supplied
as a primitive; its observation law is separate from native root discovery,
copy allocation and cleanup. Compatibility is checked at every producer and
buffered-delivery boundary, but the supplied check is not a proof of source
dependency validity or a transport between contexts.
The check is pure and fixed within one microstep. Revalidation after a native
callback changes its current context is an additional implementation obligation.

Retiring one consumer uses the existing log cancellation. It removes only that
consumer's unread retention. The producer residual and its accepted count, the
captured context, caller publications and every other consumer's ready answer
remain. Collection of the trimmed log is the existing ownership law; affine
discard of the whole delivery is not this transition and does not prove that
the producer effect ran once.

Ordinary execution and the notice-list runner share `pump`. `ordinary` keeps
the configuration and does not accumulate notices or test a recording policy.
`run` returns the notice list of that same configuration. Retiring a consumer
cancels that delivery cursor through the existing log operation. It is not
erasure of an optional history, and it is not how recording stops. While
another consumer still has a cursor, later slices commute with that
cancellation and do not restore the retired cursor. Retiring the last consumer
stops producer demand; the paid execution stays.

Bounded recording is the streaming runner `recordOrdinary`: one `pump`, an
immediate `Prefix.push` of that notice, and a tail-call on the updated prefix
and the next configuration. It does not build a notice list. The equality
`recordOrdinary_eq_append_run` specifies that stream as `Prefix.append` of
`run`; the unbounded runner belongs only to that proof and the laws derived
from it. The configuration remains the ordinary one. A full prefix counts
each later notice in its omitted field and does not alter the producer.
Continuing a prefix across slices keeps its remaining capacity. Dropping the
prefix and continuing with `ordinary` leaves every delivery cursor in place.
A prefix started after an ordinary slice contains only the later notices.
`enterProducerHistory` makes that choice at entry. `none` is `ordinary` and
allocates no prefix. `some record` streams `recordOrdinary` on that prefix,
keeping its items, remaining capacity and omissions.
`Mettapedia.GSLT.Core.InferenceControl.Recording.initial` supplies a fresh
capacity. A split continues the same prefix. Forgetting it continues with
`ordinary` on the recorded configuration and reaches the same complete
configuration as one ordinary run. Late recording starts
`Recording.initial` on the configuration an ordinary prefix already reached.
Both projections are projections of that complete configuration, so they
read the stored operational field of its discovered roots.

`Accounting.enterObservers` chooses history and numerical observation
independently at entry. Its four workers share `pump`; the joint worker
records and charges the same returned transition, rather than executing the
producer twice. Both projections recover the separate existing observers
and the whole operational continuation. Forgetting history keeps paid work;
starting a fresh prefix later records only the actual suffix. Pump-only
observation requires no equality decision on payloads. These numerical
coordinates count driver transitions and successful deliveries, not callback
latency, native instructions or recording expense.

An admitted log position is one admission occurrence. Each consumer delivery
of that row is a separate use, `delivery client position`, and cites that
admission. The causal graph contains only those admissions and deliveries.
A returned producer can already have advanced before capture or admission
refuses; the refusal, effect, handoff and cancellation notices keep their
own constructors and are not graph nodes.

Dropping that optional record cancels only a distinct recorder owner through
`OwnedLifecycle.closeScope` and then collects. It does not call
`ObservationOwnership.commit` or retire a consumer. Session roots are the
operational roots, the recorder, and an outside frame that has no recorder
owner. Operational roots cover the residual, the pending return, the captured
context, the current mode's retained effect or handoff request, the active
delivery cursors and the caller publications. Payload addresses come from a
declared discovery interface; agreement with compiled layout is a native
obligation. Forgetting preserves every graph reachable from the operational
roots or that frame, and reclaims a cell only outside their union. A context
cell whose only root was the recorder is reclaimed when both omit it. The
accepted execution is unchanged: collection neither refunds it nor grants a
new root.

Heap transport applies to that collected session only. It relocates cells and
owner roots; it does not rebuild residuals, pending values, context, delivery
rows or request payloads. `Relocation.roots_cancel` commutes recorder
cancellation with that image, and `Relocation.walk_collect_eq` reads ordered
paths after the projection. A relocation of the original heap is not required.
Cancelling the recorder root does not clear a strong reference stored in an
operational cell. A heap whose payload is `StoredFields` stores an operational
value, an optional observer value and both reference sets in that record.
`projectHeap` reads the operational value and the operational reference field.
`observeOperational` reads that same operational field from the source lookup
and does not consult the projected heap. `projectOptionalFields` collects the
projected heap under the supplied roots. The source heap stays readable by an
outside observer. A target that sits in both reference sets stays reachable
from the operational field. Collection reclaims an address only when it is
outside the roots and outside every operational reference set. A cell shared
with the retained outside frame keeps its stored fields on the source. The
private image is not an in-place relocation of every address.
`receiptFieldCleared` is the reference property of that projected heap. It is
not the erasure. Native layout agreement remains outside this development. The relocated session keeps the semantic
world. Ordered cells, their byte weights and alias identity are observations
of that heap.

Carrier transport is the separate map on this configuration. `State.map` sends
log values and keeps base, cursors, completion and limit. Delivery mapping
sends those rows and the publication addresses. `mapCarriers` sends the
producer, pending return, context, current effect or handoff request and that
delivery, with `mapProducer` as the producer-only case. Cursor positions and
the accepted count are copied. A pump or run crosses the map only under local
step, capture, capacity and context laws, and anchor roots agree only under
local discovery naturality. Those hypotheses are not a native layout scan.
The carrier map does not project receipt fields.

An already buffered delivery commutes with each producer microstep and with
any finite producer slice, preserving notices and the complete owned state.
A waiting read does not commute with admission of its next occurrence.
This atomic-operation law does not prove native concurrent memory access.

This construction selects one producer. It grants no equivalence with two
independently chosen computations, effectful broadcast, late subscription,
native parallel execution, or compiled-code verification.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.ProducerOccurrenceLog

open Mettapedia.Machines

variable {Producer Borrowed Stored Context Output Effect Handoff Observation : Type}
  {clients : Nat}

inductive ProducerOutcome (Producer Borrowed Effect Handoff : Type) where
  | progress (next : Producer)
  | returned (value : Borrowed) (next : Producer)
  | yielded (next : Producer)
  | effect (request : Effect) (next : Producer)
  | handoff (request : Handoff) (next : Producer)
  | interrupted (next : Producer)
  | completed (next : Producer)

inductive Mode (Effect Handoff : Type) where
  | active
  | effect (request : Effect)
  | handoff (request : Handoff)
  | interrupted
  deriving DecidableEq

structure Execution (Producer Borrowed Effect Handoff : Type) where
  producer : Producer
  pending : Option Borrowed
  accepted : Nat
  mode : Mode Effect Handoff

structure Configuration (Producer Borrowed Stored Context Output Effect Handoff : Type)
    (clients : Nat) where
  execution : Option (Execution Producer Borrowed Effect Handoff)
  context : Context
  delivery : SharedOccurrenceOwnership.Configuration Stored Output clients

inductive Notice (Borrowed Stored Effect Handoff : Type) where
  | progress
  | returned (value : Borrowed)
  | admitted (position : Nat) (value : Stored)
  | captureRefused
  | admissionRefused
  | noConsumers
  | backpressure
  | contextRefused
  | yielded
  | effect (request : Effect)
  | handoff (request : Handoff)
  | interrupted
  | completed
  | detached
  deriving DecidableEq

def initial (producer : Producer) (context : Context) (limit : Nat) :
    Configuration Producer Borrowed Stored Context Output Effect Handoff clients :=
  ⟨some ⟨producer, none, 0, .active⟩, context, ⟨SharedOccurrenceLog.initial limit, ∅⟩⟩

def pending (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    Option Borrowed := state.execution.bind (fun execution => execution.pending)

private def stage
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (execution : Execution Producer Borrowed Effect Handoff)
    (outcome : ProducerOutcome Producer Borrowed Effect Handoff) :
    Notice Borrowed Stored Effect Handoff ×
      Configuration Producer Borrowed Stored Context Output Effect Handoff clients :=
  match outcome with
  | .progress next =>
      (.progress, {state with execution := some {execution with producer := next}})
  | .returned value next =>
      (.returned value,
        {state with execution := some {execution with producer := next, pending := some value}})
  | .yielded next =>
      (.yielded, {state with execution := some {execution with producer := next}})
  | .effect request next =>
      (.effect request,
        {state with execution := some {execution with producer := next, mode := .effect request}})
  | .handoff request next =>
      (.handoff request,
        {state with execution := some {execution with producer := next, mode := .handoff request}})
  | .interrupted next =>
      (.interrupted,
        {state with execution := some {execution with producer := next, mode := .interrupted}})
  | .completed next =>
      (.completed,
        {state with
          execution := some {execution with producer := next}
          delivery := {state.delivery with log := SharedOccurrenceLog.complete state.delivery.log}})

/-- Capture refusal and allocation refusal retain the original borrowed return.
The attempted independent copy, if any, remains the capture service's cleanup
responsibility. Only successful append clears the pending return. -/
private def admit (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (execution : Execution Producer Borrowed Effect Handoff) (value : Borrowed) :
    Notice Borrowed Stored Effect Handoff ×
      Configuration Producer Borrowed Stored Context Output Effect Handoff clients :=
  match capture value with
  | none => (.captureRefused, state)
  | some stored =>
      if capacity stored then
        match SharedOccurrenceLog.append state.delivery.log stored with
        | (.accepted, log) =>
            (.admitted (SharedOccurrenceLog.pastEnd state.delivery.log) stored,
              {state with
                execution := some {execution with
                  pending := none
                  accepted := execution.accepted + 1}
                delivery := {state.delivery with log := log}})
        | (.backpressure, _) => (.backpressure, state)
        | (.completed, _) => (.completed, state)
      else (.admissionRefused, state)

def hasConsumers (state : SharedOccurrenceLog.State Stored clients) : Bool :=
  (List.finRange clients).any (fun client => (state.positions client).isSome)

/-- One composition microstep. The log-capacity guard precedes every producer
transition and every attempted capture. A pending return excludes a producer
transition; unresolved effect and handoff requests are inert barriers. -/
def pump (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    Notice Borrowed Stored Effect Handoff ×
      Configuration Producer Borrowed Stored Context Output Effect Handoff clients :=
  match state.execution with
  | none => (.detached, state)
  | some execution =>
      if !compatible state.context then (.contextRefused, state)
      else if state.delivery.log.completed then (.completed, state)
      else
        match execution.mode with
        | .active =>
            if !hasConsumers state.delivery.log then (.noConsumers, state)
            else if state.delivery.log.rows.length < state.delivery.log.limit then
              match execution.pending with
              | some value => admit capture capacity state execution value
              | none => stage state execution (step execution.producer)
            else (.backpressure, state)
        | .effect request => (.effect request, state)
        | .handoff request => (.handoff request, state)
        | .interrupted => (.interrupted, state)

def run (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool) : Nat →
    Configuration Producer Borrowed Stored Context Output Effect Handoff clients →
    List (Notice Borrowed Stored Effect Handoff) ×
      Configuration Producer Borrowed Stored Context Output Effect Handoff clients
  | 0, state => ([], state)
  | ticks + 1, state =>
      let first := pump step capture capacity compatible state
      let rest := run step capture capacity compatible ticks first.2
      (first.1 :: rest.1, rest.2)

/-- Ordinary execution from a run boundary. The result is the configuration.
Notices are not accumulated, and the recursion does not test a recording flag.
Each microstep is the existing `pump`: its classification is the configuration
change, not a retained history, receipt or hash. -/
def ordinary
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool) : Nat →
    Configuration Producer Borrowed Stored Context Output Effect Handoff clients →
    Configuration Producer Borrowed Stored Context Output Effect Handoff clients
  | 0, state => state
  | ticks + 1, state =>
      ordinary step capture capacity compatible ticks
        (pump step capture capacity compatible state).2

/-- Streaming recorded execution. Each step pumps once, pushes that notice into
the existing prefix immediately, and tail-calls with the updated prefix and
the next configuration. A full prefix only increases `omitted`. This does not
construct the notice list of `run`, test a recording policy inside `ordinary`
or `pump`, or cancel a delivery cursor. -/
def recordOrdinary
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool) : Nat →
    Mettapedia.GSLT.Core.InferenceControl.Recording.Prefix
      (Notice Borrowed Stored Effect Handoff) →
    Configuration Producer Borrowed Stored Context Output Effect Handoff clients →
    Mettapedia.GSLT.Core.InferenceControl.Recording.Prefix
        (Notice Borrowed Stored Effect Handoff) ×
      Configuration Producer Borrowed Stored Context Output Effect Handoff clients
  | 0, record, state => (record, state)
  | ticks + 1, record, state =>
      let first := pump step capture capacity compatible state
      recordOrdinary step capture capacity compatible ticks
        (record.push (fun _ => first.1)) first.2

/-- Moving the complete execution does not discard buffered occurrences or
caller publications. The log retains its captured source context. -/
def detach (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    Option (Execution Producer Borrowed Effect Handoff) ×
      Configuration Producer Borrowed Stored Context Output Effect Handoff clients :=
  (state.execution, {state with execution := none})

inductive DeliveryReply (Stored : Type) where
  | observed (reply : SharedOccurrenceLog.Reply Stored)
  | contextRefused
  deriving DecidableEq

/-- Buffered delivery uses the existing preparation-before-acknowledgment
operation, after independently checking the captured source context. -/
def deliver [DecidableEq Stored] [DecidableEq Output] (compatible : Context → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (client : Fin clients) (output : Output) : DeliveryReply Stored ×
    Configuration Producer Borrowed Stored Context Output Effect Handoff clients :=
  if compatible state.context then
    let observed := SharedOccurrenceOwnership.advance state.delivery client output
    (.observed observed.1, {state with delivery := observed.2})
  else (.contextRefused, state)

/-- Drop one consumer's log retention through the existing cancellation.
The producer residual, captured context and caller publications are not part
of that consumer's roots, so they stay. -/
def retireConsumer
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (client : Fin clients) :
    Configuration Producer Borrowed Stored Context Output Effect Handoff clients :=
  { state with delivery := SharedOccurrenceOwnership.cancelConsumer state.delivery client }

/-- The paid producer account is the retained execution, including its accepted
count. Cancellation does not step the producer or replace the captured context,
and it does not release caller publications. -/
theorem retireConsumer_retains_paid_source
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (client : Fin clients) :
    (retireConsumer state client).execution = state.execution ∧
      (retireConsumer state client).context = state.context ∧
      (retireConsumer state client).delivery.published = state.delivery.published := by
  unfold retireConsumer SharedOccurrenceOwnership.cancelConsumer
  exact ⟨rfl, rfl, rfl⟩

/-- The retired consumer loses its unread suffix. Every other consumer keeps
the same ready answer and the same unread suffix. -/
theorem retireConsumer_releases_only_its_retention
    [DecidableEq Stored] [DecidableEq Output]
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (client : Fin clients) :
    SharedOccurrenceLog.unread (retireConsumer state client).delivery.log client = [] ∧
      SharedOccurrenceLog.peek (retireConsumer state client).delivery.log client =
        .cancelled ∧
      ∀ other, other ≠ client →
        SharedOccurrenceLog.peek (retireConsumer state client).delivery.log other =
          SharedOccurrenceLog.peek state.delivery.log other ∧
        SharedOccurrenceLog.unread (retireConsumer state client).delivery.log other =
          SharedOccurrenceLog.unread state.delivery.log other := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [retireConsumer, SharedOccurrenceOwnership.cancelConsumer] using
      SharedOccurrenceOwnership.unread_cancel_self state.delivery.log client
  · simp [retireConsumer, SharedOccurrenceOwnership.cancelConsumer, SharedOccurrenceLog.cancel,
      SharedOccurrenceLog.peek, SharedOccurrenceLog.setPosition_self]
  · intro other distinct
    refine ⟨?_, ?_⟩
    · simpa [retireConsumer, SharedOccurrenceOwnership.cancelConsumer] using
        SharedOccurrenceLog.cancel_preserves_other state.delivery.log client other distinct
    · simpa [retireConsumer, SharedOccurrenceOwnership.cancelConsumer] using
        SharedOccurrenceOwnership.unread_cancel_other state.delivery.log client other distinct

/-- The other consumer's ready-value roots stay live under the existing
collection law. Those roots are that consumer's unread answer graph. -/
theorem retireConsumer_retains_other_ready_graph
    {Cell : Type} [DecidableEq Stored] [DecidableEq Output]
    (heap : ResourceOwnership.Heap Stored Cell)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (client other : Fin clients)
    (valid : SharedOccurrenceLog.Valid state.delivery.log)
    (distinct : other ≠ client) (location : Stored)
    (live : ResourceOwnership.Live heap
        (OwnedLifecycle.answerRoots (Sum.inl other : Sum (Fin clients) Output)
          (SharedOccurrenceLog.unread state.delivery.log other)) location) :
    (ResourceOwnership.collect heap
        (SharedOccurrenceOwnership.roots
          (SharedOccurrenceOwnership.trimLog
            (SharedOccurrenceOwnership.cancelConsumer state.delivery client)))).lookup
        location = heap.lookup location :=
  SharedOccurrenceOwnership.cancel_trim_retains_other_unread_graph
    heap state.delivery client other valid distinct location live

/-- Caller publications are not released with the consumer. The existing
collection law keeps every address reachable from those roots. -/
theorem retireConsumer_retains_caller_publication
    {Cell : Type} [DecidableEq Stored] [DecidableEq Output]
    (heap : ResourceOwnership.Heap Stored Cell)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (client : Fin clients)
    (valid : SharedOccurrenceLog.Valid state.delivery.log) (location : Stored)
    (live : ResourceOwnership.Live heap
        (SharedOccurrenceOwnership.publishedRoots (clients := clients)
          state.delivery.published) location) :
    (ResourceOwnership.collect heap
        (SharedOccurrenceOwnership.roots
          (SharedOccurrenceOwnership.trimLog
            (SharedOccurrenceOwnership.cancelConsumer state.delivery client)))).lookup
        location = heap.lookup location :=
  SharedOccurrenceOwnership.cancel_trim_retains_published_graph
    heap state.delivery client valid location live

/-- Delivery to a remaining consumer is the existing advance, moved across
this cancellation. The producer execution is not a field of that advance. -/
theorem retireConsumer_resumes_other
    [DecidableEq Stored] [DecidableEq Output]
    (compatible : Context → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (retired other : Fin clients) (output : Output)
    (distinct : other ≠ retired) (ready : compatible state.context = true) :
    deliver compatible (retireConsumer state retired) other output =
      (let resumed := deliver compatible state other output
       (resumed.1, retireConsumer resumed.2 retired)) := by
  have advanceOther :
      SharedOccurrenceOwnership.advance
          (SharedOccurrenceOwnership.cancelConsumer state.delivery retired) other output =
        (let advanced := SharedOccurrenceOwnership.advance state.delivery other output
         (advanced.1, SharedOccurrenceOwnership.cancelConsumer advanced.2 retired)) := by
    unfold SharedOccurrenceOwnership.advance SharedOccurrenceOwnership.prepare
      SharedOccurrenceOwnership.acknowledge SharedOccurrenceOwnership.cancelConsumer
    rw [SharedOccurrenceLog.cancel_preserves_other state.delivery.log retired other distinct]
    rw [SharedOccurrenceLog.cancel_pull_other state.delivery.log retired other distinct.symm]
  unfold retireConsumer deliver
  simp only [ready, if_true, advanceOther]

theorem retireConsumer_resume_does_not_step_producer
    [DecidableEq Stored] [DecidableEq Output]
    (compatible : Context → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (retired other : Fin clients) (output : Output) :
    (deliver compatible (retireConsumer state retired) other output).2.execution =
      state.execution := by
  unfold deliver retireConsumer
  split <;> rfl

def returned (notice : Notice Borrowed Stored Effect Handoff) : List Borrowed :=
  match notice with
  | .returned value => [value]
  | _ => []

def admitted (notice : Notice Borrowed Stored Effect Handoff) : List Stored :=
  match notice with
  | .admitted _ value => [value]
  | _ => []

/-- The transition debit for `driverStep`: emissions and administrative driver
progress each cost one; admission, refusal and completion inspection cost zero.
This projection does not assign a cost to arbitrary producer callbacks. -/
def driverTicks (notice : Notice Borrowed Stored Effect Handoff) : Nat :=
  match notice with
  | .progress | .returned _ => 1
  | _ => 0

theorem driverTicks_le_one (notice : Notice Borrowed Stored Effect Handoff) :
    driverTicks notice ≤ 1 := by
  cases notice <;> simp [driverTicks]

def acceptedCount
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) : Nat :=
  (state.execution.map (fun execution => execution.accepted)).getD 0

theorem run_split
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool) (first second : Nat)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    run step capture capacity compatible (first + second) state =
      (let earlier := run step capture capacity compatible first state
       let later := run step capture capacity compatible second earlier.2
       (earlier.1 ++ later.1, later.2)) := by
  induction first generalizing state with
  | zero => simp [run]
  | succ first ih => simp [Nat.succ_add, run, ih]

theorem full_preserves_complete_residual
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (execution : Execution Producer Borrowed Effect Handoff)
    (attached : state.execution = some execution) (allowed : compatible state.context = true)
    (openLog : state.delivery.log.completed = false)
    (active : execution.mode = .active) (demanded : hasConsumers state.delivery.log = true)
    (full : state.delivery.log.limit ≤ state.delivery.log.rows.length) :
    pump step capture capacity compatible state = (.backpressure, state) := by
  simp [pump, attached, allowed, openLog, active, demanded, Nat.not_lt.mpr full]

theorem no_demand_preserves_complete_residual
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (execution : Execution Producer Borrowed Effect Handoff)
    (attached : state.execution = some execution) (allowed : compatible state.context = true)
    (openLog : state.delivery.log.completed = false)
    (active : execution.mode = .active) (undemanded : hasConsumers state.delivery.log = false) :
    pump step capture capacity compatible state = (.noConsumers, state) := by
  simp [pump, attached, allowed, openLog, active, undemanded]

theorem context_refusal_preserves_complete_residual
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (execution : Execution Producer Borrowed Effect Handoff)
    (attached : state.execution = some execution) (refused : compatible state.context = false) :
    pump step capture capacity compatible state = (.contextRefused, state) := by
  simp [pump, attached, refused]

theorem capture_refusal_preserves_complete_residual
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (execution : Execution Producer Borrowed Effect Handoff) (value : Borrowed)
    (attached : state.execution = some execution) (allowed : compatible state.context = true)
    (openLog : state.delivery.log.completed = false)
    (room : state.delivery.log.rows.length < state.delivery.log.limit)
    (demanded : hasConsumers state.delivery.log = true)
    (active : execution.mode = .active) (staged : execution.pending = some value)
    (refused : capture value = none) :
    pump step capture capacity compatible state = (.captureRefused, state) := by
  simp [pump, attached, allowed, openLog, room, demanded, active, staged, admit, refused]

theorem admission_refusal_preserves_complete_residual
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (execution : Execution Producer Borrowed Effect Handoff) (value : Borrowed) (stored : Stored)
    (attached : state.execution = some execution) (allowed : compatible state.context = true)
    (openLog : state.delivery.log.completed = false)
    (room : state.delivery.log.rows.length < state.delivery.log.limit)
    (demanded : hasConsumers state.delivery.log = true)
    (active : execution.mode = .active) (staged : execution.pending = some value)
    (captured : capture value = some stored) (refused : capacity stored = false) :
    pump step capture capacity compatible state = (.admissionRefused, state) := by
  simp [pump, attached, allowed, openLog, room, demanded, active, staged, admit, captured, refused]

theorem pending_excludes_producer_step
    (left right : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (execution : Execution Producer Borrowed Effect Handoff) (value : Borrowed)
    (attached : state.execution = some execution) (staged : execution.pending = some value) :
    pump left capture capacity compatible state = pump right capture capacity compatible state := by
  simp only [pump, attached]
  split <;> try rfl
  split <;> try rfl
  cases execution.mode <;> simp [staged]

theorem buffered_context_refusal_preserves_complete_residual [DecidableEq Stored] [DecidableEq Output]
    (compatible : Context → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (client : Fin clients) (output : Output) (refused : compatible state.context = false) :
    deliver compatible state client output = (.contextRefused, state) := by
  simp [deliver, refused]

theorem delivery_preserves_complete_execution [DecidableEq Stored] [DecidableEq Output]
    (compatible : Context → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (client : Fin clients) (output : Output) :
    (deliver compatible state client output).2.execution = state.execution := by
  unfold deliver
  split <;> rfl

theorem delivery_preserves_other_consumer [DecidableEq Stored] [DecidableEq Output]
    (compatible : Context → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (client other : Fin clients) (output : Output) (distinct : other ≠ client) :
    SharedOccurrenceLog.peek (deliver compatible state client output).2.delivery.log other =
      SharedOccurrenceLog.peek state.delivery.log other := by
  unfold deliver
  split
  · exact SharedOccurrenceLog.pull_preserves_other state.delivery.log client other distinct
  · rfl

/-- Distinct consumers preserve both replies, every caller root, the captured
context and the complete producer residual when their deliveries are swapped.
The producer is not stepped. Native publication still needs synchronization. -/
theorem deliver_commute [DecidableEq Stored] [DecidableEq Output]
    (compatible : Context → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (left right : Fin clients) (leftOutput rightOutput : Output) (distinct : left ≠ right) :
    (let first := deliver compatible state left leftOutput
     let second := deliver compatible first.2 right rightOutput
     (first.1, second.1, second.2)) =
      (let second := deliver compatible state right rightOutput
       let first := deliver compatible second.2 left leftOutput
       (first.1, second.1, first.2)) := by
  by_cases allowed : compatible state.context = true
  · simp only [deliver, allowed, ↓reduceIte]
    exact congrArg
      (fun result : SharedOccurrenceLog.Reply Stored × SharedOccurrenceLog.Reply Stored ×
          SharedOccurrenceOwnership.Configuration Stored Output clients =>
        (DeliveryReply.observed result.1, DeliveryReply.observed result.2.1,
          {state with delivery := result.2.2}))
      (SharedOccurrenceOwnership.advance_commute state.delivery left right
        leftOutput rightOutput distinct)
  · simp [deliver, allowed]

theorem detach_preserves_delivery
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    (detach state).1 = state.execution ∧ (detach state).2.delivery = state.delivery ∧
      (detach state).2.context = state.context := ⟨rfl, rfl, rfl⟩

theorem detached_excludes_producer_step
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    pump step capture capacity compatible (detach state).2 = (.detached, (detach state).2) := rfl

private theorem stage_rows
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (execution : Execution Producer Borrowed Effect Handoff)
    (outcome : ProducerOutcome Producer Borrowed Effect Handoff) :
    (stage state execution outcome).2.delivery.log.rows =
      state.delivery.log.rows ++ admitted (stage state execution outcome).1 := by
  cases outcome <;> simp [stage, admitted, SharedOccurrenceLog.complete]

private theorem admit_rows (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (execution : Execution Producer Borrowed Effect Handoff) (value : Borrowed) :
    (admit capture capacity state execution value).2.delivery.log.rows =
      state.delivery.log.rows ++ admitted (admit capture capacity state execution value).1 := by
  unfold admit
  cases captured : capture value with
  | none => simp [admitted]
  | some stored =>
      simp only
      split
      · by_cases closed : state.delivery.log.completed = true
        · simp [SharedOccurrenceLog.append, closed, admitted]
        · by_cases room : state.delivery.log.rows.length < state.delivery.log.limit <;>
            simp [SharedOccurrenceLog.append, closed, room, admitted]
      · simp [admitted]

/-- Every stored row is introduced by one successful actual log append. -/
theorem pump_rows
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    (pump step capture capacity compatible state).2.delivery.log.rows =
      state.delivery.log.rows ++ admitted (pump step capture capacity compatible state).1 := by
  unfold pump
  cases state.execution with
  | none => simp [admitted]
  | some execution =>
      simp only
      split
      · simp [admitted]
      · split
        · simp [admitted]
        · cases execution.mode with
          | active =>
              simp only
              split
              · simp [admitted]
              · split
                · cases execution.pending with
                  | none => exact stage_rows state execution (step execution.producer)
                  | some value => exact admit_rows capture capacity state execution value
                · simp [admitted]
          | effect request => simp [admitted]
          | handoff request => simp [admitted]
          | interrupted => simp [admitted]

theorem run_rows
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool) (ticks : Nat)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    (run step capture capacity compatible ticks state).2.delivery.log.rows =
      state.delivery.log.rows ++
        (run step capture capacity compatible ticks state).1.flatMap admitted := by
  induction ticks generalizing state with
  | zero => simp [run]
  | succ ticks ih =>
      simp only [run]
      rw [ih, pump_rows]
      simp [List.append_assoc]

private theorem stage_conservation (borrowedView : Borrowed → Observation)
    (storedView : Stored → Observation)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (execution : Execution Producer Borrowed Effect Handoff)
    (outcome : ProducerOutcome Producer Borrowed Effect Handoff)
    (attached : state.execution = some execution) (empty : execution.pending = none) :
    (pending state).toList.map borrowedView ++
        (returned (stage state execution outcome).1).map borrowedView =
      (admitted (stage state execution outcome).1).map storedView ++
        (pending (stage state execution outcome).2).toList.map borrowedView := by
  cases outcome <;> simp [stage, returned, admitted, pending, attached, empty]

private theorem admit_conservation (borrowedView : Borrowed → Observation)
    (storedView : Stored → Observation)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (captureSound : ∀ value stored, capture value = some stored →
      storedView stored = borrowedView value)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (execution : Execution Producer Borrowed Effect Handoff) (value : Borrowed)
    (attached : state.execution = some execution) (staged : execution.pending = some value) :
    (pending state).toList.map borrowedView ++
        (returned (admit capture capacity state execution value).1).map borrowedView =
      (admitted (admit capture capacity state execution value).1).map storedView ++
        (pending (admit capture capacity state execution value).2).toList.map borrowedView := by
  unfold admit
  cases captured : capture value with
  | none => simp [returned, admitted, pending, attached, staged]
  | some stored =>
      have same := captureSound value stored captured
      simp only
      split
      · by_cases closed : state.delivery.log.completed = true
        · simp [SharedOccurrenceLog.append, closed, returned, admitted]
        · by_cases room : state.delivery.log.rows.length < state.delivery.log.limit <;>
            simp [SharedOccurrenceLog.append, closed, room, returned, admitted, pending,
              attached, staged, same]
      · simp [returned, admitted, pending, attached, staged]

/-- A primitive capture observation law licenses a real conservation equation:
new producer returns are either admitted, in order, or retained as pending. -/
theorem pump_conservation (borrowedView : Borrowed → Observation)
    (storedView : Stored → Observation)
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool)
    (captureSound : ∀ value stored, capture value = some stored →
      storedView stored = borrowedView value)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    (pending state).toList.map borrowedView ++
        (returned (pump step capture capacity compatible state).1).map borrowedView =
      (admitted (pump step capture capacity compatible state).1).map storedView ++
        (pending (pump step capture capacity compatible state).2).toList.map borrowedView := by
  unfold pump
  cases attached : state.execution with
  | none => simp [returned, admitted]
  | some execution =>
      simp only
      split
      · simp [returned, admitted]
      · split
        · simp [returned, admitted]
        · cases execution.mode with
          | active =>
              simp only
              split
              · simp [returned, admitted]
              · split
                · cases staged : execution.pending with
                  | none =>
                      exact stage_conservation borrowedView storedView state execution
                        (step execution.producer) attached staged
                  | some value =>
                      exact admit_conservation borrowedView storedView capture capacity
                        captureSound state execution value attached staged
                · simp [returned, admitted]
          | effect request => simp [returned, admitted]
          | handoff request => simp [returned, admitted]
          | interrupted => simp [returned, admitted]

/-- Complete ordered conservation across any finite sequence of retries,
administrative steps, pauses and barriers. Equal observations keep multiplicity. -/
theorem run_conservation (borrowedView : Borrowed → Observation)
    (storedView : Stored → Observation)
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool)
    (captureSound : ∀ value stored, capture value = some stored →
      storedView stored = borrowedView value)
    (ticks : Nat)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    (pending state).toList.map borrowedView ++
        ((run step capture capacity compatible ticks state).1.flatMap returned).map borrowedView =
      ((run step capture capacity compatible ticks state).1.flatMap admitted).map storedView ++
        (pending (run step capture capacity compatible ticks state).2).toList.map borrowedView := by
  induction ticks generalizing state with
  | zero => simp [run]
  | succ ticks ih =>
      simp only [run, List.flatMap_cons, List.map_append]
      rw [← List.append_assoc, pump_conservation borrowedView storedView step capture capacity
        compatible captureSound state, List.append_assoc, ih]
      simp [List.append_assoc]

def ProducerOutcome.next : ProducerOutcome Producer Borrowed Effect Handoff → Producer
  | .progress next | .returned _ next | .yielded next | .effect _ next
      | .handoff _ next | .interrupted next | .completed next => next

def ProducerOutcome.returns : ProducerOutcome Producer Borrowed Effect Handoff → List Borrowed
  | .returned value _ => [value]
  | _ => []

/-- The source trace follows actual producer transitions, independently of
capture, row storage, cursor delivery or scheduler microstep accounting. -/
inductive ProducerPath (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff) :
    Producer → List Borrowed → Producer → Prop where
  | refl (state : Producer) : ProducerPath step state [] state
  | next {source : Producer} {outcome : ProducerOutcome Producer Borrowed Effect Handoff}
      {rest : List Borrowed} {target : Producer}
      (transition : step source = outcome)
      (tail : ProducerPath step outcome.next rest target) :
      ProducerPath step source (outcome.returns ++ rest) target

theorem ProducerPath.append
    {step : Producer → ProducerOutcome Producer Borrowed Effect Handoff}
    {source middle target : Producer} {earlier later : List Borrowed}
    (first : ProducerPath step source earlier middle)
    (second : ProducerPath step middle later target) :
    ProducerPath step source (earlier ++ later) target := by
  induction first with
  | refl => simpa using second
  | next transition tail ih =>
      simpa [List.append_assoc] using ProducerPath.next transition (ih second)

private theorem stage_producer_path
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (execution : Execution Producer Borrowed Effect Handoff) :
    ∃ next, (stage state execution (step execution.producer)).2.execution = some next ∧
      ProducerPath step execution.producer
        (returned (stage state execution (step execution.producer)).1) next.producer := by
  cases transition : step execution.producer <;>
    refine ⟨_, rfl, ?_⟩ <;>
    simpa [stage, returned, ProducerOutcome.returns, ProducerOutcome.next] using
      ProducerPath.next transition (ProducerPath.refl _)

private theorem admit_retains_producer
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (execution : Execution Producer Borrowed Effect Handoff) (value : Borrowed)
    (attached : state.execution = some execution) :
    ∃ next, (admit capture capacity state execution value).2.execution = some next ∧
      next.producer = execution.producer ∧
      returned (admit capture capacity state execution value).1 = [] ∧
      driverTicks (admit capture capacity state execution value).1 = 0 := by
  unfold admit
  cases capture value with
  | none => exact ⟨execution, attached, rfl, rfl, rfl⟩
  | some stored =>
      simp only
      split
      · by_cases closed : state.delivery.log.completed = true
        · simp only [SharedOccurrenceLog.append, closed, if_pos]
          exact ⟨execution, attached, rfl, rfl, rfl⟩
        · by_cases room : state.delivery.log.rows.length < state.delivery.log.limit
          · simp only [SharedOccurrenceLog.append, closed, room, if_pos]
            exact ⟨_, rfl, rfl, rfl, rfl⟩
          · simp only [SharedOccurrenceLog.append, closed, room]
            exact ⟨execution, attached, rfl, rfl, rfl⟩
      · exact ⟨execution, attached, rfl, rfl, rfl⟩

private theorem admit_producer_path
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (execution : Execution Producer Borrowed Effect Handoff) (value : Borrowed)
    (attached : state.execution = some execution) :
    ∃ next, (admit capture capacity state execution value).2.execution = some next ∧
      ProducerPath step execution.producer
        (returned (admit capture capacity state execution value).1) next.producer := by
  obtain ⟨next, nextAttached, producer, events, _⟩ :=
    admit_retains_producer capture capacity state execution value attached
  exact ⟨next, nextAttached, by rw [producer, events]; exact ProducerPath.refl _⟩

theorem pump_producer_path
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (execution : Execution Producer Borrowed Effect Handoff)
    (attached : state.execution = some execution) :
    ∃ next, (pump step capture capacity compatible state).2.execution = some next ∧
      ProducerPath step execution.producer
        (returned (pump step capture capacity compatible state).1) next.producer := by
  unfold pump
  rw [attached]
  simp only
  split
  · exact ⟨execution, attached, ProducerPath.refl _⟩
  · split
    · exact ⟨execution, attached, ProducerPath.refl _⟩
    · cases execution.mode with
      | active =>
          simp only
          split
          · exact ⟨execution, attached, ProducerPath.refl _⟩
          · split
            · cases execution.pending with
              | none => exact stage_producer_path step state execution
              | some value => exact admit_producer_path step capture capacity state execution value attached
            · exact ⟨execution, attached, ProducerPath.refl _⟩
      | effect request => exact ⟨execution, attached, ProducerPath.refl _⟩
      | handoff request => exact ⟨execution, attached, ProducerPath.refl _⟩
      | interrupted => exact ⟨execution, attached, ProducerPath.refl _⟩

/-- Every staged return comes from an actual producer transition, and the
entire final producer residual is the endpoint of that ordered source path. -/
theorem run_producer_path
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool) (ticks : Nat)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (execution : Execution Producer Borrowed Effect Handoff)
    (attached : state.execution = some execution) :
    ∃ next, (run step capture capacity compatible ticks state).2.execution = some next ∧
      ProducerPath step execution.producer
        ((run step capture capacity compatible ticks state).1.flatMap returned) next.producer := by
  induction ticks generalizing state execution with
  | zero => exact ⟨execution, attached, ProducerPath.refl _⟩
  | succ ticks ih =>
      obtain ⟨middle, middleAttached, first⟩ :=
        pump_producer_path step capture capacity compatible state execution attached
      obtain ⟨next, nextAttached, rest⟩ := ih _ middle middleAttached
      exact ⟨next, nextAttached, by simpa only [run, List.flatMap_cons] using first.append rest⟩

/-- Adapts actual explicit-frame transitions to the selected event stream.
This observer treats events as return occurrences; it grants no effectful
sharing license for a native evaluator. The final value remains in the residual. -/
def driverStep {Value Event : Type} (state : OwnedPullDriver.State Value Event) :
    ProducerOutcome (OwnedPullDriver.State Value Event) Event Empty Empty :=
  match OwnedPullDriver.transition state with
  | none => .completed state
  | some ([], next) => .progress next
  | some (event :: _, next) => .returned event next

theorem driver_step_path {Value Event : Type} (state : OwnedPullDriver.State Value Event) :
    ∃ count, OwnedPullDriver.Path state (driverStep state).returns count (driverStep state).next := by
  rcases state with ⟨work, frames⟩
  cases work with
  | done value =>
      cases frames with
      | nil => exact ⟨0, OwnedPullDriver.Path.refl⟩
      | cons resume rest =>
          exact ⟨1, by simpa [driverStep, OwnedPullDriver.transition,
            ProducerOutcome.returns, ProducerOutcome.next] using
              OwnedPullDriver.Path.next (OwnedPullDriver.Step.resume
                (value := value) (resume := resume) (rest := rest)) OwnedPullDriver.Path.refl⟩
  | emit event next =>
      exact ⟨1, by simpa [driverStep, OwnedPullDriver.transition,
        ProducerOutcome.returns, ProducerOutcome.next] using
          OwnedPullDriver.Path.next (OwnedPullDriver.Step.emit
            (event := event) (next := next) (frames := frames)) OwnedPullDriver.Path.refl⟩
  | child work resume =>
      exact ⟨1, by simpa [driverStep, OwnedPullDriver.transition,
        ProducerOutcome.returns, ProducerOutcome.next] using
          OwnedPullDriver.Path.next (OwnedPullDriver.Step.child
            (work := work) (resume := resume) (frames := frames)) OwnedPullDriver.Path.refl⟩

/-- The producer trace of the composition is an actual path of the existing
owned driver, retaining its complete continuation stack and final work. -/
theorem driver_producer_path {Value Event : Type}
    {source target : OwnedPullDriver.State Value Event} {events : List Event}
    (path : ProducerPath driverStep source events target) :
    ∃ count, OwnedPullDriver.Path source events count target := by
  induction path with
  | refl => exact ⟨0, OwnedPullDriver.Path.refl⟩
  | @next source outcome rest target transition tail ih =>
      obtain ⟨firstCount, first⟩ := driver_step_path source
      rw [transition] at first
      obtain ⟨restCount, rest⟩ := ih
      exact ⟨firstCount + restCount, first.append rest⟩

theorem completed_driver_preserves_recursive_meaning {Value Event : Type}
    {work : OwnedPullDriver.Program Value Event} {events : List Event} {value : Value}
    (path : ProducerPath driverStep ⟨work, []⟩ events ⟨.done value, []⟩) :
    OwnedPullDriver.Runs work events value := by
  obtain ⟨count, actual⟩ := driver_producer_path path
  exact OwnedPullDriver.runs_of_path actual

private theorem stage_driver_path {Value Event : Type}
    (state : Configuration (OwnedPullDriver.State Value Event) Event Stored Context Output
      Empty Empty clients)
    (execution : Execution (OwnedPullDriver.State Value Event) Event Empty Empty) :
    ∃ next, (stage state execution (driverStep execution.producer)).2.execution = some next ∧
      OwnedPullDriver.Path execution.producer
        (returned (stage state execution (driverStep execution.producer)).1)
        (driverTicks (stage state execution (driverStep execution.producer)).1) next.producer := by
  rcases execution with ⟨⟨work, frames⟩, pending, accepted, mode⟩
  cases work with
  | done value =>
      cases frames with
      | nil => exact ⟨_, rfl, OwnedPullDriver.Path.refl⟩
      | cons resume rest =>
          refine ⟨_, rfl, ?_⟩
          simpa [stage, driverStep, OwnedPullDriver.transition, returned, driverTicks] using
            OwnedPullDriver.Path.next (OwnedPullDriver.Step.resume
              (value := value) (resume := resume) (rest := rest)) OwnedPullDriver.Path.refl
  | emit event next =>
      refine ⟨_, rfl, ?_⟩
      simpa [stage, driverStep, OwnedPullDriver.transition, returned, driverTicks] using
        OwnedPullDriver.Path.next (OwnedPullDriver.Step.emit
          (event := event) (next := next) (frames := frames)) OwnedPullDriver.Path.refl
  | child work resume =>
      refine ⟨_, rfl, ?_⟩
      simpa [stage, driverStep, OwnedPullDriver.transition, returned, driverTicks] using
        OwnedPullDriver.Path.next (OwnedPullDriver.Step.child
          (work := work) (resume := resume) (frames := frames)) OwnedPullDriver.Path.refl

/-- A composition step either performs exactly one owned-driver transition or
retains the entire producer. Successful admission is also a zero-driver step. -/
theorem pump_driver_path {Value Event : Type}
    (capture : Event → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool)
    (state : Configuration (OwnedPullDriver.State Value Event) Event Stored Context Output
      Empty Empty clients)
    (execution : Execution (OwnedPullDriver.State Value Event) Event Empty Empty)
    (attached : state.execution = some execution) :
    ∃ next, (pump driverStep capture capacity compatible state).2.execution = some next ∧
      OwnedPullDriver.Path execution.producer
        (returned (pump driverStep capture capacity compatible state).1)
        (driverTicks (pump driverStep capture capacity compatible state).1) next.producer := by
  unfold pump
  rw [attached]
  simp only
  split
  · exact ⟨execution, attached, OwnedPullDriver.Path.refl⟩
  · split
    · exact ⟨execution, attached, OwnedPullDriver.Path.refl⟩
    · cases execution.mode with
      | active =>
          simp only
          split
          · exact ⟨execution, attached, OwnedPullDriver.Path.refl⟩
          · split
            · cases execution.pending with
              | none => exact stage_driver_path state execution
              | some value =>
                  obtain ⟨next, nextAttached, producer, events, ticks⟩ :=
                    admit_retains_producer capture capacity state execution value attached
                  exact ⟨next, nextAttached, by
                    rw [producer, events, ticks]
                    exact OwnedPullDriver.Path.refl⟩
            · exact ⟨execution, attached, OwnedPullDriver.Path.refl⟩
      | effect request => exact ⟨execution, attached, OwnedPullDriver.Path.refl⟩
      | handoff request => exact ⟨execution, attached, OwnedPullDriver.Path.refl⟩
      | interrupted => exact ⟨execution, attached, OwnedPullDriver.Path.refl⟩

/-- The recorded debit counts the actual producer path, retaining duplicate
events and all caller frames across admission and retry boundaries. -/
theorem run_driver_path {Value Event : Type}
    (capture : Event → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool) (ticks : Nat)
    (state : Configuration (OwnedPullDriver.State Value Event) Event Stored Context Output
      Empty Empty clients)
    (execution : Execution (OwnedPullDriver.State Value Event) Event Empty Empty)
    (attached : state.execution = some execution) :
    ∃ next, (run driverStep capture capacity compatible ticks state).2.execution = some next ∧
      OwnedPullDriver.Path execution.producer
        ((run driverStep capture capacity compatible ticks state).1.flatMap returned)
        ((run driverStep capture capacity compatible ticks state).1.map driverTicks).sum
        next.producer := by
  induction ticks generalizing state execution with
  | zero => exact ⟨execution, attached, OwnedPullDriver.Path.refl⟩
  | succ ticks ih =>
      obtain ⟨middle, middleAttached, first⟩ :=
        pump_driver_path capture capacity compatible state execution attached
      obtain ⟨next, nextAttached, rest⟩ := ih _ middle middleAttached
      exact ⟨next, nextAttached, by
        simpa only [run, List.flatMap_cons, List.map_cons, List.sum_cons] using first.append rest⟩

/-- The independently defined unrecorded runner reaches exactly the retained
producer with this debit. Composition microsteps and accepted-return counts
are separate metrics; this law does not bound capture or scheduler work. -/
theorem run_driver_debit {Value Event : Type}
    (capture : Event → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool) (ticks : Nat)
    (state : Configuration (OwnedPullDriver.State Value Event) Event Stored Context Output
      Empty Empty clients)
    (execution : Execution (OwnedPullDriver.State Value Event) Event Empty Empty)
    (attached : state.execution = some execution) :
    ∃ next, (run driverStep capture capacity compatible ticks state).2.execution = some next ∧
      let debit := ((run driverStep capture capacity compatible ticks state).1.map driverTicks).sum
      MachineCore.runSlice (OwnedPullDriver.machineCore Value Event) debit execution.producer =
        (next.producer, debit) := by
  obtain ⟨next, nextAttached, path⟩ :=
    run_driver_path capture capacity compatible ticks state execution attached
  exact ⟨next, nextAttached, path.runSlice⟩

theorem run_driver_ticks_le {Value Event : Type}
    (capture : Event → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool) (ticks : Nat)
    (state : Configuration (OwnedPullDriver.State Value Event) Event Stored Context Output
      Empty Empty clients) :
    ((run driverStep capture capacity compatible ticks state).1.map driverTicks).sum ≤ ticks := by
  induction ticks generalizing state with
  | zero => simp [run]
  | succ ticks ih =>
      simp only [run, List.map_cons, List.sum_cons]
      have first := driverTicks_le_one (pump driverStep capture capacity compatible state).1
      have rest := ih (pump driverStep capture capacity compatible state).2
      omega

theorem run_driver_ticks_split {Value Event : Type}
    (capture : Event → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool) (first second : Nat)
    (state : Configuration (OwnedPullDriver.State Value Event) Event Stored Context Output
      Empty Empty clients) :
    ((run driverStep capture capacity compatible (first + second) state).1.map driverTicks).sum =
      ((run driverStep capture capacity compatible first state).1.map driverTicks).sum +
        ((run driverStep capture capacity compatible second
          (run driverStep capture capacity compatible first state).2).1.map driverTicks).sum := by
  rw [run_split]
  simp only [List.map_append, List.sum_append]

private theorem stage_metadata
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (execution : Execution Producer Borrowed Effect Handoff)
    (outcome : ProducerOutcome Producer Borrowed Effect Handoff) :
    (stage state execution outcome).2.context = state.context ∧
      (stage state execution outcome).2.delivery.log.base = state.delivery.log.base ∧
      (stage state execution outcome).2.delivery.log.positions = state.delivery.log.positions ∧
      (stage state execution outcome).2.delivery.published = state.delivery.published := by
  cases outcome <;> exact ⟨rfl, rfl, rfl, rfl⟩

private theorem admit_metadata (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (execution : Execution Producer Borrowed Effect Handoff) (value : Borrowed) :
    (admit capture capacity state execution value).2.context = state.context ∧
      (admit capture capacity state execution value).2.delivery.log.base = state.delivery.log.base ∧
      (admit capture capacity state execution value).2.delivery.log.positions = state.delivery.log.positions ∧
      (admit capture capacity state execution value).2.delivery.published = state.delivery.published := by
  unfold admit
  cases capture value with
  | none => exact ⟨rfl, rfl, rfl, rfl⟩
  | some stored =>
      simp only
      split
      · by_cases closed : state.delivery.log.completed = true
        · simp only [SharedOccurrenceLog.append, closed, if_pos]
          simp
        · by_cases room : state.delivery.log.rows.length < state.delivery.log.limit <;>
            simp [SharedOccurrenceLog.append, closed, room]
      · exact ⟨rfl, rfl, rfl, rfl⟩

theorem pump_preserves_context_cursors_publications
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    (pump step capture capacity compatible state).2.context = state.context ∧
      (pump step capture capacity compatible state).2.delivery.log.base = state.delivery.log.base ∧
      (pump step capture capacity compatible state).2.delivery.log.positions = state.delivery.log.positions ∧
      (pump step capture capacity compatible state).2.delivery.published = state.delivery.published := by
  unfold pump
  cases state.execution with
  | none => exact ⟨rfl, rfl, rfl, rfl⟩
  | some execution =>
      simp only
      split
      · exact ⟨rfl, rfl, rfl, rfl⟩
      · split
        · exact ⟨rfl, rfl, rfl, rfl⟩
        · cases execution.mode with
          | active =>
              simp only
              split
              · exact ⟨rfl, rfl, rfl, rfl⟩
              · split
                · cases execution.pending with
                  | none => exact stage_metadata state execution (step execution.producer)
                  | some value => exact admit_metadata capture capacity state execution value
                · exact ⟨rfl, rfl, rfl, rfl⟩
          | effect request => exact ⟨rfl, rfl, rfl, rfl⟩
          | handoff request => exact ⟨rfl, rfl, rfl, rfl⟩
          | interrupted => exact ⟨rfl, rfl, rfl, rfl⟩

theorem run_preserves_context_cursors_publications
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool) (ticks : Nat)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    (run step capture capacity compatible ticks state).2.context = state.context ∧
      (run step capture capacity compatible ticks state).2.delivery.log.base = state.delivery.log.base ∧
      (run step capture capacity compatible ticks state).2.delivery.log.positions = state.delivery.log.positions ∧
      (run step capture capacity compatible ticks state).2.delivery.published = state.delivery.published := by
  induction ticks generalizing state with
  | zero => exact ⟨rfl, rfl, rfl, rfl⟩
  | succ ticks ih =>
      have rest := ih (pump step capture capacity compatible state).2
      have first := pump_preserves_context_cursors_publications step capture capacity compatible state
      exact ⟨rest.1.trans first.1, rest.2.1.trans first.2.1,
        rest.2.2.1.trans first.2.2.1, rest.2.2.2.trans first.2.2.2⟩

/-- Producer progress retains every already buffered occurrence. An empty
buffer is different: appending a row may wake a waiting consumer. -/
theorem pump_preserves_buffered_answer
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (client : Fin clients) (position : Nat) (value : Stored)
    (answer : SharedOccurrenceLog.peek state.delivery.log client = .answer position value) :
    SharedOccurrenceLog.peek (pump step capture capacity compatible state).2.delivery.log client =
      .answer position value := by
  have metadata := pump_preserves_context_cursors_publications step capture capacity compatible state
  exact SharedOccurrenceLog.extension_preserves_prior_answer _ _ client _ position value
    metadata.2.1 (congrFun metadata.2.2.1 client)
    (pump_rows step capture capacity compatible state) answer

private def bufferedUpdate [DecidableEq Stored] [DecidableEq Output]
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (client : Fin clients) (output : Output) (position : Nat) (value : Stored) :
    Configuration Producer Borrowed Stored Context Output Effect Handoff clients :=
  {state with delivery :=
    ⟨SharedOccurrenceLog.setPosition state.delivery.log client (some (position + 1)),
      OwnedLifecycle.publish state.delivery.published output [value]⟩}

private theorem active_consumer_has_demand (log : SharedOccurrenceLog.State Stored clients)
    (client : Fin clients) (position : Nat) (active : log.positions client = some position) :
    hasConsumers log = true := by
  apply List.any_eq_true.mpr
  exact ⟨client, List.mem_finRange client, by simp [active]⟩

private theorem drop_append_suffix {α : Type} (count : Nat) (prefixRows suffix : List α)
    (bound : count ≤ prefixRows.length) :
    (prefixRows ++ suffix).drop count = prefixRows.drop count ++ suffix := by
  induction prefixRows generalizing count with
  | nil =>
      cases bound
      rfl
  | cons head tail ih =>
      cases count with
      | zero => rfl
      | succ count =>
          exact ih count (Nat.le_of_succ_le_succ bound)

private theorem drop_length {α : Type} (rows : List α) : rows.drop rows.length = [] := by
  induction rows with
  | nil => rfl
  | cons _ tail ih => exact ih

/-- `ordinary` keeps the configuration reached by `run`. The notice list is not
an input of the next ordinary step, and this equality does not cancel a cursor. -/
theorem ordinary_agrees_with_recorded_state
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool) (ticks : Nat)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    ordinary step capture capacity compatible ticks state =
      (run step capture capacity compatible ticks state).2 := by
  induction ticks generalizing state with
  | zero => rfl
  | succ ticks ih => simp only [ordinary, run, ih]

section NoticePrefix

open Mettapedia.GSLT.Core.InferenceControl.Recording

/-- The streaming runner equals `Prefix.append` of the notice list of `run`,
paired with that run's configuration. Bounds, composition and the ordinary
switch follow from this equality and the existing prefix laws. -/
theorem recordOrdinary_eq_append_run
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool) (ticks : Nat)
    (record : Prefix (Notice Borrowed Stored Effect Handoff))
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    recordOrdinary step capture capacity compatible ticks record state =
      (record.append (run step capture capacity compatible ticks state).1,
        (run step capture capacity compatible ticks state).2) := by
  induction ticks generalizing record state with
  | zero => rfl
  | succ ticks ih =>
      simp only [recordOrdinary, run, Prefix.append, ih]

theorem recordOrdinary_preserves_ordinary_configuration
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool) (ticks : Nat)
    (record : Prefix (Notice Borrowed Stored Effect Handoff))
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    (recordOrdinary step capture capacity compatible ticks record state).2 =
      ordinary step capture capacity compatible ticks state := by
  simp only [recordOrdinary_eq_append_run, ordinary_agrees_with_recorded_state]

/-- Retained items, unused capacity and the omitted count are `Prefix.append_state`
applied to the streaming specification. The producer configuration is the
ordinary slice. -/
theorem recordOrdinary_uses_prefix_bounds
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool) (ticks : Nat)
    (record : Prefix (Notice Borrowed Stored Effect Handoff))
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    let continued := run step capture capacity compatible ticks state
    let recorded := recordOrdinary step capture capacity compatible ticks record state
    recorded.1.items = record.items ++ continued.1.take record.remaining ∧
      recorded.1.remaining = record.remaining - continued.1.length ∧
      recorded.1.omitted = record.omitted + (continued.1.length - record.remaining) ∧
      recorded.2 = ordinary step capture capacity compatible ticks state := by
  refine ⟨?_, ?_, ?_, recordOrdinary_preserves_ordinary_configuration step capture capacity
    compatible ticks record state⟩
  · simpa [recordOrdinary_eq_append_run] using (Prefix.append_state record
      (run step capture capacity compatible ticks state).1).1
  · simpa [recordOrdinary_eq_append_run] using (Prefix.append_state record
      (run step capture capacity compatible ticks state).1).2.1
  · simpa [recordOrdinary_eq_append_run] using (Prefix.append_state record
      (run step capture capacity compatible ticks state).1).2.2

theorem ordinary_add
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool) (first second : Nat)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    ordinary step capture capacity compatible (first + second) state =
      ordinary step capture capacity compatible second
        (ordinary step capture capacity compatible first state) := by
  simp only [ordinary_agrees_with_recorded_state, run_split]

/-- Two recorded slices continue one prefix. The second slice receives the
first slice's remaining capacity and omitted count; it does not start a fresh
allowance. -/
theorem recordOrdinary_composes_without_resetting_capacity
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool) (first second : Nat)
    (record : Prefix (Notice Borrowed Stored Effect Handoff))
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    recordOrdinary step capture capacity compatible (first + second) record state =
      (let earlier := recordOrdinary step capture capacity compatible first record state
       recordOrdinary step capture capacity compatible second earlier.1 earlier.2) := by
  have split := run_split step capture capacity compatible first second state
  simp only [recordOrdinary_eq_append_run, split, Prefix.append_append]

/-- Dropping the prefix continues the ordinary runner from the same
configuration. No delivery cursor is cancelled by this switch. -/
theorem recordOrdinary_continues_ordinary
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool) (first second : Nat)
    (record : Prefix (Notice Borrowed Stored Effect Handoff))
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    ordinary step capture capacity compatible second
        (recordOrdinary step capture capacity compatible first record state).2 =
      ordinary step capture capacity compatible (first + second) state := by
  rw [recordOrdinary_preserves_ordinary_configuration, ordinary_add]

/-- A prefix started on the configuration of an ordinary slice retains only
that later notice list, with the existing truncation counts. It does not
contain the notices of the ordinary slice, and its configuration is the
ordinary continuation. -/
theorem late_recording_retains_only_the_suffix
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool) (recordingCapacity first second : Nat)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    let resumed := ordinary step capture capacity compatible first state
    let late := recordOrdinary step capture capacity compatible second
      (Prefix.initial recordingCapacity) resumed
    late.1.items = (run step capture capacity compatible second resumed).1.take recordingCapacity ∧
      late.1.remaining = recordingCapacity -
        (run step capture capacity compatible second resumed).1.length ∧
      late.1.omitted = (run step capture capacity compatible second resumed).1.length -
        recordingCapacity ∧
      late.2 = ordinary step capture capacity compatible (first + second) state := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [recordOrdinary_eq_append_run] using Prefix.initial_items recordingCapacity
      (run step capture capacity compatible second
        (ordinary step capture capacity compatible first state)).1
  · simpa [recordOrdinary_eq_append_run, Prefix.initial] using (Prefix.append_state
      (Prefix.initial recordingCapacity)
      (run step capture capacity compatible second
        (ordinary step capture capacity compatible first state)).1).2.1
  · simpa [recordOrdinary_eq_append_run] using Prefix.initial_omitted recordingCapacity
      (run step capture capacity compatible second
        (ordinary step capture capacity compatible first state)).1
  · rw [recordOrdinary_preserves_ordinary_configuration, ordinary_add]

end NoticePrefix

section OptionalRecord

open Mettapedia.GSLT.Core.InferenceControl.Recording
open Mettapedia.Machines.ResourceOwnership
open Mettapedia.Machines.Cursor.OwnedLifecycle (answerRoots mem_answerRoots closeScope)

variable {Value World : Type}
variable [DecidableEq Stored] [DecidableEq Output]

/-- Owners for one producer configuration and its optional record. Delivery
owners are the existing consumer and caller identities. The recorder is a
different owner, so cancelling it is not consumer retirement. -/
inductive Anchor (clients : Nat) (Output : Type) where
  | delivery (owner : Sum (Fin clients) Output)
  | residual
  | context
  | request
  | recorder
  deriving DecidableEq

/-- Addresses retained inside payloads. Active cursors and caller publications
are not discovered here; they are the existing delivery roots. `effect` and
`handoff` read only the current mode's request. A native implementation must
enumerate these addresses. Nothing in this interface reads compiled source. -/
structure Discovery
    (Producer Borrowed Stored Context Effect Handoff : Type) where
  residual : Producer → List Stored
  pending : Borrowed → List Stored
  context : Context → List Stored
  effect : Effect → List Stored
  handoff : Handoff → List Stored
  record : List (Notice Borrowed Stored Effect Handoff) → List Stored

def residualAddresses
    (discovery : Discovery Producer Borrowed Stored Context Effect Handoff)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    List Stored :=
  match state.execution with
  | none => []
  | some execution => discovery.residual execution.producer

def pendingAddresses
    (discovery : Discovery Producer Borrowed Stored Context Effect Handoff)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    List Stored :=
  match state.execution with
  | none => []
  | some execution =>
      match execution.pending with
      | none => []
      | some value => discovery.pending value

/-- Addresses owned by the request the current mode still retains.
`.active` and `.interrupted` retain none. -/
def requestAddresses
    (discovery : Discovery Producer Borrowed Stored Context Effect Handoff)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    List Stored :=
  match state.execution with
  | none => []
  | some execution =>
      match execution.mode with
      | .active | .interrupted => []
      | .effect request => discovery.effect request
      | .handoff request => discovery.handoff request

omit [DecidableEq Stored] [DecidableEq Output] in
theorem requestAddresses_none
    (discovery : Discovery Producer Borrowed Stored Context Effect Handoff)
    (context : Context)
    (delivery : SharedOccurrenceOwnership.Configuration Stored Output clients) :
    requestAddresses discovery ⟨none, context, delivery⟩ = [] := rfl

omit [DecidableEq Stored] [DecidableEq Output] in
theorem requestAddresses_active
    (discovery : Discovery Producer Borrowed Stored Context Effect Handoff)
    (producer : Producer) (pending : Option Borrowed) (accepted : Nat)
    (context : Context)
    (delivery : SharedOccurrenceOwnership.Configuration Stored Output clients) :
    requestAddresses discovery
        ⟨some ⟨producer, pending, accepted, .active⟩, context, delivery⟩ = [] := rfl

omit [DecidableEq Stored] [DecidableEq Output] in
theorem requestAddresses_interrupted
    (discovery : Discovery Producer Borrowed Stored Context Effect Handoff)
    (producer : Producer) (pending : Option Borrowed) (accepted : Nat)
    (context : Context)
    (delivery : SharedOccurrenceOwnership.Configuration Stored Output clients) :
    requestAddresses discovery
        ⟨some ⟨producer, pending, accepted, .interrupted⟩, context, delivery⟩ = [] := rfl

omit [DecidableEq Stored] [DecidableEq Output] in
theorem requestAddresses_effect
    (discovery : Discovery Producer Borrowed Stored Context Effect Handoff)
    (producer : Producer) (pending : Option Borrowed) (accepted : Nat)
    (request : Effect) (context : Context)
    (delivery : SharedOccurrenceOwnership.Configuration Stored Output clients) :
    requestAddresses discovery
        ⟨some ⟨producer, pending, accepted, .effect request⟩, context, delivery⟩ =
      discovery.effect request := rfl

omit [DecidableEq Stored] [DecidableEq Output] in
theorem requestAddresses_handoff
    (discovery : Discovery Producer Borrowed Stored Context Effect Handoff)
    (producer : Producer) (pending : Option Borrowed) (accepted : Nat)
    (request : Handoff) (context : Context)
    (delivery : SharedOccurrenceOwnership.Configuration Stored Output clients) :
    requestAddresses discovery
        ⟨some ⟨producer, pending, accepted, .handoff request⟩, context, delivery⟩ =
      discovery.handoff request := rfl

def liftDelivery (roots : Roots (Sum (Fin clients) Output) Stored) :
    Roots (Anchor clients Output) Stored :=
  roots.image (fun pair => (Anchor.delivery pair.1, pair.2))

/-- Operational roots: discovered residual, pending return, captured context
and the current mode's request, together with every active delivery cursor
and caller publication. -/
def anchorRoots
    (discovery : Discovery Producer Borrowed Stored Context Effect Handoff)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    Roots (Anchor clients Output) Stored :=
  answerRoots Anchor.residual (residualAddresses discovery state) ∪
    answerRoots Anchor.residual (pendingAddresses discovery state) ∪
    answerRoots Anchor.context (discovery.context state.context) ∪
    answerRoots Anchor.request (requestAddresses discovery state) ∪
    liftDelivery (SharedOccurrenceOwnership.roots state.delivery)

def recorderRoots
    (discovery : Discovery Producer Borrowed Stored Context Effect Handoff)
    (record : Prefix (Notice Borrowed Stored Effect Handoff)) :
    Roots (Anchor clients Output) Stored :=
  answerRoots Anchor.recorder (discovery.record record.items)

/-- The supplied roots contain every discovered operational address, including
the current mode's request, and no recorder owner. -/
def coversOperational
    (discovery : Discovery Producer Borrowed Stored Context Effect Handoff)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (roots : Roots (Anchor clients Output) Stored) : Prop :=
  (∀ address ∈ residualAddresses discovery state, (Anchor.residual, address) ∈ roots) ∧
    (∀ address ∈ pendingAddresses discovery state, (Anchor.residual, address) ∈ roots) ∧
    (∀ address ∈ discovery.context state.context, (Anchor.context, address) ∈ roots) ∧
    (∀ address ∈ requestAddresses discovery state, (Anchor.request, address) ∈ roots) ∧
    liftDelivery (SharedOccurrenceOwnership.roots state.delivery) ⊆ roots ∧
    ∀ pair ∈ roots, pair.1 ≠ Anchor.recorder

theorem anchorRoots_ne_recorder
    (discovery : Discovery Producer Borrowed Stored Context Effect Handoff)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (pair : Anchor clients Output × Stored) (member : pair ∈ anchorRoots discovery state) :
    pair.1 ≠ Anchor.recorder := by
  rcases pair with ⟨owner, _⟩
  simp only [anchorRoots, Finset.mem_union] at member
  rcases member with ((((residual | pending) | context) | request) | delivery)
  · obtain ⟨same, _⟩ := (mem_answerRoots _ _ _ _).mp residual
    subst same
    intro bad
    cases bad
  · obtain ⟨same, _⟩ := (mem_answerRoots _ _ _ _).mp pending
    subst same
    intro bad
    cases bad
  · obtain ⟨same, _⟩ := (mem_answerRoots _ _ _ _).mp context
    subst same
    intro bad
    cases bad
  · obtain ⟨same, _⟩ := (mem_answerRoots _ _ _ _).mp request
    subst same
    intro bad
    cases bad
  · obtain ⟨_, _, eq⟩ := Finset.mem_image.mp delivery
    cases eq
    intro bad
    cases bad

theorem recorderRoots_only
    (discovery : Discovery Producer Borrowed Stored Context Effect Handoff)
    (record : Prefix (Notice Borrowed Stored Effect Handoff))
    (pair : Anchor clients Output × Stored) (member : pair ∈ recorderRoots discovery record) :
    pair.1 = Anchor.recorder := by
  rcases pair with ⟨_, _⟩
  obtain ⟨same, _⟩ := (mem_answerRoots _ _ _ _).mp member
  exact same

theorem anchorRoots_covers
    (discovery : Discovery Producer Borrowed Stored Context Effect Handoff)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    coversOperational discovery state (anchorRoots discovery state) := by
  refine ⟨?_, ?_, ?_, ?_, Finset.subset_union_right, anchorRoots_ne_recorder discovery state⟩
  · intro address member
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_left _ ((mem_answerRoots _ _ _ _).mpr ⟨rfl, member⟩))))
  · intro address member
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_right _ ((mem_answerRoots _ _ _ _).mpr ⟨rfl, member⟩))))
  · intro address member
    exact Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_right _ ((mem_answerRoots _ _ _ _).mpr ⟨rfl, member⟩)))
  · intro address member
    exact Finset.mem_union_left _
      (Finset.mem_union_right _ ((mem_answerRoots _ _ _ _).mpr ⟨rfl, member⟩))

/-- Cancelling the recorder leaves the operational roots and every outside
frame root. Neither summand carries the recorder owner. -/
theorem cancel_recorder_leaves_frame
    (operational recorder frame : Roots (Anchor clients Output) Stored)
    (keptOp : ∀ pair ∈ operational, pair.1 ≠ Anchor.recorder)
    (keptFrame : ∀ pair ∈ frame, pair.1 ≠ Anchor.recorder)
    (only : ∀ pair ∈ recorder, pair.1 = Anchor.recorder) :
    cancel ((operational ∪ recorder) ∪ frame) {Anchor.recorder} = operational ∪ frame := by
  ext pair
  simp only [mem_cancel, Finset.mem_union, Finset.mem_singleton]
  constructor
  · rintro ⟨present, alive⟩
    rcases present with inside | frameMember
    · rcases inside with op | rec
      · exact Or.inl op
      · exact absurd (only pair rec) alive
    · exact Or.inr frameMember
  · intro surviving
    rcases surviving with op | frameMember
    · exact ⟨Or.inl (Or.inl op), keptOp pair op⟩
    · exact ⟨Or.inr frameMember, keptFrame pair frameMember⟩

/-- The unframed split is the empty outside frame. -/
theorem cancel_recorder_leaves_operational
    (operational recorder : Roots (Anchor clients Output) Stored)
    (kept : ∀ pair ∈ operational, pair.1 ≠ Anchor.recorder)
    (only : ∀ pair ∈ recorder, pair.1 = Anchor.recorder) :
    cancel (operational ∪ recorder) {Anchor.recorder} = operational := by
  simpa [Finset.union_empty] using
    cancel_recorder_leaves_frame operational recorder ∅ kept
      (fun _ member => absurd member (Finset.notMem_empty _)) only

/-- Cancel the recorder owner and collect. An outside frame with no recorder
owner stays. The producer configuration is the same value: no consumer
position is cleared and the accepted execution stays. -/
noncomputable def forgetOptionalRecord
    (session : OwnedLifecycle.Session (Anchor clients Output) Stored Value World)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    OwnedLifecycle.Session (Anchor clients Output) Stored Value World ×
      Configuration Producer Borrowed Stored Context Output Effect Handoff clients :=
  (closeScope session {Anchor.recorder}, state)

theorem forgetOptionalRecord_preserves_live
    (session : OwnedLifecycle.Session (Anchor clients Output) Stored Value World)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (operational recorder frame : Roots (Anchor clients Output) Stored)
    (address : Stored)
    (exact : session.roots = (operational ∪ recorder) ∪ frame)
    (keptOp : ∀ pair ∈ operational, pair.1 ≠ Anchor.recorder)
    (keptFrame : ∀ pair ∈ frame, pair.1 ≠ Anchor.recorder)
    (only : ∀ pair ∈ recorder, pair.1 = Anchor.recorder)
    (live : Live session.heap (operational ∪ frame) address) :
    let forgotten := forgetOptionalRecord session state
    forgotten.2 = state ∧
      forgotten.1.roots = operational ∪ frame ∧
      forgotten.1.heap.lookup address = session.heap.lookup address ∧
      footprint session.heap session.roots =
        footprint session.heap (operational ∪ frame) ∪ footprint session.heap recorder ∧
      footprint session.heap forgotten.1.roots =
        footprint session.heap (operational ∪ frame) ∧
      forgotten.1.roots ⊆ session.roots ∧
      forgotten.2.execution = state.execution ∧
      acceptedCount forgotten.2 = acceptedCount state := by
  have cancelled := cancel_recorder_leaves_frame operational recorder frame keptOp keptFrame only
  have rootsEq : (forgetOptionalRecord session state).1.roots = operational ∪ frame := by
    have reduced : (forgetOptionalRecord session state).1.roots =
        cancel session.roots {Anchor.recorder} := rfl
    rw [reduced, exact, cancelled]
  have lookupEq : (forgetOptionalRecord session state).1.heap.lookup address =
      session.heap.lookup address := by
    have reduced : (forgetOptionalRecord session state).1.heap =
        collect session.heap (cancel session.roots {Anchor.recorder}) := rfl
    rw [reduced, exact, cancelled]
    exact lookup_collect_of_live session.heap (operational ∪ frame) live
  have sessionFootprint : footprint session.heap session.roots =
      footprint session.heap (operational ∪ frame) ∪ footprint session.heap recorder := by
    rw [exact]
    have outer := footprint_union session.heap (operational ∪ recorder) frame
    have inner := footprint_union session.heap operational recorder
    have kept := footprint_union session.heap operational frame
    calc
      footprint session.heap ((operational ∪ recorder) ∪ frame)
          = footprint session.heap (operational ∪ recorder) ∪ footprint session.heap frame := outer
      _ = (footprint session.heap operational ∪ footprint session.heap recorder) ∪
            footprint session.heap frame := by rw [inner]
      _ = footprint session.heap operational ∪
            (footprint session.heap recorder ∪ footprint session.heap frame) := by
            rw [Finset.union_assoc]
      _ = footprint session.heap operational ∪
            (footprint session.heap frame ∪ footprint session.heap recorder) := by
            rw [Finset.union_comm (footprint session.heap recorder) (footprint session.heap frame)]
      _ = (footprint session.heap operational ∪ footprint session.heap frame) ∪
            footprint session.heap recorder := by rw [← Finset.union_assoc]
      _ = footprint session.heap (operational ∪ frame) ∪ footprint session.heap recorder := by
            rw [← kept]
  have forgottenFootprint : footprint session.heap (forgetOptionalRecord session state).1.roots =
      footprint session.heap (operational ∪ frame) := by rw [rootsEq]
  have retained : (forgetOptionalRecord session state).1.roots ⊆ session.roots := by
    rw [rootsEq, exact]
    exact Finset.union_subset_union Finset.subset_union_left (Finset.Subset.refl frame)
  exact ⟨rfl, rootsEq, lookupEq, sessionFootprint, forgottenFootprint, retained, rfl, rfl⟩

theorem forgetOptionalRecord_reclaims_unshared
    (session : OwnedLifecycle.Session (Anchor clients Output) Stored Value World)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (operational recorder frame : Roots (Anchor clients Output) Stored)
    (address : Stored)
    (exact : session.roots = (operational ∪ recorder) ∪ frame)
    (keptOp : ∀ pair ∈ operational, pair.1 ≠ Anchor.recorder)
    (keptFrame : ∀ pair ∈ frame, pair.1 ≠ Anchor.recorder)
    (only : ∀ pair ∈ recorder, pair.1 = Anchor.recorder)
    (outside : ¬ Live session.heap (operational ∪ frame) address) :
    (forgetOptionalRecord session state).1.heap.lookup address = none := by
  have cancelled := cancel_recorder_leaves_frame operational recorder frame keptOp keptFrame only
  have reduced : (forgetOptionalRecord session state).1.heap =
      collect session.heap (cancel session.roots {Anchor.recorder}) := rfl
  rw [reduced, exact, cancelled]
  exact lookup_collect_of_not_live session.heap (operational ∪ frame) outside

/-- No cell still reachable from `roots` keeps `recording` among its
references. `projectHeap_clears_observer_reference` proves this for the
projected heap when `recording` belongs to none of the stored operational
reference fields. This property is not a function that clears fields.
Cancelling the recorder owner does not. -/
abbrev receiptFieldCleared (heap : Heap Stored Value)
    (roots : Roots (Anchor clients Output) Stored) (recording : Stored) : Prop :=
  ∀ holder, Live heap roots holder →
    ∀ cell, heap.lookup holder = some cell → recording ∉ cell.references

omit [DecidableEq Output] in
theorem not_live_of_receiptFieldCleared (heap : Heap Stored Value)
    (roots : Roots (Anchor clients Output) Stored) (recording : Stored)
    (notRoot : recording ∉ rootAddresses roots)
    (cleared : receiptFieldCleared heap roots recording) :
    ¬ Live heap roots recording := by
  intro live
  cases live with
  | root rooted =>
      exact notRoot rooted.2
  | step prior edge =>
      obtain ⟨_cell, found, reference⟩ := edge
      exact cleared _ prior _ found reference

/-- A recording named by a strong edge of an operational cell stays after the
recorder root is cancelled. Root cancellation is not field erasure. -/
theorem embedded_recording_survives_recorder_cancellation
    (session : OwnedLifecycle.Session (Anchor clients Output) Stored Value World)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (operational recorder frame : Roots (Anchor clients Output) Stored)
    {owner : Anchor clients Output} (holder recording : Stored) (cell : Cell Stored Value)
    (exact : session.roots = (operational ∪ recorder) ∪ frame)
    (keptOp : ∀ pair ∈ operational, pair.1 ≠ Anchor.recorder)
    (keptFrame : ∀ pair ∈ frame, pair.1 ≠ Anchor.recorder)
    (only : ∀ pair ∈ recorder, pair.1 = Anchor.recorder)
    (holderRoot : (owner, holder) ∈ operational)
    (found : session.heap.lookup holder = some cell)
    (edge : recording ∈ cell.references) :
    Live session.heap (operational ∪ frame) recording ∧
      (forgetOptionalRecord session state).1.heap.lookup recording =
        session.heap.lookup recording := by
  have retained : (owner, holder) ∈ operational ∪ frame :=
    Finset.mem_union_left _ holderRoot
  have allocated : holder ∈ session.heap.allocated :=
    (session.heap.allocated_iff holder).mpr ⟨cell, found⟩
  have liveHolder := live_of_root session.heap (operational ∪ frame) retained allocated
  have liveRecording := live_step session.heap (operational ∪ frame) liveHolder found edge
  exact ⟨liveRecording, (forgetOptionalRecord_preserves_live session state operational recorder
    frame recording exact keptOp keptFrame only liveRecording).2.2.1⟩

/-- Once the receipt fields are cleared, the same recorder cancellation
reclaims a recording that is not otherwise a retained root. -/
theorem cleared_recording_is_reclaimed
    (session : OwnedLifecycle.Session (Anchor clients Output) Stored Value World)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (operational recorder frame : Roots (Anchor clients Output) Stored) (recording : Stored)
    (exact : session.roots = (operational ∪ recorder) ∪ frame)
    (keptOp : ∀ pair ∈ operational, pair.1 ≠ Anchor.recorder)
    (keptFrame : ∀ pair ∈ frame, pair.1 ≠ Anchor.recorder)
    (only : ∀ pair ∈ recorder, pair.1 = Anchor.recorder)
    (notRoot : recording ∉ rootAddresses (operational ∪ frame))
    (cleared : receiptFieldCleared session.heap (operational ∪ frame) recording) :
    (forgetOptionalRecord session state).1.heap.lookup recording = none :=
  forgetOptionalRecord_reclaims_unshared session state operational recorder frame recording
    exact keptOp keptFrame only
    (not_live_of_receiptFieldCleared session.heap (operational ∪ frame) recording notRoot cleared)

/-- Delivery roots use the same address map as the heap relocation. This does
not rewrite the log rows or the caller publications. -/
theorem liftDelivery_roots
    {DestinationAddress : Type} {DestinationValue : Type} [DecidableEq DestinationAddress]
    {source : Heap Stored Value} {destination : Heap DestinationAddress DestinationValue}
    (copy : Relocation source destination)
    (roots : Roots (Sum (Fin clients) Output) Stored) :
    copy.roots (liftDelivery roots) = liftDelivery (copy.roots roots) := by
  simp only [Relocation.roots, liftDelivery, Finset.image_image]
  rfl

/-- Addresses discovered from the residual, the pending return, the context,
the current request and the delivery roots agree with `copy.roots`. The
producer configuration itself is not rebuilt at the destination addresses. -/
theorem anchorRoots_relocated
    {DestinationAddress : Type} {DestinationValue : Type} [DecidableEq DestinationAddress]
    {source : Heap Stored Value} {destination : Heap DestinationAddress DestinationValue}
    (copy : Relocation source destination)
    (discovery : Discovery Producer Borrowed Stored Context Effect Handoff)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    copy.roots (anchorRoots discovery state) =
      answerRoots Anchor.residual ((residualAddresses discovery state).map copy.address) ∪
        answerRoots Anchor.residual ((pendingAddresses discovery state).map copy.address) ∪
        answerRoots Anchor.context ((discovery.context state.context).map copy.address) ∪
        answerRoots Anchor.request ((requestAddresses discovery state).map copy.address) ∪
        liftDelivery (copy.roots (SharedOccurrenceOwnership.roots state.delivery)) := by
  have union (left right : Roots (Anchor clients Output) Stored) :
      copy.roots (left ∪ right) = copy.roots left ∪ copy.roots right := by
    simp [Relocation.roots, Finset.image_union]
  rw [anchorRoots, union, union, union, union,
    OwnedLifecycle.relocate_answerRoots, OwnedLifecycle.relocate_answerRoots,
    OwnedLifecycle.relocate_answerRoots, OwnedLifecycle.relocate_answerRoots,
    liftDelivery_roots]

/-- Copy the heap session left by scoped release. `copy` relocates that
collected heap, so cells already omitted do not have to occur in the
destination. The producer configuration is not an argument and is not
relocated. -/
def transportRetained
    {DestinationAddress : Type} {DestinationValue : Type} [DecidableEq DestinationAddress]
    (retained : OwnedLifecycle.Session (Anchor clients Output) Stored Value World)
    (destination : Heap DestinationAddress DestinationValue)
    (copy : Relocation retained.heap destination) :
    OwnedLifecycle.Session (Anchor clients Output) DestinationAddress DestinationValue World :=
  OwnedLifecycle.relocateSession retained destination copy

/-- Cancellation and address transport commute on the collected heap session.
The semantic world stays. This does not map residuals, delivery rows or
request payloads. -/
theorem transportRetained_square
    {DestinationAddress : Type} {DestinationValue : Type} [DecidableEq DestinationAddress]
    (session : OwnedLifecycle.Session (Anchor clients Output) Stored Value World)
    (destination : Heap DestinationAddress DestinationValue)
    (copy : Relocation (closeScope session {Anchor.recorder}).heap destination) :
    let retained := closeScope session {Anchor.recorder}
    let transported := transportRetained retained destination copy
    transported.world = session.world ∧
      transported.roots = copy.roots (cancel session.roots {Anchor.recorder}) ∧
      copy.roots (cancel session.roots {Anchor.recorder}) =
        cancel (copy.roots session.roots) {Anchor.recorder} := by
  let retained := closeScope session {Anchor.recorder}
  let transported := transportRetained retained destination copy
  have rootsEq : retained.roots = cancel session.roots {Anchor.recorder} := rfl
  refine ⟨rfl, ?_, copy.roots_cancel session.roots {Anchor.recorder}⟩
  rw [show transported.roots = copy.roots retained.roots from rfl, rootsEq]

/-- An ordered path that survives collection is the same path in the
transported image, before and after collecting that image. Byte weights travel
inside the relocated cells. -/
theorem transportRetained_preserves_walk
    {DestinationAddress : Type} {DestinationValue : Type} [DecidableEq DestinationAddress]
    (session : OwnedLifecycle.Session (Anchor clients Output) Stored Value World)
    (destination : Heap DestinationAddress DestinationValue)
    (copy : Relocation (closeScope session {Anchor.recorder}).heap destination)
    (address : Stored) (path : List Stored)
    (live : Live session.heap (cancel session.roots {Anchor.recorder}) address) :
    let retained := closeScope session {Anchor.recorder}
    let transported := transportRetained retained destination copy
    walk transported.heap (copy.address address) (path.map copy.address) =
      (walk session.heap address path).map (fun pair =>
        (copy.address pair.1, pair.2.relocate copy.address copy.payload)) ∧
      walk (collect destination (copy.roots retained.roots))
          (copy.address address) (path.map copy.address) =
        walk transported.heap (copy.address address) (path.map copy.address) := by
  let retained := closeScope session {Anchor.recorder}
  let transported := transportRetained retained destination copy
  have rootsEq : retained.roots = cancel session.roots {Anchor.recorder} := rfl
  have heapEq : retained.heap =
      collect session.heap (cancel session.roots {Anchor.recorder}) := rfl
  have installed : transported.heap = destination := rfl
  have projectedLive : Live retained.heap retained.roots address := by
    rw [heapEq, rootsEq]
    exact (live_collect_iff session.heap (cancel session.roots {Anchor.recorder}) address).mpr live
  have sourceWalk : walk retained.heap address path = walk session.heap address path := by
    rw [heapEq]
    exact walk_collect session.heap (cancel session.roots {Anchor.recorder}) live path
  have atDestination := copy.walk_eq address path
  have atCollected := copy.walk_collect_eq retained.roots address projectedLive path
  refine ⟨?_, ?_⟩
  · calc
      walk transported.heap (copy.address address) (path.map copy.address)
          = walk destination (copy.address address) (path.map copy.address) := by rw [installed]
      _ = (walk retained.heap address path).map (fun pair =>
            (copy.address pair.1, pair.2.relocate copy.address copy.payload)) := atDestination
      _ = (walk session.heap address path).map (fun pair =>
            (copy.address pair.1, pair.2.relocate copy.address copy.payload)) := by rw [sourceWalk]
  · calc
      walk (collect destination (copy.roots retained.roots))
            (copy.address address) (path.map copy.address)
          = (walk retained.heap address path).map (fun pair =>
              (copy.address pair.1, pair.2.relocate copy.address copy.payload)) := atCollected
      _ = walk destination (copy.address address) (path.map copy.address) := atDestination.symm
      _ = walk transported.heap (copy.address address) (path.map copy.address) := by
            rw [installed]

/-- Shared endpoints survive collection and the later address transport.
Equal payloads at distinct addresses stay distinct. -/
theorem transportRetained_preserves_aliases
    {DestinationAddress : Type} {DestinationValue : Type} [DecidableEq DestinationAddress]
    (session : OwnedLifecycle.Session (Anchor clients Output) Stored Value World)
    (destination : Heap DestinationAddress DestinationValue)
    (copy : Relocation (closeScope session {Anchor.recorder}).heap destination)
    (start other : Stored) (left right : List Stored)
    (liveStart : Live session.heap (cancel session.roots {Anchor.recorder}) start)
    (liveOther : Live session.heap (cancel session.roots {Anchor.recorder}) other) :
    Aliases (collect destination
        (copy.roots (closeScope session {Anchor.recorder}).roots))
        (copy.address start) (left.map copy.address)
        (copy.address other) (right.map copy.address) ↔
      Aliases session.heap start left other right := by
  let retained := closeScope session {Anchor.recorder}
  have sameRoots : (closeScope session {Anchor.recorder}).roots = retained.roots := rfl
  rw [sameRoots]
  have rootsEq : retained.roots = cancel session.roots {Anchor.recorder} := rfl
  have heapEq : retained.heap =
      collect session.heap (cancel session.roots {Anchor.recorder}) := rfl
  have liveProjectedStart : Live retained.heap retained.roots start := by
    rw [heapEq, rootsEq]
    exact (live_collect_iff session.heap (cancel session.roots {Anchor.recorder}) start).mpr
      liveStart
  have liveProjectedOther : Live retained.heap retained.roots other := by
    rw [heapEq, rootsEq]
    exact (live_collect_iff session.heap (cancel session.roots {Anchor.recorder}) other).mpr
      liveOther
  have liveDestinationStart :
      Live destination (copy.roots retained.roots) (copy.address start) :=
    (copy.live_iff retained.roots (copy.address start)).mpr ⟨start, liveProjectedStart, rfl⟩
  have liveDestinationOther :
      Live destination (copy.roots retained.roots) (copy.address other) :=
    (copy.live_iff retained.roots (copy.address other)).mpr ⟨other, liveProjectedOther, rfl⟩
  rw [aliases_collect destination (copy.roots retained.roots)
      liveDestinationStart liveDestinationOther (left.map copy.address) (right.map copy.address),
    copy.aliases_iff start other left right, heapEq]
  exact aliases_collect session.heap (cancel session.roots {Anchor.recorder})
    liveStart liveOther left right

namespace RecordRetention

open ResourceOwnership.Examples

def retainedDelivery : SharedOccurrenceOwnership.Configuration Nat Unit 1 :=
  ⟨⟨0, [1], fun _ => some 0, false, 2⟩, {((), 1)}⟩

def carrier : Configuration Unit Unit Nat Nat Unit Unit Unit 1 :=
  ⟨some ⟨(), some (), 4, .active⟩, 0, retainedDelivery⟩

def barrierCarrier : Configuration Unit Unit Nat Nat Unit Unit Unit 1 :=
  ⟨some ⟨(), none, 4, .effect ()⟩, 0, retainedDelivery⟩

def keptNotice : Prefix (Notice Unit Nat Unit Unit) :=
  (Prefix.initial 4).append [.returned (), .admitted 0 1]

def barrierRecord : Prefix (Notice Unit Nat Unit Unit) := Prefix.initial 0

def emptyFrame : Roots (Anchor 1 Unit) Nat := ∅

def outsideFrame : Roots (Anchor 1 Unit) Nat := {(Anchor.context, 0)}

/-- The retained prefix contributes its private cell `0` and the shared cell `1`.
The pending return, residual and context contribute `1` and `2`. The current
mode is active, so neither request extractor is read. -/
def positiveDiscovery : Discovery Unit Unit Nat Nat Unit Unit where
  residual := fun _ => [1]
  pending := fun _ => [1]
  context := fun _ => [2]
  effect := fun _ => []
  handoff := fun _ => []
  record := fun notices => notices.flatMap fun
    | .returned _ => [0]
    | .admitted _ address => [address]
    | _ => []

/-- The captured context retains cell `0`, which this supply does not root. -/
def requiredDiscovery : Discovery Unit Unit Nat Nat Unit Unit :=
  {positiveDiscovery with context := fun _ => [0]}

def suppliedDiscovery : Discovery Unit Unit Nat Nat Unit Unit :=
  {positiveDiscovery with context := fun _ => []}

/-- Cell `0` is retained only by the current effect request. -/
def barrierDiscovery : Discovery Unit Unit Nat Nat Unit Unit where
  residual := fun _ => []
  pending := fun _ => []
  context := fun _ => []
  effect := fun _ => [0]
  handoff := fun _ => []
  record := fun _ => []

def omittedRequestDiscovery : Discovery Unit Unit Nat Nat Unit Unit :=
  {barrierDiscovery with effect := fun _ => []}

noncomputable def positiveSession :
    OwnedLifecycle.Session (Anchor 1 Unit) Nat Nat Nat :=
  ⟨chainHeap 2,
    (anchorRoots positiveDiscovery carrier ∪ recorderRoots positiveDiscovery keptNotice) ∪
      emptyFrame, 0⟩

noncomputable def suppliedSession :
    OwnedLifecycle.Session (Anchor 1 Unit) Nat Nat Nat :=
  ⟨chainHeap 2,
    (anchorRoots suppliedDiscovery carrier ∪ recorderRoots suppliedDiscovery keptNotice) ∪
      emptyFrame, 0⟩

noncomputable def framedSession :
    OwnedLifecycle.Session (Anchor 1 Unit) Nat Nat Nat :=
  ⟨chainHeap 2,
    (anchorRoots positiveDiscovery carrier ∪ recorderRoots positiveDiscovery keptNotice) ∪
      outsideFrame, 0⟩

noncomputable def barrierSession :
    OwnedLifecycle.Session (Anchor 1 Unit) Nat Nat Nat :=
  ⟨chainHeap 2,
    (anchorRoots barrierDiscovery barrierCarrier ∪
      recorderRoots barrierDiscovery barrierRecord) ∪ emptyFrame, 0⟩

noncomputable def omittedRequestSession :
    OwnedLifecycle.Session (Anchor 1 Unit) Nat Nat Nat :=
  ⟨chainHeap 2,
    (anchorRoots omittedRequestDiscovery barrierCarrier ∪
      recorderRoots omittedRequestDiscovery barrierRecord) ∪ emptyFrame, 0⟩

private theorem not_live_zero (roots : Roots (Anchor 1 Unit) Nat)
    (included : rootAddresses roots ⊆ ({1, 2} : Finset Nat))
    (absent : (0 : Nat) ∉ census (chainHeap 2) roots) :
    ¬ Live (chainHeap 2) roots 0 := by
  intro live
  have valid : ValidRoots (chainHeap 2) roots := by
    intro pair member
    have addr : pair.2 ∈ ({1, 2} : Finset Nat) :=
      included (Finset.mem_image.mpr ⟨pair, member, rfl⟩)
    have split : pair.2 = 1 ∨ pair.2 = 2 := by
      simpa [Finset.mem_insert, Finset.mem_singleton] using addr
    rcases split with eq | eq
    · rw [eq]; decide
    · rw [eq]; decide
  exact absent ((mem_census_iff_live (chainHeap 2) roots valid 0).mpr live)

private theorem keptEmpty (pair : Anchor 1 Unit × Nat) (member : pair ∈ emptyFrame) :
    pair.1 ≠ Anchor.recorder :=
  absurd member (Finset.notMem_empty _)

theorem shared_root_survives_recorder_collection :
    let operational := anchorRoots positiveDiscovery carrier
    let recorder : Roots (Anchor 1 Unit) Nat :=
      recorderRoots positiveDiscovery keptNotice
    let forgotten := forgetOptionalRecord positiveSession carrier
    coversOperational positiveDiscovery carrier operational ∧
      (Anchor.residual, 1) ∈ operational ∧
      (Anchor.recorder, 1) ∈ recorder ∧
      forgotten.2.delivery.log.positions 0 = some 0 ∧
      acceptedCount forgotten.2 = 4 ∧
      forgotten.1.heap.lookup 1 = (chainHeap 2).lookup 1 ∧
      forgotten.1.heap.lookup 2 = (chainHeap 2).lookup 2 ∧
      forgotten.1.heap.lookup 0 = none := by
  let operational := anchorRoots positiveDiscovery carrier
  let recorder : Roots (Anchor 1 Unit) Nat :=
    recorderRoots positiveDiscovery keptNotice
  have covered := anchorRoots_covers positiveDiscovery carrier
  have sharedOperational : (Anchor.residual, 1) ∈ operational := by decide
  have sharedRecorder : (Anchor.recorder, 1) ∈ recorder := by decide
  have contextRoot : (Anchor.context, 2) ∈ operational := by decide
  have exact : positiveSession.roots = (operational ∪ recorder) ∪ emptyFrame := rfl
  have liveShared : Live (chainHeap 2) (operational ∪ emptyFrame) 1 := by
    rw [emptyFrame, Finset.union_empty]
    exact live_of_root (chainHeap 2) operational sharedOperational (by decide)
  have liveContext : Live (chainHeap 2) (operational ∪ emptyFrame) 2 := by
    rw [emptyFrame, Finset.union_empty]
    exact live_of_root (chainHeap 2) operational contextRoot (by decide)
  have preservedShared := forgetOptionalRecord_preserves_live positiveSession carrier
    operational recorder emptyFrame 1 exact (anchorRoots_ne_recorder positiveDiscovery carrier)
    keptEmpty (recorderRoots_only positiveDiscovery keptNotice) liveShared
  have preservedContext := forgetOptionalRecord_preserves_live positiveSession carrier
    operational recorder emptyFrame 2 exact (anchorRoots_ne_recorder positiveDiscovery carrier)
    keptEmpty (recorderRoots_only positiveDiscovery keptNotice) liveContext
  have notOperational : ¬ Live (chainHeap 2) (operational ∪ emptyFrame) 0 := by
    rw [emptyFrame, Finset.union_empty]
    exact not_live_zero operational (by decide) (by decide)
  have reclaimed := forgetOptionalRecord_reclaims_unshared positiveSession carrier
    operational recorder emptyFrame 0 exact (anchorRoots_ne_recorder positiveDiscovery carrier)
    keptEmpty (recorderRoots_only positiveDiscovery keptNotice) notOperational
  refine ⟨covered, sharedOperational, sharedRecorder, rfl, rfl, ?_, ?_, reclaimed⟩
  · simpa [positiveSession] using preservedShared.2.2.1
  · simpa [positiveSession] using preservedContext.2.2.1

theorem missing_context_root_is_reclaimed :
    let required := requiredDiscovery.context carrier.context
    let supplied := anchorRoots suppliedDiscovery carrier
    let forgotten := forgetOptionalRecord suppliedSession carrier
    required = [0] ∧
      (Anchor.context, 0) ∉ supplied ∧
      ¬ coversOperational requiredDiscovery carrier supplied ∧
      forgotten.2.delivery.log.positions 0 = some 0 ∧
      acceptedCount forgotten.2 = 4 ∧
      forgotten.2.execution = carrier.execution ∧
      forgotten.1.heap.lookup 0 = none ∧
      forgotten.1.heap.lookup 1 = (chainHeap 2).lookup 1 := by
  let supplied := anchorRoots suppliedDiscovery carrier
  let recorder : Roots (Anchor 1 Unit) Nat :=
    recorderRoots suppliedDiscovery keptNotice
  have requiredAddresses : requiredDiscovery.context carrier.context = [0] := rfl
  have missing : (Anchor.context, 0) ∉ supplied := by decide
  have uncovered : ¬ coversOperational requiredDiscovery carrier supplied := by
    intro covered
    exact missing (covered.2.2.1 0 (by simp [requiredDiscovery, carrier]))
  have exact : suppliedSession.roots = (supplied ∪ recorder) ∪ emptyFrame := rfl
  have notOperational : ¬ Live (chainHeap 2) (supplied ∪ emptyFrame) 0 := by
    rw [emptyFrame, Finset.union_empty]
    exact not_live_zero supplied (by decide) (by decide)
  have reclaimed := forgetOptionalRecord_reclaims_unshared suppliedSession carrier
    supplied recorder emptyFrame 0 exact (anchorRoots_ne_recorder suppliedDiscovery carrier)
    keptEmpty (recorderRoots_only suppliedDiscovery keptNotice) notOperational
  have pendingRoot : (Anchor.residual, 1) ∈ supplied := by decide
  have livePending : Live (chainHeap 2) (supplied ∪ emptyFrame) 1 := by
    rw [emptyFrame, Finset.union_empty]
    exact live_of_root (chainHeap 2) supplied pendingRoot (by decide)
  have preserved := forgetOptionalRecord_preserves_live suppliedSession carrier
    supplied recorder emptyFrame 1 exact (anchorRoots_ne_recorder suppliedDiscovery carrier)
    keptEmpty (recorderRoots_only suppliedDiscovery keptNotice) livePending
  refine ⟨requiredAddresses, missing, uncovered, rfl, rfl, rfl, reclaimed, ?_⟩
  simpa [suppliedSession] using preserved.2.2.1

theorem outside_frame_keeps_unrecorded_cell :
    let operational := anchorRoots positiveDiscovery carrier
    let forgotten := forgetOptionalRecord framedSession carrier
    (∀ pair ∈ outsideFrame, pair.1 ≠ Anchor.recorder) ∧
      ¬ Live (chainHeap 2) operational 0 ∧
      (Anchor.context, 0) ∈ forgotten.1.roots ∧
      forgotten.1.heap.lookup 0 = (chainHeap 2).lookup 0 ∧
      forgotten.2.delivery.log.positions 0 = some 0 ∧
      acceptedCount forgotten.2 = 4 := by
  let operational := anchorRoots positiveDiscovery carrier
  let recorder : Roots (Anchor 1 Unit) Nat :=
    recorderRoots positiveDiscovery keptNotice
  have keptFrame : ∀ pair ∈ outsideFrame, pair.1 ≠ Anchor.recorder := by
    intro pair member
    rw [outsideFrame, Finset.mem_singleton] at member
    subst member
    decide
  have exact : framedSession.roots = (operational ∪ recorder) ∪ outsideFrame := rfl
  have missed : ¬ Live (chainHeap 2) operational 0 :=
    not_live_zero operational (by decide) (by decide)
  have frameRoot : (Anchor.context, 0) ∈ outsideFrame := by
    rw [outsideFrame]
    exact Finset.mem_singleton.mpr rfl
  have liveUnion : Live (chainHeap 2) (operational ∪ outsideFrame) 0 :=
    live_mono (chainHeap 2) Finset.subset_union_right
      (live_of_root (chainHeap 2) outsideFrame frameRoot (by decide))
  have preserved := forgetOptionalRecord_preserves_live framedSession carrier
    operational recorder outsideFrame 0 exact
    (anchorRoots_ne_recorder positiveDiscovery carrier) keptFrame
    (recorderRoots_only positiveDiscovery keptNotice) liveUnion
  refine ⟨keptFrame, missed, ?_, ?_, rfl, rfl⟩
  · exact preserved.2.1.symm ▸ Finset.mem_union_right _ frameRoot
  · simpa [framedSession] using preserved.2.2.1

theorem retained_request_root_is_necessary :
    let operational := anchorRoots barrierDiscovery barrierCarrier
    let omitted := anchorRoots omittedRequestDiscovery barrierCarrier
    let kept := forgetOptionalRecord barrierSession barrierCarrier
    let dropped := forgetOptionalRecord omittedRequestSession barrierCarrier
    requestAddresses barrierDiscovery barrierCarrier = [0] ∧
      requestAddresses omittedRequestDiscovery barrierCarrier = [] ∧
      residualAddresses barrierDiscovery barrierCarrier = [] ∧
      pendingAddresses barrierDiscovery barrierCarrier = [] ∧
      barrierDiscovery.context barrierCarrier.context = [] ∧
      (Anchor.request, 0) ∈ operational ∧
      (Anchor.request, 0) ∉ omitted ∧
      ¬ coversOperational barrierDiscovery barrierCarrier omitted ∧
      kept.1.heap.lookup 0 = (chainHeap 2).lookup 0 ∧
      dropped.1.heap.lookup 0 = none ∧
      kept.2.delivery.log.positions 0 = some 0 ∧
      dropped.2.delivery.log.positions 0 = some 0 ∧
      acceptedCount kept.2 = 4 ∧
      acceptedCount dropped.2 = 4 ∧
      kept.2.execution = barrierCarrier.execution ∧
      dropped.2.execution = barrierCarrier.execution := by
  let operational := anchorRoots barrierDiscovery barrierCarrier
  let omitted := anchorRoots omittedRequestDiscovery barrierCarrier
  let recorder : Roots (Anchor 1 Unit) Nat :=
    recorderRoots barrierDiscovery barrierRecord
  let omittedRecorder : Roots (Anchor 1 Unit) Nat :=
    recorderRoots omittedRequestDiscovery barrierRecord
  have fullRequest : requestAddresses barrierDiscovery barrierCarrier = [0] :=
    (requestAddresses_effect barrierDiscovery () none 4 () 0 retainedDelivery).trans rfl
  have omittedRequest : requestAddresses omittedRequestDiscovery barrierCarrier = [] :=
    (requestAddresses_effect omittedRequestDiscovery () none 4 () 0 retainedDelivery).trans rfl
  have noResidual : residualAddresses barrierDiscovery barrierCarrier = [] := rfl
  have noPending : pendingAddresses barrierDiscovery barrierCarrier = [] := rfl
  have noContext : barrierDiscovery.context barrierCarrier.context = [] := rfl
  have present : (Anchor.request, 0) ∈ operational := by decide
  have absent : (Anchor.request, 0) ∉ omitted := by decide
  have uncovered : ¬ coversOperational barrierDiscovery barrierCarrier omitted := by
    intro covered
    exact absent (covered.2.2.2.1 0 (by decide))
  have exactKept : barrierSession.roots = (operational ∪ recorder) ∪ emptyFrame := rfl
  have exactDropped : omittedRequestSession.roots = (omitted ∪ omittedRecorder) ∪ emptyFrame := rfl
  have liveRequest : Live (chainHeap 2) (operational ∪ emptyFrame) 0 := by
    rw [emptyFrame, Finset.union_empty]
    exact live_of_root (chainHeap 2) operational present (by decide)
  have keptCell := forgetOptionalRecord_preserves_live barrierSession barrierCarrier
    operational recorder emptyFrame 0 exactKept
    (anchorRoots_ne_recorder barrierDiscovery barrierCarrier) keptEmpty
    (recorderRoots_only barrierDiscovery barrierRecord) liveRequest
  have notRequest : ¬ Live (chainHeap 2) (omitted ∪ emptyFrame) 0 := by
    rw [emptyFrame, Finset.union_empty]
    exact not_live_zero omitted (by decide) (by decide)
  have droppedCell := forgetOptionalRecord_reclaims_unshared omittedRequestSession barrierCarrier
    omitted omittedRecorder emptyFrame 0 exactDropped
    (anchorRoots_ne_recorder omittedRequestDiscovery barrierCarrier) keptEmpty
    (recorderRoots_only omittedRequestDiscovery barrierRecord) notRequest
  refine ⟨fullRequest, omittedRequest, noResidual, noPending, noContext, present, absent,
    uncovered, ?_, droppedCell, rfl, rfl, rfl, rfl, rfl, rfl⟩
  simpa [barrierSession] using keptCell.2.2.1

/-- Operational cell `0` points at recording `1`. The recorder is `1`'s only
root. `0` is not a recorder owner. -/
def embeddedOperational : Roots (Anchor 1 Unit) Nat := {(Anchor.residual, 0)}

def embeddedRecorder : Roots (Anchor 1 Unit) Nat := {(Anchor.recorder, 1)}

noncomputable def embeddedSession :
    OwnedLifecycle.Session (Anchor 1 Unit) Nat Nat Nat :=
  ⟨chainHeap 1, (embeddedOperational ∪ embeddedRecorder) ∪ emptyFrame, 0⟩

/-- A witness whose cells retain no receipt edge. It is not
`projectOptionalFields`. Recorder-root cancellation still does not erase
stored fields. -/
def clearedCell (address : Nat) : Cell Nat Nat where
  value := address
  references := ∅
  bytes := 1

def clearedHeap : Heap Nat Nat where
  lookup address := if address ≤ 1 then some (clearedCell address) else none
  allocated := Finset.range 2
  allocated_iff address := by
    simp only [Finset.mem_range]
    constructor
    · intro within
      exact ⟨clearedCell address, if_pos (by omega)⟩
    · rintro ⟨_, found⟩
      split at found
      next within => omega
      next _ => cases found
  closed address cell found next reference := by
    split at found
    next _ =>
      cases found
      simp only [clearedCell] at reference
      exact absurd reference (Finset.notMem_empty _)
    next _ => cases found

noncomputable def clearedSession :
    OwnedLifecycle.Session (Anchor 1 Unit) Nat Nat Nat :=
  ⟨clearedHeap, (embeddedOperational ∪ embeddedRecorder) ∪ emptyFrame, 0⟩

private theorem embeddedKept (pair : Anchor 1 Unit × Nat) (member : pair ∈ embeddedOperational) :
    pair.1 ≠ Anchor.recorder := by
  rw [embeddedOperational, Finset.mem_singleton] at member
  subst member
  decide

private theorem embeddedOnly (pair : Anchor 1 Unit × Nat) (member : pair ∈ embeddedRecorder) :
    pair.1 = Anchor.recorder := by
  rw [embeddedRecorder, Finset.mem_singleton] at member
  subst member
  rfl

private theorem embeddedHolder : (Anchor.residual, 0) ∈ embeddedOperational := by
  rw [embeddedOperational]
  exact Finset.mem_singleton.mpr rfl

private theorem embeddedEdge : (chainHeap 1).lookup 0 = some (chainCell 1 0) ∧
    1 ∈ (chainCell 1 0).references ∧
    (chainHeap 1).lookup 1 = some (chainCell 1 1) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [chainHeap, if_pos (Nat.le_succ 0)]
  · simp only [chainCell, if_pos (Nat.lt_succ_self 0), Finset.mem_singleton]
  · simp only [chainHeap, if_pos (Nat.le_refl 1)]

private theorem embeddedSourceWalk :
    walk (chainHeap 1) 0 [1] = some (1, chainCell 1 1) := by
  obtain ⟨lookup0, edge, lookup1⟩ := embeddedEdge
  simp only [walk, lookup0, Option.bind_some, if_pos edge, lookup1, Option.map_some]

/-- Dropping the recorder root leaves the recording in place while the
operational edge still names it. The ordered step `0` then `1` remains. -/
theorem recorder_root_does_not_free_embedded_recording :
    let operational := embeddedOperational
    let recorder : Roots (Anchor 1 Unit) Nat := embeddedRecorder
    let forgotten := forgetOptionalRecord embeddedSession carrier
    (Anchor.residual, 0) ∈ operational ∧
      (Anchor.recorder, 1) ∈ recorder ∧
      (1 : Nat) ∉ rootAddresses operational ∧
      (Anchor.recorder, 1) ∉ forgotten.1.roots ∧
      forgotten.1.heap.lookup 1 = (chainHeap 1).lookup 1 ∧
      forgotten.1.heap.lookup 0 = (chainHeap 1).lookup 0 ∧
      walk forgotten.1.heap 0 [1] = some (1, chainCell 1 1) ∧
      forgotten.2.delivery.log.positions 0 = some 0 ∧
      acceptedCount forgotten.2 = 4 := by
  let operational := embeddedOperational
  let recorder : Roots (Anchor 1 Unit) Nat := embeddedRecorder
  let forgotten := forgetOptionalRecord embeddedSession carrier
  have exact : embeddedSession.roots = (operational ∪ recorder) ∪ emptyFrame := rfl
  have notRetained : (1 : Nat) ∉ rootAddresses operational := by
    simp only [operational, embeddedOperational, rootAddresses]
    decide
  obtain ⟨found, edge, _lookup1⟩ := embeddedEdge
  have survived := embedded_recording_survives_recorder_cancellation embeddedSession carrier
    operational recorder emptyFrame 0 1 (chainCell 1 0) exact embeddedKept keptEmpty
    embeddedOnly embeddedHolder found edge
  have rootsEq : forgotten.1.roots = operational ∪ emptyFrame := by
    have reduced : forgotten.1.roots = cancel embeddedSession.roots {Anchor.recorder} := rfl
    rw [reduced, exact, cancel_recorder_leaves_frame operational recorder emptyFrame
      embeddedKept keptEmpty embeddedOnly]
  have dropped : (Anchor.recorder, 1) ∉ forgotten.1.roots := by
    rw [rootsEq, emptyFrame, Finset.union_empty]
    simp only [operational, embeddedOperational]
    decide
  have lookupRecording : forgotten.1.heap.lookup 1 = (chainHeap 1).lookup 1 := by
    rw [survived.2, embeddedSession]
  have liveHolder : Live (chainHeap 1) (operational ∪ emptyFrame) 0 := by
    rw [emptyFrame, Finset.union_empty]
    exact live_of_root (chainHeap 1) operational embeddedHolder (by decide)
  have preservedHolder := forgetOptionalRecord_preserves_live embeddedSession carrier
    operational recorder emptyFrame 0 exact embeddedKept keptEmpty embeddedOnly liveHolder
  have lookupHolder : forgotten.1.heap.lookup 0 = (chainHeap 1).lookup 0 := by
    rw [preservedHolder.2.2.1, embeddedSession]
  have liveCancel : Live (chainHeap 1) (cancel embeddedSession.roots {Anchor.recorder}) 0 := by
    rw [exact, cancel_recorder_leaves_frame operational recorder emptyFrame
      embeddedKept keptEmpty embeddedOnly]
    exact liveHolder
  have ordered : walk forgotten.1.heap 0 [1] = some (1, chainCell 1 1) := by
    have heapEq : forgotten.1.heap =
        collect (chainHeap 1) (cancel embeddedSession.roots {Anchor.recorder}) := rfl
    rw [heapEq, walk_collect (chainHeap 1) (cancel embeddedSession.roots {Anchor.recorder})
      liveCancel [1], embeddedSourceWalk]
  refine ⟨embeddedHolder, ?_, notRetained, dropped, lookupRecording, lookupHolder, ordered, rfl, rfl⟩
  rw [embeddedRecorder]
  exact Finset.mem_singleton.mpr rfl

/-- The receipt-edge precondition is separate from recorder-root cancellation.
Collection then frees the recording, and relocation of that projected heap
does not copy it back. The producer configuration is not relocated. -/
theorem cleared_receipt_is_absent_after_transport :
    receiptFieldCleared clearedHeap (embeddedOperational ∪ emptyFrame) 1 ∧
      (forgetOptionalRecord clearedSession carrier).1.heap.lookup 1 = none ∧
      walk (forgetOptionalRecord clearedSession carrier).1.heap 0 [1] = none ∧
      Equiv.swap (0 : Nat) 1 1 = 0 ∧
      (transportRetained (closeScope clearedSession {Anchor.recorder})
        ((closeScope clearedSession {Anchor.recorder}).heap.relabel (Equiv.swap 0 1) id)
        (Relocation.ofEquiv (closeScope clearedSession {Anchor.recorder}).heap
          (Equiv.swap 0 1) id)).heap.lookup
        ((Relocation.ofEquiv (closeScope clearedSession {Anchor.recorder}).heap
          (Equiv.swap 0 1) id).address 1) = none ∧
      (transportRetained (closeScope clearedSession {Anchor.recorder})
        ((closeScope clearedSession {Anchor.recorder}).heap.relabel (Equiv.swap 0 1) id)
        (Relocation.ofEquiv (closeScope clearedSession {Anchor.recorder}).heap
          (Equiv.swap 0 1) id)).world = clearedSession.world ∧
      (forgetOptionalRecord clearedSession carrier).1.heap.lookup 0 = clearedHeap.lookup 0 := by
  let names := Equiv.swap (0 : Nat) 1
  let retained := closeScope clearedSession {Anchor.recorder}
  let destination := retained.heap.relabel names id
  let copy : Relocation retained.heap destination := Relocation.ofEquiv retained.heap names id
  let transported := transportRetained retained destination copy
  have exact : clearedSession.roots =
      (embeddedOperational ∪ embeddedRecorder) ∪ emptyFrame := rfl
  have clearedFields : receiptFieldCleared clearedHeap (embeddedOperational ∪ emptyFrame) 1 := by
    intro holder _live cell found reference
    simp only [clearedHeap] at found
    split at found
    · cases found
      simp only [clearedCell] at reference
      exact absurd reference (Finset.notMem_empty _)
    · cases found
  have notRoot : (1 : Nat) ∉ rootAddresses (embeddedOperational ∪ emptyFrame) := by
    rw [emptyFrame, Finset.union_empty]
    simp only [embeddedOperational, rootAddresses]
    decide
  have reclaimed := cleared_recording_is_reclaimed clearedSession carrier embeddedOperational
    embeddedRecorder emptyFrame 1 exact embeddedKept keptEmpty embeddedOnly notRoot clearedFields
  have liveHolder : Live clearedHeap (embeddedOperational ∪ emptyFrame) 0 := by
    rw [emptyFrame, Finset.union_empty]
    exact live_of_root clearedHeap embeddedOperational embeddedHolder (by decide)
  have liveCancel : Live clearedHeap (cancel clearedSession.roots {Anchor.recorder}) 0 := by
    rw [exact, cancel_recorder_leaves_frame embeddedOperational embeddedRecorder emptyFrame
      embeddedKept keptEmpty embeddedOnly]
    exact liveHolder
  have lookupHolder : (forgetOptionalRecord clearedSession carrier).1.heap.lookup 0 =
      clearedHeap.lookup 0 := by
    have heapEq : (forgetOptionalRecord clearedSession carrier).1.heap =
        collect clearedHeap (cancel clearedSession.roots {Anchor.recorder}) := rfl
    rw [heapEq]
    exact lookup_collect_of_live clearedHeap (cancel clearedSession.roots {Anchor.recorder})
      liveCancel
  have noStep : walk (forgetOptionalRecord clearedSession carrier).1.heap 0 [1] = none := by
    have lookup0 : (forgetOptionalRecord clearedSession carrier).1.heap.lookup 0 =
        some (clearedCell 0) := by
      rw [lookupHolder]
      simp only [clearedHeap, if_pos (Nat.le_succ 0)]
    simp only [walk, lookup0, Option.bind_some, clearedCell,
      if_neg (Finset.notMem_empty (1 : Nat))]
  have moved : copy.address 1 = 0 := by
    show names 1 = 0
    exact Equiv.swap_apply_right 0 1
  have absentImage : transported.heap.lookup (copy.address 1) = none := by
    have installed : transported.heap = destination := rfl
    rw [installed, copy.lookup_eq 1]
    have same : retained.heap.lookup 1 =
        (forgetOptionalRecord clearedSession carrier).1.heap.lookup 1 := rfl
    rw [same, reclaimed]
    rfl
  refine ⟨clearedFields, reclaimed, noStep, moved, absentImage, ?_, lookupHolder⟩
  exact (transportRetained_square clearedSession destination copy).1

/-- Pending address `0` and the active delivery address `1` are carrier roots.
Swapping those addresses, after recorder cancellation, makes the relocated
roots agree with `copy.roots` of the carrier roots. The configuration is not
rebuilt. -/
def routedDiscovery : Discovery Unit Unit Nat Nat Unit Unit where
  residual := fun _ => []
  pending := fun _ => [0]
  context := fun _ => []
  effect := fun _ => []
  handoff := fun _ => []
  record := fun _ => []

noncomputable def routedSession :
    OwnedLifecycle.Session (Anchor 1 Unit) Nat Nat Nat :=
  ⟨chainHeap 1,
    (anchorRoots routedDiscovery carrier ∪ {(Anchor.recorder, 1)}) ∪ emptyFrame, 0⟩

theorem pending_and_delivery_roots_follow_nonidentity_copy :
    pendingAddresses routedDiscovery carrier = [0] ∧
      requestAddresses routedDiscovery carrier = [] ∧
      carrier.delivery.log.positions 0 = some 0 ∧
      (Anchor.residual, 0) ∈ anchorRoots routedDiscovery carrier ∧
      (Anchor.delivery (Sum.inl 0), 1) ∈ anchorRoots routedDiscovery carrier ∧
      Equiv.swap (0 : Nat) 1 0 = 1 ∧
      Equiv.swap (0 : Nat) 1 1 = 0 ∧
      (transportRetained (closeScope routedSession {Anchor.recorder})
        ((closeScope routedSession {Anchor.recorder}).heap.relabel (Equiv.swap 0 1) id)
        (Relocation.ofEquiv (closeScope routedSession {Anchor.recorder}).heap
          (Equiv.swap 0 1) id)).roots =
        (Relocation.ofEquiv (closeScope routedSession {Anchor.recorder}).heap
          (Equiv.swap 0 1) id).roots (anchorRoots routedDiscovery carrier) ∧
      (Relocation.ofEquiv (closeScope routedSession {Anchor.recorder}).heap
          (Equiv.swap 0 1) id).roots (anchorRoots routedDiscovery carrier) =
        answerRoots Anchor.residual
            ((residualAddresses routedDiscovery carrier).map
              (Equiv.swap (0 : Nat) 1)) ∪
          answerRoots Anchor.residual
            ((pendingAddresses routedDiscovery carrier).map (Equiv.swap (0 : Nat) 1)) ∪
          answerRoots Anchor.context
            ((routedDiscovery.context carrier.context).map (Equiv.swap (0 : Nat) 1)) ∪
          answerRoots Anchor.request
            ((requestAddresses routedDiscovery carrier).map (Equiv.swap (0 : Nat) 1)) ∪
          liftDelivery ((Relocation.ofEquiv (closeScope routedSession {Anchor.recorder}).heap
            (Equiv.swap 0 1) id).roots (SharedOccurrenceOwnership.roots carrier.delivery)) ∧
      (Anchor.residual, 1) ∈
        (transportRetained (closeScope routedSession {Anchor.recorder})
          ((closeScope routedSession {Anchor.recorder}).heap.relabel (Equiv.swap 0 1) id)
          (Relocation.ofEquiv (closeScope routedSession {Anchor.recorder}).heap
            (Equiv.swap 0 1) id)).roots ∧
      (Anchor.delivery (Sum.inl 0), 0) ∈
        (transportRetained (closeScope routedSession {Anchor.recorder})
          ((closeScope routedSession {Anchor.recorder}).heap.relabel (Equiv.swap 0 1) id)
          (Relocation.ofEquiv (closeScope routedSession {Anchor.recorder}).heap
            (Equiv.swap 0 1) id)).roots ∧
      (transportRetained (closeScope routedSession {Anchor.recorder})
        ((closeScope routedSession {Anchor.recorder}).heap.relabel (Equiv.swap 0 1) id)
        (Relocation.ofEquiv (closeScope routedSession {Anchor.recorder}).heap
          (Equiv.swap 0 1) id)).world = routedSession.world := by
  let names := Equiv.swap (0 : Nat) 1
  let retained := closeScope routedSession {Anchor.recorder}
  let destination := retained.heap.relabel names id
  let copy : Relocation retained.heap destination := Relocation.ofEquiv retained.heap names id
  let transported := transportRetained retained destination copy
  have pendingList : pendingAddresses routedDiscovery carrier = [0] := rfl
  have noRequest : requestAddresses routedDiscovery carrier = [] :=
    (requestAddresses_active routedDiscovery () (some ()) 4 0 retainedDelivery).trans rfl
  have cursor : carrier.delivery.log.positions 0 = some 0 := rfl
  have pendingRoot : (Anchor.residual, 0) ∈ anchorRoots routedDiscovery carrier := by
    have member : ((Anchor.residual : Anchor 1 Unit), (0 : Nat)) ∈
        answerRoots (Anchor.residual : Anchor 1 Unit)
          (pendingAddresses routedDiscovery carrier) := by
      rw [pendingList]
      exact (mem_answerRoots (Anchor.residual : Anchor 1 Unit)
        (Anchor.residual : Anchor 1 Unit) [0] 0).mpr ⟨rfl, List.mem_cons_self⟩
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_right _ member)))
  have activeDelivery : (Sum.inl (0 : Fin 1), 1) ∈
      SharedOccurrenceOwnership.roots carrier.delivery := by
    refine Finset.mem_union_left _ ?_
    exact (SharedOccurrenceOwnership.mem_logRoots_consumer carrier.delivery.log 0 1).mpr
      (by decide)
  have deliveryRoot : (Anchor.delivery (Sum.inl 0), 1) ∈ anchorRoots routedDiscovery carrier := by
    refine Finset.mem_union_right _ ?_
    exact Finset.mem_image.mpr ⟨(Sum.inl 0, 1), activeDelivery, rfl⟩
  have zeroToOne : names 0 = 1 := Equiv.swap_apply_left 0 1
  have oneToZero : names 1 = 0 := Equiv.swap_apply_right 0 1
  have exact : routedSession.roots =
      (anchorRoots routedDiscovery carrier ∪ {(Anchor.recorder, 1)}) ∪ emptyFrame := rfl
  have onlyRecorder : ∀ pair ∈ ({(Anchor.recorder, 1)} : Roots (Anchor 1 Unit) Nat),
      pair.1 = Anchor.recorder := by
    intro pair member
    rw [Finset.mem_singleton] at member
    subst member
    rfl
  have retainedRoots : retained.roots = anchorRoots routedDiscovery carrier := by
    have reduced : retained.roots = cancel routedSession.roots {Anchor.recorder} := rfl
    rw [reduced, exact, cancel_recorder_leaves_frame (anchorRoots routedDiscovery carrier)
      {(Anchor.recorder, 1)} emptyFrame (anchorRoots_ne_recorder routedDiscovery carrier)
      keptEmpty onlyRecorder, emptyFrame, Finset.union_empty]
  have rootsImage : transported.roots = copy.roots (anchorRoots routedDiscovery carrier) := by
    have installed : transported.roots = copy.roots retained.roots := rfl
    rw [installed, retainedRoots]
  have agreed := anchorRoots_relocated copy routedDiscovery carrier
  have addressAgreed : copy.address = names := rfl
  have pendingMoved : (Anchor.residual, 1) ∈ transported.roots := by
    rw [rootsImage, agreed, addressAgreed, pendingList]
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_right _
        ((mem_answerRoots _ _ _ _).mpr ⟨rfl, List.mem_map.mpr ⟨0, by simp, zeroToOne⟩⟩))))
  have deliveryMoved : (Anchor.delivery (Sum.inl 0), 0) ∈ transported.roots := by
    rw [rootsImage, agreed, addressAgreed]
    refine Finset.mem_union_right _ ?_
    exact Finset.mem_image.mpr ⟨(Sum.inl (0 : Fin 1), 0),
      Finset.mem_image.mpr ⟨(Sum.inl 0, 1), activeDelivery, Prod.ext rfl oneToZero⟩, rfl⟩
  refine ⟨pendingList, noRequest, cursor, pendingRoot, deliveryRoot, zeroToOne, oneToZero,
    rootsImage, ?_, pendingMoved, deliveryMoved, ?_⟩
  · rw [addressAgreed, show names = Equiv.swap (0 : Nat) 1 from rfl,
      show copy = Relocation.ofEquiv (closeScope routedSession {Anchor.recorder}).heap
        (Equiv.swap (0 : Nat) 1) id from rfl] at agreed
    exact agreed
  · exact (transportRetained_square routedSession destination copy).1

end RecordRetention

end OptionalRecord

theorem ordinary_preserves_context_cursors_publications
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool) (ticks : Nat)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    (ordinary step capture capacity compatible ticks state).context = state.context ∧
      (ordinary step capture capacity compatible ticks state).delivery.log.base =
        state.delivery.log.base ∧
      (ordinary step capture capacity compatible ticks state).delivery.log.positions =
        state.delivery.log.positions ∧
      (ordinary step capture capacity compatible ticks state).delivery.published =
        state.delivery.published := by
  rw [ordinary_agrees_with_recorded_state]
  exact run_preserves_context_cursors_publications step capture capacity compatible ticks state

private theorem ordinary_extends_rows
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool) (ticks : Nat)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    ∃ suffix, (ordinary step capture capacity compatible ticks state).delivery.log.rows =
      state.delivery.log.rows ++ suffix := by
  induction ticks generalizing state with
  | zero => exact ⟨[], by simp [ordinary]⟩
  | succ ticks ih =>
      obtain ⟨suffix, rest⟩ := ih (pump step capture capacity compatible state).2
      refine ⟨admitted (pump step capture capacity compatible state).1 ++ suffix, ?_⟩
      rw [ordinary, rest, pump_rows step capture capacity compatible state, List.append_assoc]

private theorem ordinary_preserves_buffered_answer
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool) (ticks : Nat)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (client : Fin clients) (position : Nat) (value : Stored)
    (answer : SharedOccurrenceLog.peek state.delivery.log client = .answer position value) :
    SharedOccurrenceLog.peek
        (ordinary step capture capacity compatible ticks state).delivery.log client =
      .answer position value := by
  induction ticks generalizing state with
  | zero => simpa [ordinary] using answer
  | succ ticks ih =>
      exact ih (pump step capture capacity compatible state).2
        (pump_preserves_buffered_answer step capture capacity compatible state client
          position value answer)

private theorem stage_after_retirement
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (execution : Execution Producer Borrowed Effect Handoff)
    (outcome : ProducerOutcome Producer Borrowed Effect Handoff) (client : Fin clients) :
    stage (retireConsumer state client) execution outcome =
      ((stage state execution outcome).1,
        retireConsumer (stage state execution outcome).2 client) := by
  cases outcome <;> rfl

private theorem admit_after_retirement
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (execution : Execution Producer Borrowed Effect Handoff) (value : Borrowed)
    (client : Fin clients) :
    admit capture capacity (retireConsumer state client) execution value =
      ((admit capture capacity state execution value).1,
        retireConsumer (admit capture capacity state execution value).2 client) := by
  unfold admit
  cases captured : capture value with
  | none => rfl
  | some stored =>
      simp only
      split
      · by_cases completed : state.delivery.log.completed = true
        · simp [retireConsumer, SharedOccurrenceOwnership.cancelConsumer,
            SharedOccurrenceLog.append, SharedOccurrenceLog.cancel,
            SharedOccurrenceLog.setPosition, completed]
        · by_cases room : state.delivery.log.rows.length < state.delivery.log.limit <;>
            simp [retireConsumer, SharedOccurrenceOwnership.cancelConsumer,
              SharedOccurrenceLog.append, SharedOccurrenceLog.cancel,
              SharedOccurrenceLog.setPosition, SharedOccurrenceLog.pastEnd, completed, room]
      · rfl

/-- While another consumer keeps a cursor, one producer microstep commutes with
retirement. The notice is unchanged, and the retired cursor is not restored. -/
theorem pump_after_retained_demand
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (client other : Fin clients) (position : Nat) (distinct : other ≠ client)
    (live : state.delivery.log.positions other = some position) :
    pump step capture capacity compatible (retireConsumer state client) =
      ((pump step capture capacity compatible state).1,
        retireConsumer (pump step capture capacity compatible state).2 client) := by
  have before := active_consumer_has_demand state.delivery.log other position live
  have after : hasConsumers (retireConsumer state client).delivery.log = true :=
    active_consumer_has_demand _ other position (by
      simpa [retireConsumer, SharedOccurrenceOwnership.cancelConsumer, SharedOccurrenceLog.cancel,
        SharedOccurrenceLog.setPosition_other _ _ _ _ distinct] using live)
  unfold pump
  simp only [show (retireConsumer state client).execution = state.execution from rfl,
    show (retireConsumer state client).context = state.context from rfl,
    show (retireConsumer state client).delivery.log.completed =
      state.delivery.log.completed from rfl,
    show (retireConsumer state client).delivery.log.rows = state.delivery.log.rows from rfl,
    show (retireConsumer state client).delivery.log.limit = state.delivery.log.limit from rfl,
    before, after, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  cases execution : state.execution with
  | none => rfl
  | some producer =>
      simp only
      by_cases current : (!compatible state.context) = true
      · simp only [current, ↓reduceIte]
      · simp only [current, Bool.false_eq_true, ↓reduceIte]
        by_cases completed : state.delivery.log.completed = true
        · simp only [completed, ↓reduceIte]
        · simp only [completed, Bool.false_eq_true, ↓reduceIte]
          cases mode : producer.mode with
          | active =>
              simp only
              by_cases room : state.delivery.log.rows.length < state.delivery.log.limit
              · simp only [room, ↓reduceIte]
                cases pending : producer.pending with
                | none =>
                    exact stage_after_retirement state producer (step producer.producer) client
                | some pendingValue =>
                    exact admit_after_retirement capture capacity state producer pendingValue client
              · simp only [room, ↓reduceIte]
          | effect request => rfl
          | handoff request => rfl
          | interrupted => rfl

/-- The notice list after retiring one of several consumers is the notice list
of that same continuation. The retired cursor is not restored. -/
theorem run_after_retained_demand
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool) (ticks : Nat)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (client other : Fin clients) (position : Nat) (distinct : other ≠ client)
    (live : state.delivery.log.positions other = some position) :
    run step capture capacity compatible ticks (retireConsumer state client) =
      (let recorded := run step capture capacity compatible ticks state
       (recorded.1, retireConsumer recorded.2 client)) := by
  induction ticks generalizing state with
  | zero => rfl
  | succ ticks ih =>
      have preserved := pump_preserves_context_cursors_publications step capture capacity
        compatible state
      have kept := (congrFun preserved.2.2.1 other).trans live
      have first := pump_after_retained_demand step capture capacity compatible state client other
        position distinct live
      have rest := ih (pump step capture capacity compatible state).2 kept
      rw [run, first, run, rest]

/-- Ordinary continuation agrees with retirement after the ordinary slice.
The paid execution, including its accepted count, is that shared configuration's
execution. -/
theorem ordinary_after_retained_demand
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool) (ticks : Nat)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (client other : Fin clients) (position : Nat) (distinct : other ≠ client)
    (live : state.delivery.log.positions other = some position) :
    ordinary step capture capacity compatible ticks (retireConsumer state client) =
      retireConsumer (ordinary step capture capacity compatible ticks state) client := by
  rw [ordinary_agrees_with_recorded_state, ordinary_agrees_with_recorded_state]
  simp only [run_after_retained_demand step capture capacity compatible ticks state
    client other position distinct live]

theorem retained_demand_keeps_paid_execution
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool) (ticks : Nat)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (client other : Fin clients) (position : Nat) (distinct : other ≠ client)
    (live : state.delivery.log.positions other = some position) :
    (ordinary step capture capacity compatible ticks (retireConsumer state client)).execution =
      (ordinary step capture capacity compatible ticks state).execution := by
  rw [ordinary_after_retained_demand step capture capacity compatible ticks state
    client other position distinct live]
  exact (retireConsumer_retains_paid_source
    (ordinary step capture capacity compatible ticks state) client).1

private theorem retire_last_consumer_has_no_demand
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (client : Fin clients)
    (sole : ∀ other, other ≠ client → state.delivery.log.positions other = none) :
    hasConsumers (retireConsumer state client).delivery.log = false := by
  have stopped : ¬ hasConsumers (retireConsumer state client).delivery.log = true := by
    intro live
    unfold hasConsumers at live
    obtain ⟨other, _, cursor⟩ := List.any_eq_true.mp live
    by_cases same : other = client
    · subst other
      simp [retireConsumer, SharedOccurrenceOwnership.cancelConsumer, SharedOccurrenceLog.cancel,
        SharedOccurrenceLog.setPosition] at cursor
    · simp [retireConsumer, SharedOccurrenceOwnership.cancelConsumer, SharedOccurrenceLog.cancel,
        SharedOccurrenceLog.setPosition_other _ _ _ _ same, sole other same] at cursor
  simpa [Bool.not_eq_true] using stopped

/-- Retiring the last consumer leaves no producer demand. The microstep does
not append a row and does not change the paid execution. -/
theorem retire_last_consumer_stops
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (client : Fin clients) (execution : Execution Producer Borrowed Effect Handoff)
    (sole : ∀ other, other ≠ client → state.delivery.log.positions other = none)
    (attached : state.execution = some execution)
    (allowed : compatible state.context = true)
    (openLog : state.delivery.log.completed = false)
    (active : execution.mode = .active) :
    pump step capture capacity compatible (retireConsumer state client) =
      (.noConsumers, retireConsumer state client) := by
  have undemanded := retire_last_consumer_has_no_demand state client sole
  have attached' : (retireConsumer state client).execution = some execution := by
    rw [(retireConsumer_retains_paid_source state client).1, attached]
  have allowed' : compatible (retireConsumer state client).context = true := by
    rw [(retireConsumer_retains_paid_source state client).2.1, allowed]
  have openLog' : (retireConsumer state client).delivery.log.completed = false := by
    simpa [retireConsumer, SharedOccurrenceOwnership.cancelConsumer, SharedOccurrenceLog.cancel,
      SharedOccurrenceLog.setPosition] using openLog
  exact no_demand_preserves_complete_residual step capture capacity compatible
    (retireConsumer state client) execution attached' allowed' openLog' active undemanded

/-- After the last consumer is retired, ordinary execution stays at that
boundary. Production does not continue, and the retired cursor is not restored. -/
theorem ordinary_after_sole_retirement_stays
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool) (ticks : Nat)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (client : Fin clients) (execution : Execution Producer Borrowed Effect Handoff)
    (sole : ∀ other, other ≠ client → state.delivery.log.positions other = none)
    (attached : state.execution = some execution)
    (allowed : compatible state.context = true)
    (openLog : state.delivery.log.completed = false)
    (active : execution.mode = .active) :
    ordinary step capture capacity compatible ticks (retireConsumer state client) =
      retireConsumer state client := by
  induction ticks with
  | zero => rfl
  | succ ticks ih =>
      rw [ordinary, retire_last_consumer_stops step capture capacity compatible state client
        execution sole attached allowed openLog active, ih]

/-- The notice list after retiring the last consumer is one `noConsumers` notice
per requested microstep. It does not restore that consumer's former cursor. -/
theorem recorded_after_sole_retirement
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool) (ticks : Nat)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (client : Fin clients) (execution : Execution Producer Borrowed Effect Handoff)
    (sole : ∀ other, other ≠ client → state.delivery.log.positions other = none)
    (attached : state.execution = some execution)
    (allowed : compatible state.context = true)
    (openLog : state.delivery.log.completed = false)
    (active : execution.mode = .active) :
    run step capture capacity compatible ticks (retireConsumer state client) =
      (List.replicate ticks .noConsumers, retireConsumer state client) := by
  induction ticks with
  | zero => simp [run]
  | succ ticks ih =>
      rw [run, retire_last_consumer_stops step capture capacity compatible state client
        execution sole attached allowed openLog active, ih, List.replicate_succ]

/-- Retirement cancels only that consumer's cursor. Context, caller publications
and every other cursor stay. A remaining answer stays that answer. A remaining
cursor's unread suffix gains exactly the rows produced afterwards, and the
retired cursor stays empty. This is log cancellation, not erasure of a
recording prefix. -/
theorem ordinary_after_retirement_keeps_other_cursors
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool) (ticks : Nat)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (client : Fin clients) (valid : SharedOccurrenceLog.Valid state.delivery.log) :
    (ordinary step capture capacity compatible ticks (retireConsumer state client)).context =
        state.context ∧
      (ordinary step capture capacity compatible ticks
        (retireConsumer state client)).delivery.published = state.delivery.published ∧
      (ordinary step capture capacity compatible ticks
        (retireConsumer state client)).delivery.log.positions client = none ∧
      SharedOccurrenceLog.unread (ordinary step capture capacity compatible ticks
        (retireConsumer state client)).delivery.log client = [] ∧
      SharedOccurrenceLog.peek (ordinary step capture capacity compatible ticks
        (retireConsumer state client)).delivery.log client = .cancelled ∧
      ∀ other, other ≠ client →
        (ordinary step capture capacity compatible ticks
          (retireConsumer state client)).delivery.log.positions other =
          state.delivery.log.positions other ∧
        (∀ position value,
          SharedOccurrenceLog.peek state.delivery.log other = .answer position value →
            SharedOccurrenceLog.peek (ordinary step capture capacity compatible ticks
              (retireConsumer state client)).delivery.log other = .answer position value) ∧
        (match state.delivery.log.positions other with
          | none =>
              SharedOccurrenceLog.unread (ordinary step capture capacity compatible ticks
                (retireConsumer state client)).delivery.log other = []
          | some _ =>
              SharedOccurrenceLog.unread (ordinary step capture capacity compatible ticks
                (retireConsumer state client)).delivery.log other =
                SharedOccurrenceLog.unread state.delivery.log other ++
                  (ordinary step capture capacity compatible ticks
                    (retireConsumer state client)).delivery.log.rows.drop
                    state.delivery.log.rows.length) := by
  have preserved := ordinary_preserves_context_cursors_publications step capture capacity
    compatible ticks (retireConsumer state client)
  have retired := retireConsumer_retains_paid_source state client
  have clientNone : (ordinary step capture capacity compatible ticks
      (retireConsumer state client)).delivery.log.positions client = none := by
    rw [congrFun preserved.2.2.1 client]
    simp [retireConsumer, SharedOccurrenceOwnership.cancelConsumer, SharedOccurrenceLog.cancel,
      SharedOccurrenceLog.setPosition]
  refine ⟨preserved.1.trans retired.2.1, preserved.2.2.2.trans retired.2.2, clientNone, ?_, ?_, ?_⟩
  · simp [SharedOccurrenceLog.unread, clientNone]
  · simp [SharedOccurrenceLog.peek, clientNone]
  · intro other distinct
    have positionsLater := congrFun preserved.2.2.1 other
    have positionsRetired : (retireConsumer state client).delivery.log.positions other =
        state.delivery.log.positions other := by
      simpa [retireConsumer, SharedOccurrenceOwnership.cancelConsumer, SharedOccurrenceLog.cancel]
        using SharedOccurrenceLog.setPosition_other state.delivery.log client other none distinct
    refine ⟨positionsLater.trans positionsRetired, ?_, ?_⟩
    · intro position value answer
      have atRetired : SharedOccurrenceLog.peek
          (retireConsumer state client).delivery.log other = .answer position value := by
        simpa [retireConsumer, SharedOccurrenceOwnership.cancelConsumer] using
          (SharedOccurrenceLog.cancel_preserves_other state.delivery.log client other
            distinct).trans answer
      exact ordinary_preserves_buffered_answer step capture capacity compatible ticks
        (retireConsumer state client) other position value atRetired
    · cases cursor : state.delivery.log.positions other with
      | none =>
          have laterNone : (ordinary step capture capacity compatible ticks
              (retireConsumer state client)).delivery.log.positions other = none := by
            rw [positionsLater, positionsRetired, cursor]
          simp [SharedOccurrenceLog.unread, laterNone]
      | some position =>
          obtain ⟨_, upper⟩ := valid.2 other position cursor
          have indexBound : position - state.delivery.log.base ≤
              state.delivery.log.rows.length := by
            simp only [SharedOccurrenceLog.pastEnd] at upper
            omega
          obtain ⟨suffix, extended⟩ := ordinary_extends_rows step capture capacity compatible
            ticks (retireConsumer state client)
          have retireRows : (retireConsumer state client).delivery.log.rows =
              state.delivery.log.rows := rfl
          have laterBase := preserved.2.1
          have retireBase : (retireConsumer state client).delivery.log.base =
              state.delivery.log.base := rfl
          have laterCursor : (ordinary step capture capacity compatible ticks
              (retireConsumer state client)).delivery.log.positions other = some position := by
            rw [positionsLater, positionsRetired, cursor]
          have unreadLater : SharedOccurrenceLog.unread (ordinary step capture capacity compatible
              ticks (retireConsumer state client)).delivery.log other =
              (state.delivery.log.rows ++ suffix).drop
                (position - state.delivery.log.base) := by
            rw [SharedOccurrenceLog.unread, laterCursor, laterBase, retireBase, extended, retireRows]
          have unreadOld : SharedOccurrenceLog.unread state.delivery.log other =
              state.delivery.log.rows.drop (position - state.delivery.log.base) := by
            simp only [SharedOccurrenceLog.unread, cursor]
          have suffixEq : suffix = (ordinary step capture capacity compatible ticks
              (retireConsumer state client)).delivery.log.rows.drop
                state.delivery.log.rows.length := by
            rw [extended, retireRows, drop_append_suffix _ _ _ (Nat.le_refl _), drop_length]
            rfl
          rw [unreadLater, drop_append_suffix _ _ _ indexBound, unreadOld, suffixEq]

private theorem stage_bufferedUpdate [DecidableEq Stored] [DecidableEq Output]
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (execution : Execution Producer Borrowed Effect Handoff)
    (outcome : ProducerOutcome Producer Borrowed Effect Handoff)
    (client : Fin clients) (output : Output) (position : Nat) (value : Stored) :
    stage (bufferedUpdate state client output position value) execution outcome =
      ((stage state execution outcome).1,
        bufferedUpdate (stage state execution outcome).2 client output position value) := by
  cases outcome <;> rfl

private theorem admit_bufferedUpdate [DecidableEq Stored] [DecidableEq Output]
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (execution : Execution Producer Borrowed Effect Handoff) (pendingValue : Borrowed)
    (client : Fin clients) (output : Output) (position : Nat) (value : Stored) :
    admit capture capacity (bufferedUpdate state client output position value) execution pendingValue =
      ((admit capture capacity state execution pendingValue).1,
        bufferedUpdate (admit capture capacity state execution pendingValue).2
          client output position value) := by
  unfold admit
  cases captured : capture pendingValue with
  | none => rfl
  | some stored =>
      simp only
      split
      · by_cases completed : state.delivery.log.completed = true
        · simp [bufferedUpdate, SharedOccurrenceLog.append, SharedOccurrenceLog.setPosition,
            completed]
        · by_cases room : state.delivery.log.rows.length < state.delivery.log.limit <;>
            simp [bufferedUpdate, SharedOccurrenceLog.append, SharedOccurrenceLog.setPosition,
              SharedOccurrenceLog.pastEnd, completed, room]
      · rfl

private theorem pump_bufferedUpdate [DecidableEq Stored] [DecidableEq Output]
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (client : Fin clients) (output : Output) (position : Nat) (value : Stored)
    (active : state.delivery.log.positions client = some position) :
    pump step capture capacity compatible (bufferedUpdate state client output position value) =
      ((pump step capture capacity compatible state).1,
        bufferedUpdate (pump step capture capacity compatible state).2
          client output position value) := by
  have before := active_consumer_has_demand state.delivery.log client position active
  have after : hasConsumers
      (bufferedUpdate state client output position value).delivery.log = true :=
    active_consumer_has_demand _ client (position + 1) (by simp [bufferedUpdate])
  unfold pump
  simp only [show (bufferedUpdate state client output position value).execution =
      state.execution from rfl,
    show (bufferedUpdate state client output position value).context = state.context from rfl,
    show (bufferedUpdate state client output position value).delivery.log.completed =
      state.delivery.log.completed from rfl,
    show (bufferedUpdate state client output position value).delivery.log.rows =
      state.delivery.log.rows from rfl,
    show (bufferedUpdate state client output position value).delivery.log.limit =
      state.delivery.log.limit from rfl,
    before, after, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  cases execution : state.execution with
  | none => rfl
  | some producer =>
      simp only
      by_cases current : (!compatible state.context) = true
      · simp only [current, ↓reduceIte]
      · simp only [current, Bool.false_eq_true, ↓reduceIte]
        by_cases completed : state.delivery.log.completed = true
        · simp only [completed, ↓reduceIte]
        · simp only [completed, Bool.false_eq_true, ↓reduceIte]
          cases mode : producer.mode with
          | active =>
              simp only
              by_cases room : state.delivery.log.rows.length < state.delivery.log.limit
              · simp only [room, ↓reduceIte]
                cases pending : producer.pending with
                | none =>
                    exact stage_bufferedUpdate state producer (step producer.producer)
                      client output position value
                | some pendingValue =>
                    exact admit_bufferedUpdate capture capacity state producer
                      pendingValue client output position value
              · simp only [room, ↓reduceIte]
          | effect request => rfl
          | handoff request => rfl
          | interrupted => rfl

/-- A producer microstep commutes with delivery of an existing buffered
occurrence. Both replies, the exact producer residual and every published
caller root agree. This is an atomic-operation law; native interleaved memory
access, concurrent capture and source revalidation remain obligations. -/
theorem pump_deliver_buffered_commute [DecidableEq Stored] [DecidableEq Output]
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (client : Fin clients) (output : Output) (position : Nat) (value : Stored)
    (answer : SharedOccurrenceLog.peek state.delivery.log client = .answer position value) :
    (let produced := pump step capture capacity compatible state
     let consumed := deliver compatible produced.2 client output
     (produced.1, consumed.1, consumed.2)) =
      (let consumed := deliver compatible state client output
       let produced := pump step capture capacity compatible consumed.2
       (produced.1, consumed.1, produced.2)) := by
  have metadata := pump_preserves_context_cursors_publications step capture capacity compatible state
  by_cases current : compatible state.context = true
  · have buffered := pump_preserves_buffered_answer step capture capacity compatible
      state client position value answer
    have active := (SharedOccurrenceLog.answer_within state.delivery.log client position value answer).1
    have commute := pump_bufferedUpdate step capture capacity compatible state
      client output position value active
    simp only [deliver, metadata.1, current, ↓reduceIte,
      SharedOccurrenceOwnership.advance_answer _ client output position value buffered,
      SharedOccurrenceOwnership.advance_answer _ client output position value answer]
    change _ = ((pump step capture capacity compatible
      (bufferedUpdate state client output position value)).1,
      DeliveryReply.observed (.answer position value),
      (pump step capture capacity compatible (bufferedUpdate state client output position value)).2)
    rw [commute]
    simp only [bufferedUpdate, metadata.1]
  · simp [deliver, metadata.1, current]

/-- Any finite producer slice can overlap one already available delivery.
Ordered producer notices and the complete owned state agree, so every debit
derived from those notices agrees as well. No waiting read is reordered. -/
theorem run_deliver_buffered_commute [DecidableEq Stored] [DecidableEq Output]
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool) (ticks : Nat)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (client : Fin clients) (output : Output) (position : Nat) (value : Stored)
    (answer : SharedOccurrenceLog.peek state.delivery.log client = .answer position value) :
    (let produced := run step capture capacity compatible ticks state
     let consumed := deliver compatible produced.2 client output
     (produced.1, consumed.1, consumed.2)) =
      (let consumed := deliver compatible state client output
       let produced := run step capture capacity compatible ticks consumed.2
       (produced.1, consumed.1, produced.2)) := by
  induction ticks generalizing state with
  | zero => rfl
  | succ ticks ih =>
      have nextAnswer := pump_preserves_buffered_answer step capture capacity compatible
        state client position value answer
      have first := pump_deliver_buffered_commute step capture capacity compatible
        state client output position value answer
      have rest := ih (pump step capture capacity compatible state).2 nextAnswer
      have notice := congrArg Prod.fst first
      have delivery := congrArg (fun result => result.2.1) first
      have residual := congrArg (fun result => result.2.2) first
      simp only [run]
      change _ = _
      simp only at notice delivery residual rest
      rw [← notice, ← residual]
      have extended := congrArg
        (fun result : List (Notice Borrowed Stored Effect Handoff) ×
            DeliveryReply Stored ×
            Configuration Producer Borrowed Stored Context Output Effect Handoff clients =>
          ((pump step capture capacity compatible state).1 :: result.1, result.2)) rest
      simpa only [delivery] using extended

/-- Each consumer of a fresh cohort sees the same admitted occurrence sequence
at its own position. The producer path and capture conservation qualify that
sequence separately; cursor sharing is not substituted for independent choice. -/
theorem fresh_consumer_observes_admitted_order [DecidableEq Stored] [DecidableEq Output]
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool) (ticks budget : Nat) (producer : Producer)
    (context : Context) (limit : Nat) (client : Fin clients) (output : Output) :
    let start := initial (Borrowed := Borrowed) (Stored := Stored) (Output := Output)
      (Effect := Effect) (Handoff := Handoff) (clients := clients) producer context limit
    let result := run step capture capacity compatible ticks start
    (SharedOccurrenceOwnership.observe budget result.2.delivery client output).1 =
      (SharedOccurrenceLog.numberFrom 0 (result.1.flatMap admitted)).take budget := by
  dsimp only
  let start := initial (Borrowed := Borrowed) (Stored := Stored) (Output := Output)
    (Effect := Effect) (Handoff := Handoff) (clients := clients) producer context limit
  let result := run step capture capacity compatible ticks start
  have same := run_preserves_context_cursors_publications step capture capacity compatible ticks start
  have cursor : result.2.delivery.log.positions client = some 0 := by
    rw [same.2.2.1]
    rfl
  have base : result.2.delivery.log.base = 0 := same.2.1
  have rows : result.2.delivery.log.rows = result.1.flatMap admitted := by
    simpa only [start, result, initial, SharedOccurrenceLog.initial, List.nil_append] using
      run_rows step capture capacity compatible ticks start
  rw [(SharedOccurrenceOwnership.observe_log budget result.2.delivery client output).1]
  rw [(SharedOccurrenceLog.drain_spec budget result.2.delivery.log client 0 cursor (by omega)).1]
  simp [base, rows, result, start]

private theorem stage_log_valid
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (execution : Execution Producer Borrowed Effect Handoff)
    (outcome : ProducerOutcome Producer Borrowed Effect Handoff)
    (valid : SharedOccurrenceLog.Valid state.delivery.log) :
    SharedOccurrenceLog.Valid (stage state execution outcome).2.delivery.log := by
  cases outcome <;> exact valid

private theorem admit_log_valid (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (execution : Execution Producer Borrowed Effect Handoff) (value : Borrowed)
    (valid : SharedOccurrenceLog.Valid state.delivery.log) :
    SharedOccurrenceLog.Valid (admit capture capacity state execution value).2.delivery.log := by
  unfold admit
  cases capture value with
  | none => exact valid
  | some stored =>
      simp only
      split
      · cases appended : SharedOccurrenceLog.append state.delivery.log stored with
        | mk admission log =>
            have nextValid := SharedOccurrenceLog.append_valid state.delivery.log stored valid
            rw [appended] at nextValid
            cases admission with
            | accepted => exact nextValid
            | backpressure => exact valid
            | completed => exact valid
      · exact valid

theorem pump_log_valid
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (valid : SharedOccurrenceLog.Valid state.delivery.log) :
    SharedOccurrenceLog.Valid (pump step capture capacity compatible state).2.delivery.log := by
  unfold pump
  cases state.execution with
  | none => exact valid
  | some execution =>
      simp only
      split
      · exact valid
      · split
        · exact valid
        · cases execution.mode with
          | active =>
              simp only
              split
              · exact valid
              · split
                · cases execution.pending with
                  | none => exact stage_log_valid state execution (step execution.producer) valid
                  | some value => exact admit_log_valid capture capacity state execution value valid
                · exact valid
          | effect request => exact valid
          | handoff request => exact valid
          | interrupted => exact valid

theorem run_log_valid
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool) (ticks : Nat)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (valid : SharedOccurrenceLog.Valid state.delivery.log) :
    SharedOccurrenceLog.Valid (run step capture capacity compatible ticks state).2.delivery.log := by
  induction ticks generalizing state with
  | zero => exact valid
  | succ ticks ih =>
      exact ih _ (pump_log_valid step capture capacity compatible state valid)

theorem guarded_delivery_wellFormed [DecidableEq Stored] [DecidableEq Output]
    {Value : Type} (heap : ResourceOwnership.Heap Stored Value) (compatible : Context → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (client : Fin clients) (output : Output)
    (valid : SharedOccurrenceOwnership.WellFormed heap state.delivery) :
    SharedOccurrenceOwnership.WellFormed heap (deliver compatible state client output).2.delivery := by
  unfold deliver
  split
  · exact SharedOccurrenceOwnership.advance_wellFormed heap state.delivery client output valid
  · exact valid

/-- Successful log admission advances the accepted-return counter exactly
once. Capture retries and all refusal/barrier cases leave it unchanged. -/
theorem pump_accepted_count
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    acceptedCount (pump step capture capacity compatible state).2 = acceptedCount state +
      (admitted (pump step capture capacity compatible state).1).length := by
  unfold pump
  cases attached : state.execution with
  | none => simp [admitted]
  | some execution =>
      simp only
      split
      · simp [admitted]
      · split
        · simp [admitted]
        · cases execution.mode with
          | active =>
              simp only
              split
              · simp [admitted]
              · split
                · cases execution.pending with
                  | none =>
                      cases step execution.producer <;>
                        simp [stage, admitted, acceptedCount, attached]
                  | some value =>
                      unfold admit
                      cases captured : capture value with
                      | none => simp [captured, admitted]
                      | some stored =>
                          simp only [captured]
                          split
                          · by_cases closed : state.delivery.log.completed = true
                            · simp [SharedOccurrenceLog.append, closed, admitted]
                            · by_cases room : state.delivery.log.rows.length < state.delivery.log.limit <;>
                                simp [SharedOccurrenceLog.append, closed, room, admitted, acceptedCount, attached]
                          · simp [admitted]
                · simp [admitted]
          | effect request => simp [admitted]
          | handoff request => simp [admitted]
          | interrupted => simp [admitted]

theorem run_accepted_count
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool) (ticks : Nat)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    acceptedCount (run step capture capacity compatible ticks state).2 = acceptedCount state +
      ((run step capture capacity compatible ticks state).1.flatMap admitted).length := by
  induction ticks generalizing state with
  | zero => simp [run]
  | succ ticks ih =>
      simp only [run]
      rw [ih, pump_accepted_count]
      simp [Nat.add_assoc]

section ProducerTransport

variable {OtherProducer : Type}

/-- Change only the suspended producer representation. Return occurrences and
retained requests keep their original carriers. -/
def ProducerOutcome.mapProducer (f : Producer → OtherProducer) :
    ProducerOutcome Producer Borrowed Effect Handoff →
      ProducerOutcome OtherProducer Borrowed Effect Handoff
  | .progress next => .progress (f next)
  | .returned value next => .returned value (f next)
  | .yielded next => .yielded (f next)
  | .effect request next => .effect request (f next)
  | .handoff request next => .handoff request (f next)
  | .interrupted next => .interrupted (f next)
  | .completed next => .completed (f next)

def Execution.mapProducer (f : Producer → OtherProducer)
    (execution : Execution Producer Borrowed Effect Handoff) :
    Execution OtherProducer Borrowed Effect Handoff :=
  ⟨f execution.producer, execution.pending, execution.accepted, execution.mode⟩

/-- Pending capture, public cursor positions and published roots are outside
the producer representation. A transport does not reset or re-create them. -/
def mapProducer (f : Producer → OtherProducer)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    Configuration OtherProducer Borrowed Stored Context Output Effect Handoff clients :=
  ⟨state.execution.map (Execution.mapProducer f), state.context, state.delivery⟩

private theorem stage_mapProducer (f : Producer → OtherProducer)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (execution : Execution Producer Borrowed Effect Handoff)
    (outcome : ProducerOutcome Producer Borrowed Effect Handoff) :
    stage (mapProducer f state) (execution.mapProducer f) (outcome.mapProducer f) =
      ((stage state execution outcome).1, mapProducer f (stage state execution outcome).2) := by
  cases outcome <;> simp [stage, mapProducer, Execution.mapProducer, ProducerOutcome.mapProducer]

private theorem admit_mapProducer (f : Producer → OtherProducer)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (execution : Execution Producer Borrowed Effect Handoff) (value : Borrowed) :
    admit capture capacity (mapProducer f state) (execution.mapProducer f) value =
      ((admit capture capacity state execution value).1,
        mapProducer f (admit capture capacity state execution value).2) := by
  unfold admit
  cases captured : capture value with
  | none => rfl
  | some stored =>
      simp only [mapProducer]
      split
      · cases SharedOccurrenceLog.append state.delivery.log stored with
        | mk notice log => cases notice <;> rfl
      · rfl

/-- A concrete producer step square lifts to the entire pending/publication
composition. Capture and capacity are checked on the same retained row. -/
theorem pump_mapProducer (f : Producer → OtherProducer)
    (sourceStep : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (targetStep : OtherProducer → ProducerOutcome OtherProducer Borrowed Effect Handoff)
    (stepSquare : ∀ producer, targetStep (f producer) = (sourceStep producer).mapProducer f)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    pump targetStep capture capacity compatible (mapProducer f state) =
      ((pump sourceStep capture capacity compatible state).1,
        mapProducer f (pump sourceStep capture capacity compatible state).2) := by
  rcases state with ⟨attached, context, delivery⟩
  cases attached with
  | none => rfl
  | some execution =>
      rcases execution with ⟨producer, staged, accepted, mode⟩
      simp only [pump, mapProducer, Option.map_some, Execution.mapProducer]
      by_cases denied : (!compatible context) = true
      · simp [denied, Execution.mapProducer]
      · simp only [denied]
        by_cases closed : delivery.log.completed = true
        · simp [closed, Execution.mapProducer]
        · simp only [closed]
          cases mode with
          | active =>
              simp only
              by_cases absent : (!hasConsumers delivery.log) = true
              · simp [absent, Execution.mapProducer]
              · simp only [absent]
                by_cases room : delivery.log.rows.length < delivery.log.limit
                · simp only [room, if_true]
                  cases staged with
                  | none =>
                      simp only
                      rw [stepSquare]
                      exact stage_mapProducer f ⟨some ⟨producer, none, accepted, .active⟩,
                        context, delivery⟩ ⟨producer, none, accepted, .active⟩ (sourceStep producer)
                  | some value =>
                      exact admit_mapProducer f capture capacity
                        ⟨some ⟨producer, some value, accepted, .active⟩, context, delivery⟩
                        ⟨producer, some value, accepted, .active⟩ value
                · simp [room, Execution.mapProducer]
          | effect request => rfl
          | handoff request => rfl
          | interrupted => rfl

/-- Ordered notices, the pending return, accepted cursor, source context,
consumer positions and published roots survive finite run/resume transport. -/
theorem run_mapProducer (f : Producer → OtherProducer)
    (sourceStep : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (targetStep : OtherProducer → ProducerOutcome OtherProducer Borrowed Effect Handoff)
    (stepSquare : ∀ producer, targetStep (f producer) = (sourceStep producer).mapProducer f)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool) (ticks : Nat)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    run targetStep capture capacity compatible ticks (mapProducer f state) =
      ((run sourceStep capture capacity compatible ticks state).1,
        mapProducer f (run sourceStep capture capacity compatible ticks state).2) := by
  induction ticks generalizing state with
  | zero => rfl
  | succ ticks ih =>
      simp only [run, pump_mapProducer f sourceStep targetStep stepSquare]
      rw [ih]

theorem deliver_mapProducer [DecidableEq Stored] [DecidableEq Output]
    (f : Producer → OtherProducer) (compatible : Context → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (client : Fin clients) (output : Output) :
    deliver compatible (mapProducer f state) client output =
      ((deliver compatible state client output).1,
        mapProducer f (deliver compatible state client output).2) := by
  unfold deliver
  simp only [mapProducer]
  split <;> simp_all

end ProducerTransport

/-! ## Carrier transport

`mapCarriers` sends the execution, pending return, captured context, current
mode request and delivery through the existing log and publication maps.
`mapProducer` remains the producer-only case. Step, capture, capacity and
context laws are local service hypotheses. Discovery naturality is local to
the supplied address extractors. Neither is a native scanner, and neither
projects receipt fields.
-/

section CarrierTransport

variable {Producer' Borrowed' Stored' Context' Effect' Handoff' : Type}

def Mode.map (mapEffect : Effect → Effect') (mapHandoff : Handoff → Handoff') :
    Mode Effect Handoff → Mode Effect' Handoff'
  | .active => .active
  | .effect request => .effect (mapEffect request)
  | .handoff request => .handoff (mapHandoff request)
  | .interrupted => .interrupted

/-- Payload part of an outcome map, after `ProducerOutcome.mapProducer` has
moved the producer. -/
def ProducerOutcome.mapPayloads {Here : Type} (mapBorrowed : Borrowed → Borrowed')
    (mapEffect : Effect → Effect') (mapHandoff : Handoff → Handoff') :
    ProducerOutcome Here Borrowed Effect Handoff →
      ProducerOutcome Here Borrowed' Effect' Handoff'
  | .progress next => .progress next
  | .returned value next => .returned (mapBorrowed value) next
  | .yielded next => .yielded next
  | .effect request next => .effect (mapEffect request) next
  | .handoff request next => .handoff (mapHandoff request) next
  | .interrupted next => .interrupted next
  | .completed next => .completed next

def ProducerOutcome.mapCarriers (mapProducerFn : Producer → Producer')
    (mapBorrowed : Borrowed → Borrowed') (mapEffect : Effect → Effect')
    (mapHandoff : Handoff → Handoff')
    (outcome : ProducerOutcome Producer Borrowed Effect Handoff) :
    ProducerOutcome Producer' Borrowed' Effect' Handoff' :=
  (outcome.mapProducer mapProducerFn).mapPayloads mapBorrowed mapEffect mapHandoff

/-- Producer transport, then the pending return and the current request. -/
def Execution.mapCarriers (mapProducerFn : Producer → Producer')
    (mapBorrowed : Borrowed → Borrowed') (mapEffect : Effect → Effect')
    (mapHandoff : Handoff → Handoff')
    (execution : Execution Producer Borrowed Effect Handoff) :
    Execution Producer' Borrowed' Effect' Handoff' :=
  let moved := execution.mapProducer mapProducerFn
  ⟨moved.producer, moved.pending.map mapBorrowed, moved.accepted,
    moved.mode.map mapEffect mapHandoff⟩

def Notice.mapCarriers (mapBorrowed : Borrowed → Borrowed') (mapStored : Stored → Stored')
    (mapEffect : Effect → Effect') (mapHandoff : Handoff → Handoff') :
    Notice Borrowed Stored Effect Handoff → Notice Borrowed' Stored' Effect' Handoff'
  | .progress => .progress
  | .returned value => .returned (mapBorrowed value)
  | .admitted position value => .admitted position (mapStored value)
  | .captureRefused => .captureRefused
  | .admissionRefused => .admissionRefused
  | .noConsumers => .noConsumers
  | .backpressure => .backpressure
  | .contextRefused => .contextRefused
  | .yielded => .yielded
  | .effect request => .effect (mapEffect request)
  | .handoff request => .handoff (mapHandoff request)
  | .interrupted => .interrupted
  | .completed => .completed
  | .detached => .detached

/-- Map the producer, pending return, context, current request and delivery.
Positions and the accepted count are copied. This does not clear receipt
fields and does not read compiled source. -/
def mapCarriers [DecidableEq Output] [DecidableEq Stored']
    (mapProducerFn : Producer → Producer') (mapBorrowed : Borrowed → Borrowed')
    (mapStored : Stored → Stored') (mapContext : Context → Context')
    (mapEffect : Effect → Effect') (mapHandoff : Handoff → Handoff')
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    Configuration Producer' Borrowed' Stored' Context' Output Effect' Handoff' clients :=
  ⟨state.execution.map
      (Execution.mapCarriers mapProducerFn mapBorrowed mapEffect mapHandoff),
    mapContext state.context, state.delivery.map mapStored⟩

theorem mapCarriers_positions [DecidableEq Output] [DecidableEq Stored']
    (mapProducerFn : Producer → Producer') (mapBorrowed : Borrowed → Borrowed')
    (mapStored : Stored → Stored') (mapContext : Context → Context')
    (mapEffect : Effect → Effect') (mapHandoff : Handoff → Handoff')
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    (mapCarriers mapProducerFn mapBorrowed mapStored mapContext mapEffect mapHandoff
      state).delivery.log.positions = state.delivery.log.positions := rfl

theorem mapCarriers_acceptedCount [DecidableEq Output] [DecidableEq Stored']
    (mapProducerFn : Producer → Producer') (mapBorrowed : Borrowed → Borrowed')
    (mapStored : Stored → Stored') (mapContext : Context → Context')
    (mapEffect : Effect → Effect') (mapHandoff : Handoff → Handoff')
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    acceptedCount (mapCarriers mapProducerFn mapBorrowed mapStored mapContext mapEffect
      mapHandoff state) = acceptedCount state := by
  cases state with
  | mk execution _ _ =>
      cases execution with
      | none => rfl
      | some execution => cases execution; rfl

/-- `mapProducer` is the carrier map that leaves pending, context, requests
and delivery values in place. -/
theorem mapProducer_eq_mapCarriers [DecidableEq Stored] [DecidableEq Output]
    {OtherProducer : Type} (f : Producer → OtherProducer)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    mapProducer f state = mapCarriers f id id id id id state := by
  cases state with
  | mk execution context delivery =>
      cases execution with
      | none =>
          simp [mapProducer, mapCarriers, SharedOccurrenceOwnership.map_id]
      | some execution =>
          cases execution with
          | mk producer pending accepted mode =>
              cases pending <;> cases mode <;>
                simp [mapProducer, mapCarriers, Execution.mapProducer, Execution.mapCarriers,
                  Mode.map, SharedOccurrenceOwnership.map_id]

/-- The target extractors read the mapped producer, pending return, context
and current request. This is a hypothesis on those functions, not a scan of
compiled layouts. -/
structure DiscoveryNatural
    (source : Discovery Producer Borrowed Stored Context Effect Handoff)
    (target : Discovery Producer' Borrowed' Stored' Context' Effect' Handoff')
    (mapProducerFn : Producer → Producer') (mapBorrowed : Borrowed → Borrowed')
    (mapStored : Stored → Stored') (mapContext : Context → Context')
    (mapEffect : Effect → Effect') (mapHandoff : Handoff → Handoff') : Prop where
  residual : ∀ producer, target.residual (mapProducerFn producer) =
    (source.residual producer).map mapStored
  pending : ∀ value, target.pending (mapBorrowed value) =
    (source.pending value).map mapStored
  context : ∀ context, target.context (mapContext context) =
    (source.context context).map mapStored
  effect : ∀ request, target.effect (mapEffect request) =
    (source.effect request).map mapStored
  handoff : ∀ request, target.handoff (mapHandoff request) =
    (source.handoff request).map mapStored

theorem residualAddresses_mapCarriers [DecidableEq Output] [DecidableEq Stored']
    (source : Discovery Producer Borrowed Stored Context Effect Handoff)
    (target : Discovery Producer' Borrowed' Stored' Context' Effect' Handoff')
    (mapProducerFn : Producer → Producer') (mapBorrowed : Borrowed → Borrowed')
    (mapStored : Stored → Stored') (mapContext : Context → Context')
    (mapEffect : Effect → Effect') (mapHandoff : Handoff → Handoff')
    (natural : DiscoveryNatural source target mapProducerFn mapBorrowed mapStored mapContext
      mapEffect mapHandoff)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    residualAddresses target (mapCarriers mapProducerFn mapBorrowed mapStored mapContext
      mapEffect mapHandoff state) =
      (residualAddresses source state).map mapStored := by
  cases attached : state.execution with
  | none => simp [residualAddresses, mapCarriers, attached]
  | some execution =>
      simp [residualAddresses, mapCarriers, Execution.mapCarriers, Execution.mapProducer,
        attached, natural.residual]

theorem pendingAddresses_mapCarriers [DecidableEq Output] [DecidableEq Stored']
    (source : Discovery Producer Borrowed Stored Context Effect Handoff)
    (target : Discovery Producer' Borrowed' Stored' Context' Effect' Handoff')
    (mapProducerFn : Producer → Producer') (mapBorrowed : Borrowed → Borrowed')
    (mapStored : Stored → Stored') (mapContext : Context → Context')
    (mapEffect : Effect → Effect') (mapHandoff : Handoff → Handoff')
    (natural : DiscoveryNatural source target mapProducerFn mapBorrowed mapStored mapContext
      mapEffect mapHandoff)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    pendingAddresses target (mapCarriers mapProducerFn mapBorrowed mapStored mapContext
      mapEffect mapHandoff state) =
      (pendingAddresses source state).map mapStored := by
  cases attached : state.execution with
  | none => simp [pendingAddresses, mapCarriers, attached]
  | some execution =>
      cases staged : execution.pending with
      | none =>
          simp [pendingAddresses, mapCarriers, Execution.mapCarriers, Execution.mapProducer,
            attached, staged]
      | some value =>
          simp [pendingAddresses, mapCarriers, Execution.mapCarriers, Execution.mapProducer,
            attached, staged, natural.pending, Option.map_some]

theorem requestAddresses_mapCarriers [DecidableEq Output] [DecidableEq Stored']
    (source : Discovery Producer Borrowed Stored Context Effect Handoff)
    (target : Discovery Producer' Borrowed' Stored' Context' Effect' Handoff')
    (mapProducerFn : Producer → Producer') (mapBorrowed : Borrowed → Borrowed')
    (mapStored : Stored → Stored') (mapContext : Context → Context')
    (mapEffect : Effect → Effect') (mapHandoff : Handoff → Handoff')
    (natural : DiscoveryNatural source target mapProducerFn mapBorrowed mapStored mapContext
      mapEffect mapHandoff)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    requestAddresses target (mapCarriers mapProducerFn mapBorrowed mapStored mapContext
      mapEffect mapHandoff state) =
      (requestAddresses source state).map mapStored := by
  cases attached : state.execution with
  | none => simp [requestAddresses, mapCarriers, attached]
  | some execution =>
      rcases execution with ⟨producer, pending, accepted, mode⟩
      cases mode with
      | active =>
          simp [requestAddresses, mapCarriers, Execution.mapCarriers, Execution.mapProducer,
            Mode.map, attached]
      | interrupted =>
          simp [requestAddresses, mapCarriers, Execution.mapCarriers, Execution.mapProducer,
            Mode.map, attached]
      | effect request =>
          simp [requestAddresses, mapCarriers, Execution.mapCarriers, Execution.mapProducer,
            Mode.map, attached, natural.effect]
      | handoff request =>
          simp [requestAddresses, mapCarriers, Execution.mapCarriers, Execution.mapProducer,
            Mode.map, attached, natural.handoff]

private theorem answerRoots_address {Owner Address Destination : Type}
    [DecidableEq Owner] [DecidableEq Address] [DecidableEq Destination]
    (owner : Owner) (addresses : List Address) (address : Address → Destination) :
    (OwnedLifecycle.answerRoots owner addresses).image (fun pair => (pair.1, address pair.2)) =
      OwnedLifecycle.answerRoots owner (addresses.map address) := by
  ext ⟨other, located⟩
  constructor
  · intro held
    rw [Finset.mem_image] at held
    rcases held with ⟨⟨source, value⟩, member, same⟩
    have sourceEq : source = other := congrArg Prod.fst same
    have addressEq : address value = located := congrArg Prod.snd same
    have decoded := (OwnedLifecycle.mem_answerRoots owner source addresses value).mp member
    rw [sourceEq] at decoded
    refine (OwnedLifecycle.mem_answerRoots owner other (addresses.map address) located).mpr ?_
    exact ⟨decoded.1, List.mem_map.mpr ⟨value, decoded.2, addressEq⟩⟩
  · intro held
    have decoded :=
      (OwnedLifecycle.mem_answerRoots owner other (addresses.map address) located).mp held
    rcases List.mem_map.mp decoded.2 with ⟨value, member, addressEq⟩
    refine Finset.mem_image.mpr ?_
    refine ⟨(owner, value), ?_, ?_⟩
    · exact (OwnedLifecycle.mem_answerRoots owner owner addresses value).mpr ⟨rfl, member⟩
    · exact Prod.ext decoded.1.symm addressEq

private theorem liftDelivery_address {Destination : Type}
    [DecidableEq Stored] [DecidableEq Destination] [DecidableEq Output]
    (address : Stored → Destination)
    (roots : ResourceOwnership.Roots (Sum (Fin clients) Output) Stored) :
    liftDelivery (roots.image (fun pair => (pair.1, address pair.2))) =
      (liftDelivery roots).image (fun pair => (pair.1, address pair.2)) := by
  simp only [liftDelivery, Finset.image_image]
  rfl

/-- Anchor roots of the mapped configuration are the address image of the
source roots. Each summand is read from the mapped producer, pending return,
context, current request or delivery carrier. -/
theorem anchorRoots_mapCarriers [DecidableEq Stored] [DecidableEq Stored'] [DecidableEq Output]
    (source : Discovery Producer Borrowed Stored Context Effect Handoff)
    (target : Discovery Producer' Borrowed' Stored' Context' Effect' Handoff')
    (mapProducerFn : Producer → Producer') (mapBorrowed : Borrowed → Borrowed')
    (mapStored : Stored → Stored') (mapContext : Context → Context')
    (mapEffect : Effect → Effect') (mapHandoff : Handoff → Handoff')
    (natural : DiscoveryNatural source target mapProducerFn mapBorrowed mapStored mapContext
      mapEffect mapHandoff)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    anchorRoots target (mapCarriers mapProducerFn mapBorrowed mapStored mapContext mapEffect
      mapHandoff state) =
      (anchorRoots source state).image (fun pair => (pair.1, mapStored pair.2)) := by
  have contextCarrier :
      (mapCarriers mapProducerFn mapBorrowed mapStored mapContext mapEffect mapHandoff
        state).context = mapContext state.context := rfl
  have deliveryCarrier :
      (mapCarriers mapProducerFn mapBorrowed mapStored mapContext mapEffect mapHandoff
        state).delivery = state.delivery.map mapStored := rfl
  simp only [anchorRoots, contextCarrier, deliveryCarrier, Finset.image_union,
    residualAddresses_mapCarriers source target mapProducerFn mapBorrowed mapStored mapContext
      mapEffect mapHandoff natural state,
    pendingAddresses_mapCarriers source target mapProducerFn mapBorrowed mapStored mapContext
      mapEffect mapHandoff natural state,
    requestAddresses_mapCarriers source target mapProducerFn mapBorrowed mapStored mapContext
      mapEffect mapHandoff natural state,
    natural.context state.context,
    SharedOccurrenceOwnership.map_roots mapStored state.delivery,
    answerRoots_address, liftDelivery_address]

private theorem stage_mapCarriers [DecidableEq Output] [DecidableEq Stored']
    (mapProducerFn : Producer → Producer') (mapBorrowed : Borrowed → Borrowed')
    (mapStored : Stored → Stored') (mapContext : Context → Context')
    (mapEffect : Effect → Effect') (mapHandoff : Handoff → Handoff')
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (execution : Execution Producer Borrowed Effect Handoff)
    (outcome : ProducerOutcome Producer Borrowed Effect Handoff) :
    stage (mapCarriers mapProducerFn mapBorrowed mapStored mapContext mapEffect mapHandoff state)
        (execution.mapCarriers mapProducerFn mapBorrowed mapEffect mapHandoff)
        (outcome.mapCarriers mapProducerFn mapBorrowed mapEffect mapHandoff) =
      ((stage state execution outcome).1.mapCarriers mapBorrowed mapStored mapEffect mapHandoff,
        mapCarriers mapProducerFn mapBorrowed mapStored mapContext mapEffect mapHandoff
          (stage state execution outcome).2) := by
  cases outcome <;>
    simp [stage, mapCarriers, Execution.mapCarriers, Execution.mapProducer,
      ProducerOutcome.mapCarriers, ProducerOutcome.mapProducer, ProducerOutcome.mapPayloads,
      Mode.map, Notice.mapCarriers, SharedOccurrenceLog.map_complete,
      SharedOccurrenceOwnership.Configuration.map]

private theorem admit_mapCarriers [DecidableEq Output] [DecidableEq Stored']
    (mapProducerFn : Producer → Producer') (mapBorrowed : Borrowed → Borrowed')
    (mapStored : Stored → Stored') (mapContext : Context → Context')
    (mapEffect : Effect → Effect') (mapHandoff : Handoff → Handoff')
    (sourceCapture : Borrowed → Option Stored) (targetCapture : Borrowed' → Option Stored')
    (captureLaw : ∀ value, targetCapture (mapBorrowed value) =
      (sourceCapture value).map mapStored)
    (sourceCapacity : Stored → Bool) (targetCapacity : Stored' → Bool)
    (capacityLaw : ∀ stored, targetCapacity (mapStored stored) = sourceCapacity stored)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (execution : Execution Producer Borrowed Effect Handoff) (value : Borrowed) :
    admit targetCapture targetCapacity
        (mapCarriers mapProducerFn mapBorrowed mapStored mapContext mapEffect mapHandoff state)
        (execution.mapCarriers mapProducerFn mapBorrowed mapEffect mapHandoff)
        (mapBorrowed value) =
      ((admit sourceCapture sourceCapacity state execution value).1.mapCarriers
          mapBorrowed mapStored mapEffect mapHandoff,
        mapCarriers mapProducerFn mapBorrowed mapStored mapContext mapEffect mapHandoff
          (admit sourceCapture sourceCapacity state execution value).2) := by
  unfold admit
  rw [captureLaw]
  cases captured : sourceCapture value with
  | none => simp [Notice.mapCarriers]
  | some stored =>
      simp only [Option.map_some]
      rw [capacityLaw]
      split
      · have appended := SharedOccurrenceLog.append_map mapStored state.delivery.log stored
        have logCarrier :
            (mapCarriers mapProducerFn mapBorrowed mapStored mapContext mapEffect mapHandoff
              state).delivery.log =
              SharedOccurrenceLog.State.map mapStored state.delivery.log := rfl
        rw [logCarrier, appended]
        rcases recorded : SharedOccurrenceLog.append state.delivery.log stored with ⟨status, log⟩
        cases status with
        | accepted =>
            simp [Notice.mapCarriers, mapCarriers, Execution.mapCarriers, Execution.mapProducer,
              Mode.map, SharedOccurrenceLog.map_pastEnd, SharedOccurrenceOwnership.Configuration.map]
        | backpressure =>
            simp [Notice.mapCarriers, mapCarriers]
        | completed =>
            simp [Notice.mapCarriers, mapCarriers]
      · simp [Notice.mapCarriers, mapCarriers]

/-- One producer microstep crosses the carrier map when the target services
agree with the mapped source services. Notices stay in order, and the whole
resulting configuration is the carrier map. -/
theorem pump_mapCarriers [DecidableEq Output] [DecidableEq Stored']
    (mapProducerFn : Producer → Producer') (mapBorrowed : Borrowed → Borrowed')
    (mapStored : Stored → Stored') (mapContext : Context → Context')
    (mapEffect : Effect → Effect') (mapHandoff : Handoff → Handoff')
    (sourceStep : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (targetStep : Producer' → ProducerOutcome Producer' Borrowed' Effect' Handoff')
    (stepLaw : ∀ producer, targetStep (mapProducerFn producer) =
      (sourceStep producer).mapCarriers mapProducerFn mapBorrowed mapEffect mapHandoff)
    (sourceCapture : Borrowed → Option Stored) (targetCapture : Borrowed' → Option Stored')
    (captureLaw : ∀ value, targetCapture (mapBorrowed value) =
      (sourceCapture value).map mapStored)
    (sourceCapacity : Stored → Bool) (targetCapacity : Stored' → Bool)
    (capacityLaw : ∀ stored, targetCapacity (mapStored stored) = sourceCapacity stored)
    (sourceCompatible : Context → Bool) (targetCompatible : Context' → Bool)
    (contextLaw : ∀ context, targetCompatible (mapContext context) = sourceCompatible context)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    pump targetStep targetCapture targetCapacity targetCompatible
        (mapCarriers mapProducerFn mapBorrowed mapStored mapContext mapEffect mapHandoff state) =
      ((pump sourceStep sourceCapture sourceCapacity sourceCompatible state).1.mapCarriers
          mapBorrowed mapStored mapEffect mapHandoff,
        mapCarriers mapProducerFn mapBorrowed mapStored mapContext mapEffect mapHandoff
          (pump sourceStep sourceCapture sourceCapacity sourceCompatible state).2) := by
  rcases state with ⟨attached, context, delivery⟩
  cases attached with
  | none => simp [pump, mapCarriers, Notice.mapCarriers]
  | some execution =>
      rcases execution with ⟨producer, staged, accepted, mode⟩
      have completedEq : (delivery.map mapStored).log.completed = delivery.log.completed := rfl
      have limitEq : (delivery.map mapStored).log.limit = delivery.log.limit := rfl
      have consumersEq :
          hasConsumers (delivery.map mapStored).log = hasConsumers delivery.log := rfl
      have lengthEq : (delivery.map mapStored).log.rows.length = delivery.log.rows.length := by
        simp [SharedOccurrenceOwnership.map_log, SharedOccurrenceLog.State.map, List.length_map]
      simp only [pump, mapCarriers, Option.map_some, Execution.mapCarriers, Execution.mapProducer,
        contextLaw, completedEq, limitEq, consumersEq, lengthEq]
      by_cases denied : (!sourceCompatible context) = true
      · simp [denied, Execution.mapCarriers, Execution.mapProducer, Notice.mapCarriers]
      · simp only [denied]
        by_cases closed : delivery.log.completed = true
        · simp [closed, Execution.mapCarriers, Execution.mapProducer, Notice.mapCarriers]
        · simp only [closed]
          cases mode with
          | active =>
              simp only [Mode.map]
              by_cases absent : (!hasConsumers delivery.log) = true
              · simp [absent, Mode.map, Execution.mapCarriers, Execution.mapProducer,
                  Notice.mapCarriers]
              · simp only [absent]
                by_cases room : delivery.log.rows.length < delivery.log.limit
                · simp only [room, if_true]
                  cases staged with
                  | none =>
                      rw [stepLaw]
                      exact stage_mapCarriers mapProducerFn mapBorrowed mapStored mapContext
                        mapEffect mapHandoff ⟨some ⟨producer, none, accepted, .active⟩, context,
                          delivery⟩ ⟨producer, none, accepted, .active⟩ (sourceStep producer)
                  | some value =>
                      exact admit_mapCarriers mapProducerFn mapBorrowed mapStored mapContext
                        mapEffect mapHandoff sourceCapture targetCapture captureLaw sourceCapacity
                        targetCapacity capacityLaw ⟨some ⟨producer, some value, accepted, .active⟩,
                          context, delivery⟩ ⟨producer, some value, accepted, .active⟩ value
                · simp [room, Mode.map, Execution.mapCarriers, Execution.mapProducer,
                    Notice.mapCarriers]
          | effect request =>
              simp [Mode.map, Execution.mapCarriers, Execution.mapProducer, Notice.mapCarriers]
          | handoff request =>
              simp [Mode.map, Execution.mapCarriers, Execution.mapProducer, Notice.mapCarriers]
          | interrupted =>
              simp [Mode.map, Execution.mapCarriers, Execution.mapProducer, Notice.mapCarriers]

theorem pump_mapCarriers_keeps_cursors [DecidableEq Output] [DecidableEq Stored']
    (mapProducerFn : Producer → Producer') (mapBorrowed : Borrowed → Borrowed')
    (mapStored : Stored → Stored') (mapContext : Context → Context')
    (mapEffect : Effect → Effect') (mapHandoff : Handoff → Handoff')
    (sourceStep : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (targetStep : Producer' → ProducerOutcome Producer' Borrowed' Effect' Handoff')
    (stepLaw : ∀ producer, targetStep (mapProducerFn producer) =
      (sourceStep producer).mapCarriers mapProducerFn mapBorrowed mapEffect mapHandoff)
    (sourceCapture : Borrowed → Option Stored) (targetCapture : Borrowed' → Option Stored')
    (captureLaw : ∀ value, targetCapture (mapBorrowed value) =
      (sourceCapture value).map mapStored)
    (sourceCapacity : Stored → Bool) (targetCapacity : Stored' → Bool)
    (capacityLaw : ∀ stored, targetCapacity (mapStored stored) = sourceCapacity stored)
    (sourceCompatible : Context → Bool) (targetCompatible : Context' → Bool)
    (contextLaw : ∀ context, targetCompatible (mapContext context) = sourceCompatible context)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    (pump targetStep targetCapture targetCapacity targetCompatible
        (mapCarriers mapProducerFn mapBorrowed mapStored mapContext mapEffect mapHandoff
          state)).2.delivery.log.positions =
      (pump sourceStep sourceCapture sourceCapacity sourceCompatible state).2.delivery.log.positions ∧
      acceptedCount (pump targetStep targetCapture targetCapacity targetCompatible
        (mapCarriers mapProducerFn mapBorrowed mapStored mapContext mapEffect mapHandoff
          state)).2 =
        acceptedCount (pump sourceStep sourceCapture sourceCapacity sourceCompatible state).2 := by
  have square := pump_mapCarriers mapProducerFn mapBorrowed mapStored mapContext mapEffect
    mapHandoff sourceStep targetStep stepLaw sourceCapture targetCapture captureLaw
    sourceCapacity targetCapacity capacityLaw sourceCompatible targetCompatible contextLaw state
  refine ⟨?_, ?_⟩
  · rw [square]
    exact mapCarriers_positions mapProducerFn mapBorrowed mapStored mapContext mapEffect
      mapHandoff (pump sourceStep sourceCapture sourceCapacity sourceCompatible state).2
  · rw [square]
    exact mapCarriers_acceptedCount mapProducerFn mapBorrowed mapStored mapContext mapEffect
      mapHandoff (pump sourceStep sourceCapture sourceCapacity sourceCompatible state).2

/-- Finite `run` transports ordered notices and the resulting carrier.
Positions and the accepted count agree with the source run. -/
theorem run_mapCarriers [DecidableEq Output] [DecidableEq Stored']
    (mapProducerFn : Producer → Producer') (mapBorrowed : Borrowed → Borrowed')
    (mapStored : Stored → Stored') (mapContext : Context → Context')
    (mapEffect : Effect → Effect') (mapHandoff : Handoff → Handoff')
    (sourceStep : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (targetStep : Producer' → ProducerOutcome Producer' Borrowed' Effect' Handoff')
    (stepLaw : ∀ producer, targetStep (mapProducerFn producer) =
      (sourceStep producer).mapCarriers mapProducerFn mapBorrowed mapEffect mapHandoff)
    (sourceCapture : Borrowed → Option Stored) (targetCapture : Borrowed' → Option Stored')
    (captureLaw : ∀ value, targetCapture (mapBorrowed value) =
      (sourceCapture value).map mapStored)
    (sourceCapacity : Stored → Bool) (targetCapacity : Stored' → Bool)
    (capacityLaw : ∀ stored, targetCapacity (mapStored stored) = sourceCapacity stored)
    (sourceCompatible : Context → Bool) (targetCompatible : Context' → Bool)
    (contextLaw : ∀ context, targetCompatible (mapContext context) = sourceCompatible context)
    (ticks : Nat)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    run targetStep targetCapture targetCapacity targetCompatible ticks
        (mapCarriers mapProducerFn mapBorrowed mapStored mapContext mapEffect mapHandoff state) =
      ((run sourceStep sourceCapture sourceCapacity sourceCompatible ticks state).1.map
          (Notice.mapCarriers mapBorrowed mapStored mapEffect mapHandoff),
        mapCarriers mapProducerFn mapBorrowed mapStored mapContext mapEffect mapHandoff
          (run sourceStep sourceCapture sourceCapacity sourceCompatible ticks state).2) ∧
      (run targetStep targetCapture targetCapacity targetCompatible ticks
          (mapCarriers mapProducerFn mapBorrowed mapStored mapContext mapEffect mapHandoff
            state)).2.delivery.log.positions =
        (run sourceStep sourceCapture sourceCapacity sourceCompatible ticks
          state).2.delivery.log.positions ∧
      acceptedCount (run targetStep targetCapture targetCapacity targetCompatible ticks
          (mapCarriers mapProducerFn mapBorrowed mapStored mapContext mapEffect mapHandoff
            state)).2 =
        acceptedCount (run sourceStep sourceCapture sourceCapacity sourceCompatible ticks
          state).2 := by
  induction ticks generalizing state with
  | zero =>
      refine ⟨rfl, rfl, ?_⟩
      exact mapCarriers_acceptedCount mapProducerFn mapBorrowed mapStored mapContext mapEffect
        mapHandoff state
  | succ ticks ih =>
      have step := pump_mapCarriers mapProducerFn mapBorrowed mapStored mapContext mapEffect
        mapHandoff sourceStep targetStep stepLaw sourceCapture targetCapture captureLaw
        sourceCapacity targetCapacity capacityLaw sourceCompatible targetCompatible contextLaw state
      have later := ih (pump sourceStep sourceCapture sourceCapacity sourceCompatible state).2
      simp only [run, step, later.1, List.map_cons]
      exact ⟨trivial,
        mapCarriers_positions mapProducerFn mapBorrowed mapStored mapContext mapEffect mapHandoff
          (run sourceStep sourceCapture sourceCapacity sourceCompatible ticks
            (pump sourceStep sourceCapture sourceCapacity sourceCompatible state).2).2,
        mapCarriers_acceptedCount mapProducerFn mapBorrowed mapStored mapContext mapEffect
          mapHandoff
          (run sourceStep sourceCapture sourceCapacity sourceCompatible ticks
            (pump sourceStep sourceCapture sourceCapacity sourceCompatible state).2).2⟩

private def addressShift (address : Nat) : Nat := address + 1

private def twoConsumers : SharedOccurrenceOwnership.Configuration Nat Unit 2 :=
  ⟨⟨0, [4, 5], fun client => some client.val, false, 4⟩, {((), 9)}⟩

private def pendingActive : Configuration Unit Nat Nat Nat Unit Nat Nat 2 :=
  ⟨some ⟨(), some 0, 3, .active⟩, 8, twoConsumers⟩

private def pendingRequest : Configuration Unit Nat Nat Nat Unit Nat Nat 2 :=
  ⟨some ⟨(), some 0, 3, .effect 7⟩, 8, twoConsumers⟩

private def carrierDiscovery : Discovery Unit Nat Nat Nat Nat Nat where
  residual := fun _ => []
  pending := fun value => [value]
  context := fun value => [value]
  effect := fun request => [request]
  handoff := fun request => [request]
  record := fun _ => []

private def carrierStep : Unit → ProducerOutcome Unit Nat Nat Nat := fun _ => .progress ()

private def carrierCapture (value : Nat) : Option Nat := some value

private def carrierCapacity : Nat → Bool := fun _ => true

private def carrierContext : Nat → Bool := fun _ => true

private theorem carrierDiscovery_shift :
    DiscoveryNatural carrierDiscovery carrierDiscovery id addressShift addressShift addressShift
      addressShift addressShift where
  residual _ := rfl
  pending _ := rfl
  context _ := rfl
  effect _ := rfl
  handoff _ := rfl

/-- Shift every address by one. The active carrier has a pending return and
admits it for two consumers; the request carrier keeps that pending value and
an effect request. Cursors and the accepted count follow the source transition. -/
theorem shifted_pending_and_request_keep_two_consumer_cursors :
    addressShift 0 = 1 ∧
      (mapCarriers id addressShift addressShift addressShift addressShift addressShift
        pendingRequest).execution = some ⟨(), some 1, 3, .effect 8⟩ ∧
      (mapCarriers id addressShift addressShift addressShift addressShift addressShift
        pendingRequest).context = 9 ∧
      (mapCarriers id addressShift addressShift addressShift addressShift addressShift
        pendingRequest).delivery.log.rows = [5, 6] ∧
      ((), 10) ∈ (mapCarriers id addressShift addressShift addressShift addressShift addressShift
        pendingRequest).delivery.published ∧
      (mapCarriers id addressShift addressShift addressShift addressShift addressShift
        pendingRequest).delivery.log.positions 0 = some 0 ∧
      (mapCarriers id addressShift addressShift addressShift addressShift addressShift
        pendingRequest).delivery.log.positions 1 = some 1 ∧
      (run carrierStep carrierCapture carrierCapacity carrierContext 1
        (mapCarriers id addressShift addressShift addressShift addressShift addressShift
          pendingActive)).1 = [.admitted 2 1] ∧
      (run carrierStep carrierCapture carrierCapacity carrierContext 1
        (mapCarriers id addressShift addressShift addressShift addressShift addressShift
          pendingActive)).2.delivery.log.positions 0 = some 0 ∧
      (run carrierStep carrierCapture carrierCapacity carrierContext 1
        (mapCarriers id addressShift addressShift addressShift addressShift addressShift
          pendingActive)).2.delivery.log.positions 1 = some 1 ∧
      acceptedCount (run carrierStep carrierCapture carrierCapacity carrierContext 1
        (mapCarriers id addressShift addressShift addressShift addressShift addressShift
          pendingActive)).2 = 4 ∧
      (pump carrierStep carrierCapture carrierCapacity carrierContext
        (mapCarriers id addressShift addressShift addressShift addressShift addressShift
          pendingRequest)).1 = .effect 8 ∧
      acceptedCount (pump carrierStep carrierCapture carrierCapacity carrierContext
        (mapCarriers id addressShift addressShift addressShift addressShift addressShift
          pendingRequest)).2 = 3 ∧
      anchorRoots carrierDiscovery (mapCarriers id addressShift addressShift addressShift
        addressShift addressShift pendingRequest) =
        (anchorRoots carrierDiscovery pendingRequest).image
          (fun pair => (pair.1, addressShift pair.2)) ∧
      (Anchor.request, 8) ∈ anchorRoots carrierDiscovery
        (mapCarriers id addressShift addressShift addressShift addressShift addressShift
          pendingRequest) ∧
      (Anchor.residual, 1) ∈ anchorRoots carrierDiscovery
        (mapCarriers id addressShift addressShift addressShift addressShift addressShift
          pendingRequest) ∧
      (Anchor.delivery (Sum.inl (1 : Fin 2)), 6) ∈ anchorRoots carrierDiscovery
        (mapCarriers id addressShift addressShift addressShift addressShift addressShift
          pendingRequest) := by
  have shifted := carrierDiscovery_shift
  have activeRun := run_mapCarriers id addressShift addressShift addressShift addressShift
    addressShift carrierStep carrierStep (fun _ => rfl) carrierCapture carrierCapture
    (fun _ => rfl) carrierCapacity carrierCapacity (fun _ => rfl) carrierContext carrierContext
    (fun _ => rfl) 1 pendingActive
  have requestPump := pump_mapCarriers id addressShift addressShift addressShift addressShift
    addressShift carrierStep carrierStep (fun _ => rfl) carrierCapture carrierCapture
    (fun _ => rfl) carrierCapacity carrierCapacity (fun _ => rfl) carrierContext carrierContext
    (fun _ => rfl) pendingRequest
  have sourceNotice : (pump carrierStep carrierCapture carrierCapacity carrierContext
      pendingActive).1 = .admitted 2 0 := by
    simp [pump, admit, pendingActive, twoConsumers, carrierCapture, carrierCapacity,
      carrierContext, hasConsumers, SharedOccurrenceLog.append, SharedOccurrenceLog.pastEnd]
  have sourceActive : run carrierStep carrierCapture carrierCapacity carrierContext 1
      pendingActive = ([.admitted 2 0],
        (pump carrierStep carrierCapture carrierCapacity carrierContext pendingActive).2) := by
    simp [run, sourceNotice]
  have sourceRequest : pump carrierStep carrierCapture carrierCapacity carrierContext
      pendingRequest = (.effect 7, pendingRequest) := rfl
  have sourceAccepted : acceptedCount (run carrierStep carrierCapture carrierCapacity
      carrierContext 1 pendingActive).2 = 4 := by
    rw [sourceActive]
    rfl
  have cursors := activeRun.2.1
  refine ⟨rfl, rfl, rfl, rfl, ?_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [mapCarriers, pendingRequest, twoConsumers, addressShift,
      SharedOccurrenceOwnership.Configuration.map]
  · rw [activeRun.1, sourceActive]
    simp [Notice.mapCarriers, addressShift]
  · rw [cursors, sourceActive]
    simp [pump, admit, pendingActive, twoConsumers, carrierCapture, carrierCapacity,
      carrierContext, hasConsumers, SharedOccurrenceLog.append]
  · rw [cursors, sourceActive]
    simp [pump, admit, pendingActive, twoConsumers, carrierCapture, carrierCapacity,
      carrierContext, hasConsumers, SharedOccurrenceLog.append]
  · rw [activeRun.2.2, sourceAccepted]
  · rw [requestPump, sourceRequest]
    simp [Notice.mapCarriers, addressShift]
  · rw [requestPump, sourceRequest]
    rfl
  · exact anchorRoots_mapCarriers carrierDiscovery carrierDiscovery id addressShift addressShift
      addressShift addressShift addressShift shifted pendingRequest
  · have member : ((Anchor.request : Anchor 2 Unit), 8) ∈
        OwnedLifecycle.answerRoots (Anchor.request : Anchor 2 Unit)
          (requestAddresses carrierDiscovery
            (mapCarriers id addressShift addressShift addressShift addressShift addressShift
              pendingRequest)) := by
      have addresses : requestAddresses carrierDiscovery
          (mapCarriers id addressShift addressShift addressShift addressShift addressShift
            pendingRequest) = [8] := rfl
      rw [addresses]
      exact (OwnedLifecycle.mem_answerRoots (Anchor.request : Anchor 2 Unit)
        (Anchor.request : Anchor 2 Unit) [8] 8).mpr ⟨rfl, List.mem_cons_self⟩
    exact Finset.mem_union_left _
      (Finset.mem_union_right _ member)
  · have member : ((Anchor.residual : Anchor 2 Unit), 1) ∈
        OwnedLifecycle.answerRoots (Anchor.residual : Anchor 2 Unit)
          (pendingAddresses carrierDiscovery
            (mapCarriers id addressShift addressShift addressShift addressShift addressShift
              pendingRequest)) := by
      have addresses : pendingAddresses carrierDiscovery
          (mapCarriers id addressShift addressShift addressShift addressShift addressShift
            pendingRequest) = [1] := rfl
      rw [addresses]
      exact (OwnedLifecycle.mem_answerRoots (Anchor.residual : Anchor 2 Unit)
        (Anchor.residual : Anchor 2 Unit) [1] 1).mpr ⟨rfl, List.mem_cons_self⟩
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_right _ member)))
  · have unreadRow : 6 ∈ SharedOccurrenceLog.unread
        (mapCarriers id addressShift addressShift addressShift addressShift addressShift
          pendingRequest).delivery.log 1 := by
      decide
    have rooted : (Sum.inl (1 : Fin 2), 6) ∈ SharedOccurrenceOwnership.roots
        (mapCarriers id addressShift addressShift addressShift addressShift addressShift
          pendingRequest).delivery :=
      Finset.mem_union_left _
        ((SharedOccurrenceOwnership.mem_logRoots_consumer _ 1 6).mpr unreadRow)
    exact Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨(Sum.inl (1 : Fin 2), 6), rooted, rfl⟩)

end CarrierTransport

/-! ## Optional field projection

The stored payload is `ResourceOwnership.StoredFields`. `projectHeap` reads its
operational value and operational reference field. `observeOperational` reads
that same field from the source lookup. `projectDiscovered` collects the
projection under `anchorRoots`. Under `DiscoveryNatural`, `mapCarriers` sends
those roots to the mapped configuration. This is not an address relocation,
and a source lookup is not producer execution.
-/

section FieldProjection

open Mettapedia.Machines.ResourceOwnership

variable {Operational Observer : Type}

noncomputable def projectDiscovered [DecidableEq Stored] [DecidableEq Output]
    (discovery : Discovery Producer Borrowed Stored Context Effect Handoff)
    (heap : Heap Stored (StoredFields Stored Operational Observer)) (stored : heap.storesFields)
    (outsideFrame : Roots (Anchor clients Output) Stored)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    ProjectedFields (Address := Stored) (Owner := Anchor clients Output) Operational Observer :=
  projectOptionalFields heap stored (anchorRoots discovery state) outsideFrame

theorem projectDiscovered_spec [DecidableEq Stored] [DecidableEq Output]
    (discovery : Discovery Producer Borrowed Stored Context Effect Handoff)
    (heap : Heap Stored (StoredFields Stored Operational Observer)) (stored : heap.storesFields)
    (outsideFrame : Roots (Anchor clients Output) Stored)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    let image := projectDiscovered discovery heap stored outsideFrame state
    image.source = heap ∧ image.outsideFrame = outsideFrame ∧
      image.privateRoots = anchorRoots discovery state ∧
      image.privateImage = collect (projectHeap heap stored) (anchorRoots discovery state) := by
  exact ⟨rfl, rfl, rfl, rfl⟩

variable {Producer' Borrowed' Stored' Context' Effect' Handoff' : Type}

private theorem mapped_anchor_member [DecidableEq Stored] [DecidableEq Stored'] [DecidableEq Output]
    (sourceDiscovery : Discovery Producer Borrowed Stored Context Effect Handoff)
    (targetDiscovery : Discovery Producer' Borrowed' Stored' Context' Effect' Handoff')
    (mapProducerFn : Producer → Producer') (mapBorrowed : Borrowed → Borrowed')
    (mapStored : Stored → Stored') (mapContext : Context → Context')
    (mapEffect : Effect → Effect') (mapHandoff : Handoff → Handoff')
    (natural : DiscoveryNatural sourceDiscovery targetDiscovery mapProducerFn mapBorrowed
      mapStored mapContext mapEffect mapHandoff)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    {owner : Anchor clients Output} {address : Stored}
    (rooted : (owner, address) ∈ anchorRoots sourceDiscovery state) :
    (owner, mapStored address) ∈ anchorRoots targetDiscovery
      (mapCarriers mapProducerFn mapBorrowed mapStored mapContext mapEffect mapHandoff state) := by
  rw [anchorRoots_mapCarriers sourceDiscovery targetDiscovery mapProducerFn mapBorrowed mapStored
    mapContext mapEffect mapHandoff natural state]
  exact Finset.mem_image.mpr ⟨(owner, address), rooted, rfl⟩

/-- The mapped configuration's anchor roots are the carrier image of the roots
`projectDiscovered` collects under. -/
theorem projectDiscovered_mapped_roots [DecidableEq Stored] [DecidableEq Stored']
    [DecidableEq Output]
    (sourceDiscovery : Discovery Producer Borrowed Stored Context Effect Handoff)
    (targetDiscovery : Discovery Producer' Borrowed' Stored' Context' Effect' Handoff')
    (mapProducerFn : Producer → Producer') (mapBorrowed : Borrowed → Borrowed')
    (mapStored : Stored → Stored') (mapContext : Context → Context')
    (mapEffect : Effect → Effect') (mapHandoff : Handoff → Handoff')
    (natural : DiscoveryNatural sourceDiscovery targetDiscovery mapProducerFn mapBorrowed
      mapStored mapContext mapEffect mapHandoff)
    (heap : Heap Stored (StoredFields Stored Operational Observer)) (stored : heap.storesFields)
    (outsideFrame : Roots (Anchor clients Output) Stored)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    anchorRoots targetDiscovery
        (mapCarriers mapProducerFn mapBorrowed mapStored mapContext mapEffect mapHandoff state) =
      (projectDiscovered sourceDiscovery heap stored outsideFrame state).privateRoots.image
        (fun pair => (pair.1, mapStored pair.2)) := by
  rw [show (projectDiscovered sourceDiscovery heap stored outsideFrame state).privateRoots =
      anchorRoots sourceDiscovery state from rfl]
  exact anchorRoots_mapCarriers sourceDiscovery targetDiscovery mapProducerFn mapBorrowed
    mapStored mapContext mapEffect mapHandoff natural state

/-- A discovered anchor's stored operational field is the private image's
value and the source observation. The mapped configuration names the
transported root. -/
theorem projectDiscovered_answer [DecidableEq Stored] [DecidableEq Stored'] [DecidableEq Output]
    (sourceDiscovery : Discovery Producer Borrowed Stored Context Effect Handoff)
    (targetDiscovery : Discovery Producer' Borrowed' Stored' Context' Effect' Handoff')
    (mapProducerFn : Producer → Producer') (mapBorrowed : Borrowed → Borrowed')
    (mapStored : Stored → Stored') (mapContext : Context → Context')
    (mapEffect : Effect → Effect') (mapHandoff : Handoff → Handoff')
    (natural : DiscoveryNatural sourceDiscovery targetDiscovery mapProducerFn mapBorrowed
      mapStored mapContext mapEffect mapHandoff)
    (heap : Heap Stored (StoredFields Stored Operational Observer)) (stored : heap.storesFields)
    (outsideFrame : Roots (Anchor clients Output) Stored)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    {owner : Anchor clients Output} {address : Stored}
    {cell : Cell Stored (StoredFields Stored Operational Observer)}
    (rooted : (owner, address) ∈ anchorRoots sourceDiscovery state)
    (found : heap.lookup address = some cell) :
    (owner, mapStored address) ∈ anchorRoots targetDiscovery
        (mapCarriers mapProducerFn mapBorrowed mapStored mapContext mapEffect mapHandoff state) ∧
      observeOperational heap address = some cell.value.operational ∧
      OwnedLifecycle.observe
          (projectDiscovered sourceDiscovery heap stored outsideFrame state).privateImage
          [address] = [some (projectCell cell)] ∧
      OwnedLifecycle.observe
          (projectDiscovered sourceDiscovery heap stored outsideFrame state).source
          [address] = [some cell] := by
  have transported := mapped_anchor_member sourceDiscovery targetDiscovery mapProducerFn
    mapBorrowed mapStored mapContext mapEffect mapHandoff natural state rooted
  have read := private_root_reads_stored_operational heap stored
    (anchorRoots sourceDiscovery state) outsideFrame rooted found
  refine ⟨transported, read.1, ?_, ?_⟩
  · simp only [OwnedLifecycle.observe, List.map_cons, List.map_nil, projectDiscovered]
    exact congrArg (fun lookup => [lookup]) read.2.1
  · simp only [OwnedLifecycle.observe, List.map_cons, List.map_nil, projectDiscovered]
    exact congrArg (fun lookup => [lookup]) read.2.2

/-- A successful operational walk reads the stored operational field at its
endpoint. The private image walks the same projected cells. -/
theorem projectDiscovered_walk_readout [DecidableEq Stored] [DecidableEq Stored']
    [DecidableEq Output]
    (sourceDiscovery : Discovery Producer Borrowed Stored Context Effect Handoff)
    (targetDiscovery : Discovery Producer' Borrowed' Stored' Context' Effect' Handoff')
    (mapProducerFn : Producer → Producer') (mapBorrowed : Borrowed → Borrowed')
    (mapStored : Stored → Stored') (mapContext : Context → Context')
    (mapEffect : Effect → Effect') (mapHandoff : Handoff → Handoff')
    (natural : DiscoveryNatural sourceDiscovery targetDiscovery mapProducerFn mapBorrowed
      mapStored mapContext mapEffect mapHandoff)
    (heap : Heap Stored (StoredFields Stored Operational Observer)) (stored : heap.storesFields)
    (outsideFrame : Roots (Anchor clients Output) Stored)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    {owner : Anchor clients Output} {address : Stored}
    (rooted : (owner, address) ∈ anchorRoots sourceDiscovery state)
    (allocated : address ∈ heap.allocated) (path : List Stored)
    {endpoint : Stored} {observed : Cell Stored Operational}
    (success : walk (projectHeap heap stored) address path = some (endpoint, observed)) :
    (owner, mapStored address) ∈ anchorRoots targetDiscovery
        (mapCarriers mapProducerFn mapBorrowed mapStored mapContext mapEffect mapHandoff state) ∧
      walk (projectDiscovered sourceDiscovery heap stored outsideFrame state).privateImage
          address path = some (endpoint, observed) ∧
      observeOperational heap endpoint = some observed.value ∧
      ∃ storedCell, heap.lookup endpoint = some storedCell ∧
        observed = projectCell storedCell ∧
        observed.value = storedCell.value.operational := by
  have transported := mapped_anchor_member sourceDiscovery targetDiscovery mapProducerFn
    mapBorrowed mapStored mapContext mapEffect mapHandoff natural state rooted
  have allocatedImage : address ∈ (projectHeap heap stored).allocated := by
    rw [projectHeap_allocated]
    exact allocated
  have live := live_of_root (projectHeap heap stored) (anchorRoots sourceDiscovery state)
    rooted allocatedImage
  have walked := walk_privateImage heap stored (anchorRoots sourceDiscovery state)
    outsideFrame live path
  obtain ⟨observedField, storedCell, sourceFound, same, valueEq⟩ :=
    walk_endpoint_is_stored_operational heap stored path success
  refine ⟨transported, ?_, observedField, storedCell, sourceFound, same, valueEq⟩
  simpa [projectDiscovered] using walked.trans success

theorem projectDiscovered_aliases [DecidableEq Stored] [DecidableEq Stored'] [DecidableEq Output]
    (sourceDiscovery : Discovery Producer Borrowed Stored Context Effect Handoff)
    (targetDiscovery : Discovery Producer' Borrowed' Stored' Context' Effect' Handoff')
    (mapProducerFn : Producer → Producer') (mapBorrowed : Borrowed → Borrowed')
    (mapStored : Stored → Stored') (mapContext : Context → Context')
    (mapEffect : Effect → Effect') (mapHandoff : Handoff → Handoff')
    (natural : DiscoveryNatural sourceDiscovery targetDiscovery mapProducerFn mapBorrowed
      mapStored mapContext mapEffect mapHandoff)
    (heap : Heap Stored (StoredFields Stored Operational Observer)) (stored : heap.storesFields)
    (outsideFrame : Roots (Anchor clients Output) Stored)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    {leftOwner rightOwner : Anchor clients Output} {leftAddress rightAddress : Stored}
    (leftRoot : (leftOwner, leftAddress) ∈ anchorRoots sourceDiscovery state)
    (rightRoot : (rightOwner, rightAddress) ∈ anchorRoots sourceDiscovery state)
    (leftAllocated : leftAddress ∈ heap.allocated)
    (rightAllocated : rightAddress ∈ heap.allocated)
    (left right : List Stored) :
    (leftOwner, mapStored leftAddress) ∈ anchorRoots targetDiscovery
        (mapCarriers mapProducerFn mapBorrowed mapStored mapContext mapEffect mapHandoff state) ∧
      (rightOwner, mapStored rightAddress) ∈ anchorRoots targetDiscovery
        (mapCarriers mapProducerFn mapBorrowed mapStored mapContext mapEffect mapHandoff state) ∧
      (Aliases (projectDiscovered sourceDiscovery heap stored outsideFrame state).privateImage
          leftAddress left rightAddress right ↔
        Aliases (projectHeap heap stored) leftAddress left rightAddress right) := by
  have leftTransported := mapped_anchor_member sourceDiscovery targetDiscovery mapProducerFn
    mapBorrowed mapStored mapContext mapEffect mapHandoff natural state leftRoot
  have rightTransported := mapped_anchor_member sourceDiscovery targetDiscovery mapProducerFn
    mapBorrowed mapStored mapContext mapEffect mapHandoff natural state rightRoot
  have leftAllocatedImage : leftAddress ∈ (projectHeap heap stored).allocated := by
    rw [projectHeap_allocated]
    exact leftAllocated
  have rightAllocatedImage : rightAddress ∈ (projectHeap heap stored).allocated := by
    rw [projectHeap_allocated]
    exact rightAllocated
  have leftLive := live_of_root (projectHeap heap stored) (anchorRoots sourceDiscovery state)
    leftRoot leftAllocatedImage
  have rightLive := live_of_root (projectHeap heap stored) (anchorRoots sourceDiscovery state)
    rightRoot rightAllocatedImage
  have aliasEq := aliases_privateImage heap stored (anchorRoots sourceDiscovery state)
    outsideFrame leftLive rightLive left right
  exact ⟨leftTransported, rightTransported, by simpa [projectDiscovered] using aliasEq⟩

/-- An address outside the discovered roots, and outside every stored
operational reference field, is released on the private image. Source
operational observation still reads the stored field. -/
theorem projectDiscovered_releases [DecidableEq Stored] [DecidableEq Stored'] [DecidableEq Output]
    (sourceDiscovery : Discovery Producer Borrowed Stored Context Effect Handoff)
    (targetDiscovery : Discovery Producer' Borrowed' Stored' Context' Effect' Handoff')
    (mapProducerFn : Producer → Producer') (mapBorrowed : Borrowed → Borrowed')
    (mapStored : Stored → Stored') (mapContext : Context → Context')
    (mapEffect : Effect → Effect') (mapHandoff : Handoff → Handoff')
    (natural : DiscoveryNatural sourceDiscovery targetDiscovery mapProducerFn mapBorrowed
      mapStored mapContext mapEffect mapHandoff)
    (heap : Heap Stored (StoredFields Stored Operational Observer)) (stored : heap.storesFields)
    (outsideFrame : Roots (Anchor clients Output) Stored)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (recording : Stored)
    (notRoot : recording ∉ rootAddresses (anchorRoots sourceDiscovery state))
    (absent : ∀ holder cell, heap.lookup holder = some cell →
      recording ∉ cell.value.operationalReferences) :
    anchorRoots targetDiscovery
        (mapCarriers mapProducerFn mapBorrowed mapStored mapContext mapEffect mapHandoff state) =
      (projectDiscovered sourceDiscovery heap stored outsideFrame state).privateRoots.image
        (fun pair => (pair.1, mapStored pair.2)) ∧
      (projectDiscovered sourceDiscovery heap stored outsideFrame state).privateImage.lookup
          recording = none ∧
      (projectDiscovered sourceDiscovery heap stored outsideFrame state).source.lookup recording =
        heap.lookup recording ∧
      observeOperational heap recording =
        ((projectDiscovered sourceDiscovery heap stored outsideFrame state).source.lookup
          recording).map (fun cell => cell.value.operational) := by
  have transported := projectDiscovered_mapped_roots sourceDiscovery targetDiscovery mapProducerFn
    mapBorrowed mapStored mapContext mapEffect mapHandoff natural heap stored outsideFrame state
  have released := observer_only_reclaimed heap stored (anchorRoots sourceDiscovery state)
    outsideFrame recording notRoot absent
  exact ⟨transported, by simpa [projectDiscovered] using released.1,
    by simpa [projectDiscovered] using released.2.1,
    by simpa [projectDiscovered] using released.2.2⟩

theorem projectDiscovered_frame [DecidableEq Stored] [DecidableEq Output]
    (discovery : Discovery Producer Borrowed Stored Context Effect Handoff)
    (heap : Heap Stored (StoredFields Stored Operational Observer)) (stored : heap.storesFields)
    (outsideFrame : Roots (Anchor clients Output) Stored)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    {owner : Anchor clients Output} {address : Stored}
    (framed : (owner, address) ∈ outsideFrame) :
    let image := projectDiscovered discovery heap stored outsideFrame state
    image.outsideFrame = outsideFrame ∧ (owner, address) ∈ image.outsideFrame ∧
      image.source = heap ∧ image.source.lookup address = heap.lookup address ∧
      observeOperational image.source address = observeOperational heap address := by
  simpa [projectDiscovered] using framed_source_keeps_stored_cell heap stored
    (anchorRoots discovery state) outsideFrame framed

theorem projectHeap_clears_observer_reference {Operational Observer : Type} [DecidableEq Stored]
    (heap : Heap Stored (StoredFields Stored Operational Observer)) (stored : heap.storesFields)
    (roots : Roots (Anchor clients Output) Stored) (recording : Stored)
    (absent : ∀ holder cell, heap.lookup holder = some cell →
      recording ∉ cell.value.operationalReferences) :
    receiptFieldCleared (projectHeap heap stored) roots recording :=
  projectHeap_omits_observer_reference heap stored roots recording absent

/-! ## Producer history entry

`none` runs `ordinary` and returns no prefix. `some record` streams
`recordOrdinary` on that prefix, so resumption keeps its items, remaining
capacity and omissions. Fresh capacity is
`Mettapedia.GSLT.Core.InferenceControl.Recording.initial`. `pump` does not
inspect the choice. Forgetting drops the prefix and continues with `ordinary`
from the recorded configuration. Late recording starts from
`Recording.initial` on the configuration reached by an earlier ordinary
slice. The projected heap is the projection of that complete configuration.
-/

open Mettapedia.GSLT.Core.InferenceControl.Recording

def enterProducerHistory
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool) :
    Option (Prefix (Notice Borrowed Stored Effect Handoff)) → Nat →
    Configuration Producer Borrowed Stored Context Output Effect Handoff clients →
    Option (Prefix (Notice Borrowed Stored Effect Handoff)) ×
      Configuration Producer Borrowed Stored Context Output Effect Handoff clients
  | none, ticks, state =>
      (none, ordinary step capture capacity compatible ticks state)
  | some record, ticks, state =>
      let continued := recordOrdinary step capture capacity compatible ticks record state
      (some continued.1, continued.2)

theorem enter_unrecorded
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool) (ticks : Nat)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    enterProducerHistory step capture capacity compatible none ticks state =
      (none, ordinary step capture capacity compatible ticks state) := rfl

theorem enter_recorded_keeps_ordinary
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool)
    (record : Prefix (Notice Borrowed Stored Effect Handoff)) (ticks : Nat)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    (enterProducerHistory step capture capacity compatible (some record) ticks state).2 =
      ordinary step capture capacity compatible ticks state := by
  simpa [enterProducerHistory] using recordOrdinary_preserves_ordinary_configuration step
    capture capacity compatible ticks record state

theorem enter_recorded_prefix
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool)
    (record : Prefix (Notice Borrowed Stored Effect Handoff)) (ticks : Nat)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    let continued := recordOrdinary step capture capacity compatible ticks record state
    let notices := run step capture capacity compatible ticks state
    enterProducerHistory step capture capacity compatible (some record) ticks state =
        (some continued.1, continued.2) ∧
      continued.2 = ordinary step capture capacity compatible ticks state ∧
      continued.1.items = record.items ++ notices.1.take record.remaining ∧
      continued.1.remaining = record.remaining - notices.1.length ∧
      continued.1.omitted = record.omitted + (notices.1.length - record.remaining) := by
  refine ⟨rfl, recordOrdinary_preserves_ordinary_configuration step capture capacity compatible
      ticks record state, ?_, ?_, ?_⟩
  · simpa [recordOrdinary_eq_append_run] using
      (Prefix.append_state record (run step capture capacity compatible ticks state).1).1
  · simpa [recordOrdinary_eq_append_run] using
      (Prefix.append_state record (run step capture capacity compatible ticks state).1).2.1
  · simpa [recordOrdinary_eq_append_run] using
      (Prefix.append_state record (run step capture capacity compatible ticks state).1).2.2

/-- The second slice receives the prefix left by the first. Unrecorded slices
use `ordinary_add`. Recorded slices use
`recordOrdinary_composes_without_resetting_capacity`. -/
theorem enter_split
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool)
    (choice : Option (Prefix (Notice Borrowed Stored Effect Handoff)))
    (first second : Nat)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    enterProducerHistory step capture capacity compatible choice (first + second) state =
      enterProducerHistory step capture capacity compatible
        (enterProducerHistory step capture capacity compatible choice first state).1
        second
        (enterProducerHistory step capture capacity compatible choice first state).2 := by
  cases choice with
  | none =>
      simp only [enterProducerHistory, ordinary_add]
  | some record =>
      simp only [enterProducerHistory, recordOrdinary_composes_without_resetting_capacity]

/-- Dropping the prefix continues from the recorded configuration and reaches
the ordinary configuration of the combined slice. -/
theorem forget_recorded_entry_is_complete
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool)
    (record : Prefix (Notice Borrowed Stored Effect Handoff)) (first second : Nat)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    ordinary step capture capacity compatible second
        (enterProducerHistory step capture capacity compatible (some record) first state).2 =
      ordinary step capture capacity compatible (first + second) state := by
  simpa [enterProducerHistory] using recordOrdinary_continues_ordinary step capture capacity
    compatible first second record state

/-- A recorder started from `Recording.initial` on the ordinary configuration
retains only the later notices. Its configuration is the ordinary continuation. -/
theorem late_entry_is_suffix
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool) (bound first second : Nat)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    (enterProducerHistory step capture capacity compatible
        (Mettapedia.GSLT.Core.InferenceControl.Recording.initial (some bound)) second
        (ordinary step capture capacity compatible first state)).2 =
      ordinary step capture capacity compatible (first + second) state ∧
    ((enterProducerHistory step capture capacity compatible
        (Mettapedia.GSLT.Core.InferenceControl.Recording.initial (some bound)) second
        (ordinary step capture capacity compatible first state)).1).map Prefix.items =
      some ((run step capture capacity compatible second
        (ordinary step capture capacity compatible first state)).1.take bound) ∧
    ((enterProducerHistory step capture capacity compatible
        (Mettapedia.GSLT.Core.InferenceControl.Recording.initial (some bound)) second
        (ordinary step capture capacity compatible first state)).1).map
      (fun retained => retained.remaining) =
      some (bound - (run step capture capacity compatible second
        (ordinary step capture capacity compatible first state)).1.length) ∧
    ((enterProducerHistory step capture capacity compatible
        (Mettapedia.GSLT.Core.InferenceControl.Recording.initial (some bound)) second
        (ordinary step capture capacity compatible first state)).1).map
      (fun retained => retained.omitted) =
      some ((run step capture capacity compatible second
        (ordinary step capture capacity compatible first state)).1.length - bound) := by
  have fresh :
      Mettapedia.GSLT.Core.InferenceControl.Recording.initial
        (Event := Notice Borrowed Stored Effect Handoff) (some bound) =
      some (Prefix.initial bound) := rfl
  rw [fresh]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [enterProducerHistory, recordOrdinary_preserves_ordinary_configuration, ← ordinary_add]
  · simp only [enterProducerHistory, Option.map_some]
    simpa [recordOrdinary_eq_append_run] using Prefix.initial_items bound
      (run step capture capacity compatible second
        (ordinary step capture capacity compatible first state)).1
  · simp only [enterProducerHistory, Option.map_some]
    simpa [recordOrdinary_eq_append_run, Prefix.initial] using
      (Prefix.append_state
        (Prefix.initial (Event := Notice Borrowed Stored Effect Handoff) bound)
        (run step capture capacity compatible second
          (ordinary step capture capacity compatible first state)).1).2.1
  · simp only [enterProducerHistory, Option.map_some]
    simpa [recordOrdinary_eq_append_run] using Prefix.initial_omitted bound
      (run step capture capacity compatible second
        (ordinary step capture capacity compatible first state)).1

theorem enter_projection_reads_stored [DecidableEq Stored] [DecidableEq Output]
    (discovery : Discovery Producer Borrowed Stored Context Effect Handoff)
    (heap : Heap Stored (StoredFields Stored Operational Observer)) (stored : heap.storesFields)
    (outsideFrame : Roots (Anchor clients Output) Stored)
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool)
    (choice : Option (Prefix (Notice Borrowed Stored Effect Handoff))) (ticks : Nat)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    {owner : Anchor clients Output} {address : Stored}
    {cell : Cell Stored (StoredFields Stored Operational Observer)}
    (rooted : (owner, address) ∈ anchorRoots discovery
      (enterProducerHistory step capture capacity compatible choice ticks state).2)
    (found : heap.lookup address = some cell) :
    let config := (enterProducerHistory step capture capacity compatible choice ticks state).2
    let image := projectDiscovered discovery heap stored outsideFrame config
    observeOperational heap address = some cell.value.operational ∧
      (image.privateImage.lookup address).map Cell.value = some cell.value.operational ∧
      image.source.lookup address = some cell := by
  have read := private_root_reads_stored_operational heap stored
    (anchorRoots discovery (enterProducerHistory step capture capacity compatible choice ticks
      state).2) outsideFrame rooted found
  refine ⟨read.1, ?_, ?_⟩
  · unfold projectDiscovered
    rw [read.2.1]
    rfl
  · unfold projectDiscovered
    exact read.2.2

theorem forget_projection_is_complete [DecidableEq Stored] [DecidableEq Output]
    (discovery : Discovery Producer Borrowed Stored Context Effect Handoff)
    (heap : Heap Stored (StoredFields Stored Operational Observer)) (stored : heap.storesFields)
    (outsideFrame : Roots (Anchor clients Output) Stored)
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool)
    (record : Prefix (Notice Borrowed Stored Effect Handoff)) (first second : Nat)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    ordinary step capture capacity compatible second
        (enterProducerHistory step capture capacity compatible (some record) first state).2 =
      ordinary step capture capacity compatible (first + second) state ∧
    projectDiscovered discovery heap stored outsideFrame
        (ordinary step capture capacity compatible second
          (enterProducerHistory step capture capacity compatible (some record) first state).2) =
      projectDiscovered discovery heap stored outsideFrame
        (ordinary step capture capacity compatible (first + second) state) := by
  refine ⟨forget_recorded_entry_is_complete step capture capacity compatible record first second
      state, ?_⟩
  rw [forget_recorded_entry_is_complete step capture capacity compatible record first second state]

theorem late_projection_is_complete [DecidableEq Stored] [DecidableEq Output]
    (discovery : Discovery Producer Borrowed Stored Context Effect Handoff)
    (heap : Heap Stored (StoredFields Stored Operational Observer)) (stored : heap.storesFields)
    (outsideFrame : Roots (Anchor clients Output) Stored)
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool) (bound first second : Nat)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    (enterProducerHistory step capture capacity compatible
        (Mettapedia.GSLT.Core.InferenceControl.Recording.initial (some bound)) second
        (ordinary step capture capacity compatible first state)).2 =
      ordinary step capture capacity compatible (first + second) state ∧
    ((enterProducerHistory step capture capacity compatible
        (Mettapedia.GSLT.Core.InferenceControl.Recording.initial (some bound)) second
        (ordinary step capture capacity compatible first state)).1).map Prefix.items =
      some ((run step capture capacity compatible second
        (ordinary step capture capacity compatible first state)).1.take bound) ∧
    projectDiscovered discovery heap stored outsideFrame
        (enterProducerHistory step capture capacity compatible
          (Mettapedia.GSLT.Core.InferenceControl.Recording.initial (some bound)) second
          (ordinary step capture capacity compatible first state)).2 =
      projectDiscovered discovery heap stored outsideFrame
        (ordinary step capture capacity compatible (first + second) state) := by
  have suffix := late_entry_is_suffix step capture capacity compatible bound first second state
  refine ⟨suffix.1, suffix.2.1, ?_⟩
  rw [suffix.1]

/-! One recorded producer and the same unrecorded producer, on one stored heap.
The configuration law is `recordOrdinary_preserves_ordinary_configuration`.
The root law is `anchorRoots_mapCarriers`. Neither `pump_mapCarriers` nor
`run_mapCarriers` is assumed. -/

def serviceStep : Unit → ProducerOutcome Unit Nat Unit Unit := fun _ => .progress ()

def serviceCapture : Nat → Option Nat := fun value => some value

def serviceCapacity : Nat → Bool := fun _ => true

def serviceCompatible : Nat → Bool := fun _ => true

def serviceState : Configuration Unit Nat Nat Nat Unit Unit Unit 1 :=
  ⟨some ⟨(), some 2, 3, .active⟩, 8, ⟨⟨0, [], fun _ => some 0, false, 2⟩, ∅⟩⟩

def serviceAfter : Configuration Unit Nat Nat Nat Unit Unit Unit 1 :=
  ⟨some ⟨(), none, 4, .active⟩, 8, ⟨⟨0, [2], fun _ => some 0, false, 2⟩, ∅⟩⟩

def servicePrefix : Mettapedia.GSLT.Core.InferenceControl.Recording.Prefix
    (Notice Nat Nat Unit Unit) :=
  .initial 4

def serviceDiscovery : Discovery Unit Nat Nat Nat Unit Unit where
  residual := fun _ => [0]
  pending := fun value => [value]
  context := fun _ => []
  effect := fun _ => []
  handoff := fun _ => []
  record := fun _ => [1]

def shiftedDiscovery : Discovery Unit Nat Nat Nat Unit Unit where
  residual := fun _ => [1]
  pending := fun value => [value]
  context := fun _ => []
  effect := fun _ => []
  handoff := fun _ => []
  record := fun _ => [2]

def serviceShift (address : Nat) : Nat := address + 1

def servicePayload (address : Nat) : StoredFields Nat Nat Nat :=
  if address = 0 then
    { operational := 7, observer := some 99, operationalReferences := {2},
      observerReferences := {1, 2} }
  else if address = 1 then
    { operational := 0, observer := some 99, operationalReferences := ∅,
      observerReferences := ∅ }
  else
    { operational := 7, observer := none, operationalReferences := ∅,
      observerReferences := ∅ }

def serviceCell (address : Nat) : Cell Nat (StoredFields Nat Nat Nat) where
  value := servicePayload address
  references := (servicePayload address).operationalReferences ∪
    (servicePayload address).observerReferences
  bytes := if address = 0 then 5 else 1

def serviceHeap : Heap Nat (StoredFields Nat Nat Nat) where
  lookup address := if address ≤ 2 then some (serviceCell address) else none
  allocated := Finset.range 3
  allocated_iff address := by
    simp only [Finset.mem_range]
    constructor
    · intro within
      exact ⟨serviceCell address, if_pos (by omega)⟩
    · rintro ⟨_, found⟩
      split at found
      next within => omega
      next _ => cases found
  closed address _cell found next reference := by
    split at found
    next _ =>
      cases found
      by_cases zero : address = 0
      · subst zero
        have refs : (serviceCell 0).references = ({2} ∪ {1, 2} : Finset Nat) := rfl
        rw [refs] at reference
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at reference
        rcases reference with rfl | rfl | rfl <;> exact Finset.mem_range.mpr (by decide)
      · by_cases one : address = 1
        · subst one
          have refs : (serviceCell 1).references = (∅ ∪ ∅ : Finset Nat) := rfl
          rw [refs, Finset.empty_union] at reference
          exact absurd reference (Finset.notMem_empty _)
        · have two : address = 2 := by omega
          subst two
          have refs : (serviceCell 2).references = (∅ ∪ ∅ : Finset Nat) := rfl
          rw [refs, Finset.empty_union] at reference
          exact absurd reference (Finset.notMem_empty _)
    next _ => cases found

theorem serviceHeap_stores : serviceHeap.storesFields := by
  intro address cell found
  rw [show serviceHeap.lookup address =
    (if address ≤ 2 then some (serviceCell address) else none) from rfl] at found
  split at found
  next _ =>
    cases found
    rfl
  next _ => cases found

def serviceFrame : Roots (Anchor 1 Unit) Nat := {(Anchor.context, 0)}

theorem serviceDiscovery_shift : DiscoveryNatural serviceDiscovery shiftedDiscovery id serviceShift
    serviceShift serviceShift id id where
  residual _ := rfl
  pending _ := rfl
  context _ := rfl
  effect _ := rfl
  handoff _ := rfl

theorem service_ordinary_admits :
    ordinary serviceStep serviceCapture serviceCapacity serviceCompatible 1 serviceState =
      serviceAfter := rfl

theorem service_recorded_agrees :
    (recordOrdinary serviceStep serviceCapture serviceCapacity serviceCompatible 1
      servicePrefix serviceState).2 =
      ordinary serviceStep serviceCapture serviceCapacity serviceCompatible 1 serviceState ∧
      (recordOrdinary serviceStep serviceCapture serviceCapacity serviceCompatible 1
        servicePrefix serviceState).1.items = [.admitted 0 2] ∧
      acceptedCount (ordinary serviceStep serviceCapture serviceCapacity serviceCompatible 1
        serviceState) = 4 := by
  refine ⟨recordOrdinary_preserves_ordinary_configuration serviceStep serviceCapture
      serviceCapacity serviceCompatible 1 servicePrefix serviceState, rfl, ?_⟩
  rw [service_ordinary_admits]
  rfl

private theorem service_residual_root :
    ((Anchor.residual : Anchor 1 Unit), 0) ∈ anchorRoots serviceDiscovery serviceState := by
  have addresses : residualAddresses serviceDiscovery serviceState = [0] := rfl
  have member : ((Anchor.residual : Anchor 1 Unit), 0) ∈
      OwnedLifecycle.answerRoots (Anchor.residual : Anchor 1 Unit) [0] :=
    (OwnedLifecycle.mem_answerRoots (Anchor.residual : Anchor 1 Unit)
      (Anchor.residual : Anchor 1 Unit) [0] 0).mpr ⟨rfl, List.mem_cons_self⟩
  rw [← addresses] at member
  exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
    (Finset.mem_union_left _ member)))

private theorem service_after_residual_root :
    ((Anchor.residual : Anchor 1 Unit), 0) ∈ anchorRoots serviceDiscovery serviceAfter := by
  have addresses : residualAddresses serviceDiscovery serviceAfter = [0] := rfl
  have member : ((Anchor.residual : Anchor 1 Unit), 0) ∈
      OwnedLifecycle.answerRoots (Anchor.residual : Anchor 1 Unit) [0] :=
    (OwnedLifecycle.mem_answerRoots (Anchor.residual : Anchor 1 Unit)
      (Anchor.residual : Anchor 1 Unit) [0] 0).mpr ⟨rfl, List.mem_cons_self⟩
  rw [← addresses] at member
  exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
    (Finset.mem_union_left _ member)))

private theorem service_receipt_absent (owner : Anchor 1 Unit) :
    (owner, (1 : Nat)) ∉ anchorRoots serviceDiscovery serviceState := by
  cases owner with
  | residual => decide
  | context => decide
  | request => decide
  | recorder => decide
  | delivery carrier =>
      cases carrier with
      | inl client =>
          cases client using Fin.cases with
          | zero => decide
          | succ client => exact Fin.elim0 client
      | inr output =>
          cases output
          decide

private theorem service_after_receipt_absent (owner : Anchor 1 Unit) :
    (owner, (1 : Nat)) ∉ anchorRoots serviceDiscovery serviceAfter := by
  cases owner with
  | residual => decide
  | context => decide
  | request => decide
  | recorder => decide
  | delivery carrier =>
      cases carrier with
      | inl client =>
          cases client using Fin.cases with
          | zero => decide
          | succ client => exact Fin.elim0 client
      | inr output =>
          cases output
          decide

private theorem service_operational_reference_absent :
    ∀ holder cell, serviceHeap.lookup holder = some cell →
      (1 : Nat) ∉ cell.value.operationalReferences := by
  intro holder cell found
  rw [show serviceHeap.lookup holder =
    (if holder ≤ 2 then some (serviceCell holder) else none) from rfl] at found
  split at found
  next _ =>
    cases found
    by_cases zero : holder = 0
    · subst zero
      have refs : (serviceCell 0).value.operationalReferences = ({2} : Finset Nat) := rfl
      rw [refs, Finset.mem_singleton]
      decide
    · by_cases one : holder = 1
      · subst one
        have refs : (serviceCell 1).value.operationalReferences = (∅ : Finset Nat) := rfl
        rw [refs]
        exact Finset.notMem_empty _
      · have two : holder = 2 := by omega
        subst two
        have refs : (serviceCell 2).value.operationalReferences = (∅ : Finset Nat) := rfl
        rw [refs]
        exact Finset.notMem_empty _
  next _ => cases found

private theorem service_walk_receipt :
    walk serviceHeap 0 [1] = some (1, serviceCell 1) := by
  have lookup0 : serviceHeap.lookup 0 = some (serviceCell 0) := by simp [serviceHeap]
  have lookup1 : serviceHeap.lookup 1 = some (serviceCell 1) := by simp [serviceHeap]
  have edge : (1 : Nat) ∈ (serviceCell 0).references := by
    have refs : (serviceCell 0).references = ({2} ∪ {1, 2} : Finset Nat) := rfl
    rw [refs]
    exact Finset.mem_union.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl rfl)))
  simp only [walk, lookup0, Option.bind_some]
  rw [if_pos edge, lookup1]
  rfl

private theorem service_projected_walk_misses_receipt :
    walk (projectHeap serviceHeap serviceHeap_stores) 0 [1] = none := by
  have lookup0 : (projectHeap serviceHeap serviceHeap_stores).lookup 0 =
      some (projectCell (serviceCell 0)) := by simp [projectHeap, serviceHeap]
  have missing : (1 : Nat) ∉ (projectCell (serviceCell 0)).references := by
    have refs : (projectCell (serviceCell 0)).references = ({2} : Finset Nat) := rfl
    rw [refs, Finset.mem_singleton]
    decide
  simp only [walk, lookup0, Option.bind_some]
  rw [if_neg missing]

/-- Recorded and unrecorded execution admit the same occurrence and the same
paid count. The private image reads stored operational payload 7, keeps the
shared reference 2, and reclaims observer-only address 1. The source cell still
shows observer payload 99. Shifting carriers moves the discovered roots and
does not replace the stored payload. -/
theorem recorded_service_projects_stored_operational :
    (recordOrdinary serviceStep serviceCapture serviceCapacity serviceCompatible 1
      servicePrefix serviceState).2 = serviceAfter ∧
      acceptedCount serviceAfter = 4 ∧
      (recordOrdinary serviceStep serviceCapture serviceCapacity serviceCompatible 1
        servicePrefix serviceState).1.items = [.admitted 0 2] ∧
      observeOperational serviceHeap 0 = some 7 ∧
      ((projectDiscovered serviceDiscovery serviceHeap serviceHeap_stores serviceFrame
        serviceState).privateImage.lookup 0).map Cell.value = some 7 ∧
      ((projectDiscovered serviceDiscovery serviceHeap serviceHeap_stores serviceFrame
        serviceState).privateImage.lookup 0).map Cell.value ≠ some 99 ∧
      ((projectDiscovered serviceDiscovery serviceHeap serviceHeap_stores serviceFrame
        serviceState).source.lookup 0).map (fun cell => cell.value.observer) =
        some (some 99) ∧
      (projectDiscovered serviceDiscovery serviceHeap serviceHeap_stores serviceFrame
        serviceState).privateImage.lookup 1 = none ∧
      (2 : Nat) ∈ (serviceCell 0).value.operationalReferences ∩
        (serviceCell 0).value.observerReferences ∧
      ((projectDiscovered serviceDiscovery serviceHeap serviceHeap_stores serviceFrame
        serviceState).privateImage.lookup 2).map Cell.value = some 7 ∧
      walk serviceHeap 0 [1] = some (1, serviceCell 1) ∧
      walk (projectHeap serviceHeap serviceHeap_stores) 0 [1] = none ∧
      (projectCell (serviceCell 0)).bytes = 5 ∧
      ((projectDiscovered serviceDiscovery serviceHeap serviceHeap_stores serviceFrame
        serviceAfter).privateImage.lookup 0).map Cell.value = some 7 ∧
      (projectDiscovered serviceDiscovery serviceHeap serviceHeap_stores serviceFrame
        serviceAfter).privateImage.lookup 1 = none ∧
      anchorRoots shiftedDiscovery (mapCarriers id serviceShift serviceShift serviceShift id id
        serviceState) =
        (projectDiscovered serviceDiscovery serviceHeap serviceHeap_stores serviceFrame
          serviceState).privateRoots.image (fun pair => (pair.1, serviceShift pair.2)) ∧
      ((Anchor.residual : Anchor 1 Unit), 1) ∈ anchorRoots shiftedDiscovery
        (mapCarriers id serviceShift serviceShift serviceShift id id serviceState) := by
  have recorded := service_recorded_agrees
  have found0 : serviceHeap.lookup 0 = some (serviceCell 0) := by simp [serviceHeap]
  have read0 := projected_value_eq_stored_operational serviceHeap serviceHeap_stores found0
  have rooted := service_residual_root
  have imageRead := private_root_reads_stored_operational serviceHeap serviceHeap_stores
    (anchorRoots serviceDiscovery serviceState) serviceFrame rooted found0
  have notRoot : (1 : Nat) ∉ rootAddresses (anchorRoots serviceDiscovery serviceState) := by
    intro member
    obtain ⟨⟨owner, address⟩, paired, same⟩ := Finset.mem_image.mp member
    subst same
    exact service_receipt_absent owner paired
  have released := observer_only_reclaimed serviceHeap serviceHeap_stores
    (anchorRoots serviceDiscovery serviceState) serviceFrame 1 notRoot
    service_operational_reference_absent
  have shared : (2 : Nat) ∈ (serviceCell 0).value.operationalReferences ∩
      (serviceCell 0).value.observerReferences := by
    have operationalRefs : (serviceCell 0).value.operationalReferences = {2} := rfl
    have observerRefs : (serviceCell 0).value.observerReferences = {1, 2} := rfl
    rw [operationalRefs, observerRefs]
    exact Finset.mem_inter.mpr ⟨Finset.mem_singleton.mpr rfl,
      Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr rfl))⟩
  have live0 : Live (projectHeap serviceHeap serviceHeap_stores)
      (anchorRoots serviceDiscovery serviceState) 0 :=
    live_of_root _ _ rooted (by rw [projectHeap_allocated]; simp [serviceHeap])
  have live2 := shared_operational_reference_stays serviceHeap serviceHeap_stores
    (anchorRoots serviceDiscovery serviceState) live0 found0 shared
  have kept2 := lookup_collect_of_live (projectHeap serviceHeap serviceHeap_stores)
    (anchorRoots serviceDiscovery serviceState) live2
  have projected2 : (projectHeap serviceHeap serviceHeap_stores).lookup 2 =
      some (projectCell (serviceCell 2)) := by simp [projectHeap, serviceHeap, serviceCell]
  have foundAfter : serviceHeap.lookup 0 = some (serviceCell 0) := found0
  have afterRead := private_root_reads_stored_operational serviceHeap serviceHeap_stores
    (anchorRoots serviceDiscovery serviceAfter) serviceFrame service_after_residual_root foundAfter
  have afterNotRoot : (1 : Nat) ∉ rootAddresses (anchorRoots serviceDiscovery serviceAfter) := by
    intro member
    obtain ⟨⟨owner, address⟩, paired, same⟩ := Finset.mem_image.mp member
    subst same
    exact service_after_receipt_absent owner paired
  have afterReleased := observer_only_reclaimed serviceHeap serviceHeap_stores
    (anchorRoots serviceDiscovery serviceAfter) serviceFrame 1 afterNotRoot
    service_operational_reference_absent
  have mapped := projectDiscovered_mapped_roots serviceDiscovery shiftedDiscovery id serviceShift
    serviceShift serviceShift id id serviceDiscovery_shift serviceHeap serviceHeap_stores
    serviceFrame serviceState
  have shiftedRoot : ((Anchor.residual : Anchor 1 Unit), 1) ∈ anchorRoots shiftedDiscovery
      (mapCarriers id serviceShift serviceShift serviceShift id id serviceState) := by
    rw [mapped]
    exact Finset.mem_image.mpr ⟨(Anchor.residual, 0), rooted, rfl⟩
  have observed7 : observeOperational serviceHeap 0 = some 7 := by
    rw [read0.1]
    rfl
  have imageValue :
      ((projectDiscovered serviceDiscovery serviceHeap serviceHeap_stores serviceFrame
        serviceState).privateImage.lookup 0).map Cell.value = some 7 := by
    unfold projectDiscovered
    rw [imageRead.2.1]
    rfl
  refine ⟨?_, rfl, recorded.2.1, observed7, imageValue, ?_, ?_, ?_, shared, ?_, ?_, ?_, rfl, ?_, ?_,
      mapped, shiftedRoot⟩
  · rw [recorded.1, service_ordinary_admits]
  · rw [imageValue]
    decide
  · unfold projectDiscovered
    rw [imageRead.2.2]
    rfl
  · unfold projectDiscovered
    exact released.1
  · have imageLookup :
        (projectDiscovered serviceDiscovery serviceHeap serviceHeap_stores serviceFrame
          serviceState).privateImage.lookup 2 =
          (projectHeap serviceHeap serviceHeap_stores).lookup 2 := by
      unfold projectDiscovered
      exact kept2
    rw [imageLookup, projected2]
    rfl
  · exact service_walk_receipt
  · exact service_projected_walk_misses_receipt
  · unfold projectDiscovered
    rw [afterRead.2.1]
    rfl
  · unfold projectDiscovered
    exact afterReleased.1

/-- Projection establishes `receiptFieldCleared` for observer-only address 1.
Shared address 2 remains an operational reference, so that property fails
there. The private image aliases the projected path `0 [2]`. The source walk
still reaches the receipt, and the recorded producer keeps its paid count. -/
theorem service_erasure_splits_shared_and_observer_receipt :
    receiptFieldCleared (projectHeap serviceHeap serviceHeap_stores)
        (anchorRoots serviceDiscovery serviceState) 1 ∧
      ¬ receiptFieldCleared (projectHeap serviceHeap serviceHeap_stores)
        (anchorRoots serviceDiscovery serviceState) 2 ∧
      (projectDiscovered serviceDiscovery serviceHeap serviceHeap_stores serviceFrame
        serviceState).privateImage.lookup 1 = none ∧
      Aliases (projectDiscovered serviceDiscovery serviceHeap serviceHeap_stores serviceFrame
          serviceState).privateImage 0 [2] 2 [] ∧
      walk serviceHeap 0 [1] = some (1, serviceCell 1) ∧
      walk (projectHeap serviceHeap serviceHeap_stores) 0 [1] = none ∧
      observeOperational serviceHeap 0 = some 7 ∧
      acceptedCount (recordOrdinary serviceStep serviceCapture serviceCapacity
        serviceCompatible 1 servicePrefix serviceState).2 = 4 := by
  have found0 : serviceHeap.lookup 0 = some (serviceCell 0) := by simp [serviceHeap]
  have rooted := service_residual_root
  have live0 : Live (projectHeap serviceHeap serviceHeap_stores)
      (anchorRoots serviceDiscovery serviceState) 0 :=
    live_of_root _ _ rooted (by
      rw [projectHeap_allocated]
      exact Finset.mem_range.mpr (by decide))
  have shared : (2 : Nat) ∈ (serviceCell 0).value.operationalReferences ∩
      (serviceCell 0).value.observerReferences := by
    have operationalRefs : (serviceCell 0).value.operationalReferences = {2} := rfl
    have observerRefs : (serviceCell 0).value.observerReferences = {1, 2} := rfl
    rw [operationalRefs, observerRefs]
    exact Finset.mem_inter.mpr ⟨Finset.mem_singleton.mpr rfl,
      Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr rfl))⟩
  have live2 := shared_operational_reference_stays serviceHeap serviceHeap_stores
    (anchorRoots serviceDiscovery serviceState) live0 found0 shared
  have cleared1 := projectHeap_clears_observer_reference serviceHeap serviceHeap_stores
    (anchorRoots serviceDiscovery serviceState) 1 service_operational_reference_absent
  have notCleared2 : ¬ receiptFieldCleared (projectHeap serviceHeap serviceHeap_stores)
      (anchorRoots serviceDiscovery serviceState) 2 := by
    intro cleared
    have looked : (projectHeap serviceHeap serviceHeap_stores).lookup 0 =
        some (projectCell (serviceCell 0)) := by simp [projectHeap, serviceHeap]
    have edge : (2 : Nat) ∈ (projectCell (serviceCell 0)).references := by
      have refs : (projectCell (serviceCell 0)).references = ({2} : Finset Nat) := rfl
      rw [refs]
      exact Finset.mem_singleton.mpr rfl
    exact cleared 0 live0 (projectCell (serviceCell 0)) looked edge
  have projectedAlias : Aliases (projectHeap serviceHeap serviceHeap_stores) 0 [2] 2 [] := by
    have lookup0 : (projectHeap serviceHeap serviceHeap_stores).lookup 0 =
        some (projectCell (serviceCell 0)) := by simp [projectHeap, serviceHeap]
    have lookup2 : (projectHeap serviceHeap serviceHeap_stores).lookup 2 =
        some (projectCell (serviceCell 2)) := by simp [projectHeap, serviceHeap]
    have edge : (2 : Nat) ∈ (projectCell (serviceCell 0)).references := by
      have refs : (projectCell (serviceCell 0)).references = ({2} : Finset Nat) := rfl
      rw [refs]
      exact Finset.mem_singleton.mpr rfl
    have walk0 : walk (projectHeap serviceHeap serviceHeap_stores) 0 [2] =
        some (2, projectCell (serviceCell 2)) := by
      simp only [walk, lookup0, Option.bind_some]
      rw [if_pos edge, lookup2]
      rfl
    have walk2 : walk (projectHeap serviceHeap serviceHeap_stores) 2 [] =
        some (2, projectCell (serviceCell 2)) := by
      simp only [walk, lookup2, Option.map_some]
    refine ⟨2, ?_, ?_⟩
    · rw [walk0]
      simp [Option.map_some]
    · rw [walk2]
      simp [Option.map_some]
  have imageAlias : Aliases
      (projectDiscovered serviceDiscovery serviceHeap serviceHeap_stores serviceFrame
        serviceState).privateImage 0 [2] 2 [] := by
    have aliasEq := aliases_privateImage serviceHeap serviceHeap_stores
      (anchorRoots serviceDiscovery serviceState) serviceFrame live0 live2 [2] []
    unfold projectDiscovered
    exact aliasEq.mpr projectedAlias
  obtain ⟨configEq, paid, _, observed, _, _, _, dropped, _, _, sourceWalk, projectedMiss,
      _, _, _, _, _⟩ := recorded_service_projects_stored_operational
  refine ⟨cleared1, notCleared2, dropped, imageAlias, sourceWalk, projectedMiss, observed, ?_⟩
  rw [configEq]
  exact paid

private theorem service_progress_notice :
    pump serviceStep serviceCapture serviceCapacity serviceCompatible serviceAfter =
      (.progress, serviceAfter) := rfl

private theorem service_ordinary_two :
    ordinary serviceStep serviceCapture serviceCapacity serviceCompatible 2 serviceState =
      serviceAfter := by
  have split := ordinary_add serviceStep serviceCapture serviceCapacity serviceCompatible 1 1
    serviceState
  rw [split, service_ordinary_admits]
  simp [ordinary, service_progress_notice]

private theorem service_late_items :
    (recordOrdinary serviceStep serviceCapture serviceCapacity serviceCompatible 1
      (Prefix.initial 4) serviceAfter).1.items = [.progress] := rfl

/-- Unrecorded entry and a resumed prefix both reach `serviceAfter`. Forgetting
one more ordinary step, and starting the recorder only on that configuration,
both reach the same complete configuration. Its projection reads stored
operational payload 7 and drops observer-only address 1. The late prefix
contains only `.progress`. -/
theorem service_history_entry_projects_stored :
    enterProducerHistory serviceStep serviceCapture serviceCapacity serviceCompatible
        none 1 serviceState = (none, serviceAfter) ∧
      acceptedCount (enterProducerHistory serviceStep serviceCapture serviceCapacity
        serviceCompatible none 1 serviceState).2 = 4 ∧
      (enterProducerHistory serviceStep serviceCapture serviceCapacity serviceCompatible
        (Mettapedia.GSLT.Core.InferenceControl.Recording.initial (some 4)) 1
        serviceState).2 = serviceAfter ∧
      ((enterProducerHistory serviceStep serviceCapture serviceCapacity serviceCompatible
        (Mettapedia.GSLT.Core.InferenceControl.Recording.initial (some 4)) 1
        serviceState).1).map Prefix.items = some [.admitted 0 2] ∧
      ordinary serviceStep serviceCapture serviceCapacity serviceCompatible 1
          (enterProducerHistory serviceStep serviceCapture serviceCapacity serviceCompatible
            (Mettapedia.GSLT.Core.InferenceControl.Recording.initial (some 4)) 1
            serviceState).2 =
        ordinary serviceStep serviceCapture serviceCapacity serviceCompatible 2 serviceState ∧
      (enterProducerHistory serviceStep serviceCapture serviceCapacity serviceCompatible
          (Mettapedia.GSLT.Core.InferenceControl.Recording.initial (some 4)) 1
          (ordinary serviceStep serviceCapture serviceCapacity serviceCompatible 1
            serviceState)).2 =
        ordinary serviceStep serviceCapture serviceCapacity serviceCompatible 2 serviceState ∧
      ((enterProducerHistory serviceStep serviceCapture serviceCapacity serviceCompatible
          (Mettapedia.GSLT.Core.InferenceControl.Recording.initial (some 4)) 1
          (ordinary serviceStep serviceCapture serviceCapacity serviceCompatible 1
            serviceState)).1).map Prefix.items = some [.progress] ∧
      observeOperational serviceHeap 0 = some 7 ∧
      ((projectDiscovered serviceDiscovery serviceHeap serviceHeap_stores serviceFrame
          (ordinary serviceStep serviceCapture serviceCapacity serviceCompatible 2
            serviceState)).privateImage.lookup 0).map Cell.value = some 7 ∧
      (projectDiscovered serviceDiscovery serviceHeap serviceHeap_stores serviceFrame
        (ordinary serviceStep serviceCapture serviceCapacity serviceCompatible 2
          serviceState)).privateImage.lookup 1 = none ∧
      ((projectDiscovered serviceDiscovery serviceHeap serviceHeap_stores serviceFrame
          (ordinary serviceStep serviceCapture serviceCapacity serviceCompatible 2
            serviceState)).source.lookup 0).map (fun cell => cell.value.observer) =
        some (some 99) := by
  have unrecorded := enter_unrecorded serviceStep serviceCapture serviceCapacity serviceCompatible
    1 serviceState
  have resumedConfig := enter_recorded_keeps_ordinary serviceStep serviceCapture serviceCapacity
    serviceCompatible servicePrefix 1 serviceState
  have forgotten := forget_recorded_entry_is_complete serviceStep serviceCapture serviceCapacity
    serviceCompatible servicePrefix 1 1 serviceState
  have late := late_entry_is_suffix serviceStep serviceCapture serviceCapacity serviceCompatible
    4 1 1 serviceState
  have fresh :
      Mettapedia.GSLT.Core.InferenceControl.Recording.initial
        (Event := Notice Nat Nat Unit Unit) (some 4) = some servicePrefix := rfl
  obtain ⟨_, paid, _, observed, _, _, _, _, _, _, _, _, _, afterValue, afterDropped, _, _⟩ :=
    recorded_service_projects_stored_operational
  have sameComplete : ordinary serviceStep serviceCapture serviceCapacity serviceCompatible 2
      serviceState = serviceAfter := service_ordinary_two
  refine ⟨?_, ?_, ?_, ?_, forgotten, late.1, ?_, observed, ?_, ?_, ?_⟩
  · rw [unrecorded, service_ordinary_admits]
  · rw [unrecorded, service_ordinary_admits]
    exact paid
  · rw [fresh, resumedConfig, service_ordinary_admits]
  · rw [fresh]
    have items : (recordOrdinary serviceStep serviceCapture serviceCapacity serviceCompatible 1
        servicePrefix serviceState).1.items = [.admitted 0 2] := by
      simpa [servicePrefix] using service_recorded_agrees.2.1
    simp [enterProducerHistory, items]
  · rw [fresh]
    have lateRecord : (recordOrdinary serviceStep serviceCapture serviceCapacity serviceCompatible 1
        servicePrefix (ordinary serviceStep serviceCapture serviceCapacity serviceCompatible 1
          serviceState)).1.items = [.progress] := by
      rw [service_ordinary_admits]
      exact service_late_items
    simp [enterProducerHistory, lateRecord]
  · rw [sameComplete]
    exact afterValue
  · rw [sameComplete]
    exact afterDropped
  · rw [sameComplete]
    unfold projectDiscovered
    rfl

end FieldProjection


/-! ## Shared factors as actual owned producers

The indexed producer and flat producer take different lookup paths. The
existing producer transport carries their proved step square through pending
returns, capture/admission refusal, independent consumers and publication.
-/

namespace FactorTransport

open SharedFactorMachine

variable {Input Value : Type}

def indexedStep : Checked Input Value 1 →
    ProducerOutcome (Checked Input Value 1) (Input × Value) Empty Empty := fun state =>
  match SharedFactor.peek state.val 0 with
  | .answer position value => .returned value (reposition state 0 (some (position + 1)))
  | .paused => .yielded state
  | .completed => .completed state
  | .cancelled | .invalid => .interrupted state

def flatStep : SharedOccurrenceLog.State (Input × Value) 1 →
    ProducerOutcome (SharedOccurrenceLog.State (Input × Value) 1) (Input × Value) Empty Empty :=
  fun state => match SharedOccurrenceLog.peek state 0 with
  | .answer position value =>
      .returned value (SharedOccurrenceLog.setPosition state 0 (some (position + 1)))
  | .paused => .yielded state
  | .completed => .completed state
  | .cancelled | .invalid => .interrupted state

def readback (state : Checked Input Value 1) : SharedOccurrenceLog.State (Input × Value) 1 :=
  SharedFactor.decode state.val

theorem step_readback (state : Checked Input Value 1) :
    flatStep (readback state) = (indexedStep state).mapProducer readback := by
  have same := SharedFactor.peek_decode state.val 0 state.property
  unfold flatStep indexedStep readback
  rw [← same]
  cases SharedFactor.peek state.val 0 <;> rfl

/-- Exact ownership-protocol correspondence, including the pending return
and complete producer residual. No assumption of a step square is exposed:
it is proved from the two actual reader operations above. -/
theorem run_readback {Context Output : Type} {readers : Nat}
    (capture : (Input × Value) → Option (Input × Value))
    (capacity : (Input × Value) → Bool) (compatible : Context → Bool) (ticks : Nat)
    (state : Configuration (Checked Input Value 1) (Input × Value) (Input × Value)
      Context Output Empty Empty readers) :
    run flatStep capture capacity compatible ticks (mapProducer readback state) =
      ((run indexedStep capture capacity compatible ticks state).1,
        mapProducer readback (run indexedStep capture capacity compatible ticks state).2) :=
  run_mapProducer readback indexedStep flatStep step_readback capture capacity compatible ticks state

private def sample : Checked Nat Nat 1 :=
  ⟨⟨#[7, 7], ⟨41, 0, 2, true⟩, fun _ => some 0⟩, by constructor <;> decide⟩

private def staged : Configuration (Checked Nat Nat 1) (Nat × Nat) (Nat × Nat)
    Nat Nat Empty Empty 2 :=
  (pump indexedStep some (fun _ => true) (fun _ => true) (initial sample 0 2)).2

theorem refusal_keeps_advanced_reader_and_pending_occurrence :
    staged.execution.map (fun execution => execution.producer.val.positions 0) = some (some 1) ∧
      pending staged = some (41, 7) ∧
      pump indexedStep some (fun _ => false) (fun _ => true) staged =
        (.admissionRefused, staged) := ⟨rfl, rfl, rfl⟩

theorem repeated_refusal_does_not_read_the_suffix_again :
    (run indexedStep some (fun _ => false) (fun _ => true) 20 staged).2 = staged := rfl

end FactorTransport

namespace Controls

abbrev Driver := OwnedPullDriver.State Nat Nat
abbrev Packet := Configuration Driver Nat Nat Nat Nat Empty Empty 2

def captureEvent (value : Nat) : Option Nat := some (value + 100)
def decodeEvent (value : Nat) : Nat := value - 100

theorem captureEvent_preserves_observation (value stored : Nat)
    (captured : captureEvent value = some stored) : decodeEvent stored = value := by
  simp only [captureEvent, Option.some.injEq] at captured
  subst stored
  simp [decodeEvent]

def start (limit : Nat) : Packet := initial ⟨OwnedPullDriver.exampleProgram, []⟩ 0 limit

def feed (ticks limit : Nat) : List (Notice Nat Nat Empty Empty) × Packet :=
  run driverStep captureEvent (fun _ => true) (fun _ => true) ticks (start limit)

theorem staged_occurrences_are_actual_driver_events : (feed 10 4).1.flatMap returned = [1, 1, 3] := rfl

theorem admitted_occurrences_keep_order_and_duplicates :
    (feed 10 4).1.flatMap admitted = [101, 101, 103] ∧
      (feed 10 4).2.delivery.log.rows = [101, 101, 103] := ⟨rfl, rfl⟩

/-- Both equal return occurrences stay in a prefix that has room for the whole
slice. The delivery cursors remain the initial cursors. -/
theorem recorded_slice_keeps_both_equal_returns :
    let recorded := recordOrdinary driverStep captureEvent (fun _ => true) (fun _ => true) 10
      (Mettapedia.GSLT.Core.InferenceControl.Recording.Prefix.initial 10) (start 4)
    recorded.1.items.flatMap returned = [1, 1, 3] ∧
      recorded.1.omitted = 0 ∧
      recorded.2.delivery.log.rows = [101, 101, 103] ∧
      recorded.2.delivery.log.positions 0 = some 0 ∧
      recorded.2.delivery.log.positions 1 = some 0 := by
  decide

/-- Recording that starts after the ordinary prefix does not contain that
prefix. Its complete suffix has one later equal return, not both, while both
delivery cursors stay active. -/
theorem late_recording_cannot_reconstruct_the_ordinary_prefix :
    let early := ordinary driverStep captureEvent (fun _ => true) (fun _ => true) 2 (start 4)
    let late := recordOrdinary driverStep captureEvent (fun _ => true) (fun _ => true) 8
      (Mettapedia.GSLT.Core.InferenceControl.Recording.Prefix.initial 8) early
    (feed 2 4).1.flatMap returned = [1] ∧
      late.1.omitted = 0 ∧
      late.1.items.flatMap returned ≠ [1, 1, 3] ∧
      List.isPrefixOf (feed 2 4).1 late.1.items = false ∧
      late.2.delivery.log.positions 0 = some 0 ∧
      late.2.delivery.log.positions 1 = some 0 := by
  decide

theorem completed_execution_retains_actual_final_value :
    (feed 10 4).2.execution = some ⟨⟨.done 6, []⟩, none, 3, .active⟩ ∧
      (feed 10 4).2.delivery.log.completed = true := ⟨rfl, rfl⟩

theorem driver_transitions_and_returns_have_distinct_debits :
    (feed 10 4).1.length = 10 ∧ ((feed 10 4).1.map driverTicks).sum = 5 ∧
      acceptedCount (feed 10 4).2 = 3 := ⟨rfl, rfl, rfl⟩

theorem charging_each_notice_overcharges_the_driver :
    (feed 10 4).1.length ≠ ((feed 10 4).1.map driverTicks).sum := by decide

theorem zero_limit_does_not_step_the_driver :
    (feed 20 0).2 = start 0 := rfl

theorem backpressure_does_not_charge_unexecuted_work :
    ((feed 20 0).1.map driverTicks).sum = 0 ∧
      ((feed 20 2).1.map driverTicks).sum = 4 := ⟨rfl, rfl⟩

theorem full_log_retains_unexecuted_suffix :
    (feed 20 2).2.execution = some ⟨⟨.emit 3 (.done 6), []⟩, none, 2, .active⟩ ∧
      (feed 20 2).2.delivery.log.rows = [101, 101] ∧
      (feed 20 2).2.delivery.log.completed = false := ⟨rfl, rfl, rfl⟩

def staged : Packet := (feed 2 4).2

theorem staged_return_keeps_its_caller_frame :
    staged.execution = some
      ⟨⟨.done 2, [fun value => .emit 1 (.emit 3 (.done (value + 4)))]⟩, some 1, 0, .active⟩ := rfl

theorem capture_refusal_keeps_pending_return_and_frame :
    pump driverStep (fun _ => none) (fun _ => true) (fun _ => true) staged =
      (.captureRefused, staged) := rfl

theorem capacity_refusal_keeps_pending_return_and_frame :
    pump driverStep captureEvent (fun _ => false) (fun _ => true) staged =
      (.admissionRefused, staged) := rfl

theorem repeated_refusal_does_not_reexecute_the_pending_return :
    (run driverStep captureEvent (fun _ => false) (fun _ => true) 20 staged).2 = staged := rfl

theorem refusal_and_successful_admission_do_not_recharge_the_producer :
    ((run driverStep captureEvent (fun _ => false) (fun _ => true) 20 staged).1.map driverTicks).sum = 0 ∧
      driverTicks (pump driverStep captureEvent (fun _ => true) (fun _ => true) staged).1 = 0 :=
  ⟨rfl, rfl⟩

def retried : Packet := (pump driverStep captureEvent (fun _ => true) (fun _ => true) staged).2

theorem retry_admits_once_and_preserves_the_complete_driver_residual :
    retried.delivery.log.rows = [101] ∧
      retried.execution = some
        ⟨⟨.done 2, [fun value => .emit 1 (.emit 3 (.done (value + 4)))]⟩, none, 1, .active⟩ := ⟨rfl, rfl⟩

/-- A faulty boundary dropping its pending value skips an admitted occurrence. -/
def droppedPending : Packet :=
  {staged with execution := staged.execution.map (fun execution => {execution with pending := none})}

theorem dropping_pending_loses_the_first_occurrence :
    admitted (pump driverStep captureEvent (fun _ => true) (fun _ => true) droppedPending).1 ≠ [101] := by
  decide

theorem malformed_capture_changes_the_observation :
    (admitted (pump driverStep (fun _ => some 999) (fun _ => true) (fun _ => true) staged).1).map
        decodeEvent ≠ (pending staged).toList := by decide

theorem refusal_is_not_completion :
    (pump driverStep (fun _ => none) (fun _ => true) (fun _ => true) staged).2.delivery.log.completed ≠ true := by
  decide

def deliveredA : Packet := (deliver (fun _ => true) (feed 10 4).2 0 7).2

theorem consumers_have_independent_duplicate_occurrences :
    (deliver (fun _ => true) (feed 10 4).2 0 7).1 = .observed (.answer 0 101) ∧
      (deliver (fun _ => true) deliveredA 0 7).1 = .observed (.answer 1 101) ∧
      (deliver (fun _ => true) deliveredA 1 8).1 = .observed (.answer 0 101) := ⟨rfl, rfl, rfl⟩

/-- The first occurrence is buffered while its producer retains two more
emissions and nested return work. This is not a completed log snapshot. -/
def buffered : Packet := (feed 3 4).2

theorem recursive_slice_overlaps_buffered_delivery (ticks : Nat) :
    (let produced := run driverStep captureEvent (fun _ => true) (fun _ => true) ticks buffered
     let consumed := deliver (fun _ => true) produced.2 0 7
     (produced.1, consumed.1, consumed.2)) =
      (let consumed := deliver (fun _ => true) buffered 0 7
       let produced := run driverStep captureEvent (fun _ => true) (fun _ => true) ticks consumed.2
       (produced.1, consumed.1, produced.2)) :=
  run_deliver_buffered_commute _ _ _ _ ticks buffered 0 7 0 101 rfl

theorem interleaved_delivery_retains_occurrences_cursors_and_caller :
    let consumed := deliver (fun _ => true) buffered 0 7
    let finished := run driverStep captureEvent (fun _ => true) (fun _ => true) 7 consumed.2
    finished.2.delivery.log.rows = [101, 101, 103] ∧
      finished.2.delivery.log.completed = true ∧
      finished.2.delivery.log.positions 0 = some 1 ∧
      finished.2.delivery.log.positions 1 = some 0 ∧
      (7, 101) ∈ finished.2.delivery.published := by decide

/-- An unserved consumer observes the new occurrence only after admission.
Moving that read earlier leaves it paused at its old position. -/
theorem waiting_delivery_cannot_commute_with_admission :
    (deliver (fun _ => true) staged 0 7).1 = .observed .paused ∧
      (deliver (fun _ => true) retried 0 7).1 = .observed (.answer 0 101) ∧
      (pump driverStep captureEvent (fun _ => true) (fun _ => true)
        (deliver (fun _ => true) staged 0 7).2).2.delivery.log.positions 0 = some 0 ∧
      (deliver (fun _ => true) retried 0 7).2.delivery.log.positions 0 = some 1 := by decide

theorem stale_context_cannot_deliver_a_buffered_answer :
    deliver (fun context => context == 1) (feed 10 4).2 0 7 =
      (.contextRefused, (feed 10 4).2) := rfl

theorem arbitrary_split_preserves_the_entire_configuration (first second : Nat) :
    feed (first + second) 4 =
      (let earlier := feed first 4
       let later := run driverStep captureEvent (fun _ => true) (fun _ => true) second earlier.2
       (earlier.1 ++ later.1, later.2)) := run_split _ _ _ _ first second (start 4)

abbrev SignalPacket := Configuration Nat Nat Nat Nat Nat Nat Nat 1

def signalStart : SignalPacket := initial 0 0 2

def paused : SignalPacket :=
  (pump (fun state => .yielded (state + 1)) captureEvent (fun _ => true) (fun _ => true) signalStart).2

def finished : SignalPacket :=
  (pump (fun state => .completed (state + 1)) captureEvent (fun _ => true) (fun _ => true) signalStart).2

theorem yield_and_completion_have_distinct_residuals :
    paused.execution = some ⟨1, none, 0, .active⟩ ∧
      paused.delivery.log.completed = false ∧ finished.delivery.log.completed = true := ⟨rfl, rfl, rfl⟩

def awaiting : SignalPacket :=
  (pump (fun state => .effect 7 (state + 1)) captureEvent (fun _ => true) (fun _ => true) signalStart).2

def handedOff : SignalPacket :=
  (pump (fun state => .handoff 8 (state + 1)) captureEvent (fun _ => true) (fun _ => true) signalStart).2

def interrupted : SignalPacket :=
  (pump (fun state => .interrupted (state + 1)) captureEvent (fun _ => true) (fun _ => true) signalStart).2

theorem effect_request_is_an_inert_barrier :
    pump (fun state => .returned 99 (state + 1)) captureEvent (fun _ => true) (fun _ => true) awaiting =
      (.effect 7, awaiting) ∧ awaiting.delivery.log.completed = false := ⟨rfl, rfl⟩

theorem handoff_is_an_inert_barrier :
    pump (fun state => .returned 99 (state + 1)) captureEvent (fun _ => true) (fun _ => true) handedOff =
      (.handoff 8, handedOff) ∧ handedOff.delivery.log.completed = false := ⟨rfl, rfl⟩

theorem handoff_does_not_certify_exhaustion : handedOff.delivery.log.completed ≠ true := by decide

theorem interruption_keeps_an_open_inert_residual :
    pump (fun state => .returned 99 (state + 1)) captureEvent (fun _ => true) (fun _ => true) interrupted =
      (.interrupted, interrupted) ∧ interrupted.delivery.log.completed = false := ⟨rfl, rfl⟩

theorem detach_moves_pending_and_retains_buffered_occurrences :
    (detach staged).1 = staged.execution ∧ pending (detach staged).2 = none ∧
      (detach (feed 10 4).2).2.delivery.log.rows = [101, 101, 103] := ⟨rfl, rfl, rfl⟩

theorem detached_is_distinct_from_completion :
    (pump driverStep captureEvent (fun _ => true) (fun _ => true) (detach (feed 10 4).2).2).1 =
      .detached := rfl

theorem empty_open_buffer_is_a_pause :
    (deliver (fun _ => true) signalStart 0 7).1 = .observed .paused := rfl

theorem empty_completed_buffer_is_completion :
    (deliver (fun _ => true) finished 0 7).1 = .observed .completed := rfl

abbrev EmptyPacket := Configuration Driver Nat Nat Nat Nat Empty Empty 0

def noCohort : EmptyPacket := initial ⟨OwnedPullDriver.exampleProgram, []⟩ 0 0

def noDemand : Packet :=
  {staged with delivery :=
    SharedOccurrenceOwnership.cancelConsumer (SharedOccurrenceOwnership.cancelConsumer staged.delivery 0) 1}

theorem empty_cohort_does_not_step_or_certify_exhaustion :
    pump driverStep captureEvent (fun _ => true) (fun _ => true) noCohort =
      (.noConsumers, noCohort) ∧ noCohort.delivery.log.completed = false := ⟨rfl, rfl⟩

theorem cancelled_cohort_keeps_pending_return_and_residual :
    pump driverStep captureEvent (fun _ => true) (fun _ => true) noDemand =
      (.noConsumers, noDemand) ∧ pending noDemand = some 1 := ⟨rfl, rfl⟩

theorem absent_demand_is_not_completion :
    (pump driverStep captureEvent (fun _ => true) (fun _ => true) noCohort).1 ≠ .completed := by decide

def fullHandoff : SignalPacket :=
  {handedOff with delivery := {handedOff.delivery with log := {handedOff.delivery.log with limit := 0}}}

theorem retained_handoff_precedes_row_backpressure :
    pump (fun state => .returned 99 (state + 1)) captureEvent (fun _ => true) (fun _ => true) fullHandoff =
      (.handoff 8, fullHandoff) := rfl

end Controls

/-! ## Admission and delivery history

A log position names the admission of that row. Delivering the row to two
consumers creates two uses, both citing that admission. Answer readout uses
the existing event prefix. Ancestry uses the existing causal receipt.
Refusals, barriers and cancellation stay on their original constructors.
-/

section HistoryAdapter

open Mettapedia.GSLT.Core.InferenceControl.Recording
open Mettapedia.Machines.ExecutionHistoryReadout

inductive HistoryOccurrence (clients : Nat) where
  | admission (position : Nat)
  | delivery (client : Fin clients) (position : Nat)
  deriving DecidableEq, Repr

def admissionOccurrence (position : Nat) : HistoryOccurrence clients :=
  .admission position

def deliveryOccurrence (client : Fin clients) (position : Nat) : HistoryOccurrence clients :=
  .delivery client position

def admissionCausal (position : Nat) : CausalEvent (HistoryOccurrence clients) :=
  ⟨.admission position, []⟩

def deliveryCausal (client : Fin clients) (position : Nat) :
    CausalEvent (HistoryOccurrence clients) :=
  ⟨.delivery client position, [.admission position]⟩

def noticeAdmission? (notice : Notice Borrowed Stored Effect Handoff) :
    Option (CausalEvent (HistoryOccurrence clients)) :=
  match notice with
  | .admitted position _ => some (admissionCausal position)
  | _ => none

def deliveryUse? (client : Fin clients) (reply : DeliveryReply Stored) :
    Option (CausalEvent (HistoryOccurrence clients)) :=
  match reply with
  | .observed (.answer position _) => some (deliveryCausal client position)
  | _ => none

def deliveryAnswer? (reply : DeliveryReply Stored) : Option (Event Stored) :=
  match reply with
  | .observed (.answer position value) => some ⟨position, .answer, none, some value⟩
  | _ => none

def sharedAdmissionReceipt (client other : Fin clients) (position : Nat) :
    CausalReceipt (HistoryOccurrence clients) :=
  ⟨[admissionOccurrence position],
    [admissionCausal position, deliveryCausal client position, deliveryCausal other position]⟩

theorem pump_admits
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (execution : Execution Producer Borrowed Effect Handoff)
    (value : Borrowed) (stored : Stored)
    (attached : state.execution = some execution)
    (allowed : compatible state.context = true)
    (openLog : state.delivery.log.completed = false)
    (room : state.delivery.log.rows.length < state.delivery.log.limit)
    (demanded : hasConsumers state.delivery.log = true)
    (active : execution.mode = .active) (staged : execution.pending = some value)
    (captured : capture value = some stored) (fits : capacity stored = true) :
    pump step capture capacity compatible state =
      (.admitted (SharedOccurrenceLog.pastEnd state.delivery.log) stored,
        {state with
          execution := some {execution with pending := none, accepted := execution.accepted + 1}
          delivery := {state.delivery with
            log := {state.delivery.log with rows := state.delivery.log.rows ++ [stored]}}}) := by
  simp [pump, admit, attached, allowed, openLog, room, demanded, active, staged, captured, fits,
    SharedOccurrenceLog.append, SharedOccurrenceLog.pastEnd]

theorem pump_admission_is_row_identity
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (execution : Execution Producer Borrowed Effect Handoff)
    (value : Borrowed) (stored : Stored)
    (attached : state.execution = some execution)
    (allowed : compatible state.context = true)
    (openLog : state.delivery.log.completed = false)
    (room : state.delivery.log.rows.length < state.delivery.log.limit)
    (demanded : hasConsumers state.delivery.log = true)
    (active : execution.mode = .active) (staged : execution.pending = some value)
    (captured : capture value = some stored) (fits : capacity stored = true) :
    (pump step capture capacity compatible state).1 =
        .admitted (SharedOccurrenceLog.pastEnd state.delivery.log) stored ∧
      noticeAdmission? (clients := clients) (pump step capture capacity compatible state).1 =
        some (admissionCausal (clients := clients)
          (SharedOccurrenceLog.pastEnd state.delivery.log)) ∧
      (pump step capture capacity compatible state).2.delivery.log.rows =
        state.delivery.log.rows ++ [stored] ∧
      (admissionCausal (clients := clients)
          (SharedOccurrenceLog.pastEnd state.delivery.log)).event =
        admissionOccurrence (clients := clients)
          (SharedOccurrenceLog.pastEnd state.delivery.log) ∧
      (admissionCausal (clients := clients)
          (SharedOccurrenceLog.pastEnd state.delivery.log)).directCauses =
        ([] : List (HistoryOccurrence clients)) := by
  have admitted := pump_admits step capture capacity compatible state execution value stored
    attached allowed openLog room demanded active staged captured fits
  refine ⟨congrArg Prod.fst admitted, ?_,
    congrArg (fun result => result.2.delivery.log.rows) admitted, rfl, rfl⟩
  rw [congrArg Prod.fst admitted]
  rfl

theorem admission_key_is_position (position : Nat) (left right : Stored) :
    noticeAdmission? (clients := clients)
        (.admitted position left : Notice Borrowed Stored Effect Handoff) =
      noticeAdmission? (clients := clients)
        (.admitted position right : Notice Borrowed Stored Effect Handoff) ∧
      noticeAdmission? (clients := clients)
          (.admitted position left : Notice Borrowed Stored Effect Handoff) =
        some (admissionCausal (clients := clients) position) := by
  exact ⟨rfl, rfl⟩

theorem distinct_rows_are_distinct_admissions (left right : Nat) (different : left ≠ right) :
    admissionOccurrence (clients := clients) left ≠
      admissionOccurrence (clients := clients) right := by
  intro same
  cases same
  exact different rfl

theorem deliver_observes_answer [DecidableEq Stored] [DecidableEq Output]
    (compatible : Context → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (client : Fin clients) (output : Output) (position : Nat) (value : Stored)
    (ready : compatible state.context = true)
    (waiting : SharedOccurrenceLog.peek state.delivery.log client = .answer position value) :
    (deliver compatible state client output).1 = .observed (.answer position value) ∧
      deliveryUse? client (deliver compatible state client output).1 =
        some (deliveryCausal client position) ∧
      deliveryAnswer? (deliver compatible state client output).1 =
        some ⟨position, .answer, none, some value⟩ ∧
      (deliveryCausal client position).event = deliveryOccurrence client position ∧
      (deliveryCausal client position).directCauses = [admissionOccurrence position] ∧
      deliveryOccurrence client position ≠ admissionOccurrence position := by
  have delivered := SharedOccurrenceOwnership.advance_answer state.delivery client output position
    value waiting
  refine ⟨?_, ?_, ?_, rfl, rfl, ?_⟩
  · simp [deliver, ready, delivered]
  · simp [deliver, ready, delivered, deliveryUse?, deliveryCausal]
  · simp [deliver, ready, delivered, deliveryAnswer?]
  · intro same
    cases same

theorem two_deliveries_cite_one_admission [DecidableEq Stored] [DecidableEq Output]
    (compatible : Context → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (client other : Fin clients) (output : Output) (position : Nat) (value : Stored)
    (distinct : other ≠ client) (ready : compatible state.context = true)
    (leftWaiting : SharedOccurrenceLog.peek state.delivery.log client = .answer position value)
    (rightWaiting : SharedOccurrenceLog.peek state.delivery.log other = .answer position value) :
    let left := deliver compatible state client output
    let right := deliver compatible left.2 other output
    left.1 = .observed (.answer position value) ∧
      right.1 = .observed (.answer position value) ∧
      deliveryUse? client left.1 = some (deliveryCausal client position) ∧
      deliveryUse? other right.1 = some (deliveryCausal other position) ∧
      deliveryOccurrence client position ≠ deliveryOccurrence other position ∧
      (deliveryCausal client position).directCauses = [admissionOccurrence position] ∧
      (deliveryCausal other position).directCauses = [admissionOccurrence position] := by
  have leftReply := deliver_observes_answer compatible state client output position value ready
    leftWaiting
  have stillWaiting : SharedOccurrenceLog.peek (deliver compatible state client output).2.delivery.log
      other = .answer position value := by
    rw [delivery_preserves_other_consumer compatible state client other output distinct]
    exact rightWaiting
  have rightReady : compatible (deliver compatible state client output).2.context = true := by
    simp [deliver, ready]
  have rightReply := deliver_observes_answer compatible (deliver compatible state client output).2
    other output position value rightReady stillWaiting
  refine ⟨leftReply.1, rightReply.1, leftReply.2.1, rightReply.2.1, ?_, leftReply.2.2.2.2.1,
    rightReply.2.2.2.2.1⟩
  intro same
  cases same
  exact distinct rfl

theorem equal_delivery_values_remain_two_answers (position : Nat) (value : Stored) :
    completeAnswers ((Prefix.initial 2).append
      [⟨position, Kind.answer, none, some value⟩, ⟨position, Kind.answer, none, some value⟩]) =
      some [value, value] := by
  have fits : ([⟨position, Kind.answer, none, some value⟩,
      ⟨position, Kind.answer, none, some value⟩] : List (Event Stored)).length ≤ 2 := by
    simp
  have full := (Prefix.complete_iff 2
    [⟨position, Kind.answer, none, some value⟩, ⟨position, Kind.answer, none, some value⟩]).2 fits
  unfold completeAnswers
  rw [full]
  simp [answers]
  rfl

private theorem shared_row_ordered (client other : Fin clients) (position : Nat)
    (distinct : other ≠ client) :
    CausalReceipt.Ordered ([] : List (HistoryOccurrence clients))
      [admissionCausal position, deliveryCausal client position, deliveryCausal other position] := by
  simpa [CausalReceipt.Ordered, admissionCausal, deliveryCausal] using distinct

theorem shared_row_receipt_wellFormed (client other : Fin clients) (position : Nat)
    (distinct : other ≠ client) :
    CausalReceipt.WellFormed [] (sharedAdmissionReceipt client other position) := by
  refine ⟨List.nodup_nil, shared_row_ordered client other position distinct, ?_⟩
  intro root present
  simp only [sharedAdmissionReceipt, List.mem_singleton] at present
  subst root
  simp [CausalReceipt.known, CausalReceipt.flattenedSupport, sharedAdmissionReceipt,
    admissionCausal, deliveryCausal, admissionOccurrence]

private theorem shared_row_direct (client other : Fin clients) (position : Nat)
    {cause effect : HistoryOccurrence clients} :
    (sharedAdmissionReceipt client other position).Direct cause effect ↔
      (effect = deliveryOccurrence client position ∧ cause = admissionOccurrence position) ∨
      (effect = deliveryOccurrence other position ∧ cause = admissionOccurrence position) := by
  constructor
  · intro edge
    obtain ⟨event, present, sameEvent, depends⟩ := edge
    simp only [sharedAdmissionReceipt] at present
    rcases List.mem_cons.mp present with rfl | present
    · simp [admissionCausal] at depends
    · rcases List.mem_cons.mp present with rfl | present
      · simp only [deliveryCausal, List.mem_singleton] at depends
        exact Or.inl ⟨sameEvent.symm, depends⟩
      · rcases List.mem_singleton.mp present with rfl
        simp only [deliveryCausal, List.mem_singleton] at depends
        exact Or.inr ⟨sameEvent.symm, depends⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨deliveryCausal client position, by simp [sharedAdmissionReceipt], rfl,
        by simp [deliveryCausal, admissionOccurrence]⟩
    · exact ⟨deliveryCausal other position, by simp [sharedAdmissionReceipt], rfl,
        by simp [deliveryCausal, admissionOccurrence]⟩

private theorem shared_row_no_cause_of_admission (client other : Fin clients) (position : Nat)
    (cause : HistoryOccurrence clients) :
    ¬ (sharedAdmissionReceipt client other position).Direct cause (admissionOccurrence position) := by
  intro edge
  rcases (shared_row_direct client other position).1 edge with ⟨same, _⟩ | ⟨same, _⟩
  · cases same
  · cases same

private theorem shared_row_admission_unreachable (client other : Fin clients) (position : Nat)
    (cause : HistoryOccurrence clients) :
    ¬ Relation.TransGen (sharedAdmissionReceipt client other position).Direct cause
        (admissionOccurrence position) := by
  intro path
  cases path with
  | single edge => exact shared_row_no_cause_of_admission client other position cause edge
  | tail _ edge => exact shared_row_no_cause_of_admission client other position _ edge

private theorem shared_row_use_predecessor (client other : Fin clients) (position : Nat)
    (distinct : other ≠ client) (cause use : HistoryOccurrence clients)
    (isUse : use = deliveryOccurrence client position ∨ use = deliveryOccurrence other position) :
    Relation.TransGen (sharedAdmissionReceipt client other position).Direct cause use ↔
      cause = admissionOccurrence position := by
  rcases isUse with rfl | rfl
  · constructor
    · intro path
      cases path with
      | single edge =>
          rcases (shared_row_direct client other position).1 edge with ⟨_, causeEq⟩ | ⟨same, _⟩
          · exact causeEq
          · cases same
            exact False.elim (distinct rfl)
      | tail earlier edge =>
          rcases (shared_row_direct client other position).1 edge with ⟨_, midEq⟩ | ⟨same, _⟩
          · rw [midEq] at earlier
            exact False.elim (shared_row_admission_unreachable client other position cause earlier)
          · cases same
            exact False.elim (distinct rfl)
    · intro causeEq
      subst causeEq
      exact Relation.TransGen.single ((shared_row_direct client other position).2 (Or.inl ⟨rfl, rfl⟩))
  · constructor
    · intro path
      cases path with
      | single edge =>
          rcases (shared_row_direct client other position).1 edge with ⟨same, _⟩ | ⟨_, causeEq⟩
          · cases same
            exact False.elim (distinct.symm rfl)
          · exact causeEq
      | tail earlier edge =>
          rcases (shared_row_direct client other position).1 edge with ⟨same, _⟩ | ⟨_, midEq⟩
          · cases same
            exact False.elim (distinct.symm rfl)
          · rw [midEq] at earlier
            exact False.elim (shared_row_admission_unreachable client other position cause earlier)
    · intro causeEq
      subst causeEq
      exact Relation.TransGen.single ((shared_row_direct client other position).2 (Or.inr ⟨rfl, rfl⟩))

theorem shared_row_delivery_ancestry
    (client other : Fin clients) (position : Nat) (distinct : other ≠ client) :
    ∃ clientResult otherResult : List (HistoryOccurrence clients),
      (sharedAdmissionReceipt client other position).ancestors? [] (deliveryOccurrence client position) =
        some clientResult ∧
      (sharedAdmissionReceipt client other position).ancestors? [] (deliveryOccurrence other position) =
        some otherResult ∧
      (∀ cause, cause ∈ clientResult ↔
        cause = deliveryOccurrence client position ∨ cause = admissionOccurrence position) ∧
      (∀ cause, cause ∈ otherResult ↔
        cause = deliveryOccurrence other position ∨ cause = admissionOccurrence position) := by
  have valid := shared_row_receipt_wellFormed client other position distinct
  have checked : (sharedAdmissionReceipt client other position).check [] = true :=
    (CausalReceipt.check_iff [] _).2 valid
  have clientKnown : deliveryOccurrence client position ∈
      (sharedAdmissionReceipt client other position).known [] := by
    simp [sharedAdmissionReceipt, CausalReceipt.known, CausalReceipt.flattenedSupport, deliveryCausal,
      deliveryOccurrence]
  have otherKnown : deliveryOccurrence other position ∈
      (sharedAdmissionReceipt client other position).known [] := by
    simp [sharedAdmissionReceipt, CausalReceipt.known, CausalReceipt.flattenedSupport, deliveryCausal,
      deliveryOccurrence]
  have clientRead : (sharedAdmissionReceipt client other position).ancestors? []
      (deliveryOccurrence client position) =
      some (((sharedAdmissionReceipt client other position).dependencyCatalogue []).affected
        [deliveryOccurrence client position]) := by
    simp [CausalReceipt.ancestors?, checked, clientKnown]
  have otherRead : (sharedAdmissionReceipt client other position).ancestors? []
      (deliveryOccurrence other position) =
      some (((sharedAdmissionReceipt client other position).dependencyCatalogue []).affected
        [deliveryOccurrence other position]) := by
    simp [CausalReceipt.ancestors?, checked, otherKnown]
  refine ⟨_, _, clientRead, otherRead, ?_, ?_⟩
  · intro cause
    have exact := (CausalReceipt.ancestors?_exact [] (sharedAdmissionReceipt client other position)
      (deliveryOccurrence client position) _ clientRead).2.2 cause
    rw [exact, shared_row_use_predecessor client other position distinct cause
      (deliveryOccurrence client position) (Or.inl rfl)]
  · intro cause
    have exact := (CausalReceipt.ancestors?_exact [] (sharedAdmissionReceipt client other position)
      (deliveryOccurrence other position) _ otherRead).2.2 cause
    rw [exact, shared_row_use_predecessor client other position distinct cause
      (deliveryOccurrence other position) (Or.inr rfl)]

/-- A returned producer has already advanced and incurred its driver tick before
capture refuses. The refusal notice stays `captureRefused`, and no admission
node is created. -/
theorem returned_work_remains_after_capture_refusal
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (execution : Execution Producer Borrowed Effect Handoff)
    (value : Borrowed) (next : Producer)
    (attached : state.execution = some execution)
    (allowed : compatible state.context = true)
    (openLog : state.delivery.log.completed = false)
    (room : state.delivery.log.rows.length < state.delivery.log.limit)
    (demanded : hasConsumers state.delivery.log = true)
    (active : execution.mode = .active) (empty : execution.pending = none)
    (returns : step execution.producer = .returned value next)
    (refused : capture value = none) :
    let first := pump step capture capacity compatible state
    first.1 = .returned value ∧
      driverTicks first.1 = 1 ∧
      noticeAdmission? (clients := clients) first.1 = none ∧
      pending first.2 = some value ∧
      acceptedCount first.2 = acceptedCount state ∧
      first.2.execution = some {execution with producer := next, pending := some value} ∧
      pump step capture capacity compatible first.2 = (.captureRefused, first.2) ∧
      noticeAdmission? (clients := clients)
        (.captureRefused : Notice Borrowed Stored Effect Handoff) = none := by
  have stepped : pump step capture capacity compatible state =
      (.returned value,
        {state with execution := some {execution with producer := next, pending := some value}}) := by
    simp [pump, stage, attached, allowed, openLog, room, demanded, active, empty, returns]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · simp [stepped]
  · simp [stepped, driverTicks]
  · simp [stepped, noticeAdmission?]
  · simp [stepped, pending]
  · simp [stepped, acceptedCount, attached]
  · simp [stepped]
  · rw [stepped]
    exact capture_refusal_preserves_complete_residual step capture capacity compatible
      {state with execution := some {execution with producer := next, pending := some value}}
      {execution with producer := next, pending := some value} value rfl allowed openLog room
      demanded active rfl refused

theorem effect_barrier_is_not_admission
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (execution : Execution Producer Borrowed Effect Handoff) (request : Effect)
    (attached : state.execution = some execution)
    (allowed : compatible state.context = true)
    (openLog : state.delivery.log.completed = false)
    (waiting : execution.mode = .effect request) :
    pump step capture capacity compatible state = (.effect request, state) ∧
      noticeAdmission? (clients := clients)
        (.effect request : Notice Borrowed Stored Effect Handoff) = none := by
  refine ⟨?_, rfl⟩
  simp [pump, attached, allowed, openLog, waiting]

theorem handoff_barrier_is_not_admission
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (execution : Execution Producer Borrowed Effect Handoff) (request : Handoff)
    (attached : state.execution = some execution)
    (allowed : compatible state.context = true)
    (openLog : state.delivery.log.completed = false)
    (waiting : execution.mode = .handoff request) :
    pump step capture capacity compatible state = (.handoff request, state) ∧
      noticeAdmission? (clients := clients)
        (.handoff request : Notice Borrowed Stored Effect Handoff) = none := by
  refine ⟨?_, rfl⟩
  simp [pump, attached, allowed, openLog, waiting]

theorem interruption_is_not_admission
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (execution : Execution Producer Borrowed Effect Handoff)
    (attached : state.execution = some execution)
    (allowed : compatible state.context = true)
    (openLog : state.delivery.log.completed = false)
    (waiting : execution.mode = .interrupted) :
    pump step capture capacity compatible state = (.interrupted, state) ∧
      noticeAdmission? (clients := clients)
        (.interrupted : Notice Borrowed Stored Effect Handoff) = none := by
  refine ⟨?_, rfl⟩
  simp [pump, attached, allowed, openLog, waiting]

theorem cancellation_is_not_a_delivery [DecidableEq Stored] [DecidableEq Output]
    (compatible : Context → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (client : Fin clients) (output : Output) (ready : compatible state.context = true) :
    (deliver compatible (retireConsumer state client) client output).1 = .observed .cancelled ∧
      deliveryUse? client (deliver compatible (retireConsumer state client) client output).1 = none ∧
      deliveryAnswer? (deliver compatible (retireConsumer state client) client output).1 = none ∧
      (deliver compatible (retireConsumer state client) client output).2.execution = state.execution := by
  have readyAfter : compatible (retireConsumer state client).context = true := by
    simp [retireConsumer, ready]
  have cancelled : SharedOccurrenceLog.peek
      (SharedOccurrenceLog.cancel state.delivery.log client) client = .cancelled := by
    simp [SharedOccurrenceLog.cancel, SharedOccurrenceLog.peek, SharedOccurrenceLog.setPosition_self]
  have pulled : SharedOccurrenceOwnership.advance
      (SharedOccurrenceOwnership.cancelConsumer state.delivery client) client output =
      (.cancelled, SharedOccurrenceOwnership.cancelConsumer state.delivery client) := by
    simp [SharedOccurrenceOwnership.cancelConsumer, SharedOccurrenceOwnership.advance,
      SharedOccurrenceOwnership.acknowledge, SharedOccurrenceOwnership.prepare,
      SharedOccurrenceLog.pull, cancelled]
  unfold deliver
  rw [readyAfter]
  simp only [if_true, retireConsumer]
  simp [pulled, deliveryUse?, deliveryAnswer?]

/-- One admitted row, delivered to two consumers. Both uses cite that admission
and remain distinct when the stored value is the same. -/
def serviceCohortStep (_ : Unit) : ProducerOutcome Unit Nat Unit Unit :=
  .returned 2 ()

def serviceCohort : Configuration Unit Nat Nat Nat Unit Unit Unit 2 :=
  initial () 8 2

theorem service_one_row_two_consumers :
    let returned := pump serviceCohortStep (fun value => some value) (fun _ => true) (fun _ => true)
      serviceCohort
    let admitted := pump serviceCohortStep (fun value => some value) (fun _ => true) (fun _ => true)
      returned.2
    let left := deliver (fun _ => true) admitted.2 (0 : Fin 2) ()
    let right := deliver (fun _ => true) left.2 (1 : Fin 2) ()
    returned.1 = .returned 2 ∧
      driverTicks returned.1 = 1 ∧
      noticeAdmission? (clients := clients) returned.1 = none ∧
      admitted.1 = .admitted 0 2 ∧
      noticeAdmission? (clients := clients) admitted.1 =
        some (admissionCausal (clients := clients) 0) ∧
      admitted.2.delivery.log.rows = [2] ∧
      left.1 = .observed (.answer 0 2) ∧
      right.1 = .observed (.answer 0 2) ∧
      deliveryOccurrence (0 : Fin 2) 0 ≠ deliveryOccurrence (1 : Fin 2) 0 ∧
      (deliveryCausal (0 : Fin 2) 0).directCauses = [admissionOccurrence 0] ∧
      (deliveryCausal (1 : Fin 2) 0).directCauses = [admissionOccurrence 0] ∧
      completeAnswers ((Prefix.initial 2).append
        [⟨0, Kind.answer, none, some 2⟩, ⟨0, Kind.answer, none, some 2⟩]) = some [2, 2] := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, rfl, rfl,
    equal_delivery_values_remain_two_answers 0 2⟩
  decide

theorem service_return_survives_capture_refusal :
    let returned := pump serviceCohortStep (fun value => some value) (fun _ => true) (fun _ => true)
      serviceCohort
    returned.1 = .returned 2 ∧
      driverTicks returned.1 = 1 ∧
      pending returned.2 = some 2 ∧
      acceptedCount returned.2 = 0 ∧
      pump serviceCohortStep (fun _ => none) (fun _ => true) (fun _ => true) returned.2 =
        (.captureRefused, returned.2) ∧
      noticeAdmission? (clients := clients)
        (.captureRefused : Notice Nat Nat Unit Unit) = none := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end HistoryAdapter

/-! ## Online production and delivery accounts

Numerical observation is independent of history retention. The ordinary entry
uses the existing uncounted runner. A requested account streams its updates
from each actual producer/delivery reply, without retaining a notice list or
building the mathematical path used in its comparison theorem. These are
protocol units: driver progress and successful consumer delivery. They do not
bound arbitrary callback work, physical instructions or external services.
-/

namespace Accounting

open _root_.CategoryTheory Mettapedia.Effects Mettapedia.GSLT.Contracts.Accounts

variable {Producer Borrowed Stored Context Output Effect Handoff : Type}
variable {clients : Nat}

/-- One observed answer is one delivery unit. Every other reply is zero. -/
def answerUnits : DeliveryReply Stored → Nat
  | .observed (.answer _ _) => 1
  | .observed .paused => 0
  | .observed .completed => 0
  | .observed .cancelled => 0
  | .observed .invalid => 0
  | .contextRefused => 0

/-- The two protocol coordinates. Multiplication is componentwise. -/
abbrev ProtocolAccount := Multiplicative Nat × Multiplicative Nat

/-- Production charge of one pump notice. The delivery coordinate stays the unit. -/
def productionCharge (notice : Notice Borrowed Stored Effect Handoff) : ProtocolAccount :=
  (Multiplicative.ofAdd (driverTicks notice), 1)

/-- Delivery charge of one reply. The production coordinate stays the unit. -/
def deliveryCharge (reply : DeliveryReply Stored) : ProtocolAccount :=
  (1, Multiplicative.ofAdd (answerUnits reply))

theorem driverTicks_progress :
    driverTicks (.progress : Notice Borrowed Stored Effect Handoff) = 1 := rfl

theorem driverTicks_returned (value : Borrowed) :
    driverTicks (.returned value : Notice Borrowed Stored Effect Handoff) = 1 := rfl

theorem driverTicks_admitted (position : Nat) (value : Stored) :
    driverTicks (.admitted position value : Notice Borrowed Stored Effect Handoff) = 0 := rfl

theorem driverTicks_captureRefused :
    driverTicks (.captureRefused : Notice Borrowed Stored Effect Handoff) = 0 := rfl

theorem driverTicks_admissionRefused :
    driverTicks (.admissionRefused : Notice Borrowed Stored Effect Handoff) = 0 := rfl

/-- Admission, capture refusal, and admission refusal are the monoid unit.
None of them is another production unit. -/
theorem quiet_notices_are_not_production :
    productionCharge (.captureRefused : Notice Borrowed Stored Effect Handoff) = 1 ∧
      productionCharge (.admissionRefused : Notice Borrowed Stored Effect Handoff) = 1 ∧
      ∀ (position : Nat) (value : Stored),
        productionCharge (.admitted position value : Notice Borrowed Stored Effect Handoff) = 1 := by
  exact ⟨rfl, rfl, fun _ _ => rfl⟩

theorem answerUnits_answer (position : Nat) (value : Stored) :
    answerUnits (.observed (SharedOccurrenceLog.Reply.answer position value)) = 1 := rfl

theorem answerUnits_cancelled :
    answerUnits (.observed (SharedOccurrenceLog.Reply.cancelled : SharedOccurrenceLog.Reply Stored)) = 0 := rfl

theorem answerUnits_contextRefused :
    answerUnits (.contextRefused : DeliveryReply Stored) = 0 := rfl

/-- A requested producer step or one consumer delivery. -/
inductive Action (Output : Type) (clients : Nat) where
  | pump
  | deliver (client : Fin clients) (output : Output)

variable [DecidableEq Stored] [DecidableEq Output]
variable (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
variable (capture : Borrowed → Option Stored)
variable (capacity : Stored → Bool)
variable (compatible : Context → Bool)

/-- Execute one request. `pump` or `deliver` is called once; `result` is that
returned pair. The next configuration and the account are its two components. -/
def advanceAction (action : Action Output clients)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    Configuration Producer Borrowed Stored Context Output Effect Handoff clients ×
      ProtocolAccount :=
  match action with
  | .pump =>
      let result := pump step capture capacity compatible state
      (result.2, productionCharge result.1)
  | .deliver client output =>
      let result := deliver compatible state client output
      (result.2, deliveryCharge result.1)

/-- Uncounted interleaved execution. The match is the action, and the next
configuration is `.2` of that `pump` or `deliver`. No charge is calculated. -/
def runActions : List (Action Output clients) →
    Configuration Producer Borrowed Stored Context Output Effect Handoff clients →
    Configuration Producer Borrowed Stored Context Output Effect Handoff clients
  | [], state => state
  | .pump :: rest, state =>
      runActions rest (ProducerOccurrenceLog.pump step capture capacity compatible state).2
  | .deliver client output :: rest, state =>
      runActions rest (ProducerOccurrenceLog.deliver compatible state client output).2

/-- The counted step reaches the same configuration as one uncounted action. -/
theorem advanceAction_state (action : Action Output clients)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    (advanceAction step capture capacity compatible action state).1 =
      runActions step capture capacity compatible [action] state := by
  cases action <;> simp [advanceAction, runActions]

/-- Online accumulation. `advanced` is one `advanceAction` pair. The account is
multiplied by that pair's charge and the next step starts at that pair's
configuration. The notice or reply is not retained. -/
def count : List (Action Output clients) → ProtocolAccount →
    Configuration Producer Borrowed Stored Context Output Effect Handoff clients →
    Configuration Producer Borrowed Stored Context Output Effect Handoff clients × ProtocolAccount
  | [], account, state => (state, account)
  | action :: rest, account, state =>
      let advanced := advanceAction step capture capacity compatible action state
      count rest (account * advanced.2) advanced.1

theorem count_erases (actions : List (Action Output clients)) (account : ProtocolAccount)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    (count step capture capacity compatible actions account state).1 =
      runActions step capture capacity compatible actions state := by
  induction actions generalizing account state with
  | nil => rfl
  | cons action rest ih =>
      cases action with
      | pump => simp only [count, advanceAction, runActions, ih]
      | deliver _ _ => simp only [count, advanceAction, runActions, ih]

theorem runActions_pumps_are_ordinary (ticks : Nat)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    runActions step capture capacity compatible (List.replicate ticks Action.pump) state =
      ordinary step capture capacity compatible ticks state := by
  induction ticks generalizing state with
  | zero => rfl
  | succ _ ih =>
      simp only [List.replicate_succ, runActions, ordinary]
      exact ih _

/-- A finite pump request erases to ordinary composition. The account is not
an input of `ordinary`. -/
theorem finite_pumps_erase (first second : Nat) (account : ProtocolAccount)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    (count step capture capacity compatible
        (List.replicate (first + second) Action.pump) account state).1 =
      ordinary step capture capacity compatible second
        (ordinary step capture capacity compatible first state) := by
  rw [count_erases, runActions_pumps_are_ordinary, ordinary_add]

/-- Composition of an arbitrary finite request. -/
theorem runActions_append (first second : List (Action Output clients))
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    runActions step capture capacity compatible (first ++ second) state =
      runActions step capture capacity compatible second
        (runActions step capture capacity compatible first state) := by
  induction first generalizing state with
  | nil => rfl
  | cons action rest ih =>
      cases action with
      | pump => simp only [List.cons_append, runActions, ih]
      | deliver _ _ => simp only [List.cons_append, runActions, ih]

theorem count_append (first second : List (Action Output clients))
    (account : ProtocolAccount)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    count step capture capacity compatible (first ++ second) account state =
      count step capture capacity compatible second
        (count step capture capacity compatible first account state).2
        (count step capture capacity compatible first account state).1 := by
  induction first generalizing account state with
  | nil => rfl
  | cons _ _ ih =>
      simp only [List.cons_append, count, ih]

theorem count_scales (actions : List (Action Output clients))
    (account : ProtocolAccount)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    (count step capture capacity compatible actions account state).2 =
      account * (count step capture capacity compatible actions (1, 1) state).2 := by
  induction actions generalizing account state with
  | nil => simp [count]
  | cons action rest ih =>
      simp only [count]
      rw [ih (account * (advanceAction step capture capacity compatible action state).2)]
      rw [ih (((1, 1) : ProtocolAccount) *
        (advanceAction step capture capacity compatible action state).2)]
      simp [mul_assoc]

/-- A paid pump followed by a quiet pump keeps exactly that one production unit.
A follow-up whose notice is admission, capture refusal, or admission refusal
is quiet, so a retry or an admission does not open another production unit. -/
theorem paid_production_survives_quiet_followup
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (account : ProtocolAccount)
    (paid : driverTicks (pump step capture capacity compatible state).1 = 1)
    (quiet : driverTicks (pump step capture capacity compatible
        (pump step capture capacity compatible state).2).1 = 0) :
    (count step capture capacity compatible [Action.pump, Action.pump] account state).2 =
      account * (Multiplicative.ofAdd 1, 1) := by
  simp only [count, advanceAction, productionCharge, paid, quiet]
  rfl

theorem one_observed_answer
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (account : ProtocolAccount) (client : Fin clients) (output : Output)
    (answered : answerUnits (deliver compatible state client output).1 = 1) :
    (count step capture capacity compatible [Action.deliver client output] account state).2 =
      account * (1, Multiplicative.ofAdd 1) := by
  simp only [count, advanceAction, deliveryCharge, answered]

/-- Each observed answer contributes its own delivery unit, whatever the
client, position, or stored value. -/
theorem successive_answers_are_separate_deliveries
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (account : ProtocolAccount)
    (client other : Fin clients) (output otherOutput : Output)
    (first : answerUnits (deliver compatible state client output).1 = 1)
    (second : answerUnits (deliver compatible
        (deliver compatible state client output).2 other otherOutput).1 = 1) :
    (count step capture capacity compatible
        [Action.deliver client output, Action.deliver other otherOutput] account state).2 =
      account * (1, Multiplicative.ofAdd 2) := by
  simp only [count, advanceAction, deliveryCharge, first, second]
  rfl

theorem quiet_delivery_keeps_account
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (account : ProtocolAccount) (client : Fin clients) (output : Output)
    (quiet : answerUnits (deliver compatible state client output).1 = 0) :
    (count step capture capacity compatible [Action.deliver client output] account state).2 =
      account := by
  simp only [count, advanceAction, deliveryCharge, quiet]
  rfl

/-! ### Retirement under interleaved production and delivery -/
section InterleavedRetirement

variable {Producer Borrowed Stored Context Output Effect Handoff : Type}
variable {clients : Nat}

/-- No delivery in the list names `retired`. Pumps, and deliveries to every
other consumer, are allowed. -/
def sparesRetired (retired : Fin clients) : List (Action Output clients) → Prop
  | [] => True
  | .pump :: rest => sparesRetired retired rest
  | .deliver client _ :: rest => client ≠ retired ∧ sparesRetired retired rest

/-- Delivery to a different consumer commutes with retirement. The reply is
the same reply, so its delivery charge is the same charge. The configuration
is that delivery with the retirement applied afterwards. An incompatible
context refuses on both sides and leaves the producer state in place. -/
theorem deliver_after_retained_demand
    [DecidableEq Stored] [DecidableEq Output]
    (compatible : Context → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (retired other : Fin clients) (output : Output)
    (distinct : other ≠ retired) :
    deliver compatible (retireConsumer state retired) other output =
      ((deliver compatible state other output).1,
        retireConsumer (deliver compatible state other output).2 retired) ∧
      deliveryCharge (deliver compatible (retireConsumer state retired) other output).1 =
        deliveryCharge (deliver compatible state other output).1 := by
  have same : deliver compatible (retireConsumer state retired) other output =
      ((deliver compatible state other output).1,
        retireConsumer (deliver compatible state other output).2 retired) := by
    cases ready : compatible state.context with
    | true =>
        have raw := retireConsumer_resumes_other compatible state retired other output distinct ready
        dsimp only at raw
        exact raw
    | false =>
        have retiredReady : compatible (retireConsumer state retired).context = false := by
          rw [(retireConsumer_retains_paid_source state retired).2.1]
          exact ready
        rw [buffered_context_refusal_preserves_complete_residual compatible
            (retireConsumer state retired) other output retiredReady,
          buffered_context_refusal_preserves_complete_residual compatible
            state other output ready]
  exact ⟨same, congrArg (fun result => deliveryCharge result.1) same⟩

/-- An observed answer to `recipient` advances that cursor by one occurrence.
Any other reply, including context refusal, leaves every cursor in place.
A consumer other than `recipient` keeps `position`. -/
theorem deliver_cursor
    [DecidableEq Stored] [DecidableEq Output]
    (compatible : Context → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (recipient witness : Fin clients) (output : Output) (position : Nat)
    (live : state.delivery.log.positions witness = some position) :
    (deliver compatible state recipient output).2.delivery.log.positions witness =
      if witness = recipient then
        match (deliver compatible state recipient output).1 with
        | .observed (.answer _ _) => some (position + 1)
        | _ => some position
      else some position := by
  by_cases same : witness = recipient
  · rw [if_pos same]
    cases ready : compatible state.context with
    | false =>
        simp only [buffered_context_refusal_preserves_complete_residual compatible
          state recipient output ready, live]
    | true =>
        cases peekEq : SharedOccurrenceLog.peek state.delivery.log recipient with
        | answer found value =>
            have cursor :=
              (SharedOccurrenceLog.answer_within state.delivery.log recipient found value peekEq).1
            have found_eq : found = position := by
              rw [same] at live
              exact Option.some.inj (cursor.symm.trans live)
            simp only [deliver, ready, ↓reduceIte,
              SharedOccurrenceOwnership.advance_answer state.delivery recipient output
                found value peekEq,
              SharedOccurrenceLog.setPosition_self, same, found_eq]
        | paused =>
            simp only [deliver, ready, ↓reduceIte, SharedOccurrenceOwnership.advance,
              SharedOccurrenceOwnership.acknowledge, SharedOccurrenceOwnership.prepare,
              SharedOccurrenceLog.pull, peekEq]
            exact same ▸ live
        | completed =>
            simp only [deliver, ready, ↓reduceIte, SharedOccurrenceOwnership.advance,
              SharedOccurrenceOwnership.acknowledge, SharedOccurrenceOwnership.prepare,
              SharedOccurrenceLog.pull, peekEq]
            exact same ▸ live
        | cancelled =>
            simp only [deliver, ready, ↓reduceIte, SharedOccurrenceOwnership.advance,
              SharedOccurrenceOwnership.acknowledge, SharedOccurrenceOwnership.prepare,
              SharedOccurrenceLog.pull, peekEq]
            exact same ▸ live
        | invalid =>
            simp only [deliver, ready, ↓reduceIte, SharedOccurrenceOwnership.advance,
              SharedOccurrenceOwnership.acknowledge, SharedOccurrenceOwnership.prepare,
              SharedOccurrenceLog.pull, peekEq]
            exact same ▸ live
  · rw [if_neg same]
    cases ready : compatible state.context with
    | false =>
        simp only [buffered_context_refusal_preserves_complete_residual compatible
          state recipient output ready, live]
    | true =>
        cases peekEq : SharedOccurrenceLog.peek state.delivery.log recipient with
        | answer found value =>
            simp only [deliver, ready, ↓reduceIte,
              SharedOccurrenceOwnership.advance_answer state.delivery recipient output
                found value peekEq,
              SharedOccurrenceLog.setPosition_other state.delivery.log recipient witness
                (some (found + 1)) same,
              live]
        | paused =>
            simp only [deliver, ready, ↓reduceIte, SharedOccurrenceOwnership.advance,
              SharedOccurrenceOwnership.acknowledge, SharedOccurrenceOwnership.prepare,
              SharedOccurrenceLog.pull, peekEq, live]
        | completed =>
            simp only [deliver, ready, ↓reduceIte, SharedOccurrenceOwnership.advance,
              SharedOccurrenceOwnership.acknowledge, SharedOccurrenceOwnership.prepare,
              SharedOccurrenceLog.pull, peekEq, live]
        | cancelled =>
            simp only [deliver, ready, ↓reduceIte, SharedOccurrenceOwnership.advance,
              SharedOccurrenceOwnership.acknowledge, SharedOccurrenceOwnership.prepare,
              SharedOccurrenceLog.pull, peekEq, live]
        | invalid =>
            simp only [deliver, ready, ↓reduceIte, SharedOccurrenceOwnership.advance,
              SharedOccurrenceOwnership.acknowledge, SharedOccurrenceOwnership.prepare,
              SharedOccurrenceLog.pull, peekEq, live]

/-- Action lists that never deliver to `retired` commute with that retirement
while `other` still has a cursor. The account is the account of the same
replies and pump notices. The configuration is `retireConsumer` of the
unretired run, so a cursor advanced by an answer has its new position there.
`runActions` is that configuration via `count_erases`. Delivery to `retired`
is excluded by `sparesRetired`. -/
theorem count_after_retained_demand
    [DecidableEq Stored] [DecidableEq Output]
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool)
    (actions : List (Action Output clients)) (account : ProtocolAccount)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (retired other : Fin clients) (position : Nat)
    (distinct : other ≠ retired)
    (live : state.delivery.log.positions other = some position)
    (spares : sparesRetired retired actions) :
    count step capture capacity compatible actions account (retireConsumer state retired) =
      (retireConsumer (count step capture capacity compatible actions account state).1 retired,
        (count step capture capacity compatible actions account state).2) := by
  suffices ∀ actions account state position,
      state.delivery.log.positions other = some position →
      sparesRetired retired actions →
      count step capture capacity compatible actions account (retireConsumer state retired) =
        (retireConsumer (count step capture capacity compatible actions account state).1 retired,
          (count step capture capacity compatible actions account state).2) by
    exact this actions account state position live spares
  intro actions
  induction actions with
  | nil => exact fun _ _ _ _ _ => rfl
  | cons action rest ih =>
      intro account state position live spares
      cases action with
      | pump =>
          have tail : sparesRetired retired rest := by
            simpa [sparesRetired] using spares
          have preserved := pump_preserves_context_cursors_publications step capture capacity
            compatible state
          have kept := (congrFun preserved.2.2.1 other).trans live
          have first := pump_after_retained_demand step capture capacity compatible state
            retired other position distinct live
          simpa only [count, advanceAction, first] using
            ih (account * productionCharge (pump step capture capacity compatible state).1)
              (pump step capture capacity compatible state).2 position kept tail
      | deliver recipient output =>
          have spared : recipient ≠ retired ∧ sparesRetired retired rest := by
            simpa [sparesRetired] using spares
          have stepped :=
            (deliver_after_retained_demand compatible state retired recipient output spared.1).1
          have equation := deliver_cursor compatible state recipient other output position live
          suffices ∃ position',
              (deliver compatible state recipient output).2.delivery.log.positions other =
                some position' by
            obtain ⟨position', kept⟩ := this
            simpa only [count, advanceAction, stepped] using
              ih (account * deliveryCharge (deliver compatible state recipient output).1)
                (deliver compatible state recipient output).2 position' kept spared.2
          by_cases same : other = recipient
          · rw [if_pos same] at equation
            cases replyEq : (deliver compatible state recipient output).1 with
            | observed reply =>
                cases reply with
                | answer _ _ =>
                    simp only [replyEq] at equation
                    exact ⟨position + 1, equation⟩
                | paused =>
                    simp only [replyEq] at equation
                    exact ⟨position, equation⟩
                | completed =>
                    simp only [replyEq] at equation
                    exact ⟨position, equation⟩
                | cancelled =>
                    simp only [replyEq] at equation
                    exact ⟨position, equation⟩
                | invalid =>
                    simp only [replyEq] at equation
                    exact ⟨position, equation⟩
            | contextRefused =>
                simp only [replyEq] at equation
                exact ⟨position, equation⟩
          · rw [if_neg same] at equation
            exact ⟨position, equation⟩

/-- The uncounted walk is the configuration component of `count_after_retained_demand`. -/
theorem runActions_after_retained_demand
    [DecidableEq Stored] [DecidableEq Output]
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool)
    (actions : List (Action Output clients))
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (retired other : Fin clients) (position : Nat)
    (distinct : other ≠ retired)
    (live : state.delivery.log.positions other = some position)
    (spares : sparesRetired retired actions) :
    runActions step capture capacity compatible actions (retireConsumer state retired) =
      retireConsumer (runActions step capture capacity compatible actions state) retired := by
  have counted := count_after_retained_demand step capture capacity compatible actions (1, 1)
    state retired other position distinct live spares
  have states := congrArg Prod.fst counted
  rw [count_erases step capture capacity compatible actions (1, 1) (retireConsumer state retired),
    count_erases step capture capacity compatible actions (1, 1) state] at states
  exact states

/-- Delivering to the retired consumer is not the retained-demand commute.
Consumer 1 still has its cursor, so this is not the last-consumer stop.
The excluded action delivers to consumer 0: the reply is `.cancelled`, that
cursor stays `none`, and no answer is published. The same delivery before
retirement observes the admitted row, moves consumer 0 from `some 0` to
`some 1`, and publishes that row. The accounts differ by that answer unit. -/
theorem delivery_to_the_retired_consumer_is_not_retained :
    ¬ sparesRetired (0 : Fin 2) [.deliver (0 : Fin 2) ()] ∧
      let earlier := count serviceCohortStep some (fun _ => true) (fun _ => true)
        [.pump, .pump] (1, 1) serviceCohort
      let cancelled := retireConsumer earlier.1 (0 : Fin 2)
      let toRetired := deliver (fun _ => true) cancelled (0 : Fin 2) ()
      let toLive := deliver (fun _ => true) earlier.1 (0 : Fin 2) ()
      earlier.1.delivery.log.positions (1 : Fin 2) = some 0 ∧
        toRetired.1 = .observed .cancelled ∧
        toRetired.2.delivery.log.positions (0 : Fin 2) = none ∧
        toRetired.2.delivery.published = ∅ ∧
        toLive.1 = .observed (.answer 0 2) ∧
        toLive.2.delivery.log.positions (0 : Fin 2) = some 1 ∧
        ((), 2) ∈ toLive.2.delivery.published ∧
        (count serviceCohortStep some (fun _ => true) (fun _ => true)
          [.deliver (0 : Fin 2) ()] earlier.2 cancelled).2 ≠
          (count serviceCohortStep some (fun _ => true) (fun _ => true)
            [.deliver (0 : Fin 2) ()] earlier.2 earlier.1).2 := by
  refine ⟨?_, ?_⟩
  · intro spared
    simp only [sparesRetired] at spared
    exact spared.1 rfl
  · decide

end InterleavedRetirement

section PumpObservation

omit [DecidableEq Stored] [DecidableEq Output]

/-- Count `fuel` pumps. The actual `pump` result supplies both the next
configuration and the charge. No action list or equality test is needed. -/
def countPumps : Nat → ProtocolAccount →
    Configuration Producer Borrowed Stored Context Output Effect Handoff clients →
    Configuration Producer Borrowed Stored Context Output Effect Handoff clients × ProtocolAccount
  | 0, account, state => (state, account)
  | fuel + 1, account, state =>
      let result := pump step capture capacity compatible state
      countPumps fuel (account * productionCharge result.1) result.2

/-- A fuel count erases to the existing ordinary runner. -/
theorem countPumps_erases (fuel : Nat) (account : ProtocolAccount)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    (countPumps step capture capacity compatible fuel account state).1 =
      ordinary step capture capacity compatible fuel state := by
  induction fuel generalizing account state with
  | zero => rfl
  | succ _ ih =>
      simp only [countPumps, ordinary, ih]

/-- Split fuel erases to ordinary composition. The account is not an input of
`ordinary`. -/
theorem countPumps_add_erases (first second : Nat) (account : ProtocolAccount)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    (countPumps step capture capacity compatible (first + second) account state).1 =
      ordinary step capture capacity compatible second
        (ordinary step capture capacity compatible first state) := by
  rw [countPumps_erases, ordinary_add]

/-- Split fuel returns the whole pair. The second segment starts at the first
segment's configuration and multiplies from its accumulated account. -/
theorem countPumps_add (first second : Nat) (account : ProtocolAccount)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    countPumps step capture capacity compatible (first + second) account state =
      countPumps step capture capacity compatible second
        (countPumps step capture capacity compatible first account state).2
        (countPumps step capture capacity compatible first account state).1 := by
  induction first generalizing account state with
  | zero => simp only [Nat.zero_add, countPumps]
  | succ _ ih => simp only [Nat.succ_add, countPumps, ih]

/-- Cancelling one consumer leaves the other consumer's producer work and
account unchanged. The resulting configuration keeps the cancellation. -/
theorem countPumps_after_retained_demand (fuel : Nat) (account : ProtocolAccount)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (client other : Fin clients) (position : Nat) (distinct : other ≠ client)
    (live : state.delivery.log.positions other = some position) :
    countPumps step capture capacity compatible fuel account (retireConsumer state client) =
      (retireConsumer (countPumps step capture capacity compatible fuel account state).1 client,
        (countPumps step capture capacity compatible fuel account state).2) := by
  induction fuel generalizing account state with
  | zero => rfl
  | succ fuel ih =>
      have preserved := pump_preserves_context_cursors_publications step capture capacity
        compatible state
      have kept := (congrFun preserved.2.2.1 other).trans live
      have first := pump_after_retained_demand step capture capacity compatible state
        client other position distinct live
      simpa only [countPumps, first] using
        ih (account * productionCharge (pump step capture capacity compatible state).1)
          (pump step capture capacity compatible state).2 kept

/-- Retiring the last consumer stops production. The retained execution and
the already paid account remain at that boundary; no new work is charged. -/
theorem countPumps_after_sole_retirement (fuel : Nat) (account : ProtocolAccount)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (client : Fin clients) (execution : Execution Producer Borrowed Effect Handoff)
    (sole : ∀ other, other ≠ client → state.delivery.log.positions other = none)
    (attached : state.execution = some execution)
    (allowed : compatible state.context = true)
    (openLog : state.delivery.log.completed = false)
    (active : execution.mode = .active) :
    countPumps step capture capacity compatible fuel account (retireConsumer state client) =
      (retireConsumer state client, account) := by
  induction fuel generalizing account with
  | zero => rfl
  | succ fuel ih =>
      rw [countPumps, retire_last_consumer_stops step capture capacity compatible state client
        execution sole attached allowed openLog active]
      change countPumps step capture capacity compatible fuel (account * 1)
        (retireConsumer state client) = (retireConsumer state client, account)
      simpa only [mul_one] using ih account

/-- Entry-selected pump count. `none` is ordinary execution and calculates no
charge. `some account` continues `countPumps` from that account. -/
def enterCounted : Option ProtocolAccount → Nat →
    Configuration Producer Borrowed Stored Context Output Effect Handoff clients →
    Option ProtocolAccount ×
      Configuration Producer Borrowed Stored Context Output Effect Handoff clients
  | none, fuel, state =>
      (none, ordinary step capture capacity compatible fuel state)
  | some account, fuel, state =>
      let continued := countPumps step capture capacity compatible fuel account state
      (some continued.2, continued.1)

theorem enterCounted_unrecorded (fuel : Nat)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    enterCounted step capture capacity compatible none fuel state =
      (none, ordinary step capture capacity compatible fuel state) := rfl

/-- Both entries reach the ordinary configuration. The disabled entry does so
without calculating a charge. -/
theorem enterCounted_erases (choice : Option ProtocolAccount) (fuel : Nat)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    (enterCounted step capture capacity compatible choice fuel state).2 =
      ordinary step capture capacity compatible fuel state := by
  cases choice with
  | none => rfl
  | some _ => simp only [enterCounted, countPumps_erases]

/-- The second slice receives the account left by the first. A disabled entry
composes by `ordinary_add`. -/
theorem enterCounted_split (choice : Option ProtocolAccount) (first second : Nat)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    enterCounted step capture capacity compatible choice (first + second) state =
      enterCounted step capture capacity compatible
        (enterCounted step capture capacity compatible choice first state).1
        second
        (enterCounted step capture capacity compatible choice first state).2 := by
  cases choice with
  | none => simp only [enterCounted, ordinary_add]
  | some _ => simp only [enterCounted, countPumps_add]

end PumpObservation

/-- The direct fuel worker has the same complete result as the action-list
reference. The fuel worker itself never allocates that reference list. -/
theorem countPumps_eq_count (fuel : Nat) (account : ProtocolAccount)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    countPumps step capture capacity compatible fuel account state =
      count step capture capacity compatible (List.replicate fuel Action.pump) account state := by
  induction fuel generalizing account state with
  | zero => rfl
  | succ _ ih => simp only [countPumps, List.replicate_succ, count, advanceAction, ih]

/-! ## Independent path-account reference

Each edge is one existing action applied to the uncounted source transition.
The reference category is selected explicitly; it is never runtime state.
-/

local notation "Cfg" =>
  Configuration Producer Borrowed Stored Context Output Effect Handoff clients

inductive ActionEdge : Cfg → Cfg → Type where
  | ofAction (source : Cfg) (action : Action Output clients) :
      ActionEdge source (runActions step capture capacity compatible [action] source)

abbrev actionQuiver : Quiver Cfg :=
  ⟨ActionEdge step capture capacity compatible⟩

/-- Edge charges read the actual operation's reply, independently of `count`. -/
def edgeCharge {source target : Cfg}
    (edge : ActionEdge step capture capacity compatible source target) : ProtocolAccount := by
  cases edge with
  | ofAction action =>
      cases action with
      | pump => exact productionCharge (pump step capture capacity compatible source).1
      | deliver client output => exact deliveryCharge (deliver compatible source client output).1

def progressAccount :
    letI := actionQuiver (Output := Output) (clients := clients) step capture capacity compatible
    RunAccount (Paths Cfg) (Multiplicative Nat) := by
  letI := actionQuiver (Output := Output) (clients := clients) step capture capacity compatible
  exact pathAccount (fun edge => (edgeCharge step capture capacity compatible edge).1)

def deliveryAccount :
    letI := actionQuiver (Output := Output) (clients := clients) step capture capacity compatible
    RunAccount (Paths Cfg) (Multiplicative Nat) := by
  letI := actionQuiver (Output := Output) (clients := clients) step capture capacity compatible
  exact pathAccount (fun edge => (edgeCharge step capture capacity compatible edge).2)

/-- The existing product account keeps production and delivery separate. -/
def splitAccount :
    letI := actionQuiver (Output := Output) (clients := clients) step capture capacity compatible
    RunAccount (Paths Cfg) ProtocolAccount := by
  letI := actionQuiver (Output := Output) (clients := clients) step capture capacity compatible
  exact (progressAccount step capture capacity compatible).prod
    (deliveryAccount step capture capacity compatible)

/-- A mathematical path of the uncounted walk; no worker constructs it. -/
def actionPath : (actions : List (Action Output clients)) → (state : Cfg) →
    letI := actionQuiver (Output := Output) (clients := clients) step capture capacity compatible
    Quiver.Path state (runActions step capture capacity compatible actions state)
  | [], state => by
      letI := actionQuiver (Output := Output) (clients := clients) step capture capacity compatible
      exact .nil
  | .pump :: rest, state => by
      letI := actionQuiver (Output := Output) (clients := clients) step capture capacity compatible
      exact (Quiver.Hom.toPath (ActionEdge.ofAction (step := step) (capture := capture) (capacity := capacity) (compatible := compatible)
        state .pump)).comp
          (actionPath rest (pump step capture capacity compatible state).2)
  | .deliver client output :: rest, state => by
      letI := actionQuiver (Output := Output) (clients := clients) step capture capacity compatible
      exact (Quiver.Hom.toPath (ActionEdge.ofAction (step := step) (capture := capture) (capacity := capacity) (compatible := compatible)
        state (.deliver client output))).comp
          (actionPath rest (deliver compatible state client output).2)

set_option backward.isDefEq.respectTransparency false in
theorem account_edge (state : Cfg) (action : Action Output clients) :
    letI := actionQuiver (Output := Output) (clients := clients) step capture capacity compatible
    (splitAccount step capture capacity compatible).of
      (Quiver.Hom.toPath (ActionEdge.ofAction (step := step) (capture := capture) (capacity := capacity) (compatible := compatible) state action)) =
        (advanceAction step capture capacity compatible action state).2 := by
  cases action <;> apply Prod.ext <;>
    simp [splitAccount, RunAccount.prod, progressAccount, deliveryAccount,
      Quiver.Hom.toPath, pathAccount_cons, pathAccount_nil, edgeCharge, advanceAction]

set_option backward.isDefEq.respectTransparency false in
theorem count_eq_pathAccount (actions : List (Action Output clients)) (state : Cfg) :
    letI := actionQuiver (Output := Output) (clients := clients) step capture capacity compatible
    (count step capture capacity compatible actions (1, 1) state).2 =
      (splitAccount step capture capacity compatible).of
        (actionPath step capture capacity compatible actions state) := by
  let _ := actionQuiver (Output := Output) (clients := clients) step capture capacity compatible
  induction actions generalizing state with
  | nil => rfl
  | cons action rest ih =>
      cases action <;>
        simp only [count, actionPath] <;>
        rw [count_scales, ih] <;>
        erw [(splitAccount step capture capacity compatible).of_comp] <;>
        rw [account_edge] <;>
        simp [advanceAction]

theorem splitAccount_components {source target : Cfg} :
    letI := actionQuiver (Output := Output) (clients := clients) step capture capacity compatible
    ∀ (path : Quiver.Path source target),
      (splitAccount step capture capacity compatible).of path =
        ((progressAccount step capture capacity compatible).of path,
          (deliveryAccount step capture capacity compatible).of path) := by
  intro path
  rfl

/-- Direct fuel-driven accumulation reads the same product path account;
the mathematical path and request list remain outside execution. -/
theorem countPumps_eq_pathAccount (fuel : Nat) (state : Cfg) :
    letI := actionQuiver (Output := Output) (clients := clients) step capture capacity compatible
    (countPumps step capture capacity compatible fuel (1, 1) state).2 =
      (splitAccount step capture capacity compatible).of
        (actionPath step capture capacity compatible (List.replicate fuel Action.pump) state) := by
  rw [countPumps_eq_count]
  exact count_eq_pathAccount step capture capacity compatible _ _

/-- Two consumers of the same admitted payload incur one production and
one delivery each. The two equal payloads do not collapse into one use. -/
theorem shared_production_two_deliveries :
    (count serviceCohortStep some (fun _ => true) (fun _ => true)
      [.pump, .pump, .deliver (0 : Fin 2) (), .deliver (1 : Fin 2) ()]
      (1, 1) serviceCohort).2 =
        (Multiplicative.ofAdd 1, Multiplicative.ofAdd 2) := by
  decide

/-- An incompatible context does not perform producer work or deliver a row. -/
theorem refused_context_is_not_production_or_delivery :
    (count serviceCohortStep some (fun _ => true) (fun _ => false)
      [.pump, .pump, .deliver (0 : Fin 2) (), .deliver (1 : Fin 2) ()]
      (1, 1) serviceCohort).2 = (1, 1) := by
  decide

/-- Cancellation removes one delivery right; the other consumer retains its
answer, and the already paid production remains in the account. -/
theorem cancellation_keeps_paid_production_and_other_delivery :
    let earlier := count serviceCohortStep some (fun _ => true) (fun _ => true)
      [.pump, .pump] (1, 1) serviceCohort
    let cancelled := retireConsumer earlier.1 (0 : Fin 2)
    (count serviceCohortStep some (fun _ => true) (fun _ => true)
      [.deliver (0 : Fin 2) (), .deliver (1 : Fin 2) ()] earlier.2 cancelled).2 =
        (Multiplicative.ofAdd 1, Multiplicative.ofAdd 1) := by
  decide

/-! ### Independently selected history and numerical observation

All four policies preserve the same producer configuration. The joint worker
uses one pump result for both updates; disabling both observers delegates to
ordinary execution. None of these pump-only operations needs value equality.
-/

section JointObservation

open Mettapedia.GSLT.Core.InferenceControl.Recording

omit [DecidableEq Stored] [DecidableEq Output]

local notation "Note" => Notice Borrowed Stored Effect Handoff

/-- Stream both observers. Each fuel step calls `pump` once. The prefix is
pushed with that notice and the account is multiplied by its production
charge. There is no option test and no accumulated list. -/
def recordCounted : Nat → Prefix Note → ProtocolAccount → Cfg →
    Prefix Note × Cfg × ProtocolAccount
  | 0, record, account, state => (record, state, account)
  | fuel + 1, record, account, state =>
      let result := pump step capture capacity compatible state
      recordCounted fuel (record.push (fun _ => result.1))
        (account * productionCharge result.1) result.2

theorem recordCounted_projects_history (fuel : Nat) (record : Prefix Note)
    (account : ProtocolAccount) (state : Cfg) :
    ((recordCounted step capture capacity compatible fuel record account state).1,
      (recordCounted step capture capacity compatible fuel record account state).2.1) =
      recordOrdinary step capture capacity compatible fuel record state := by
  induction fuel generalizing record account state with
  | zero => rfl
  | succ _ ih =>
      simp only [recordCounted, recordOrdinary, ih]

theorem recordCounted_projects_account (fuel : Nat) (record : Prefix Note)
    (account : ProtocolAccount) (state : Cfg) :
    (recordCounted step capture capacity compatible fuel record account state).2 =
      countPumps step capture capacity compatible fuel account state := by
  induction fuel generalizing record account state with
  | zero => rfl
  | succ _ ih =>
      simp only [recordCounted, countPumps, ih]

/-- The second slice receives the prefix, account, and configuration produced
by the first. -/
theorem recordCounted_add (first second : Nat) (record : Prefix Note)
    (account : ProtocolAccount) (state : Cfg) :
    recordCounted step capture capacity compatible (first + second) record account state =
      recordCounted step capture capacity compatible second
        (recordCounted step capture capacity compatible first record account state).1
        (recordCounted step capture capacity compatible first record account state).2.2
        (recordCounted step capture capacity compatible first record account state).2.1 := by
  induction first generalizing record account state with
  | zero => simp only [Nat.zero_add, recordCounted]
  | succ _ ih => simp only [Nat.succ_add, recordCounted, ih]

/-- With another live consumer, cancellation preserves both observers and
the complete producer continuation, while retaining the retired cursor. -/
theorem recordCounted_after_retained_demand (fuel : Nat) (record : Prefix Note)
    (account : ProtocolAccount) (state : Cfg)
    (client other : Fin clients) (position : Nat) (distinct : other ≠ client)
    (live : state.delivery.log.positions other = some position) :
    recordCounted step capture capacity compatible fuel record account
        (retireConsumer state client) =
      ((recordCounted step capture capacity compatible fuel record account state).1,
        retireConsumer
          (recordCounted step capture capacity compatible fuel record account state).2.1 client,
        (recordCounted step capture capacity compatible fuel record account state).2.2) := by
  induction fuel generalizing record account state with
  | zero => rfl
  | succ fuel ih =>
      have preserved := pump_preserves_context_cursors_publications step capture capacity
        compatible state
      have kept := (congrFun preserved.2.2.1 other).trans live
      have first := pump_after_retained_demand step capture capacity compatible state
        client other position distinct live
      simpa only [recordCounted, first] using
        ih (record.push (fun _ => (pump step capture capacity compatible state).1))
          (account * productionCharge (pump step capture capacity compatible state).1)
          (pump step capture capacity compatible state).2 kept

/-- Resumption keeps the first slice's remaining capacity and omitted count. -/
theorem recordCounted_resume_keeps_bounds (first second : Nat) (record : Prefix Note)
    (account : ProtocolAccount) (state : Cfg) :
    (recordCounted step capture capacity compatible second
      (recordCounted step capture capacity compatible first record account state).1
      (recordCounted step capture capacity compatible first record account state).2.2
      (recordCounted step capture capacity compatible first record account state).2.1).1.remaining =
      (recordCounted step capture capacity compatible (first + second)
        record account state).1.remaining ∧
    (recordCounted step capture capacity compatible second
      (recordCounted step capture capacity compatible first record account state).1
      (recordCounted step capture capacity compatible first record account state).2.2
      (recordCounted step capture capacity compatible first record account state).2.1).1.omitted =
      (recordCounted step capture capacity compatible (first + second)
        record account state).1.omitted := by
  constructor <;> simp only [recordCounted_add]

/-- A prefix with no remaining capacity only increments `omitted`. The account
projection has no capacity hypothesis, so these steps are still charged. -/
theorem full_prefix_only_omits (fuel : Nat) (record : Prefix Note)
    (full : record.remaining = 0) (account : ProtocolAccount) (state : Cfg) :
    (recordCounted step capture capacity compatible fuel record account state).1.remaining = 0 ∧
      (recordCounted step capture capacity compatible fuel record account state).1.omitted =
        record.omitted + fuel := by
  induction fuel generalizing record account state with
  | zero => simp [recordCounted, full]
  | succ _ ih =>
      match record, full with
      | ⟨reversed, 0, omittedCount⟩, rfl =>
          simp only [recordCounted, Prefix.push]
          rcases ih ⟨reversed, 0, omittedCount + 1⟩ rfl
            (account * productionCharge (pump step capture capacity compatible state).1)
            (pump step capture capacity compatible state).2 with ⟨remaining, omittedEq⟩
          refine ⟨remaining, ?_⟩
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using omittedEq

/-- Choose the observers once. `none`/`none` calls `ordinary` directly. -/
def enterObservers : Option (Prefix Note) → Option ProtocolAccount → Nat → Cfg →
    Option (Prefix Note) × Option ProtocolAccount × Cfg
  | none, none, fuel, state =>
      (none, none, ordinary step capture capacity compatible fuel state)
  | some record, none, fuel, state =>
      let continued := recordOrdinary step capture capacity compatible fuel record state
      (some continued.1, none, continued.2)
  | none, some account, fuel, state =>
      let continued := countPumps step capture capacity compatible fuel account state
      (none, some continued.2, continued.1)
  | some record, some account, fuel, state =>
      let continued :=
        recordCounted step capture capacity compatible fuel record account state
      (some continued.1, some continued.2.2, continued.2.1)

theorem enterObservers_neither (fuel : Nat) (state : Cfg) :
    enterObservers step capture capacity compatible none none fuel state =
      ((enterProducerHistory step capture capacity compatible none fuel state).1,
        (enterCounted step capture capacity compatible none fuel state).1,
        (enterProducerHistory step capture capacity compatible none fuel state).2) := rfl

theorem enterObservers_history (record : Prefix Note) (fuel : Nat) (state : Cfg) :
    enterObservers step capture capacity compatible (some record) none fuel state =
      let continued :=
        enterProducerHistory step capture capacity compatible (some record) fuel state
      (continued.1, none, continued.2) := rfl

theorem enterObservers_history_erases (record : Prefix Note) (fuel : Nat) (state : Cfg) :
    (enterObservers step capture capacity compatible (some record) none fuel state).2.2 =
      (enterCounted step capture capacity compatible none fuel state).2 := by
  simp only [enterObservers, enterCounted, recordOrdinary_preserves_ordinary_configuration]

theorem enterObservers_counts (account : ProtocolAccount) (fuel : Nat) (state : Cfg) :
    enterObservers step capture capacity compatible none (some account) fuel state =
      let continued :=
        enterCounted step capture capacity compatible (some account) fuel state
      (none, continued.1, continued.2) := rfl

theorem enterObservers_counts_erases (account : ProtocolAccount) (fuel : Nat) (state : Cfg) :
    (enterObservers step capture capacity compatible none (some account) fuel state).2.2 =
      (enterProducerHistory step capture capacity compatible none fuel state).2 := by
  simp only [enterObservers, enterProducerHistory, countPumps_erases]

theorem enterObservers_both_history (record : Prefix Note) (account : ProtocolAccount)
    (fuel : Nat) (state : Cfg) :
    ((enterObservers step capture capacity compatible (some record) (some account)
        fuel state).1,
      (enterObservers step capture capacity compatible (some record) (some account)
        fuel state).2.2) =
      enterProducerHistory step capture capacity compatible (some record) fuel state := by
  simp only [enterObservers, enterProducerHistory]
  exact congrArg (fun pair : Prefix Note × Cfg => (some pair.1, pair.2))
    (recordCounted_projects_history step capture capacity compatible fuel record account state)

theorem enterObservers_both_account (record : Prefix Note) (account : ProtocolAccount)
    (fuel : Nat) (state : Cfg) :
    ((enterObservers step capture capacity compatible (some record) (some account)
        fuel state).2.1,
      (enterObservers step capture capacity compatible (some record) (some account)
        fuel state).2.2) =
      enterCounted step capture capacity compatible (some account) fuel state := by
  simp only [enterObservers, enterCounted, recordCounted_projects_account]

theorem enterObservers_split (history : Option (Prefix Note))
    (account : Option ProtocolAccount) (first second : Nat) (state : Cfg) :
    enterObservers step capture capacity compatible history account (first + second) state =
      enterObservers step capture capacity compatible
        (enterObservers step capture capacity compatible history account first state).1
        (enterObservers step capture capacity compatible history account first state).2.1
        second
        (enterObservers step capture capacity compatible history account first state).2.2 := by
  cases history with
  | none =>
      cases account with
      | none => simp only [enterObservers, ordinary_add]
      | some _ => simp only [enterObservers, countPumps_add]
  | some _ =>
      cases account with
      | none =>
          simp only [enterObservers, recordOrdinary_composes_without_resetting_capacity]
      | some _ => simp only [enterObservers, recordCounted_add]

/-- Forgetting the prefix keeps the accumulated account and continues from the
joint configuration. The result is the counted entry of the whole fuel. -/
theorem forget_history_preserves_account (record : Prefix Note)
    (account : ProtocolAccount) (first second : Nat) (state : Cfg) :
    enterObservers step capture capacity compatible none
        (enterObservers step capture capacity compatible (some record) (some account)
          first state).2.1
        second
        (enterObservers step capture capacity compatible (some record) (some account)
          first state).2.2 =
      (none,
        (enterCounted step capture capacity compatible (some account)
          (first + second) state).1,
        (enterCounted step capture capacity compatible (some account)
          (first + second) state).2) := by
  simp only [enterObservers, enterCounted, recordCounted_projects_account, countPumps_add]

theorem forget_history_continues (record : Prefix Note) (account : ProtocolAccount)
    (first second : Nat) (state : Cfg) :
    (enterObservers step capture capacity compatible none
        (enterObservers step capture capacity compatible (some record) (some account)
          first state).2.1
        second
        (enterObservers step capture capacity compatible (some record) (some account)
          first state).2.2).2.2 =
      ordinary step capture capacity compatible (first + second) state := by
  rw [forget_history_preserves_account]
  simp only [enterCounted_erases]

/-- Every joint policy has exactly the existing history projection. -/
theorem enterObservers_projects_history (history : Option (Prefix Note))
    (account : Option ProtocolAccount) (fuel : Nat) (state : Cfg) :
    ((enterObservers step capture capacity compatible history account fuel state).1,
      (enterObservers step capture capacity compatible history account fuel state).2.2) =
        enterProducerHistory step capture capacity compatible history fuel state := by
  cases history with
  | none =>
      cases account with
      | none => rfl
      | some account =>
          simpa only [enterObservers, enterProducerHistory] using
            congrArg (fun state : Cfg => ((none : Option (Prefix Note)), state))
              (countPumps_erases step capture capacity compatible fuel account state)
  | some record =>
      cases account with
      | none => rfl
      | some account =>
          exact enterObservers_both_history step capture capacity compatible
            record account fuel state

/-- Every joint policy has exactly the existing numerical projection. -/
theorem enterObservers_projects_account (history : Option (Prefix Note))
    (account : Option ProtocolAccount) (fuel : Nat) (state : Cfg) :
    ((enterObservers step capture capacity compatible history account fuel state).2.1,
      (enterObservers step capture capacity compatible history account fuel state).2.2) =
        enterCounted step capture capacity compatible account fuel state := by
  cases history with
  | none =>
      cases account <;> rfl
  | some record =>
      cases account with
      | none =>
          simpa only [enterObservers, enterCounted] using
            congrArg (fun state : Cfg => ((none : Option ProtocolAccount), state))
              (recordOrdinary_preserves_ordinary_configuration step capture capacity compatible
                fuel record state)
      | some account =>
          exact enterObservers_both_account step capture capacity compatible
            record account fuel state

/-- Recording and metering choices do not change the operational continuation. -/
theorem enterObservers_erases (history : Option (Prefix Note))
    (account : Option ProtocolAccount) (fuel : Nat) (state : Cfg) :
    (enterObservers step capture capacity compatible history account fuel state).2.2 =
      ordinary step capture capacity compatible fuel state := by
  have projection := congrArg Prod.snd
    (enterObservers_projects_account step capture capacity compatible history account fuel state)
  exact projection.trans (enterCounted_erases step capture capacity compatible account fuel state)

/-- Starting a diary after a counted prefix preserves the whole account.
The initial history choice has no influence on that numerical projection. -/
theorem start_history_preserves_account (record : Prefix Note)
    (account : Option ProtocolAccount) (first second : Nat) (state : Cfg) :
    let earlier := enterCounted step capture capacity compatible account first state
    let later := enterObservers step capture capacity compatible (some record)
      earlier.1 second earlier.2
    (later.2.1, later.2.2) =
      enterCounted step capture capacity compatible account (first + second) state := by
  dsimp only
  rw [enterObservers_projects_account, ← enterCounted_split]

/-- A fresh late diary is precisely a recording of the suffix from the actual
counted checkpoint. It contains none of the earlier execution's notices. -/
theorem late_history_records_the_actual_suffix (slots : Nat)
    (account : Option ProtocolAccount) (first second : Nat) (state : Cfg) :
    let earlier := enterCounted step capture capacity compatible account first state
    (enterObservers step capture capacity compatible (some (Prefix.initial slots))
      earlier.1 second earlier.2).1 =
        some ((recordOrdinary step capture capacity compatible second
          (Prefix.initial slots) earlier.2).1) := by
  dsimp only
  have projection := congrArg Prod.fst
    (enterObservers_projects_history step capture capacity compatible
      (some (Prefix.initial slots))
      (enterCounted step capture capacity compatible account first state).1 second
      (enterCounted step capture capacity compatible account first state).2)
  exact projection

end JointObservation

/-! ### Source driver debits and program bounds

The online account recovers the existing driver's performed transition debit
and complete retained state. Bounds come from `CostedRuns`, independently of
recording. Root completion requires an empty caller-frame stack; pending
capture or publication is not completion of the consumer protocol.
-/
section DriverAccounting

open Mettapedia.Machines.OwnedPullDriver

omit [DecidableEq Stored] [DecidableEq Output]


/-- Direct production coordinate. The right-hand sum is the specification
already used by `run_driver_debit`; `countPumps` does not build that list.
The delivery coordinate is unchanged. -/
theorem countPumps_account
    {Producer Borrowed Stored Context Output Effect Handoff : Type} {clients : Nat}
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool) (ticks : Nat) (account : ProtocolAccount)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    (countPumps step capture capacity compatible ticks account state).2 =
      (account.1 * Multiplicative.ofAdd
        ((run step capture capacity compatible ticks state).1.map driverTicks).sum,
        account.2) := by
  induction ticks generalizing account state with
  | zero => rfl
  | succ ticks ih =>
      cases account with
      | mk produced delivered =>
          have ihAccount :=
            ih ((produced, delivered) *
                productionCharge (pump step capture capacity compatible state).1)
              (pump step capture capacity compatible state).2
          simp only [countPumps, run, List.map_cons, List.sum_cons]
          rw [ihAccount]
          simp only [productionCharge, Prod.mk_mul_mk, mul_one]
          rw [mul_assoc]
          rfl

/-- Counted pumps retain the ordinary configuration, hence the recorded
execution. `ordinary_agrees_with_recorded_state` identifies that configuration
with `run`, and `run_driver_debit` is the performed driver debit. The
production coordinate is that debit; delivery stays the unit. -/
theorem countPumps_driver_debit
    {Value Event Stored Context Output : Type} {clients : Nat}
    (capture : Event → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool) (ticks : Nat)
    (state : Configuration (State Value Event) Event Stored Context Output Empty Empty clients)
    (execution : Execution (State Value Event) Event Empty Empty)
    (attached : state.execution = some execution) :
    ∃ next,
      (countPumps driverStep capture capacity compatible ticks (1, 1) state).1 =
        (run driverStep capture capacity compatible ticks state).2 ∧
      (countPumps driverStep capture capacity compatible ticks (1, 1) state).1.execution =
        some next ∧
      (countPumps driverStep capture capacity compatible ticks (1, 1) state).2 =
        (Multiplicative.ofAdd
          ((run driverStep capture capacity compatible ticks state).1.map driverTicks).sum, 1) ∧
      MachineCore.runSlice (machineCore Value Event)
        ((run driverStep capture capacity compatible ticks state).1.map driverTicks).sum
        execution.producer =
          (next.producer,
            ((run driverStep capture capacity compatible ticks state).1.map driverTicks).sum) := by
  obtain ⟨next, retained, performed⟩ :=
    run_driver_debit capture capacity compatible ticks state execution attached
  dsimp only at performed
  have config :=
    (countPumps_erases driverStep capture capacity compatible ticks (1, 1) state).trans
      (ordinary_agrees_with_recorded_state driverStep capture capacity compatible ticks state)
  refine ⟨next, config, ?_, ?_, performed⟩
  · rw [config]
    exact retained
  · simpa [one_mul] using
      countPumps_account driverStep capture capacity compatible ticks (1, 1) state

/-- Root load. Any online debit larger than `events.length + 2 * calls` would
be a budget that `CostedRuns.runSlice_after_completion` runs with charge equal
only to that semantic count. `run_driver_debit` charges the debit it performed,
so the recorded sum is at most the semantic count. The second inequality is
the coarser `CostedRuns.linear_steps` estimate. Outer frames are
`pending_return_not_final`, outside this root budget. -/
private theorem countPumps_root_debit_spec
    {Value Event Stored Context Output : Type} {clients : Nat}
    {work : Program Value Event} {events : List Event} {value : Value}
    {calls depth : Nat}
    (semantic : CostedRuns work events value calls depth)
    (capture : Event → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool) (ticks : Nat)
    (state : Configuration (State Value Event) Event Stored Context Output Empty Empty clients)
    (execution : Execution (State Value Event) Event Empty Empty)
    (attached : state.execution = some execution)
    (root : execution.producer = ⟨work, []⟩) :
    (countPumps driverStep capture capacity compatible ticks (1, 1) state).2 =
        (Multiplicative.ofAdd
          ((run driverStep capture capacity compatible ticks state).1.map driverTicks).sum, 1) ∧
      ((run driverStep capture capacity compatible ticks state).1.map driverTicks).sum ≤
        events.length + 2 * calls ∧
      ((run driverStep capture capacity compatible ticks state).1.map driverTicks).sum ≤
        2 * (events.length + calls) := by
  set debit :=
      ((run driverStep capture capacity compatible ticks state).1.map driverTicks).sum
  have account :
      (countPumps driverStep capture capacity compatible ticks (1, 1) state).2 =
        (Multiplicative.ofAdd debit, 1) := by
    have raw :=
      countPumps_account driverStep capture capacity compatible ticks (1, 1) state
    rw [one_mul] at raw
    exact raw
  obtain ⟨_, _, performed⟩ :=
    run_driver_debit capture capacity compatible ticks state execution attached
  dsimp only at performed
  rw [root] at performed
  obtain ⟨debit_le, linear⟩ := semantic.root_debit_le debit performed
  exact ⟨account, debit_le, linear⟩

/-- The directly accumulated production coordinate obeys the source-program
bound. The reference notice list appears only in the proof of this bound. -/
theorem countPumps_root_debit_le
    {Value Event Stored Context Output : Type} {clients : Nat}
    {work : Program Value Event} {events : List Event} {value : Value}
    {calls depth : Nat}
    (semantic : CostedRuns work events value calls depth)
    (capture : Event → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool) (ticks : Nat)
    (state : Configuration (State Value Event) Event Stored Context Output Empty Empty clients)
    (execution : Execution (State Value Event) Event Empty Empty)
    (attached : state.execution = some execution)
    (root : execution.producer = ⟨work, []⟩) :
    (countPumps driverStep capture capacity compatible ticks (1, 1) state).2.1.toAdd ≤
        events.length + 2 * calls ∧
      (countPumps driverStep capture capacity compatible ticks (1, 1) state).2.1.toAdd ≤
        2 * (events.length + calls) ∧
      (countPumps driverStep capture capacity compatible ticks (1, 1) state).2.2 = 1 := by
  obtain ⟨account, strong, linear⟩ :=
    countPumps_root_debit_spec semantic capture capacity compatible ticks state execution attached root
  rw [account]
  exact ⟨strong, linear, rfl⟩

/-- The retained driver is terminal, so the semantic fuel after the online
debit charges nothing (`runSlice_of_final`). With the root bound,
`CostedRuns.runSlice` forces that debit to equal `events.length + 2 * calls`
and the driver to be `⟨.done value, []⟩`. Terminality is `machineCore.step` on
the driver; `next.pending` and `next.accepted` stay unconstrained. -/
theorem countPumps_root_terminal_eq
    {Value Event Stored Context Output : Type} {clients : Nat}
    {work : Program Value Event} {events : List Event} {value : Value}
    {calls depth : Nat}
    (semantic : CostedRuns work events value calls depth)
    (capture : Event → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool) (ticks : Nat)
    (state : Configuration (State Value Event) Event Stored Context Output Empty Empty clients)
    (execution : Execution (State Value Event) Event Empty Empty)
    (attached : state.execution = some execution)
    (root : execution.producer = ⟨work, []⟩)
    (next : Execution (State Value Event) Event Empty Empty)
    (retained : (countPumps driverStep capture capacity compatible ticks (1, 1) state).1.execution =
      some next)
    (terminal : (machineCore Value Event).step next.producer = none) :
    (countPumps driverStep capture capacity compatible ticks (1, 1) state).2 =
      (Multiplicative.ofAdd (events.length + 2 * calls), 1) ∧
      next.producer = ⟨.done value, []⟩ := by
  obtain ⟨nextCount, _, retainedCount, account, performed⟩ :=
    countPumps_driver_debit capture capacity compatible ticks state execution attached
  have nextCount_eq : nextCount = next :=
    Option.some.inj (retainedCount.symm.trans retained)
  have terminalCount : (machineCore Value Event).step nextCount.producer = none := by
    rw [nextCount_eq]
    exact terminal
  set debit :=
    ((run driverStep capture capacity compatible ticks state).1.map driverTicks).sum
  rw [root] at performed
  have identified := semantic.root_eq_of_final debit performed terminalCount
  refine ⟨?_, ?_⟩
  · rw [identified.1] at account
    exact account
  · rw [← nextCount_eq]
    exact identified.2

/-- Every joint history choice projects to `countPumps`. Specialization of
`enterObservers_projects_account`; not a separate account. -/
private theorem joint_projects_countPumps
    {Producer Borrowed Stored Context Output Effect Handoff : Type} {clients : Nat}
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool)
    (history : Option (Mettapedia.GSLT.Core.InferenceControl.Recording.Prefix
      (Notice Borrowed Stored Effect Handoff)))
    (account : ProtocolAccount) (ticks : Nat)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    ((enterObservers step capture capacity compatible history (some account) ticks state).2.1,
      (enterObservers step capture capacity compatible history (some account) ticks state).2.2) =
      (some (countPumps step capture capacity compatible ticks account state).2,
        (countPumps step capture capacity compatible ticks account state).1) := by
  rw [enterObservers_projects_account]
  rfl

/-- The joint numerical observer carries the same driver debit and the same
retained configuration as direct `countPumps`. -/
theorem joint_driver_debit
    {Value Event Stored Context Output : Type} {clients : Nat}
    (capture : Event → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool) (ticks : Nat)
    (history : Option (Mettapedia.GSLT.Core.InferenceControl.Recording.Prefix
      (Notice Event Stored Empty Empty)))
    (state : Configuration (State Value Event) Event Stored Context Output Empty Empty clients)
    (execution : Execution (State Value Event) Event Empty Empty)
    (attached : state.execution = some execution) :
    ∃ next,
      (enterObservers driverStep capture capacity compatible history (some (1, 1))
        ticks state).2.2 =
        (run driverStep capture capacity compatible ticks state).2 ∧
      (enterObservers driverStep capture capacity compatible history (some (1, 1))
        ticks state).2.2.execution = some next ∧
      (enterObservers driverStep capture capacity compatible history (some (1, 1))
        ticks state).2.1 =
        some (Multiplicative.ofAdd
          ((run driverStep capture capacity compatible ticks state).1.map driverTicks).sum, 1) ∧
      MachineCore.runSlice (machineCore Value Event)
        ((run driverStep capture capacity compatible ticks state).1.map driverTicks).sum
        execution.producer =
          (next.producer,
            ((run driverStep capture capacity compatible ticks state).1.map driverTicks).sum) := by
  have projected :=
    joint_projects_countPumps driverStep capture capacity compatible history (1, 1) ticks state
  obtain ⟨next, config, retained, account, performed⟩ :=
    countPumps_driver_debit capture capacity compatible ticks state execution attached
  refine ⟨next, ?_, ?_, ?_, performed⟩
  · exact (congrArg Prod.snd projected).trans config
  · rw [congrArg Prod.snd projected]
    exact retained
  · rw [congrArg Prod.fst projected, account]

/-- The root bound is the joint account's production coordinate. -/
theorem joint_root_debit_le
    {Value Event Stored Context Output : Type} {clients : Nat}
    {work : Program Value Event} {events : List Event} {value : Value}
    {calls depth : Nat}
    (semantic : CostedRuns work events value calls depth)
    (capture : Event → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool) (ticks : Nat)
    (history : Option (Mettapedia.GSLT.Core.InferenceControl.Recording.Prefix
      (Notice Event Stored Empty Empty)))
    (state : Configuration (State Value Event) Event Stored Context Output Empty Empty clients)
    (execution : Execution (State Value Event) Event Empty Empty)
    (attached : state.execution = some execution)
    (root : execution.producer = ⟨work, []⟩) :
    (enterObservers driverStep capture capacity compatible history (some (1, 1))
        ticks state).2.1 =
      some (countPumps driverStep capture capacity compatible ticks (1, 1) state).2 ∧
      (countPumps driverStep capture capacity compatible ticks (1, 1) state).2 =
        (Multiplicative.ofAdd
          ((run driverStep capture capacity compatible ticks state).1.map driverTicks).sum, 1) ∧
      ((run driverStep capture capacity compatible ticks state).1.map driverTicks).sum ≤
        events.length + 2 * calls ∧
      ((run driverStep capture capacity compatible ticks state).1.map driverTicks).sum ≤
        2 * (events.length + calls) := by
  have projected :=
    joint_projects_countPumps driverStep capture capacity compatible history (1, 1) ticks state
  obtain ⟨account, strong, linear⟩ :=
    countPumps_root_debit_spec semantic capture capacity compatible ticks state execution attached root
  exact ⟨congrArg Prod.fst projected, account, strong, linear⟩

/-- The existing root program: ten composition steps, semantic debit
`3 + 2 * 1`, retained driver `⟨.done 6, []⟩`. -/
theorem exampleProgram_root_debit :
    (countPumps driverStep Controls.captureEvent (fun _ => true) (fun _ => true)
      10 (1, 1) (Controls.start 4)).2 =
      (Multiplicative.ofAdd ([1, 1, 3].length + 2 * 1), 1) ∧
    (countPumps driverStep Controls.captureEvent (fun _ => true) (fun _ => true)
      10 (1, 1) (Controls.start 4)).1.execution =
      some ⟨⟨.done 6, []⟩, none, 3, .active⟩ := by
  have attached : (Controls.start 4).execution =
      some (⟨⟨exampleProgram, []⟩, none, 0, .active⟩ :
        Execution (State Nat Nat) Nat Empty Empty) := rfl
  have root : (⟨⟨exampleProgram, []⟩, none, 0, .active⟩ :
      Execution (State Nat Nat) Nat Empty Empty).producer = ⟨exampleProgram, []⟩ := rfl
  have config :
      (countPumps driverStep Controls.captureEvent (fun _ => true) (fun _ => true)
        10 (1, 1) (Controls.start 4)).1 = (Controls.feed 10 4).2 := by
    simp only [Controls.feed, countPumps_erases, ordinary_agrees_with_recorded_state]
  have retained := Controls.completed_execution_retains_actual_final_value.1
  rw [← config] at retained
  have terminal : (machineCore Nat Nat).step (⟨.done 6, []⟩ : State Nat Nat) = none := rfl
  have identified :=
    countPumps_root_terminal_eq exampleProgram_costed
      Controls.captureEvent (fun _ => true) (fun _ => true) 10 (Controls.start 4)
      ⟨⟨exampleProgram, []⟩, none, 0, .active⟩ attached root
      ⟨⟨.done 6, []⟩, none, 3, .active⟩ retained terminal
  exact ⟨identified.1, retained⟩


/-! ### Driver bounds for actual interleaved producer/consumer actions -/
section InterleavedDriverAccounting

private theorem production_add (left right : Nat) :
    Multiplicative.ofAdd left * Multiplicative.ofAdd right =
      Multiplicative.ofAdd (left + right) :=
  (ofAdd_add left right).symm

/-- One counted pump is one `run` tick. The production coordinate is that
tick's `driverTicks` sum, and `run_driver_debit` sends it through
`MachineCore.runSlice` with the retained execution. -/
theorem pump_step_driver_debit
    {Value Event Stored Context Output : Type} {clients : Nat}
    [DecidableEq Stored] [DecidableEq Output]
    (capture : Event → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool)
    (state : Configuration (State Value Event) Event Stored Context Output Empty Empty clients)
    (execution : Execution (State Value Event) Event Empty Empty)
    (attached : state.execution = some execution) :
    ∃ next debit,
      (count driverStep capture capacity compatible [Action.pump] (1, 1) state).1.execution =
        some next ∧
      (count driverStep capture capacity compatible [Action.pump] (1, 1) state).2.1 =
        Multiplicative.ofAdd debit ∧
      MachineCore.runSlice (machineCore Value Event) debit execution.producer =
        (next.producer, debit) := by
  obtain ⟨next, retained, performed⟩ :=
    run_driver_debit capture capacity compatible 1 state execution attached
  dsimp only at performed
  have shape : run driverStep capture capacity compatible 1 state =
      ([(pump driverStep capture capacity compatible state).1],
        (pump driverStep capture capacity compatible state).2) := by
    simp [run]
  simp only [shape, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Nat.add_zero] at performed retained
  refine ⟨next, driverTicks (pump driverStep capture capacity compatible state).1, ?_, ?_, performed⟩
  · simpa only [count, advanceAction] using retained
  · simp only [count, advanceAction, productionCharge, Prod.mk_mul_mk, one_mul, mul_one]

/-- A delivery keeps the execution and adds no driver transition. The
delivery coordinate is the answer charge; the producer is not run again. -/
theorem deliver_step_driver_debit
    {Value Event Stored Context Output : Type} {clients : Nat}
    [DecidableEq Stored] [DecidableEq Output]
    (capture : Event → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool)
    (state : Configuration (State Value Event) Event Stored Context Output Empty Empty clients)
    (execution : Execution (State Value Event) Event Empty Empty)
    (attached : state.execution = some execution)
    (client : Fin clients) (output : Output) :
    (count driverStep capture capacity compatible [.deliver client output] (1, 1) state).1.execution =
        some execution ∧
      (count driverStep capture capacity compatible [.deliver client output] (1, 1) state).2.1 =
        Multiplicative.ofAdd 0 ∧
      MachineCore.runSlice (machineCore Value Event) 0 execution.producer =
        (execution.producer, 0) := by
  have kept := delivery_preserves_complete_execution compatible state client output
  refine ⟨?_, ?_, rfl⟩
  · simpa only [count, advanceAction, kept] using attached
  · simp only [count, advanceAction, deliveryCharge, Prod.mk_mul_mk, one_mul, mul_one]
    exact ofAdd_zero.symm

/-- Arbitrary pump/delivery lists. The production coordinate is the debit of
the pumps that ran, in order, on the configurations the preceding deliveries
left. The retained execution is the execution of that walk. -/
theorem count_driver_debit
    {Value Event Stored Context Output : Type} {clients : Nat}
    [DecidableEq Stored] [DecidableEq Output]
    (capture : Event → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool)
    (actions : List (Action Output clients))
    (state : Configuration (State Value Event) Event Stored Context Output Empty Empty clients)
    (execution : Execution (State Value Event) Event Empty Empty)
    (attached : state.execution = some execution) :
    ∃ next debit,
      (count driverStep capture capacity compatible actions (1, 1) state).1.execution =
        some next ∧
      (count driverStep capture capacity compatible actions (1, 1) state).2.1 =
        Multiplicative.ofAdd debit ∧
      MachineCore.runSlice (machineCore Value Event) debit execution.producer =
        (next.producer, debit) := by
  induction actions generalizing state execution with
  | nil =>
      refine ⟨execution, 0, ?_, ?_, rfl⟩
      · simpa [count] using attached
      · simp [count, ofAdd_zero]
  | cons action rest ih =>
      cases action with
      | pump =>
          obtain ⟨middle, stepDebit, headExec, headAccount, headSlice⟩ :=
            pump_step_driver_debit capture capacity compatible state execution attached
          obtain ⟨next, restDebit, tailExec, tailAccount, tailSlice⟩ :=
            ih (count driverStep capture capacity compatible [Action.pump] (1, 1) state).1
              middle headExec
          have joined :
              count driverStep capture capacity compatible (Action.pump :: rest) (1, 1) state =
                count driverStep capture capacity compatible rest
                  (count driverStep capture capacity compatible [Action.pump] (1, 1) state).2
                  (count driverStep capture capacity compatible [Action.pump] (1, 1) state).1 := by
            simpa only [List.singleton_append] using
              count_append driverStep capture capacity compatible
                [Action.pump] rest (1, 1) state
          have scaled := count_scales driverStep capture capacity compatible rest
            (count driverStep capture capacity compatible [Action.pump] (1, 1) state).2
            (count driverStep capture capacity compatible [Action.pump] (1, 1) state).1
          have sameWalk :=
            (count_erases driverStep capture capacity compatible rest
                (count driverStep capture capacity compatible [Action.pump] (1, 1) state).2
                (count driverStep capture capacity compatible [Action.pump] (1, 1) state).1).trans
              (count_erases driverStep capture capacity compatible rest (1, 1)
                (count driverStep capture capacity compatible [Action.pump] (1, 1) state).1).symm
          have combined := MachineCore.runSlice_add (machineCore Value Event)
            stepDebit restDebit execution.producer
          rw [headSlice] at combined
          dsimp only at combined
          rw [tailSlice] at combined
          dsimp only at combined
          refine ⟨next, stepDebit + restDebit, ?_, ?_, combined⟩
          · rw [joined, sameWalk]
            exact tailExec
          · rw [joined, scaled, Prod.fst_mul, headAccount, tailAccount]
            exact production_add stepDebit restDebit
      | deliver client output =>
          have headExec :=
            (deliver_step_driver_debit capture capacity compatible state execution attached
              client output).1
          have headAccount :=
            (deliver_step_driver_debit capture capacity compatible state execution attached
              client output).2.1
          have headSlice :=
            (deliver_step_driver_debit capture capacity compatible state execution attached
              client output).2.2
          obtain ⟨next, restDebit, tailExec, tailAccount, tailSlice⟩ :=
            ih (count driverStep capture capacity compatible [.deliver client output] (1, 1)
                state).1
              execution headExec
          have joined :
              count driverStep capture capacity compatible
                  (Action.deliver client output :: rest) (1, 1) state =
                count driverStep capture capacity compatible rest
                  (count driverStep capture capacity compatible
                    [Action.deliver client output] (1, 1) state).2
                  (count driverStep capture capacity compatible
                    [Action.deliver client output] (1, 1) state).1 := by
            simpa only [List.singleton_append] using
              count_append driverStep capture capacity compatible
                [Action.deliver client output] rest (1, 1) state
          have scaled := count_scales driverStep capture capacity compatible rest
            (count driverStep capture capacity compatible [.deliver client output] (1, 1) state).2
            (count driverStep capture capacity compatible [.deliver client output] (1, 1) state).1
          have sameWalk :=
            (count_erases driverStep capture capacity compatible rest
                (count driverStep capture capacity compatible [.deliver client output] (1, 1)
                  state).2
                (count driverStep capture capacity compatible [.deliver client output] (1, 1)
                  state).1).trans
              (count_erases driverStep capture capacity compatible rest (1, 1)
                (count driverStep capture capacity compatible [.deliver client output] (1, 1)
                  state).1).symm
          have combined := MachineCore.runSlice_add (machineCore Value Event)
            0 restDebit execution.producer
          rw [headSlice] at combined
          dsimp only at combined
          rw [tailSlice] at combined
          dsimp only at combined
          refine ⟨next, 0 + restDebit, ?_, ?_, combined⟩
          · rw [joined, sameWalk]
            exact tailExec
          · rw [joined, scaled, Prod.fst_mul, headAccount, tailAccount]
            exact production_add 0 restDebit

/-- Root load, any interleaving. The exhibited debit is the one
`count_driver_debit` performed. Delivery units are not part of this budget. -/
theorem count_root_debit_le
    {Value Event Stored Context Output : Type} {clients : Nat}
    [DecidableEq Stored] [DecidableEq Output]
    {work : Program Value Event} {events : List Event} {value : Value}
    {calls depth : Nat}
    (semantic : CostedRuns work events value calls depth)
    (capture : Event → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool)
    (actions : List (Action Output clients))
    (state : Configuration (State Value Event) Event Stored Context Output Empty Empty clients)
    (execution : Execution (State Value Event) Event Empty Empty)
    (attached : state.execution = some execution)
    (root : execution.producer = ⟨work, []⟩) :
    ∃ debit,
      (count driverStep capture capacity compatible actions (1, 1) state).2.1 =
          Multiplicative.ofAdd debit ∧
        debit ≤ events.length + 2 * calls ∧
        debit ≤ 2 * (events.length + calls) := by
  obtain ⟨_, debit, _, account, performed⟩ :=
    count_driver_debit capture capacity compatible actions state execution attached
  rw [root] at performed
  obtain ⟨strong, linear⟩ := semantic.root_debit_le debit performed
  exact ⟨debit, account, strong, linear⟩

/-- The retained driver is terminal, so unused semantic fuel charges nothing.
The performed debit is then exactly `events.length + 2 * calls`, and the
driver is `⟨.done value, []⟩`. `next.pending` and `next.accepted` stay free.
The delivery coordinate is not identified with that debit. -/
theorem count_root_terminal_eq
    {Value Event Stored Context Output : Type} {clients : Nat}
    [DecidableEq Stored] [DecidableEq Output]
    {work : Program Value Event} {events : List Event} {value : Value}
    {calls depth : Nat}
    (semantic : CostedRuns work events value calls depth)
    (capture : Event → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool)
    (actions : List (Action Output clients))
    (state : Configuration (State Value Event) Event Stored Context Output Empty Empty clients)
    (execution : Execution (State Value Event) Event Empty Empty)
    (attached : state.execution = some execution)
    (root : execution.producer = ⟨work, []⟩)
    (next : Execution (State Value Event) Event Empty Empty)
    (retained : (count driverStep capture capacity compatible actions (1, 1) state).1.execution =
      some next)
    (terminal : (machineCore Value Event).step next.producer = none) :
    (count driverStep capture capacity compatible actions (1, 1) state).2.1 =
        Multiplicative.ofAdd (events.length + 2 * calls) ∧
      next.producer = ⟨.done value, []⟩ := by
  obtain ⟨nextCount, debit, retainedCount, account, performed⟩ :=
    count_driver_debit capture capacity compatible actions state execution attached
  have nextCount_eq : nextCount = next :=
    Option.some.inj (retainedCount.symm.trans retained)
  have terminalCount : (machineCore Value Event).step nextCount.producer = none := by
    rw [nextCount_eq]
    exact terminal
  rw [root] at performed
  have identified := semantic.root_eq_of_final debit performed terminalCount
  refine ⟨?_, ?_⟩
  · rw [identified.1] at account
    exact account
  · rw [← nextCount_eq]
    exact identified.2


end InterleavedDriverAccounting

end DriverAccounting

/-! ## Delivery accounts and retained occurrence budgets

The numerical delivery coordinate is the actual cursor travel. Its bound
uses the initial unread occurrences and the admitted suffix, keeping equal
payloads at different positions distinct. These laws exclude retirement
and trimming; their ownership operations have separate transport laws.
-/

section DeliveryAccounting

open SharedOccurrenceLog
open scoped BigOperators

private theorem ofAdd_mul (left right : Nat) :
    Multiplicative.ofAdd left * Multiplicative.ofAdd right =
      Multiplicative.ofAdd (left + right) :=
  (ofAdd_add left right).symm

private theorem deliver_keeps_absent_cursor
    {Producer Borrowed Stored Context Output Effect Handoff : Type} {clients : Nat}
    [DecidableEq Stored] [DecidableEq Output]
    (compatible : Context → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (recipient witness : Fin clients) (output : Output)
    (absent : state.delivery.log.positions witness = none) :
    (deliver compatible state recipient output).2.delivery.log.positions witness = none := by
  unfold deliver
  split
  · unfold Cursor.SharedOccurrenceOwnership.advance Cursor.SharedOccurrenceOwnership.acknowledge
      Cursor.SharedOccurrenceOwnership.prepare pull
    cases peekEq : peek state.delivery.log recipient with
    | answer found payload =>
        by_cases same : witness = recipient
        · subst same
          simp [peek, absent] at peekEq
        · simp [setPosition, absent, same]
    | paused => simp [absent]
    | completed => simp [absent]
    | cancelled => simp [absent]
    | invalid => simp [absent]
  · exact absent

private theorem observed_answer_is_ready
    {Producer Borrowed Stored Context Output Effect Handoff : Type} {clients : Nat}
    [DecidableEq Stored] [DecidableEq Output]
    (compatible : Context → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (client : Fin clients) (output : Output) (position : Nat) (value : Stored)
    (reply : (deliver compatible state client output).1 =
      .observed (.answer position value)) :
    compatible state.context = true := by
  cases ready : compatible state.context with
  | true => rfl
  | false =>
      simp [buffered_context_refusal_preserves_complete_residual compatible state client output
        ready] at reply

private theorem observed_answer_is_peek
    {Producer Borrowed Stored Context Output Effect Handoff : Type} {clients : Nat}
    [DecidableEq Stored] [DecidableEq Output]
    (compatible : Context → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (client : Fin clients) (output : Output) (position : Nat) (value : Stored)
    (ready : compatible state.context = true)
    (reply : (deliver compatible state client output).1 =
      .observed (.answer position value)) :
    peek state.delivery.log client = .answer position value := by
  unfold deliver at reply
  rw [if_pos ready] at reply
  have inner : (Cursor.SharedOccurrenceOwnership.advance state.delivery client output).1 =
      .answer position value := by
    simpa [DeliveryReply.observed.injEq] using reply
  unfold Cursor.SharedOccurrenceOwnership.advance Cursor.SharedOccurrenceOwnership.acknowledge
    Cursor.SharedOccurrenceOwnership.prepare pull at inner
  cases peekEq : peek state.delivery.log client with
  | answer found payload =>
      simp only [peekEq, Reply.answer.injEq] at inner
      obtain ⟨foundEq, payloadEq⟩ := inner
      simp [foundEq, payloadEq]
  | paused => simp [peekEq] at inner
  | completed => simp [peekEq] at inner
  | cancelled => simp [peekEq] at inner
  | invalid => simp [peekEq] at inner

private theorem answer_shortens_unread
    {Producer Borrowed Stored Context Output Effect Handoff : Type} {clients : Nat}
    [DecidableEq Stored] [DecidableEq Output]
    (compatible : Context → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (client : Fin clients) (output : Output) (position found : Nat) (value : Stored)
    (live : state.delivery.log.positions client = some position)
    (reply : (deliver compatible state client output).1 =
      .observed (.answer found value)) :
    (deliver compatible state client output).2.delivery.log.rows = state.delivery.log.rows ∧
      (deliver compatible state client output).2.delivery.log.base =
        state.delivery.log.base ∧
      (deliver compatible state client output).2.delivery.log.positions client =
        some (position + 1) ∧
      (unread (deliver compatible state client output).2.delivery.log client).length + 1 =
        (unread state.delivery.log client).length := by
  have ready := observed_answer_is_ready compatible state client output found value reply
  have seenAtFound := observed_answer_is_peek compatible state client output found value ready reply
  have foundEq : found = position :=
    Option.some.inj ((answer_within state.delivery.log client found value seenAtFound).1.symm.trans
      live)
  have seen : peek state.delivery.log client = .answer position value := by
    simpa [foundEq] using seenAtFound
  have advanced := Cursor.SharedOccurrenceOwnership.advance_answer state.delivery client output
    position value seen
  have shape : deliver compatible state client output =
      (.observed (Cursor.SharedOccurrenceOwnership.advance state.delivery client output).1,
        {state with delivery :=
          (Cursor.SharedOccurrenceOwnership.advance state.delivery client output).2}) := by
    simp [deliver, ready]
  rw [advanced] at shape
  have consumed := answer_unread state.delivery.log client position value seen
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [shape, setPosition]
  · simp [shape, setPosition]
  · simp [shape, setPosition_self]
  · have lengthEq :
        (unread state.delivery.log client).length =
          (unread (setPosition state.delivery.log client (some (position + 1))) client).length
            + 1 := by
      simp [consumed, List.length_cons]
    simpa [shape, unread, setPosition_self] using lengthEq.symm

private theorem deliver_preserves_row_base
    {Producer Borrowed Stored Context Output Effect Handoff : Type} {clients : Nat}
    [DecidableEq Stored] [DecidableEq Output]
    (compatible : Context → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (client : Fin clients) (output : Output) :
    (deliver compatible state client output).2.delivery.log.rows = state.delivery.log.rows ∧
      (deliver compatible state client output).2.delivery.log.base =
        state.delivery.log.base := by
  unfold deliver Cursor.SharedOccurrenceOwnership.advance Cursor.SharedOccurrenceOwnership.acknowledge
    Cursor.SharedOccurrenceOwnership.prepare pull
  split
  · cases peek state.delivery.log client <;> exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

private theorem positions_agree_are_still
    {clients : Nat}
    (start finish : Fin clients → Option Nat)
    (same : ∀ client, finish client = start client) :
    cohortAdvance start finish = 0 ∧
      ∀ client, CursorStep (start client) (finish client) := by
  refine ⟨?_, ?_⟩
  · have identified : finish = start := funext same
    rw [identified]
    exact cohortAdvance_refl _
  · intro client
    rw [same client]
    exact cursorStep_refl _

private theorem deliver_one_cursor
    {Producer Borrowed Stored Context Output Effect Handoff : Type} {clients : Nat}
    [DecidableEq Stored] [DecidableEq Output]
    (compatible : Context → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (client : Fin clients) (output : Output) :
    cohortAdvance state.delivery.log.positions
        (deliver compatible state client output).2.delivery.log.positions =
      answerUnits (deliver compatible state client output).1 ∧
      ∀ witness, CursorStep (state.delivery.log.positions witness)
        ((deliver compatible state client output).2.delivery.log.positions witness) := by
  cases replyEq : (deliver compatible state client output).1 with
  | contextRefused =>
      have sameState : deliver compatible state client output = (.contextRefused, state) := by
        cases ready : compatible state.context with
        | false =>
            simp [buffered_context_refusal_preserves_complete_residual compatible state client
              output ready]
        | true => simp [deliver, ready] at replyEq
      have still := positions_agree_are_still state.delivery.log.positions
        (deliver compatible state client output).2.delivery.log.positions
        (fun witness => by simp [sameState])
      simpa [replyEq, answerUnits] using still
  | observed inner =>
      cases inner with
      | answer found value =>
          have ready := observed_answer_is_ready compatible state client output found value replyEq
          have seen := observed_answer_is_peek compatible state client output found value ready
            replyEq
          have cursor := (answer_within state.delivery.log client found value seen).1
          refine ⟨?_, ?_⟩
          · unfold cohortAdvance
            simp only [answerUnits]
            rw [Finset.sum_eq_single client]
            · have moved := deliver_cursor compatible state client client output found cursor
              simp only [replyEq, if_true] at moved
              simp only [cursorAdvance, cursor, moved]
              exact Nat.add_sub_cancel_left found 1
            · intro witness _ distinct
              cases old : state.delivery.log.positions witness with
              | none => simp [cursorAdvance]
              | some position =>
                  have moved := deliver_cursor compatible state client witness output position old
                  simp only [replyEq, if_neg distinct] at moved
                  simp [cursorAdvance, moved]
            · simp
          · intro witness
            cases old : state.delivery.log.positions witness with
            | none =>
                simp [CursorStep,
                  deliver_keeps_absent_cursor compatible state client witness output old]
            | some position =>
                have moved := deliver_cursor compatible state client witness output position old
                by_cases same : witness = client
                · subst same
                  simp only [replyEq, if_true] at moved
                  simp only [CursorStep, moved]
                  exact Nat.le_add_right position 1
                · simp only [replyEq, if_neg same] at moved
                  simp only [CursorStep, moved]
                  exact Nat.le_refl position
      | paused =>
          have still := positions_agree_are_still state.delivery.log.positions
            (deliver compatible state client output).2.delivery.log.positions (fun witness => by
              cases old : state.delivery.log.positions witness with
              | none =>
                  exact deliver_keeps_absent_cursor compatible state client witness output old
              | some position =>
                  have moved := deliver_cursor compatible state client witness output position old
                  simp only [replyEq] at moved
                  have flat :
                      (if witness = client then some position else some position) = some position := by
                    split <;> rfl
                  exact moved.trans flat)
          simpa [replyEq, answerUnits] using still
      | completed =>
          have still := positions_agree_are_still state.delivery.log.positions
            (deliver compatible state client output).2.delivery.log.positions (fun witness => by
              cases old : state.delivery.log.positions witness with
              | none =>
                  exact deliver_keeps_absent_cursor compatible state client witness output old
              | some position =>
                  have moved := deliver_cursor compatible state client witness output position old
                  simp only [replyEq] at moved
                  have flat :
                      (if witness = client then some position else some position) = some position := by
                    split <;> rfl
                  exact moved.trans flat)
          simpa [replyEq, answerUnits] using still
      | cancelled =>
          have still := positions_agree_are_still state.delivery.log.positions
            (deliver compatible state client output).2.delivery.log.positions (fun witness => by
              cases old : state.delivery.log.positions witness with
              | none =>
                  exact deliver_keeps_absent_cursor compatible state client witness output old
              | some position =>
                  have moved := deliver_cursor compatible state client witness output position old
                  simp only [replyEq] at moved
                  have flat :
                      (if witness = client then some position else some position) = some position := by
                    split <;> rfl
                  exact moved.trans flat)
          simpa [replyEq, answerUnits] using still
      | invalid =>
          have still := positions_agree_are_still state.delivery.log.positions
            (deliver compatible state client output).2.delivery.log.positions (fun witness => by
              cases old : state.delivery.log.positions witness with
              | none =>
                  exact deliver_keeps_absent_cursor compatible state client witness output old
              | some position =>
                  have moved := deliver_cursor compatible state client witness output position old
                  simp only [replyEq] at moved
                  have flat :
                      (if witness = client then some position else some position) = some position := by
                    split <;> rfl
                  exact moved.trans flat)
          simpa [replyEq, answerUnits] using still

/-- The delivery coordinate counts the cursor steps of this action list.
The producer debit is untouched. `CursorStep` records that a live cursor only
moves forward and an absent cursor stays absent. -/
theorem count_delivery_eq_cursor_advance
    {Producer Borrowed Stored Context Output Effect Handoff : Type} {clients : Nat}
    [DecidableEq Stored] [DecidableEq Output]
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool)
    (actions : List (Action Output clients)) (account : ProtocolAccount)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    (count step capture capacity compatible actions account state).2.2 =
        account.2 * Multiplicative.ofAdd (cohortAdvance state.delivery.log.positions
          (count step capture capacity compatible actions account state).1.delivery.log.positions) ∧
      ∀ client, CursorStep (state.delivery.log.positions client)
        ((count step capture capacity compatible actions account state).1.delivery.log.positions
          client) := by
  induction actions generalizing state account with
  | nil =>
      refine ⟨?_, ?_⟩
      · simp [count, cohortAdvance_refl, ofAdd_zero, mul_one]
      · intro client
        exact cursorStep_refl _
  | cons action rest ih =>
      cases action with
      | pump =>
          simp only [count, advanceAction]
          have preserved := pump_preserves_context_cursors_publications step capture capacity
            compatible state
          have ihResult := ih
            (account * productionCharge (pump step capture capacity compatible state).1)
            (pump step capture capacity compatible state).2
          have charge :
              (account * productionCharge (pump step capture capacity compatible state).1).2 =
                account.2 := by
            cases account with
            | mk produced delivered =>
                simp [productionCharge, Prod.mk_mul_mk, mul_one]
          refine ⟨?_, ?_⟩
          · rw [ihResult.1, charge, preserved.2.2.1]
          · intro client
            have stayed : CursorStep (state.delivery.log.positions client)
                ((pump step capture capacity compatible state).2.delivery.log.positions client) := by
              rw [preserved.2.2.1]
              exact cursorStep_refl _
            exact cursorStep_trans stayed (ihResult.2 client)
      | deliver client output =>
          simp only [count, advanceAction]
          have moved := deliver_one_cursor compatible state client output
          have ihResult := ih
            (account * deliveryCharge (deliver compatible state client output).1)
            (deliver compatible state client output).2
          have charge :
              (account * deliveryCharge (deliver compatible state client output).1).2 =
                account.2 * Multiplicative.ofAdd
                  (answerUnits (deliver compatible state client output).1) := by
            cases account with
            | mk produced delivered =>
                simp [deliveryCharge, Prod.mk_mul_mk, mul_one]
          refine ⟨?_, ?_⟩
          · rw [ihResult.1, charge, mul_assoc, ofAdd_mul, ← moved.1]
            have telescope := cohortAdvance_add state.delivery.log.positions
              (deliver compatible state client output).2.delivery.log.positions
              (count step capture capacity compatible rest
                (account * deliveryCharge (deliver compatible state client output).1)
                (deliver compatible state client output).2).1.delivery.log.positions
              moved.2 ihResult.2
            rw [← telescope]
          · intro witness
            exact cursorStep_trans (moved.2 witness) (ihResult.2 witness)

/-- Same comparison on the uncounted walk. `count_erases` is the configuration. -/
theorem count_delivery_eq_executed_cursors
    {Producer Borrowed Stored Context Output Effect Handoff : Type} {clients : Nat}
    [DecidableEq Stored] [DecidableEq Output]
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool)
    (actions : List (Action Output clients)) (account : ProtocolAccount)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    (count step capture capacity compatible actions account state).2.2 =
        account.2 * Multiplicative.ofAdd (cohortAdvance state.delivery.log.positions
          (runActions step capture capacity compatible actions state).delivery.log.positions) ∧
      ∀ client, CursorStep (state.delivery.log.positions client)
        ((runActions step capture capacity compatible actions state).delivery.log.positions
          client) := by
  simpa [count_erases] using
    count_delivery_eq_cursor_advance step capture capacity compatible actions account state

theorem runActions_preserves_base
    {Producer Borrowed Stored Context Output Effect Handoff : Type} {clients : Nat}
    [DecidableEq Stored] [DecidableEq Output]
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool)
    (actions : List (Action Output clients))
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    (runActions step capture capacity compatible actions state).delivery.log.base =
      state.delivery.log.base := by
  induction actions generalizing state with
  | nil => rfl
  | cons action rest ih =>
      cases action with
      | pump =>
          simp only [runActions]
          exact (ih (pump step capture capacity compatible state).2).trans
            (pump_preserves_context_cursors_publications step capture capacity compatible
              state).2.1
      | deliver client output =>
          simp only [runActions]
          exact (ih (deliver compatible state client output).2).trans
            (deliver_preserves_row_base compatible state client output).2

theorem runActions_extends_rows
    {Producer Borrowed Stored Context Output Effect Handoff : Type} {clients : Nat}
    [DecidableEq Stored] [DecidableEq Output]
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool)
    (actions : List (Action Output clients))
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients) :
    ∃ suffix,
      (runActions step capture capacity compatible actions state).delivery.log.rows =
        state.delivery.log.rows ++ suffix := by
  induction actions generalizing state with
  | nil =>
      exact ⟨[], by simp [runActions]⟩
  | cons action rest ih =>
      cases action with
      | pump =>
          simp only [runActions]
          obtain ⟨suffix, later⟩ := ih (pump step capture capacity compatible state).2
          refine ⟨admitted (pump step capture capacity compatible state).1 ++ suffix, ?_⟩
          rw [later, pump_rows step capture capacity compatible state, List.append_assoc]
      | deliver client output =>
          simp only [runActions]
          obtain ⟨suffix, later⟩ := ih (deliver compatible state client output).2
          refine ⟨suffix, ?_⟩
          rw [later, (deliver_preserves_row_base compatible state client output).1]

private theorem runActions_keeps_absent_cursor
    {Producer Borrowed Stored Context Output Effect Handoff : Type} {clients : Nat}
    [DecidableEq Stored] [DecidableEq Output]
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool)
    (actions : List (Action Output clients))
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (client : Fin clients)
    (absent : state.delivery.log.positions client = none) :
    (runActions step capture capacity compatible actions state).delivery.log.positions client =
      none := by
  induction actions generalizing state with
  | nil =>
      simpa [runActions] using absent
  | cons action rest ih =>
      cases action with
      | pump =>
          simp only [runActions]
          exact ih (pump step capture capacity compatible state).2
            ((congrFun (pump_preserves_context_cursors_publications step capture capacity
              compatible state).2.2.1 client).trans absent)
      | deliver recipient output =>
          simp only [runActions]
          exact ih (deliver compatible state recipient output).2
            (deliver_keeps_absent_cursor compatible state recipient client output absent)

private theorem drop_append_length {Stored : Type} (rows suffix : List Stored) (index : Nat) :
    ((rows ++ suffix).drop index).length ≤ (rows.drop index).length + suffix.length := by
  simp only [List.length_drop, List.length_append]
  omega

private theorem client_travel_room
    {Producer Borrowed Stored Context Output Effect Handoff : Type} {clients : Nat}
    [DecidableEq Stored] [DecidableEq Output]
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool)
    (client : Fin clients) (originBase start originUnread originRowsLen : Nat) :
    ∀ (actions : List (Action Output clients))
      (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
      (pos : Nat),
      state.delivery.log.base = originBase →
      originRowsLen ≤ state.delivery.log.rows.length →
      state.delivery.log.positions client = some pos →
      start ≤ pos →
      originBase ≤ pos →
      (pos - start) + (unread state.delivery.log client).length ≤
        originUnread + (state.delivery.log.rows.length - originRowsLen) →
      let final := runActions step capture capacity compatible actions state
      final.delivery.log.base = originBase ∧
        originRowsLen ≤ final.delivery.log.rows.length ∧
        ∃ finalPos,
          final.delivery.log.positions client = some finalPos ∧
          start ≤ finalPos ∧
          originBase ≤ finalPos ∧
          (finalPos - start) + (unread final.delivery.log client).length ≤
            originUnread + (final.delivery.log.rows.length - originRowsLen) := by
  intro actions
  induction actions with
  | nil =>
      intro state pos baseFixed rowsGe live started indexed fits
      refine ⟨baseFixed, rowsGe, pos, live, started, indexed, fits⟩
  | cons action rest ih =>
      intro state pos baseFixed rowsGe live started indexed fits
      cases action with
      | pump =>
          have preserved := pump_preserves_context_cursors_publications step capture capacity
            compatible state
          have midRows := pump_rows step capture capacity compatible state
          have midBase :
              (pump step capture capacity compatible state).2.delivery.log.base = originBase := by
            rw [preserved.2.1, baseFixed]
          have midLive :
              (pump step capture capacity compatible state).2.delivery.log.positions client =
                some pos := by
            rw [congrFun preserved.2.2.1 client, live]
          have midLen :
              (pump step capture capacity compatible state).2.delivery.log.rows.length =
                state.delivery.log.rows.length +
                  (admitted (pump step capture capacity compatible state).1).length := by
            simp [midRows]
          have grown :
              (unread (pump step capture capacity compatible state).2.delivery.log client).length ≤
                (unread state.delivery.log client).length +
                  (admitted (pump step capture capacity compatible state).1).length := by
            simp only [unread, midLive, midBase, midRows, live, baseFixed]
            exact drop_append_length state.delivery.log.rows
              (admitted (pump step capture capacity compatible state).1) (pos - originBase)
          have midFits :
              (pos - start) +
                  (unread (pump step capture capacity compatible state).2.delivery.log
                    client).length ≤
                originUnread +
                  ((pump step capture capacity compatible state).2.delivery.log.rows.length -
                    originRowsLen) := by
            omega
          exact ih (pump step capture capacity compatible state).2 pos midBase
            (by omega) midLive started indexed midFits
      | deliver recipient output =>
          have carrier := deliver_preserves_row_base compatible state recipient output
          have midBase :
              (deliver compatible state recipient output).2.delivery.log.base = originBase := by
            rw [carrier.2, baseFixed]
          have midLen :
              (deliver compatible state recipient output).2.delivery.log.rows.length =
                state.delivery.log.rows.length := by
            simp [carrier.1]
          cases replyEq : (deliver compatible state recipient output).1 with
          | observed inner =>
              cases inner with
              | answer found value =>
                  by_cases same : client = recipient
                  · subst same
                    have short := answer_shortens_unread compatible state client output pos found
                      value live replyEq
                    have midLive :
                        (deliver compatible state client output).2.delivery.log.positions client =
                          some (pos + 1) := short.2.2.1
                    have midUnread :
                        (unread (deliver compatible state client output).2.delivery.log
                          client).length + 1 =
                          (unread state.delivery.log client).length := short.2.2.2
                    have midFits :
                        (pos + 1 - start) +
                            (unread (deliver compatible state client output).2.delivery.log
                              client).length ≤
                          originUnread +
                            ((deliver compatible state client output).2.delivery.log.rows.length -
                              originRowsLen) := by
                      omega
                    exact ih (deliver compatible state client output).2 (pos + 1) midBase
                      (by omega) midLive (by omega) (by omega) midFits
                  · have moved := deliver_cursor compatible state recipient client output pos live
                    simp only [replyEq, same] at moved
                    have midUnread :
                        (unread (deliver compatible state recipient output).2.delivery.log
                          client).length =
                          (unread state.delivery.log client).length := by
                      simp [unread, moved, carrier.1, carrier.2, live]
                    have midFits :
                        (pos - start) +
                            (unread (deliver compatible state recipient output).2.delivery.log
                              client).length ≤
                          originUnread +
                            ((deliver compatible state recipient output).2.delivery.log.rows.length -
                              originRowsLen) := by
                      omega
                    exact ih (deliver compatible state recipient output).2 pos midBase
                      (by omega) moved started indexed midFits
              | paused =>
                  have moved := deliver_cursor compatible state recipient client output pos live
                  simp only [replyEq] at moved
                  have stayed :
                      (deliver compatible state recipient output).2.delivery.log.positions client =
                        some pos :=
                    moved.trans (by split <;> rfl)
                  have midUnread :
                      (unread (deliver compatible state recipient output).2.delivery.log
                        client).length = (unread state.delivery.log client).length := by
                    simp [unread, stayed, carrier.1, carrier.2, live]
                  exact ih (deliver compatible state recipient output).2 pos midBase (by omega)
                    stayed started indexed (by omega)
              | completed =>
                  have moved := deliver_cursor compatible state recipient client output pos live
                  simp only [replyEq] at moved
                  have stayed :
                      (deliver compatible state recipient output).2.delivery.log.positions client =
                        some pos :=
                    moved.trans (by split <;> rfl)
                  have midUnread :
                      (unread (deliver compatible state recipient output).2.delivery.log
                        client).length = (unread state.delivery.log client).length := by
                    simp [unread, stayed, carrier.1, carrier.2, live]
                  exact ih (deliver compatible state recipient output).2 pos midBase (by omega)
                    stayed started indexed (by omega)
              | cancelled =>
                  have moved := deliver_cursor compatible state recipient client output pos live
                  simp only [replyEq] at moved
                  have stayed :
                      (deliver compatible state recipient output).2.delivery.log.positions client =
                        some pos :=
                    moved.trans (by split <;> rfl)
                  have midUnread :
                      (unread (deliver compatible state recipient output).2.delivery.log
                        client).length = (unread state.delivery.log client).length := by
                    simp [unread, stayed, carrier.1, carrier.2, live]
                  exact ih (deliver compatible state recipient output).2 pos midBase (by omega)
                    stayed started indexed (by omega)
              | invalid =>
                  have moved := deliver_cursor compatible state recipient client output pos live
                  simp only [replyEq] at moved
                  have stayed :
                      (deliver compatible state recipient output).2.delivery.log.positions client =
                        some pos :=
                    moved.trans (by split <;> rfl)
                  have midUnread :
                      (unread (deliver compatible state recipient output).2.delivery.log
                        client).length = (unread state.delivery.log client).length := by
                    simp [unread, stayed, carrier.1, carrier.2, live]
                  exact ih (deliver compatible state recipient output).2 pos midBase (by omega)
                    stayed started indexed (by omega)
          | contextRefused =>
              have sameState : deliver compatible state recipient output =
                  (.contextRefused, state) := by
                cases ready : compatible state.context with
                | false =>
                    simp [buffered_context_refusal_preserves_complete_residual compatible state
                      recipient output ready]
                | true => simp [deliver, ready] at replyEq
              simp only [runActions, sameState]
              exact ih state pos baseFixed rowsGe live started indexed fits

/-- One live consumer reads at most the occurrences already waiting for it,
plus the occurrences admitted while the action list runs. Equal payloads at
different positions both count. The initial `Valid` hypothesis is the cursor
lower and upper bound `base ≤ position ≤ pastEnd`; the conclusion records that
base does not move and the final rows are the retained rows plus one suffix. -/
theorem client_cursor_travel_le_retained_occurrences
    {Producer Borrowed Stored Context Output Effect Handoff : Type} {clients : Nat}
    [DecidableEq Stored] [DecidableEq Output]
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (valid : Valid state.delivery.log)
    (actions : List (Action Output clients))
    (client : Fin clients) :
    ∃ suffix,
      (runActions step capture capacity compatible actions state).delivery.log.base =
          state.delivery.log.base ∧
        (runActions step capture capacity compatible actions state).delivery.log.rows =
          state.delivery.log.rows ++ suffix ∧
        cursorAdvance (state.delivery.log.positions client)
            ((runActions step capture capacity compatible actions state).delivery.log.positions
              client) ≤
          (unread state.delivery.log client).length + suffix.length := by
  obtain ⟨suffix, rows⟩ := runActions_extends_rows step capture capacity compatible actions state
  have baseFixed := runActions_preserves_base step capture capacity compatible actions state
  have suffixLen :
      suffix.length =
        (runActions step capture capacity compatible actions state).delivery.log.rows.length -
          state.delivery.log.rows.length := by
    rw [rows, List.length_append]
    omega
  cases live : state.delivery.log.positions client with
  | none =>
      have stayed := runActions_keeps_absent_cursor step capture capacity compatible actions
        state client live
      refine ⟨suffix, baseFixed, rows, ?_⟩
      simp [cursorAdvance, live, unread]
  | some start =>
      have indexed := (valid.2 client start live).1
      have room := client_travel_room step capture capacity compatible client
        state.delivery.log.base start (unread state.delivery.log client).length
        state.delivery.log.rows.length actions state start rfl (by omega) live le_rfl indexed
        (by simp)
      obtain ⟨_, _, finalPos, finalLive, started, _, fits⟩ := room
      refine ⟨suffix, baseFixed, rows, ?_⟩
      have advanceEq : cursorAdvance (some start) (some finalPos) = finalPos - start := by
        simp [cursorAdvance]
      rw [finalLive, advanceEq, suffixLen]
      omega

/-- The executed delivery coordinate is the cohort's cursor travel, and that
travel is bounded by the initial unread occurrences plus one copy of the
admitted suffix for each consumer. A consumer with no cursor contributes no
travel and no initial unread rows. -/
theorem delivery_units_bounded_by_retained_occurrences
    {Producer Borrowed Stored Context Output Effect Handoff : Type} {clients : Nat}
    [DecidableEq Stored] [DecidableEq Output]
    (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
    (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool)
    (state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
    (valid : Valid state.delivery.log)
    (actions : List (Action Output clients)) (account : ProtocolAccount) :
    ∃ suffix,
      (runActions step capture capacity compatible actions state).delivery.log.base =
          state.delivery.log.base ∧
        (runActions step capture capacity compatible actions state).delivery.log.rows =
          state.delivery.log.rows ++ suffix ∧
        cohortAdvance state.delivery.log.positions
            (runActions step capture capacity compatible actions state).delivery.log.positions ≤
          (∑ client, (unread state.delivery.log client).length) +
            clients * suffix.length ∧
        (count step capture capacity compatible actions account state).2.2 =
          account.2 * Multiplicative.ofAdd (cohortAdvance state.delivery.log.positions
            (runActions step capture capacity compatible actions state).delivery.log.positions) := by
  obtain ⟨suffix, rows⟩ := runActions_extends_rows step capture capacity compatible actions state
  have baseFixed := runActions_preserves_base step capture capacity compatible actions state
  have compared := count_delivery_eq_executed_cursors step capture capacity compatible actions
    account state
  have suffixLen :
      suffix.length =
        (runActions step capture capacity compatible actions state).delivery.log.rows.length -
          state.delivery.log.rows.length := by
    rw [rows, List.length_append]
    omega
  have each : ∀ client,
      cursorAdvance (state.delivery.log.positions client)
          ((runActions step capture capacity compatible actions state).delivery.log.positions
            client) ≤
        (unread state.delivery.log client).length + suffix.length := by
    intro client
    obtain ⟨suffix', _, rows', bound⟩ :=
      client_cursor_travel_le_retained_occurrences step capture capacity compatible state valid
        actions client
    have sameLen : suffix'.length = suffix.length := by
      have left : suffix'.length =
          (runActions step capture capacity compatible actions state).delivery.log.rows.length -
            state.delivery.log.rows.length := by
        rw [rows', List.length_append]
        omega
      rw [left, suffixLen]
    rw [sameLen] at bound
    exact bound
  have travelLe : cohortAdvance state.delivery.log.positions
      (runActions step capture capacity compatible actions state).delivery.log.positions ≤
        (∑ client, (unread state.delivery.log client).length) + clients * suffix.length := by
    unfold cohortAdvance
    calc
      _ ≤ ∑ client, ((unread state.delivery.log client).length + suffix.length) :=
        Finset.sum_le_sum (fun client _ => each client)
      _ = _ := by simp [Finset.sum_add_distrib]
  exact ⟨suffix, baseFixed, rows, travelLe, compared.1⟩


end DeliveryAccounting

/-! ## Optional history for interleaved production and delivery

The requested observers consume one actual operation reply. History retains
only admissions and successful deliveries; quiet actions remain ordinary
source steps. Numerical observation, recording and execution limits are
separate. The unobserved entry remains the independent `runActions`.
-/

open Mettapedia.GSLT.Core.InferenceControl.Recording

section InterleavedObservation

local notation "Occurrence" => CausalEvent (HistoryOccurrence clients)

/-- An executed operation retains its actual reply. Numerical and history
projections are computed only by the observers that request them. -/
inductive ActionResult (Producer Borrowed Stored Context Output Effect Handoff : Type)
    (clients : Nat) where
  | pumped (reply : Notice Borrowed Stored Effect Handoff)
      (next : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)
  | delivered (client : Fin clients) (reply : DeliveryReply Stored)
      (next : Configuration Producer Borrowed Stored Context Output Effect Handoff clients)

@[simp] def ActionResult.next :
    ActionResult Producer Borrowed Stored Context Output Effect Handoff clients → Cfg
  | .pumped _ next => next
  | .delivered _ _ next => next

@[simp] def ActionResult.charge :
    ActionResult Producer Borrowed Stored Context Output Effect Handoff clients → ProtocolAccount
  | .pumped reply _ => productionCharge reply
  | .delivered _ reply _ => deliveryCharge reply

@[simp] def ActionResult.occurrence :
    ActionResult Producer Borrowed Stored Context Output Effect Handoff clients → Option Occurrence
  | .pumped reply _ => noticeAdmission? reply
  | .delivered client reply _ => deliveryUse? client reply

def actionResult (action : Action Output clients) (state : Cfg) :
    @ActionResult Producer Borrowed Stored Context Output Effect Handoff clients :=
  match action with
  | .pump =>
      let result := pump step capture capacity compatible state
      .pumped result.1 result.2
  | .deliver client output =>
      let result := deliver compatible state client output
      .delivered client result.1 result.2

private theorem actionResult_state (action : Action Output clients) (state : Cfg) :
    (actionResult step capture capacity compatible action state).next =
      (advanceAction step capture capacity compatible action state).1 := by
  cases action <;> simp [actionResult, advanceAction]

private theorem actionResult_charge (action : Action Output clients) (state : Cfg) :
    (actionResult step capture capacity compatible action state).charge =
      (advanceAction step capture capacity compatible action state).2 := by
  cases action <;> simp [actionResult, advanceAction]

theorem actionResult_pump_occurrence (state : Cfg) :
    (actionResult step capture capacity compatible .pump state).occurrence =
      noticeAdmission? (clients := clients)
        (pump step capture capacity compatible state).1 := by
  simp [actionResult]

theorem actionResult_deliver_occurrence (client : Fin clients) (output : Output) (state : Cfg) :
    (actionResult step capture capacity compatible (.deliver client output) state).occurrence =
      deliveryUse? client (deliver compatible state client output).1 := by
  simp [actionResult]

/-- `none` leaves the prefix unchanged, including its remaining capacity. -/
def pushOccurrence (record : Prefix Occurrence) (occurrence : Option Occurrence) :
    Prefix Occurrence :=
  match occurrence with
  | none => record
  | some occurrence => record.push (fun _ => occurrence)

theorem absent_occurrence_preserves_prefix (record : Prefix Occurrence) :
    pushOccurrence record none = record := rfl

/-- A full prefix omits a real occurrence and ignores an absent one.
Neither branch restores `remaining`. -/
theorem pushOccurrence_exhausted (record : Prefix Occurrence)
    (occurrence : Option Occurrence) (full : record.remaining = 0) :
    (pushOccurrence record occurrence).remaining = 0 ∧
      (pushOccurrence record occurrence).omitted =
        record.omitted +
          match occurrence with
          | none => 0
          | some _ => 1 := by
  cases occurrence with
  | none => simp [pushOccurrence, full]
  | some _ => simp [pushOccurrence, Prefix.push, full]

/-- Retain only actual admissions or deliveries. The payload constructor is
inside `Prefix.push`'s thunk, including when the prefix is already full. -/
def ActionResult.record
    (performed : ActionResult Producer Borrowed Stored Context Output Effect Handoff clients)
    (record : Prefix Occurrence) : Prefix Occurrence :=
  match performed with
  | .pumped (.admitted position _) _ => record.push (fun _ => admissionCausal position)
  | .delivered client (.observed (.answer position _)) _ =>
      record.push (fun _ => deliveryCausal client position)
  | _ => record

omit [DecidableEq Stored] [DecidableEq Output] in
@[simp] theorem ActionResult.record_eq_pushOccurrence
    (performed : ActionResult Producer Borrowed Stored Context Output Effect Handoff clients)
    (record : Prefix Occurrence) :
    performed.record record = pushOccurrence record performed.occurrence := by
  cases performed with
  | pumped reply _ => cases reply <;> rfl
  | delivered client reply _ =>
      cases reply with
      | contextRefused => rfl
      | observed reply => cases reply <;> rfl

/-- History only. Each action runs once; no account is built. -/
def recordActions : List (Action Output clients) → Prefix Occurrence → Cfg →
    Prefix Occurrence × Cfg
  | [], record, state => (record, state)
  | action :: rest, record, state =>
      let performed := actionResult step capture capacity compatible action state
      recordActions rest (performed.record record) performed.next

/-- Both observers. The same `actionResult` supplies the prefix and the charge. -/
def observeActions : List (Action Output clients) → Prefix Occurrence →
    ProtocolAccount → Cfg → Prefix Occurrence × Cfg × ProtocolAccount
  | [], record, account, state => (record, state, account)
  | action :: rest, record, account, state =>
      let performed := actionResult step capture capacity compatible action state
      observeActions rest (performed.record record)
        (account * performed.charge) performed.next

theorem recordActions_erases (actions : List (Action Output clients))
    (record : Prefix Occurrence) (state : Cfg) :
    (recordActions step capture capacity compatible actions record state).2 =
      runActions step capture capacity compatible actions state := by
  induction actions generalizing record state with
  | nil => rfl
  | cons action rest ih =>
      cases action with
      | pump => simp only [recordActions, actionResult, ActionResult.next, runActions, ih]
      | deliver _ _ => simp only [recordActions, actionResult, ActionResult.next, runActions, ih]

theorem observeActions_projects_history (actions : List (Action Output clients))
    (record : Prefix Occurrence) (account : ProtocolAccount) (state : Cfg) :
    ((observeActions step capture capacity compatible actions record account state).1,
      (observeActions step capture capacity compatible actions record account state).2.1) =
      recordActions step capture capacity compatible actions record state := by
  induction actions generalizing record account state with
  | nil => rfl
  | cons _ _ ih => simp only [observeActions, recordActions, ih]

theorem observeActions_projects_account (actions : List (Action Output clients))
    (record : Prefix Occurrence) (account : ProtocolAccount) (state : Cfg) :
    (observeActions step capture capacity compatible actions record account state).2 =
      count step capture capacity compatible actions account state := by
  induction actions generalizing record account state with
  | nil => rfl
  | cons action rest ih =>
      rw [observeActions, count, ih, actionResult_state step capture capacity compatible action state,
        actionResult_charge step capture capacity compatible action state]

/-- The recording limit is not an execution limit. The account is `count`
with no hypothesis on `remaining`. -/
theorem recording_limit_does_not_stop_account (actions : List (Action Output clients))
    (record : Prefix Occurrence) (account : ProtocolAccount) (state : Cfg) :
    (observeActions step capture capacity compatible actions record account state).2.2 =
        (count step capture capacity compatible actions account state).2 ∧
      (observeActions step capture capacity compatible actions record account state).2.1 =
        (count step capture capacity compatible actions account state).1 := by
  have projected :=
    observeActions_projects_account step capture capacity compatible actions record account state
  exact ⟨congrArg Prod.snd projected, congrArg Prod.fst projected⟩

theorem observeActions_exhausted (actions : List (Action Output clients))
    (record : Prefix Occurrence) (account : ProtocolAccount) (state : Cfg)
    (full : record.remaining = 0) :
    (observeActions step capture capacity compatible actions record account state).1.remaining = 0 := by
  induction actions generalizing record account state with
  | nil => simp [observeActions, full]
  | cons action rest ih =>
      simp only [observeActions]
      exact ih ((actionResult step capture capacity compatible action state).record record)
        (account * (actionResult step capture capacity compatible action state).charge)
        (actionResult step capture capacity compatible action state).next
        (by simpa only [ActionResult.record_eq_pushOccurrence] using
          (pushOccurrence_exhausted record
            (actionResult step capture capacity compatible action state).occurrence full).1)

theorem recordActions_append (first second : List (Action Output clients))
    (record : Prefix Occurrence) (state : Cfg) :
    recordActions step capture capacity compatible (first ++ second) record state =
      recordActions step capture capacity compatible second
        (recordActions step capture capacity compatible first record state).1
        (recordActions step capture capacity compatible first record state).2 := by
  induction first generalizing record state with
  | nil => simp [recordActions]
  | cons _ _ ih => simp only [List.cons_append, recordActions, ih]

theorem observeActions_append (first second : List (Action Output clients))
    (record : Prefix Occurrence) (account : ProtocolAccount) (state : Cfg) :
    observeActions step capture capacity compatible (first ++ second) record account state =
      observeActions step capture capacity compatible second
        (observeActions step capture capacity compatible first record account state).1
        (observeActions step capture capacity compatible first record account state).2.2
        (observeActions step capture capacity compatible first record account state).2.1 := by
  induction first generalizing record account state with
  | nil => simp [observeActions]
  | cons _ _ ih => simp only [List.cons_append, observeActions, ih]

/-- Resumption sees the remaining capacity and omission count of the first slice. -/
theorem observeActions_resume_keeps_bounds (first second : List (Action Output clients))
    (record : Prefix Occurrence) (account : ProtocolAccount) (state : Cfg) :
    (observeActions step capture capacity compatible second
      (observeActions step capture capacity compatible first record account state).1
      (observeActions step capture capacity compatible first record account state).2.2
      (observeActions step capture capacity compatible first record account state).2.1).1.remaining =
        (observeActions step capture capacity compatible (first ++ second)
          record account state).1.remaining ∧
      (observeActions step capture capacity compatible second
        (observeActions step capture capacity compatible first record account state).1
        (observeActions step capture capacity compatible first record account state).2.2
        (observeActions step capture capacity compatible first record account state).2.1).1.omitted =
        (observeActions step capture capacity compatible (first ++ second)
          record account state).1.omitted := by
  constructor <;> simp only [observeActions_append]

/-- Choose the observers once. `none`/`none` is only `runActions`. -/
def enterActionObservers : Option (Prefix Occurrence) → Option ProtocolAccount →
    List (Action Output clients) → Cfg →
    Option (Prefix Occurrence) × Option ProtocolAccount × Cfg
  | none, none, actions, state =>
      (none, none, runActions step capture capacity compatible actions state)
  | some record, none, actions, state =>
      let continued := recordActions step capture capacity compatible actions record state
      (some continued.1, none, continued.2)
  | none, some account, actions, state =>
      let continued := count step capture capacity compatible actions account state
      (none, some continued.2, continued.1)
  | some record, some account, actions, state =>
      let continued :=
        observeActions step capture capacity compatible actions record account state
      (some continued.1, some continued.2.2, continued.2.1)

theorem enterActionObservers_neither (actions : List (Action Output clients)) (state : Cfg) :
    enterActionObservers step capture capacity compatible none none actions state =
      (none, none, runActions step capture capacity compatible actions state) := rfl

theorem enterActionObservers_erases (history : Option (Prefix Occurrence))
    (account : Option ProtocolAccount) (actions : List (Action Output clients)) (state : Cfg) :
    (enterActionObservers step capture capacity compatible history account actions state).2.2 =
      runActions step capture capacity compatible actions state := by
  cases history with
  | none =>
      cases account with
      | none => rfl
      | some account =>
          simp only [enterActionObservers, count_erases]
  | some record =>
      cases account with
      | none => simp only [enterActionObservers, recordActions_erases]
      | some account =>
          simp only [enterActionObservers, observeActions_projects_account, count_erases]

theorem enterActionObservers_projects_account (history : Option (Prefix Occurrence))
    (account : Option ProtocolAccount) (actions : List (Action Output clients)) (state : Cfg) :
    ((enterActionObservers step capture capacity compatible history account actions state).2.1,
      (enterActionObservers step capture capacity compatible history account actions state).2.2) =
      match account with
      | none => (none, runActions step capture capacity compatible actions state)
      | some account =>
          (some (count step capture capacity compatible actions account state).2,
            (count step capture capacity compatible actions account state).1) := by
  cases history with
  | none =>
      cases account with
      | none => rfl
      | some _ => rfl
  | some record =>
      cases account with
      | none => simp only [enterActionObservers, recordActions_erases]
      | some account => simp only [enterActionObservers, observeActions_projects_account]

theorem enterActionObservers_projects_history (history : Option (Prefix Occurrence))
    (account : Option ProtocolAccount) (actions : List (Action Output clients)) (state : Cfg) :
    ((enterActionObservers step capture capacity compatible history account actions state).1,
      (enterActionObservers step capture capacity compatible history account actions state).2.2) =
      match history with
      | none => (none, runActions step capture capacity compatible actions state)
      | some record =>
          (some (recordActions step capture capacity compatible actions record state).1,
            (recordActions step capture capacity compatible actions record state).2) := by
  cases history with
  | none =>
      cases account with
      | none => rfl
      | some account => simp only [enterActionObservers, count_erases]
  | some record =>
      cases account with
      | none => rfl
      | some account =>
          simp only [enterActionObservers]
          exact congrArg (fun result => (some result.1, result.2))
            (observeActions_projects_history step capture capacity compatible
              actions record account state)

theorem enterActionObservers_append (history : Option (Prefix Occurrence))
    (account : Option ProtocolAccount) (first second : List (Action Output clients))
    (state : Cfg) :
    enterActionObservers step capture capacity compatible history account (first ++ second) state =
      enterActionObservers step capture capacity compatible
        (enterActionObservers step capture capacity compatible history account first state).1
        (enterActionObservers step capture capacity compatible history account first state).2.1
        second
        (enterActionObservers step capture capacity compatible history account first state).2.2 := by
  cases history with
  | none =>
      cases account with
      | none => simp only [enterActionObservers, runActions_append]
      | some _ => simp only [enterActionObservers, count_append]
  | some _ =>
      cases account with
      | none => simp only [enterActionObservers, recordActions_append]
      | some _ => simp only [enterActionObservers, observeActions_append]

/-- Dropping the prefix keeps the account and continues from the joint state.
The result is the counted entry of the concatenated actions. -/
theorem forget_action_history_preserves_account (record : Prefix Occurrence)
    (account : ProtocolAccount) (first second : List (Action Output clients)) (state : Cfg) :
    enterActionObservers step capture capacity compatible none
        (enterActionObservers step capture capacity compatible (some record) (some account)
          first state).2.1
        second
        (enterActionObservers step capture capacity compatible (some record) (some account)
          first state).2.2 =
      (none,
        some (count step capture capacity compatible (first ++ second) account state).2,
        (count step capture capacity compatible (first ++ second) account state).1) := by
  simp only [enterActionObservers, observeActions_projects_account, count_append]

theorem forget_action_history_continues (record : Prefix Occurrence) (account : ProtocolAccount)
    (first second : List (Action Output clients)) (state : Cfg) :
    (enterActionObservers step capture capacity compatible none
        (enterActionObservers step capture capacity compatible (some record) (some account)
          first state).2.1
        second
        (enterActionObservers step capture capacity compatible (some record) (some account)
          first state).2.2).2.2 =
      runActions step capture capacity compatible (first ++ second) state := by
  rw [forget_action_history_preserves_account]
  simp only [count_erases]

/-- A pump list uses the existing fuel observer. This history does not store
the raw notice; `countPumps` remains the numerical projection. -/
theorem counted_pumps_are_the_pump_observer (fuel : Nat) (account : ProtocolAccount)
    (state : Cfg) :
    enterActionObservers step capture capacity compatible none (some account)
        (List.replicate fuel Action.pump) state =
      (none, some (countPumps step capture capacity compatible fuel account state).2,
        ordinary step capture capacity compatible fuel state) := by
  simp only [enterActionObservers, ← countPumps_eq_count, countPumps_erases]

omit [DecidableEq Stored] in
/-- The same stored value at one position is two deliveries when two consumers
read it. This is the occurrence identity used by `deliveryUse?`. -/
theorem duplicate_payload_stays_two_deliveries (client other : Fin clients)
    (position : Nat) (value : Stored) (distinct : other ≠ client) :
    deliveryUse? client (.observed (.answer position value)) =
        some (deliveryCausal client position) ∧
      deliveryUse? other (.observed (.answer position value)) =
        some (deliveryCausal other position) ∧
      deliveryCausal client position ≠ deliveryCausal other position := by
  refine ⟨rfl, rfl, ?_⟩
  intro same
  have events := congrArg CausalEvent.event same
  simp [deliveryCausal] at events
  cases events
  exact distinct rfl

/-- Cancellation contributes no occurrence and does not spend prefix capacity.
`cancellation_is_not_a_delivery` is the reply; the prefix step is `none`. -/
theorem retired_delivery_leaves_prefix (record : Prefix Occurrence) (state : Cfg)
    (client : Fin clients) (output : Output) (ready : compatible state.context = true) :
    (recordActions step capture capacity compatible [.deliver client output] record
        (retireConsumer state client)).1 = record := by
  have quiet :=
    (cancellation_is_not_a_delivery compatible state client output ready).2.1
  simp [recordActions, actionResult, pushOccurrence, quiet]

/-- Occurrences label actual source edges; quiet steps contribute no event. -/
def edgeOccurrence {source target : Cfg}
    (edge : ActionEdge step capture capacity compatible source target) :
    Option (Mettapedia.Machines.CausalEvent (HistoryOccurrence clients)) := by
  cases edge with
  | ofAction action =>
      cases action with
      | pump => exact noticeAdmission? (pump step capture capacity compatible source).1
      | deliver client output => exact deliveryUse? client (deliver compatible source client output).1


/-- Ordered occurrence words use the same maintained run-account construction
as numerical costs. This account is a mathematical reference, not an
intermediate unbounded log constructed by the bounded worker. -/
def occurrenceAccount :
    letI := actionQuiver (Output := Output) (clients := clients) step capture capacity compatible
    RunAccount (Paths Cfg) (FreeMonoid (Mettapedia.Machines.CausalEvent (HistoryOccurrence clients))) := by
  letI := actionQuiver (Output := Output) (clients := clients) step capture capacity compatible
  exact pathAccount (fun edge =>
    FreeMonoid.ofList (edgeOccurrence step capture capacity compatible edge).toList)

set_option backward.isDefEq.respectTransparency false in
theorem occurrenceAccount_edge (state : Cfg) (action : Action Output clients) :
    letI := actionQuiver (Output := Output) (clients := clients) step capture capacity compatible
    (occurrenceAccount step capture capacity compatible).of
      (Quiver.Hom.toPath (ActionEdge.ofAction (step := step) (capture := capture)
        (capacity := capacity) (compatible := compatible) state action)) =
      FreeMonoid.ofList (actionResult step capture capacity compatible action state).occurrence.toList := by
  cases action <;> simp [occurrenceAccount, Quiver.Hom.toPath,
    pathAccount_cons, pathAccount_nil, edgeOccurrence, actionResult]

/-- Chronological projection of a source path through its free-monoid account. -/
def pathOccurrences {source target : Cfg}
    (path : letI := actionQuiver (Output := Output) (clients := clients) step capture capacity compatible
      Quiver.Path source target) : List (Mettapedia.Machines.CausalEvent (HistoryOccurrence clients)) :=
  letI := actionQuiver (Output := Output) (clients := clients) step capture capacity compatible
  FreeMonoid.toList ((occurrenceAccount step capture capacity compatible).of path)

set_option backward.isDefEq.respectTransparency false in
theorem pathOccurrences_comp {source mid target : Cfg} :
    letI := actionQuiver (Output := Output) (clients := clients) step capture capacity compatible
    ∀ (left : Quiver.Path source mid) (right : Quiver.Path mid target),
      pathOccurrences step capture capacity compatible (left.comp right) =
        pathOccurrences step capture capacity compatible left ++
          pathOccurrences step capture capacity compatible right := by
  let _ := actionQuiver (Output := Output) (clients := clients) step capture capacity compatible
  intro left right
  change FreeMonoid.toList ((occurrenceAccount step capture capacity compatible).of (left ≫ right)) = _
  rw [RunAccount.of_comp, FreeMonoid.toList_mul]
  rfl


/-! ## Streaming diaries compared with source occurrence accounts

The reference word follows the actual source path. The operational worker
streams its bounded prefix and never materializes this whole reference word.
The comparison is relative to the supplied configuration and prefix; earlier
admissions can lie outside that diary and do not become replay authority.
-/

set_option backward.isDefEq.respectTransparency false in
private theorem pathOccurrences_single (state : Cfg) (action : Action Output clients) :
    letI := actionQuiver (Output := Output) (clients := clients) step capture capacity compatible
    pathOccurrences step capture capacity compatible
        (Quiver.Hom.toPath (ActionEdge.ofAction (step := step) (capture := capture)
          (capacity := capacity) (compatible := compatible) state action)) =
      (actionResult step capture capacity compatible action state).occurrence.toList := by
  let _ := actionQuiver (Output := Output) (clients := clients) step capture capacity compatible
  change FreeMonoid.toList ((occurrenceAccount step capture capacity compatible).of _) = _
  rw [occurrenceAccount_edge]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem pathOccurrences_action (action : Action Output clients)
    (rest : List (Action Output clients)) (state : Cfg) :
    pathOccurrences step capture capacity compatible
        (actionPath step capture capacity compatible (action :: rest) state) =
      (actionResult step capture capacity compatible action state).occurrence.toList ++
        pathOccurrences step capture capacity compatible
          (actionPath step capture capacity compatible rest
            (runActions step capture capacity compatible [action] state)) := by
  let _ := actionQuiver (Output := Output) (clients := clients) step capture capacity compatible
  cases action <;> rw [actionPath, pathOccurrences_comp, pathOccurrences_single] <;> rfl

private theorem pushOccurrence_eq_append (record : Prefix Occurrence)
    (occurred : Option Occurrence) :
    pushOccurrence record occurred = Prefix.append record occurred.toList := by
  cases occurred <;> simp [pushOccurrence, Prefix.append]

theorem recordActions_eq_source_prefix (actions : List (Action Output clients))
    (record : Prefix Occurrence) (state : Cfg) :
    recordActions step capture capacity compatible actions record state =
      (Prefix.append record (pathOccurrences step capture capacity compatible
          (actionPath step capture capacity compatible actions state)),
        runActions step capture capacity compatible actions state) := by
  induction actions generalizing record state with
  | nil => rfl
  | cons action rest ih =>
      rw [pathOccurrences_action]
      cases action <;>
        simp only [recordActions, actionResult, ActionResult.record_eq_pushOccurrence,
          ActionResult.next, ActionResult.occurrence, runActions, ih,
          pushOccurrence_eq_append, Prefix.append_append]

/-- Stopping observation leaves the retained computation in place. Restarting
records the suffix from its actual resumed state, without replaying the prefix
or pretending that the unrecorded interval was observed. -/
theorem record_after_unrecorded_gap
    (first gap last : List (Action Output clients))
    (earlier resumed : Prefix Occurrence) (state : Cfg) :
    recordActions step capture capacity compatible last resumed
        (runActions step capture capacity compatible gap
          (recordActions step capture capacity compatible first earlier state).2) =
      (Prefix.append resumed (pathOccurrences step capture capacity compatible
          (actionPath step capture capacity compatible last
            (runActions step capture capacity compatible (first ++ gap) state))),
        runActions step capture capacity compatible (first ++ gap ++ last) state) := by
  rw [recordActions_erases, ← runActions_append, recordActions_eq_source_prefix]
  simp only [runActions_append]

theorem record_prefix_bounds (actions : List (Action Output clients))
    (record : Prefix Occurrence) (state : Cfg) :
    let events := pathOccurrences step capture capacity compatible
      (actionPath step capture capacity compatible actions state)
    (recordActions step capture capacity compatible actions record state).1.items =
        record.items ++ events.take record.remaining ∧
      (recordActions step capture capacity compatible actions record state).1.remaining =
        record.remaining - events.length ∧
      (recordActions step capture capacity compatible actions record state).1.omitted =
        record.omitted + (events.length - record.remaining) := by
  rw [recordActions_eq_source_prefix]
  exact Prefix.append_state record _

set_option backward.isDefEq.respectTransparency false in
/-- A fresh suffix diary has its own bound. Earlier recorded and unrecorded
actions neither consume that capacity nor appear as reconstructed entries. -/
theorem fresh_record_after_unrecorded_gap_bounds
    (first gap last : List (Action Output clients))
    (earlier : Prefix Occurrence) (bound : Nat) (state : Cfg) :
    let resumed := runActions step capture capacity compatible gap
      (recordActions step capture capacity compatible first earlier state).2
    let events := pathOccurrences step capture capacity compatible
      (actionPath step capture capacity compatible last resumed)
    let result := recordActions step capture capacity compatible last
      (Prefix.initial bound) resumed
    result.1.items = events.take bound ∧
      result.1.remaining = bound - events.length ∧
      result.1.omitted = events.length - bound := by
  dsimp only
  simpa only [Prefix.initial, Prefix.items, List.reverse_nil,
    List.nil_append, Nat.zero_add] using
    (record_prefix_bounds step capture capacity compatible last
      (Prefix.initial bound)
      (runActions step capture capacity compatible gap
        (recordActions step capture capacity compatible first earlier state).2))

set_option backward.isDefEq.respectTransparency false in
theorem observeActions_eq_source_accounts (actions : List (Action Output clients))
    (record : Prefix Occurrence) (account : ProtocolAccount) (state : Cfg) :
    letI := actionQuiver (Output := Output) (clients := clients) step capture capacity compatible
    observeActions step capture capacity compatible actions record account state =
      (Prefix.append record (pathOccurrences step capture capacity compatible
          (actionPath step capture capacity compatible actions state)),
        runActions step capture capacity compatible actions state,
        account * (splitAccount step capture capacity compatible).of
          (actionPath step capture capacity compatible actions state)) := by
  let _ := actionQuiver (Output := Output) (clients := clients) step capture capacity compatible
  apply Prod.ext
  · exact (congrArg Prod.fst
      (observeActions_projects_history step capture capacity compatible actions record account state)).trans
        (congrArg Prod.fst
          (recordActions_eq_source_prefix step capture capacity compatible actions record state))
  · rw [observeActions_projects_account]
    apply Prod.ext
    · exact count_erases step capture capacity compatible actions account state
    · rw [count_scales, count_eq_pathAccount]

theorem projected_occurrence_is_a_source_reply (actions : List (Action Output clients))
    (state : Cfg) {event : Occurrence}
    (member : event ∈ pathOccurrences step capture capacity compatible
      (actionPath step capture capacity compatible actions state)) :
    ∃ done action later,
      actions = done ++ action :: later ∧
        (actionResult step capture capacity compatible action
          (runActions step capture capacity compatible done state)).occurrence = some event := by
  induction actions generalizing state with
  | nil =>
      change event ∈ ([] : List Occurrence) at member
      cases member
  | cons head tail ih =>
      rw [pathOccurrences_action] at member
      cases List.mem_append.mp member with
      | inl here =>
          cases label : (actionResult step capture capacity compatible head state).occurrence with
          | none => simp only [label, Option.toList, List.not_mem_nil] at here
          | some value =>
              simp only [label, Option.toList, List.mem_singleton] at here
              cases here
              exact ⟨[], head, tail, rfl, by simpa only [runActions] using label⟩
      | inr laterMember =>
          obtain ⟨done, action, later, split, label⟩ :=
            ih (runActions step capture capacity compatible [head] state) laterMember
          refine ⟨head :: done, action, later, ?_, ?_⟩
          · simp only [List.cons_append, split]
          · change (actionResult step capture capacity compatible action
              (runActions step capture capacity compatible ([head] ++ done) state)).occurrence = _
            rw [runActions_append]
            exact label

theorem occurrence_count_le_source_actions (actions : List (Action Output clients)) (state : Cfg) :
    (pathOccurrences step capture capacity compatible
      (actionPath step capture capacity compatible actions state)).length ≤ actions.length := by
  induction actions generalizing state with
  | nil => exact Nat.le_refl 0
  | cons action rest ih =>
      rw [pathOccurrences_action, List.length_append, List.length_cons]
      have atMost :
          (actionResult step capture capacity compatible action state).occurrence.toList.length ≤ 1 := by
        cases (actionResult step capture capacity compatible action state).occurrence <;> simp
      have tail := ih (runActions step capture capacity compatible [action] state)
      omega

/-- A suffix diary may cite an earlier admission without reconstructing it.
The projected diary alone is therefore not a closed replay graph. -/
theorem late_delivery_has_external_admission (client : Fin clients) (position : Nat) :
    ((Prefix.initial 1 : Prefix Occurrence).append [deliveryCausal client position]).items =
        [deliveryCausal client position] ∧
      admissionCausal (clients := clients) position ∉
        ((Prefix.initial 1 : Prefix Occurrence).append [deliveryCausal client position]).items ∧
      (deliveryCausal client position).directCauses =
        [admissionOccurrence (clients := clients) position] := by
  simp [Prefix.append, Prefix.initial, Prefix.push, Prefix.items,
    deliveryCausal, admissionCausal, admissionOccurrence]

/-! ### Admission and delivery causal projection

Empty direct causes discharge dependency availability only. An admission is
fresh because its position is the current row count, so it is distinct from
every earlier admission and from any captured boundary. A delivery identity is
unique because that consumer's cursor advances on the observed answer, and a
repeated publication or refusal adds no event. `CausalReceipt.Ordered` is
accumulated from those state facts. A graph label is not itself freshness or
source authority. Structural validity does not authenticate an edge or grant
execution (`valid_structure_does_not_authenticate_edges`).

The projection retains admissions and successful deliveries. It is not a
complete effect trace: `noticeAdmission?` is `some` only for `.admitted`
(`effect_request_is_not_admission`, `handoff_barrier_is_not_admission`,
`interruption_is_not_admission`). Equal stored values stay distinct occurrences
(`duplicate_payload_stays_two_deliveries`).
-/

/-- Admission positions in the order the projection recorded them. -/
def admittedPositions : List Occurrence → List Nat
  | [] => []
  | ⟨.admission position, _⟩ :: rest => position :: admittedPositions rest
  | ⟨.delivery _ _, _⟩ :: rest => admittedPositions rest

/-- Delivery positions of one consumer, in the order they were recorded. -/
def deliveredPositions : List Occurrence → Fin clients → List Nat
  | [], _ => []
  | ⟨.admission _, _⟩ :: rest, client => deliveredPositions rest client
  | ⟨.delivery found position, _⟩ :: rest, client =>
      if found = client then position :: deliveredPositions rest client
      else deliveredPositions rest client

/-- Admission identities present in a projection. Payloads are not identities. -/
def admissionIdentities : List Occurrence → List (HistoryOccurrence clients)
  | [] => []
  | ⟨.admission position, _⟩ :: rest => .admission position :: admissionIdentities rest
  | ⟨.delivery _ _, _⟩ :: rest => admissionIdentities rest

/-- Roots are the admission identities the projection actually contains. -/
def protocolReceipt (events : List Occurrence) : CausalReceipt (HistoryOccurrence clients) :=
  ⟨admissionIdentities events, events⟩

private theorem admittedPositions_append (first second : List Occurrence) :
    admittedPositions (first ++ second) =
      admittedPositions first ++ admittedPositions second := by
  induction first with
  | nil => rfl
  | cons head tail ih =>
      cases head with
      | mk identity _ =>
          cases identity with
          | admission position => simp [admittedPositions, ih]
          | delivery _ _ => simp [admittedPositions, ih]

private theorem deliveredPositions_append (first second : List Occurrence) (client : Fin clients) :
    deliveredPositions (first ++ second) client =
      deliveredPositions first client ++ deliveredPositions second client := by
  induction first with
  | nil => rfl
  | cons head tail ih =>
      cases head with
      | mk identity _ =>
          cases identity with
          | admission _ => simp [deliveredPositions, ih]
          | delivery found position =>
              by_cases same : found = client
              · simp [deliveredPositions, ih, same]
              · simp [deliveredPositions, ih, same]

private theorem admission_in_support_iff (events : List Occurrence) (position : Nat) :
    HistoryOccurrence.admission position ∈ events.map CausalEvent.event ↔
      position ∈ admittedPositions events := by
  induction events with
  | nil => simp [admittedPositions]
  | cons head tail ih =>
      cases head with
      | mk identity _ =>
          cases identity with
          | admission found =>
              constructor
              · intro member
                rw [List.map_cons, List.mem_cons] at member
                rcases member with same | later
                · cases same
                  simp [admittedPositions]
                · rw [admittedPositions]
                  exact List.mem_cons_of_mem _ (ih.mp later)
              · intro member
                rw [admittedPositions] at member
                rcases List.mem_cons.mp member with rfl | later
                · simp
                · exact List.mem_cons_of_mem _ (ih.mpr later)
          | delivery _ _ =>
              constructor
              · intro member
                rw [List.map_cons, List.mem_cons] at member
                rcases member with same | later
                · cases same
                · rw [admittedPositions]
                  exact ih.mp later
              · intro member
                rw [admittedPositions] at member
                exact List.mem_cons_of_mem _ (ih.mpr member)

private theorem delivery_in_support_iff (events : List Occurrence) (client : Fin clients)
    (position : Nat) :
    HistoryOccurrence.delivery client position ∈ events.map CausalEvent.event ↔
      position ∈ deliveredPositions events client := by
  induction events with
  | nil => simp [deliveredPositions]
  | cons head tail ih =>
      cases head with
      | mk identity _ =>
          cases identity with
          | admission _ =>
              constructor
              · intro member
                rw [List.map_cons, List.mem_cons] at member
                rcases member with same | later
                · cases same
                · rw [deliveredPositions]
                  exact ih.mp later
              · intro member
                rw [deliveredPositions] at member
                exact List.mem_cons_of_mem _ (ih.mpr member)
          | delivery found pos =>
              by_cases sameClient : found = client
              · subst found
                by_cases samePos : pos = position
                · subst pos
                  constructor
                  · intro _
                    simp [deliveredPositions]
                  · intro _
                    simp
                · constructor
                  · intro member
                    rw [List.map_cons, List.mem_cons] at member
                    rcases member with same | later
                    · cases same
                      exact absurd rfl samePos
                    · have tailMem := ih.mp later
                      simp only [deliveredPositions]
                      exact List.mem_cons_of_mem _ tailMem
                  · intro member
                    simp only [deliveredPositions] at member
                    rcases List.mem_cons.mp member with eq | later
                    · exact absurd eq.symm samePos
                    · exact List.mem_cons_of_mem _ (ih.mpr later)
              · constructor
                · intro member
                  rw [List.map_cons, List.mem_cons] at member
                  rcases member with same | later
                  · cases same
                    exact absurd rfl sameClient
                  · have tailMem := ih.mp later
                    simp only [deliveredPositions, sameClient]
                    exact tailMem
                · intro member
                  simp only [deliveredPositions, sameClient] at member
                  exact List.mem_cons_of_mem _ (ih.mpr member)

theorem admissionIdentity_in_support (events : List Occurrence)
    {root : HistoryOccurrence clients} (member : root ∈ admissionIdentities events) :
    root ∈ events.map CausalEvent.event := by
  induction events with
  | nil => cases member
  | cons head tail ih =>
      cases head with
      | mk identity _ =>
          cases identity with
          | admission position =>
              rw [admissionIdentities] at member
              rcases List.mem_cons.mp member with rfl | later
              · simp
              · exact List.mem_cons_of_mem _ (ih later)
          | delivery _ _ =>
              rw [admissionIdentities] at member
              exact List.mem_cons_of_mem _ (ih member)

private theorem admissionIdentities_eq_positions (events : List Occurrence) :
    admissionIdentities events =
      (admittedPositions events).map HistoryOccurrence.admission := by
  induction events with
  | nil => rfl
  | cons head tail ih =>
      cases head with
      | mk identity _ =>
          cases identity with
          | admission _ => simp [admissionIdentities, admittedPositions, ih]
          | delivery _ _ => simp [admissionIdentities, admittedPositions, ih]

omit [DecidableEq Stored] [DecidableEq Output] in
/-- The receipt's roots are the monotone row positions, not an extra label. -/
theorem synced_roots_are_row_positions
    (events : List Occurrence) (state : Cfg) (admissions : admittedPositions events =
      List.range state.delivery.log.rows.length) :
    (protocolReceipt events).roots =
      (List.range state.delivery.log.rows.length).map HistoryOccurrence.admission := by
  simp [protocolReceipt, admissionIdentities_eq_positions, admissions]

/-- Packaging `Ordered` as a receipt. Roots sit in the support by construction.
This does not read a cause label as authority. -/
theorem protocolReceipt_of_ordered (events : List Occurrence)
    (ordered : CausalReceipt.Ordered ([] : List (HistoryOccurrence clients)) events) :
    CausalReceipt.WellFormed [] (protocolReceipt events) := by
  refine ⟨List.nodup_nil, ordered, ?_⟩
  intro root member
  rw [CausalReceipt.known, CausalReceipt.flattenedSupport, protocolReceipt,
    List.nil_append]
  exact admissionIdentity_in_support events member

omit [DecidableEq Stored] [DecidableEq Output] in
/-- Ancestry of one completed producer prefix. Roots are the admission
identities inside that prefix. `boundary` is the predecessor list already
captured with the recording, not a replay of forgotten actions. An omitted
prefix refuses before any receipt is built. This readout does not grant
authority and does not release storage. -/
def producerPrefixAncestry (boundary : List (HistoryOccurrence clients))
    (record : Prefix Occurrence) (identity : HistoryOccurrence clients) :
    Option (List (HistoryOccurrence clients)) :=
  match record.complete? with
  | none => none
  | some events =>
      Mettapedia.Machines.ExecutionHistoryReadout.completeAncestors record boundary
        (protocolReceipt events).roots identity

omit [DecidableEq Stored] [DecidableEq Output] in
/-- A completed prefix answers the same ancestry as its protocol receipt.
The receipt's roots and the supplied boundary are the ones `completeAncestors`
checks. -/
theorem producerPrefixAncestry_eq_receipt
    (boundary : List (HistoryOccurrence clients)) (events : List Occurrence) (bound : Nat)
    (identity : HistoryOccurrence clients) (fits : events.length ≤ bound) :
    producerPrefixAncestry boundary ((Prefix.initial bound).append events) identity =
      (protocolReceipt events).ancestors? boundary identity := by
  have complete :
      ((Prefix.initial bound).append events).complete? = some events :=
    (Prefix.complete_iff bound events).mpr fits
  unfold producerPrefixAncestry
  rw [complete]
  exact Mettapedia.Machines.ExecutionHistoryReadout.recorded_ancestry
    (protocolReceipt events) bound boundary identity fits

omit [DecidableEq Stored] [DecidableEq Output] in
/-- Omitted capture refuses. Retained items are not promoted to a complete ancestry. -/
theorem producerPrefixAncestry_omitted
    (boundary : List (HistoryOccurrence clients)) (events : List Occurrence) (bound : Nat)
    (identity : HistoryOccurrence clients) (lost : bound < events.length) :
    producerPrefixAncestry boundary ((Prefix.initial bound).append events) identity = none := by
  have omitted : ((Prefix.initial bound).append events).omitted ≠ 0 := by
    rw [Prefix.initial_omitted]
    exact Nat.ne_of_gt (Nat.sub_pos_of_lt lost)
  unfold producerPrefixAncestry
  rw [Prefix.complete?]
  simp only [omitted, ite_false]

omit [DecidableEq Stored] [DecidableEq Output] in
/-- An identity outside the captured boundary and the completed prefix is not
given an ancestor. -/
theorem producerPrefixAncestry_missing
    (boundary : List (HistoryOccurrence clients)) (events : List Occurrence) (bound : Nat)
    (identity : HistoryOccurrence clients) (fits : events.length ≤ bound)
    (missing : identity ∉ (protocolReceipt events).known boundary) :
    producerPrefixAncestry boundary ((Prefix.initial bound).append events) identity = none := by
  rw [producerPrefixAncestry_eq_receipt boundary events bound identity fits]
  exact CausalReceipt.ancestors?_refused boundary (protocolReceipt events) identity missing

omit [DecidableEq Stored] [DecidableEq Output] in
/-- A predecessor that is not in the recorded boundary or the completed prefix
makes the protocol receipt fail its existing check. The readout stays `none`. -/
theorem producerPrefixAncestry_unchecked
    (boundary : List (HistoryOccurrence clients)) (events : List Occurrence) (bound : Nat)
    (identity : HistoryOccurrence clients) (fits : events.length ≤ bound)
    (invalid : ¬ CausalReceipt.WellFormed boundary (protocolReceipt events)) :
    producerPrefixAncestry boundary ((Prefix.initial bound).append events) identity = none := by
  rw [producerPrefixAncestry_eq_receipt boundary events bound identity fits]
  have unchecked : (protocolReceipt events).check boundary = false := by
    cases probe : (protocolReceipt events).check boundary with
    | false => rfl
    | true =>
        exact absurd ((CausalReceipt.check_iff boundary (protocolReceipt events)).mp probe) invalid
  simp only [CausalReceipt.ancestors?, unchecked, Bool.false_eq_true, false_and, ite_false]

omit [DecidableEq Stored] [DecidableEq Output] in
/-- A positive ancestry answer is the existing exact cause relation of the
protocol receipt. No ancestor is added outside that relation. -/
theorem producerPrefixAncestry_exact
    (boundary : List (HistoryOccurrence clients)) (events : List Occurrence) (bound : Nat)
    (identity : HistoryOccurrence clients) (result : List (HistoryOccurrence clients))
    (fits : events.length ≤ bound)
    (reported : producerPrefixAncestry boundary ((Prefix.initial bound).append events) identity =
      some result) :
    CausalReceipt.WellFormed boundary (protocolReceipt events) ∧
      identity ∈ (protocolReceipt events).known boundary ∧
      ∀ cause, cause ∈ result ↔
        cause = identity ∨
          Relation.TransGen (protocolReceipt events).Direct cause identity := by
  rw [producerPrefixAncestry_eq_receipt boundary events bound identity fits] at reported
  exact CausalReceipt.ancestors?_exact boundary (protocolReceipt events) identity result reported

omit [DecidableEq Stored] [DecidableEq Output] in
/-- `serviceCohort` admits one row and delivers it to both consumer positions.
Ancestry is the retained prefix read by `producerPrefixAncestry`. The boundary
is the empty predecessor list captured with that prefix. -/
theorem service_cohort_two_consumer_ancestry :
    let returned := pump serviceCohortStep (fun value => some value) (fun _ => true) (fun _ => true)
      serviceCohort
    let admitted := pump serviceCohortStep (fun value => some value) (fun _ => true) (fun _ => true)
      returned.2
    let left := deliver (fun _ => true) admitted.2 (0 : Fin 2) ()
    let right := deliver (fun _ => true) left.2 (1 : Fin 2) ()
    noticeAdmission? (clients := 2) admitted.1 = some (admissionCausal (clients := 2) 0) ∧
      deliveryUse? (0 : Fin 2) left.1 = some (deliveryCausal (0 : Fin 2) 0) ∧
      deliveryUse? (1 : Fin 2) right.1 = some (deliveryCausal (1 : Fin 2) 0) ∧
      ∃ clientAncestors otherAncestors : List (HistoryOccurrence 2),
        producerPrefixAncestry (clients := 2) ([] : List (HistoryOccurrence 2))
          ((Prefix.initial 3).append
            [admissionCausal (clients := 2) 0, deliveryCausal (0 : Fin 2) 0,
              deliveryCausal (1 : Fin 2) 0])
          (deliveryOccurrence (0 : Fin 2) 0) = some clientAncestors ∧
        producerPrefixAncestry (clients := 2) ([] : List (HistoryOccurrence 2))
          ((Prefix.initial 3).append
            [admissionCausal (clients := 2) 0, deliveryCausal (0 : Fin 2) 0,
              deliveryCausal (1 : Fin 2) 0])
          (deliveryOccurrence (1 : Fin 2) 0) = some otherAncestors ∧
        (∀ cause, cause ∈ clientAncestors ↔
          cause = deliveryOccurrence (0 : Fin 2) 0 ∨
            cause = admissionOccurrence (clients := 2) 0) ∧
        (∀ cause, cause ∈ otherAncestors ↔
          cause = deliveryOccurrence (1 : Fin 2) 0 ∨
            cause = admissionOccurrence (clients := 2) 0) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  let events : List (CausalEvent (HistoryOccurrence 2)) :=
    [admissionCausal 0, deliveryCausal (0 : Fin 2) 0, deliveryCausal (1 : Fin 2) 0]
  have fits : events.length ≤ 3 := by decide
  have receipt :
      protocolReceipt (clients := 2) events =
        sharedAdmissionReceipt (0 : Fin 2) (1 : Fin 2) 0 := by
    simp [events, protocolReceipt, admissionIdentities, sharedAdmissionReceipt,
      admissionCausal, admissionOccurrence, deliveryCausal]
  have ancestry :=
    shared_row_delivery_ancestry (0 : Fin 2) (1 : Fin 2) 0 (by decide)
  rcases ancestry with ⟨clientAncestors, otherAncestors, clientRead, otherRead, clientMem, otherMem⟩
  refine ⟨clientAncestors, otherAncestors, ?_, ?_, clientMem, otherMem⟩
  · rw [producerPrefixAncestry_eq_receipt (clients := 2) [] events 3
        (deliveryOccurrence (0 : Fin 2) 0) fits, receipt]
    exact clientRead
  · rw [producerPrefixAncestry_eq_receipt (clients := 2) [] events 3
        (deliveryOccurrence (1 : Fin 2) 0) fits, receipt]
    exact otherRead

omit [DecidableEq Stored] [DecidableEq Output] in
/-- The same captured cohort refuses when the prefix omits part of the receipt.
Retained items are not promoted to a complete ancestry. -/
theorem service_cohort_ancestry_omitted :
    producerPrefixAncestry (clients := 2) ([] : List (HistoryOccurrence 2))
        ((Prefix.initial 2).append
          [admissionCausal (clients := 2) 0, deliveryCausal (0 : Fin 2) 0,
            deliveryCausal (1 : Fin 2) 0])
        (deliveryOccurrence (0 : Fin 2) 0) = none ∧
      producerPrefixAncestry (clients := 2) ([] : List (HistoryOccurrence 2))
        ((Prefix.initial 2).append
          [admissionCausal (clients := 2) 0, deliveryCausal (0 : Fin 2) 0,
            deliveryCausal (1 : Fin 2) 0])
        (deliveryOccurrence (1 : Fin 2) 0) = none := by
  let events : List (CausalEvent (HistoryOccurrence 2)) :=
    [admissionCausal 0, deliveryCausal (0 : Fin 2) 0, deliveryCausal (1 : Fin 2) 0]
  have lost : 2 < events.length := by decide
  exact ⟨producerPrefixAncestry_omitted (clients := 2) [] events 2
      (deliveryOccurrence (0 : Fin 2) 0) lost,
    producerPrefixAncestry_omitted (clients := 2) [] events 2
      (deliveryOccurrence (1 : Fin 2) 0) lost⟩

omit [DecidableEq Stored] [DecidableEq Output] in
/-- A duplicated boundary is not the recorded predecessor list. The readout
refuses both consumer positions and does not manufacture an ancestor. -/
theorem service_cohort_ancestry_wrong_boundary :
    producerPrefixAncestry (clients := 2)
        [admissionOccurrence (clients := 2) 0, admissionOccurrence (clients := 2) 0]
        ((Prefix.initial 3).append
          [admissionCausal (clients := 2) 0, deliveryCausal (0 : Fin 2) 0,
            deliveryCausal (1 : Fin 2) 0])
        (deliveryOccurrence (0 : Fin 2) 0) = none ∧
      producerPrefixAncestry (clients := 2)
        [admissionOccurrence (clients := 2) 0, admissionOccurrence (clients := 2) 0]
        ((Prefix.initial 3).append
          [admissionCausal (clients := 2) 0, deliveryCausal (0 : Fin 2) 0,
            deliveryCausal (1 : Fin 2) 0])
        (deliveryOccurrence (1 : Fin 2) 0) = none := by
  let events : List (CausalEvent (HistoryOccurrence 2)) :=
    [admissionCausal 0, deliveryCausal (0 : Fin 2) 0, deliveryCausal (1 : Fin 2) 0]
  let boundary : List (HistoryOccurrence 2) :=
    [admissionOccurrence 0, admissionOccurrence 0]
  have fits : events.length ≤ 3 := by decide
  have invalid : ¬ CausalReceipt.WellFormed boundary (protocolReceipt (clients := 2) events) := by
    intro well
    have dup : ¬ boundary.Nodup := by decide
    exact dup well.1
  exact ⟨producerPrefixAncestry_unchecked (clients := 2) boundary events 3
      (deliveryOccurrence (0 : Fin 2) 0) fits invalid,
    producerPrefixAncestry_unchecked (clients := 2) boundary events 3
      (deliveryOccurrence (1 : Fin 2) 0) fits invalid⟩

/-- A second copy of an admission still fails `Ordered` when its cause list is
empty. Emptiness discharges the dependency conjunct; the identity is already
available. -/
theorem duplicate_admission_rejected_despite_empty_causes (position : Nat) :
    (admissionCausal (clients := clients) position).directCauses =
        ([] : List (HistoryOccurrence clients)) ∧
      ¬ CausalReceipt.Ordered ([] : List (HistoryOccurrence clients))
          [admissionCausal position, admissionCausal position] := by
  refine ⟨rfl, ?_⟩
  intro ordered
  rcases ordered with ⟨_, _, ⟨stale, _, _⟩⟩
  exact stale (List.mem_singleton_self _)

/-- A delivery whose admission is not available is not a closed receipt. -/
theorem delivery_without_admission_is_not_ordered (client : Fin clients) (position : Nat) :
    ¬ CausalReceipt.Ordered ([] : List (HistoryOccurrence clients))
        [deliveryCausal client position] := by
  intro ordered
  rcases ordered with ⟨_, causes, _⟩
  exact absurd (causes (HistoryOccurrence.admission position) (by simp [deliveryCausal]))
    List.not_mem_nil

/-- Repeating a delivery keeps the admission available and still fails freshness. -/
theorem duplicate_delivery_is_not_ordered (client : Fin clients) (position : Nat) :
    let prior : List Occurrence := [admissionCausal position, deliveryCausal client position]
    (∀ cause ∈ (deliveryCausal client position).directCauses,
        cause ∈ prior.map CausalEvent.event) ∧
      (deliveryCausal client position).event ∈ prior.map CausalEvent.event ∧
      ¬ CausalReceipt.Ordered ([] : List (HistoryOccurrence clients))
          (prior ++ [deliveryCausal client position]) := by
  refine ⟨?_, ?_, ?_⟩
  · intro cause member
    simp [deliveryCausal] at member
    subst cause
    simp [admissionCausal]
  · simp [deliveryCausal]
  · intro ordered
    rcases ordered with ⟨_, _, tail⟩
    rcases tail with ⟨_, _, ⟨stale, _, _⟩⟩
    exact stale (by simp [admissionCausal, deliveryCausal])

omit [DecidableEq Stored] [DecidableEq Output] in
/-- Rows that do not grow did not admit. The absent notice is the no-event case. -/
private theorem stable_rows_add_no_admission (state : Cfg)
    (notice : Notice Borrowed Stored Effect Handoff)
    (stable : state.delivery.log.rows ++ admitted notice = state.delivery.log.rows) :
    noticeAdmission? (clients := clients) notice = none := by
  cases notice with
  | admitted position value =>
      rw [admitted] at stable
      have lengths := congrArg List.length stable
      simp only [List.length_append, List.length_singleton] at lengths
      omega
  | progress => rfl
  | returned _ => rfl
  | captureRefused => rfl
  | admissionRefused => rfl
  | noConsumers => rfl
  | backpressure => rfl
  | contextRefused => rfl
  | yielded => rfl
  | effect _ => rfl
  | handoff _ => rfl
  | interrupted => rfl
  | completed => rfl
  | detached => rfl

omit [DecidableEq Stored] [DecidableEq Output] in
/-- One pump either keeps the log, completes it, or admits at the current end.
The admitted position is `pastEnd` because that is where `append` writes the row. -/
private theorem pump_log_change (state : Cfg) :
    (pump step capture capacity compatible state).2.delivery.log = state.delivery.log ∨
      (pump step capture capacity compatible state).2.delivery.log =
        SharedOccurrenceLog.complete state.delivery.log ∨
      ∃ value,
        (pump step capture capacity compatible state).1 =
          .admitted (SharedOccurrenceLog.pastEnd state.delivery.log) value ∧
        state.delivery.log.rows.length < state.delivery.log.limit ∧
        (pump step capture capacity compatible state).2.delivery.log =
          {state.delivery.log with rows := state.delivery.log.rows ++ [value]} := by
  cases executionEq : state.execution with
  | none =>
      refine Or.inl ?_
      simp [pump, executionEq]
  | some execution =>
      cases allowed : compatible state.context with
      | false =>
          refine Or.inl ?_
          simp [pump, executionEq, allowed]
      | true =>
          cases done : state.delivery.log.completed with
          | true =>
              refine Or.inl ?_
              simp [pump, executionEq, allowed, done]
          | false =>
              cases modeEq : execution.mode with
              | effect request =>
                  refine Or.inl ?_
                  simp [pump, executionEq, allowed, done, modeEq]
              | handoff request =>
                  refine Or.inl ?_
                  simp [pump, executionEq, allowed, done, modeEq]
              | interrupted =>
                  refine Or.inl ?_
                  simp [pump, executionEq, allowed, done, modeEq]
              | active =>
                  cases demanded : hasConsumers state.delivery.log with
                  | false =>
                      refine Or.inl ?_
                      simp [pump, executionEq, allowed, done, modeEq, demanded]
                  | true =>
                      by_cases room : state.delivery.log.rows.length < state.delivery.log.limit
                      · cases pendingEq : execution.pending with
                        | none =>
                            cases outcomeEq : step execution.producer with
                            | progress next =>
                                refine Or.inl ?_
                                simp [pump, stage, executionEq, allowed, done, modeEq, demanded,
                                  room, pendingEq, outcomeEq]
                            | returned value next =>
                                refine Or.inl ?_
                                simp [pump, stage, executionEq, allowed, done, modeEq, demanded,
                                  room, pendingEq, outcomeEq]
                            | yielded next =>
                                refine Or.inl ?_
                                simp [pump, stage, executionEq, allowed, done, modeEq, demanded,
                                  room, pendingEq, outcomeEq]
                            | effect request next =>
                                refine Or.inl ?_
                                simp [pump, stage, executionEq, allowed, done, modeEq, demanded,
                                  room, pendingEq, outcomeEq]
                            | handoff request next =>
                                refine Or.inl ?_
                                simp [pump, stage, executionEq, allowed, done, modeEq, demanded,
                                  room, pendingEq, outcomeEq]
                            | interrupted next =>
                                refine Or.inl ?_
                                simp [pump, stage, executionEq, allowed, done, modeEq, demanded,
                                  room, pendingEq, outcomeEq]
                            | completed next =>
                                refine Or.inr (Or.inl ?_)
                                simp [pump, stage, SharedOccurrenceLog.complete, executionEq, allowed,
                                  done, modeEq, demanded, room, pendingEq, outcomeEq]
                        | some value =>
                            cases captured : capture value with
                            | none =>
                                refine Or.inl ?_
                                simp [pump, admit, executionEq, allowed, done, modeEq, demanded,
                                  room, pendingEq, captured]
                            | some stored =>
                                cases fits : capacity stored with
                                | false =>
                                    refine Or.inl ?_
                                    simp [pump, admit, executionEq, allowed, done, modeEq, demanded,
                                      room, pendingEq, captured, fits]
                                | true =>
                                    refine Or.inr (Or.inr ⟨stored, ?_, room, ?_⟩)
                                    · simp [pump, admit, SharedOccurrenceLog.append,
                                        SharedOccurrenceLog.pastEnd, executionEq, allowed, done,
                                        modeEq, demanded, room, pendingEq, captured, fits]
                                    · simp [pump, admit, SharedOccurrenceLog.append, executionEq,
                                        allowed, done, modeEq, demanded, room, pendingEq, captured,
                                        fits]
                      · refine Or.inl ?_
                        simp [pump, executionEq, allowed, done, modeEq, demanded, room]

private theorem ordered_snoc (events : List Occurrence) (event : Occurrence)
    (ordered : CausalReceipt.Ordered ([] : List (HistoryOccurrence clients)) events)
    (fresh : event.event ∉ events.map CausalEvent.event)
    (available : ∀ cause ∈ event.directCauses, cause ∈ events.map CausalEvent.event) :
    CausalReceipt.Ordered [] (events ++ [event]) :=
  (CausalReceipt.ordered_append [] events [event]).mpr ⟨ordered, fresh, available, trivial⟩

/-- Log validity, base zero, admission positions equal to `0 ..< rows.length`,
and each live cursor's deliveries equal to `0 ..< cursor`. `shape` records the
cause lists the protocol emits. Freshness is not one of those lists: an empty
cause list only makes the dependency check vacuous. -/
structure ProtocolSync (events : List Occurrence) (state : Cfg) : Prop where
  valid : SharedOccurrenceLog.Valid state.delivery.log
  anchored : state.delivery.log.base = 0
  admissions : admittedPositions events = List.range state.delivery.log.rows.length
  deliveries : ∀ client cursor, state.delivery.log.positions client = some cursor →
    deliveredPositions events client = List.range cursor
  shape : ∀ event ∈ events,
    match event.event with
    | .admission _ => event.directCauses = []
    | .delivery _ position => event.directCauses = [HistoryOccurrence.admission position]

omit [DecidableEq Stored] [DecidableEq Output] in
private theorem protocolSync_initial_proof (producer : Producer) (context : Context) (limit : Nat) :
    ProtocolSync ([] : List Occurrence)
      (@initial Producer Borrowed Stored Context Output Effect Handoff clients producer context
        limit) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [initial]
    exact SharedOccurrenceLog.initial_valid limit
  · simp [initial, SharedOccurrenceLog.initial]
  · simp [initial, SharedOccurrenceLog.initial, admittedPositions, List.range_zero]
  · intro client cursor present
    simp only [initial, SharedOccurrenceLog.initial] at present
    cases present
    simp [deliveredPositions, List.range_zero]
  · intro event member
    cases member

omit [DecidableEq Stored] [DecidableEq Output] in
theorem protocolSync_initial (producer : Producer) (context : Context) (limit : Nat) :
    ProtocolSync ([] : List Occurrence)
      (@initial Producer Borrowed Stored Context Output Effect Handoff clients producer context
        limit) ∧
      CausalReceipt.Ordered ([] : List (HistoryOccurrence clients)) ([] : List Occurrence) :=
  ⟨protocolSync_initial_proof producer context limit, trivial⟩

omit [DecidableEq Stored] [DecidableEq Output] in
private theorem protocolSync_preserve_log (events : List Occurrence) (state next : Cfg)
    (synced : ProtocolSync events state)
    (sameRows : next.delivery.log = state.delivery.log ∨
      next.delivery.log = SharedOccurrenceLog.complete state.delivery.log) :
    ProtocolSync events next := by
  rcases sameRows with same | completed
  · refine ⟨?_, ?_, ?_, ?_, synced.shape⟩
    · rw [same]; exact synced.valid
    · rw [same]; exact synced.anchored
    · rw [same]; exact synced.admissions
    · intro client cursor present
      rw [same] at present
      exact synced.deliveries client cursor present
  · refine ⟨?_, ?_, ?_, ?_, synced.shape⟩
    · rw [completed]
      exact SharedOccurrenceLog.complete_valid _ synced.valid
    · rw [completed]
      exact synced.anchored
    · rw [completed]
      exact synced.admissions
    · intro client cursor present
      rw [completed] at present
      exact synced.deliveries client cursor present

omit [DecidableEq Stored] [DecidableEq Output] in
private theorem protocolSync_pump (events : List Occurrence) (state : Cfg)
    (synced : ProtocolSync events state)
    (ordered : CausalReceipt.Ordered ([] : List (HistoryOccurrence clients)) events) :
    ProtocolSync (events ++ (noticeAdmission? (clients := clients)
        (pump step capture capacity compatible state).1).toList)
      (pump step capture capacity compatible state).2 ∧
      CausalReceipt.Ordered []
        (events ++ (noticeAdmission? (clients := clients)
          (pump step capture capacity compatible state).1).toList) := by
  rcases pump_log_change step capture capacity compatible state with
    same | completed | ⟨value, notice, room, logEq⟩
  · have rowEq : (pump step capture capacity compatible state).2.delivery.log.rows =
        state.delivery.log.rows := by rw [same]
    have rows := pump_rows step capture capacity compatible state
    have stable : state.delivery.log.rows ++
        admitted (pump step capture capacity compatible state).1 = state.delivery.log.rows := by
      rw [← rows, rowEq]
    have quiet := stable_rows_add_no_admission state
      (pump step capture capacity compatible state).1 stable
    rw [quiet]
    simp only [Option.toList, List.append_nil]
    exact ⟨protocolSync_preserve_log events state _ synced (Or.inl same), ordered⟩
  · have rowEq : (pump step capture capacity compatible state).2.delivery.log.rows =
        state.delivery.log.rows := by rw [completed, SharedOccurrenceLog.complete]
    have rows := pump_rows step capture capacity compatible state
    have stable : state.delivery.log.rows ++
        admitted (pump step capture capacity compatible state).1 = state.delivery.log.rows := by
      rw [← rows, rowEq]
    have quiet := stable_rows_add_no_admission state
      (pump step capture capacity compatible state).1 stable
    rw [quiet]
    simp only [Option.toList, List.append_nil]
    exact ⟨protocolSync_preserve_log events state _ synced (Or.inr completed), ordered⟩
  · have occurred : noticeAdmission? (clients := clients)
        (pump step capture capacity compatible state).1 =
        some (admissionCausal (SharedOccurrenceLog.pastEnd state.delivery.log)) := by
      rw [notice]
      rfl
    rw [occurred]
    simp only [Option.toList]
    let position := SharedOccurrenceLog.pastEnd state.delivery.log
    have posLen : position = state.delivery.log.rows.length := by
      simp [SharedOccurrenceLog.pastEnd, synced.anchored, position]
    have fresh : (admissionCausal position).event ∉ events.map CausalEvent.event := by
      intro member
      have posMem := (admission_in_support_iff events position).mp member
      rw [synced.admissions, List.mem_range, posLen] at posMem
      exact Nat.lt_irrefl _ posMem
    have causes : ∀ cause ∈ (admissionCausal position).directCauses,
        cause ∈ events.map CausalEvent.event := by
      intro cause member
      simp [admissionCausal] at member
    refine ⟨?_, ordered_snoc events (admissionCausal position) ordered fresh causes⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [logEq]
      refine ⟨?_, ?_⟩
      · simp only [List.length_append, List.length_singleton]
        omega
      · intro client cursor present
        have old := synced.valid.2 client cursor present
        simp only [SharedOccurrenceLog.pastEnd, List.length_append, List.length_singleton] at old ⊢
        omega
    · rw [logEq]
      exact synced.anchored
    · have added : admittedPositions (events ++ [admissionCausal position]) =
          admittedPositions events ++ [position] := by
        rw [admittedPositions_append]
        simp [admittedPositions, admissionCausal]
      rw [added, synced.admissions, posLen, logEq, List.length_append, List.length_singleton,
        List.range_succ]
    · intro client cursor present
      have oldPresent : state.delivery.log.positions client = some cursor := by
        rw [logEq] at present
        exact present
      have sameDelivered : deliveredPositions (events ++ [admissionCausal position]) client =
          deliveredPositions events client := by
        rw [deliveredPositions_append]
        simp [deliveredPositions, admissionCausal]
      rw [sameDelivered]
      exact synced.deliveries client cursor oldPresent
    · intro event member
      rcases List.mem_append.mp member with earlier | later
      · exact synced.shape event earlier
      · rcases List.mem_singleton.mp later with rfl
        rfl

private theorem deliver_answer_cursor (state : Cfg) (client : Fin clients) (output : Output)
    (position : Nat) (value : Stored) (ready : compatible state.context = true)
    (waiting : SharedOccurrenceLog.peek state.delivery.log client = .answer position value) :
    (deliver compatible state client output).1 = .observed (.answer position value) ∧
      (deliver compatible state client output).2.delivery.log.rows = state.delivery.log.rows ∧
      (deliver compatible state client output).2.delivery.log.base = state.delivery.log.base ∧
      (deliver compatible state client output).2.delivery.log.limit = state.delivery.log.limit ∧
      (deliver compatible state client output).2.delivery.log.completed =
        state.delivery.log.completed ∧
      (deliver compatible state client output).2.delivery.log.positions client =
        some (position + 1) ∧
      ∀ other, other ≠ client →
        (deliver compatible state client output).2.delivery.log.positions other =
          state.delivery.log.positions other := by
  have advanced := SharedOccurrenceOwnership.advance_answer state.delivery client output
    position value waiting
  unfold deliver
  rw [if_pos ready, advanced]
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · simp [SharedOccurrenceLog.setPosition_self]
  · intro other distinct
    simp [SharedOccurrenceLog.setPosition_other state.delivery.log client other
      (some (position + 1)) distinct]

private theorem deliver_preserves_valid (state : Cfg) (client : Fin clients) (output : Output)
    (valid : SharedOccurrenceLog.Valid state.delivery.log) :
    SharedOccurrenceLog.Valid (deliver compatible state client output).2.delivery.log := by
  cases ready : compatible state.context with
  | false =>
      rw [buffered_context_refusal_preserves_complete_residual compatible state client output ready]
      exact valid
  | true =>
      have logEq : (deliver compatible state client output).2.delivery.log =
          (SharedOccurrenceLog.pull state.delivery.log client).2 := by
        simp [deliver, ready, SharedOccurrenceOwnership.advance,
          SharedOccurrenceOwnership.acknowledge, SharedOccurrenceOwnership.prepare]
      rw [logEq]
      exact SharedOccurrenceLog.pull_valid state.delivery.log client valid

private theorem protocolSync_deliver (events : List Occurrence) (state : Cfg)
    (synced : ProtocolSync events state)
    (ordered : CausalReceipt.Ordered ([] : List (HistoryOccurrence clients)) events)
    (client : Fin clients) (output : Output) :
    ProtocolSync (events ++ (deliveryUse? client
        (deliver compatible state client output).1).toList)
      (deliver compatible state client output).2 ∧
      CausalReceipt.Ordered [] (events ++ (deliveryUse? client
        (deliver compatible state client output).1).toList) := by
  cases ready : compatible state.context with
  | false =>
      have eqResult := buffered_context_refusal_preserves_complete_residual compatible state client
        output ready
      rw [eqResult]
      rw [show deliveryUse? client (.contextRefused : DeliveryReply Stored) = none from rfl]
      simp only [Option.toList, List.append_nil]
      exact ⟨synced, ordered⟩
  | true =>
      cases peekEq : SharedOccurrenceLog.peek state.delivery.log client with
      | answer position value =>
          have stepped := deliver_answer_cursor compatible state client output position value ready
            peekEq
          have within := SharedOccurrenceLog.answer_within state.delivery.log client position value
            peekEq
          have occurred : deliveryUse? client (deliver compatible state client output).1 =
              some (deliveryCausal client position) := by
            rw [stepped.1]
            rfl
          rw [occurred]
          simp only [Option.toList]
          have oldCursor := within.1
          have fresh : (deliveryCausal client position).event ∉ events.map CausalEvent.event := by
            intro member
            have posMem := (delivery_in_support_iff events client position).mp member
            rw [synced.deliveries client position oldCursor, List.mem_range] at posMem
            exact Nat.lt_irrefl _ posMem
          have causeReady : HistoryOccurrence.admission position ∈ events.map CausalEvent.event := by
            apply (admission_in_support_iff events position).mpr
            rw [synced.admissions, List.mem_range]
            have upper := within.2.2
            simp only [SharedOccurrenceLog.pastEnd, synced.anchored, Nat.zero_add] at upper
            exact upper
          have causes : ∀ cause ∈ (deliveryCausal client position).directCauses,
              cause ∈ events.map CausalEvent.event := by
            intro cause member
            simp [deliveryCausal] at member
            subst cause
            exact causeReady
          refine ⟨?_, ordered_snoc events (deliveryCausal client position) ordered fresh causes⟩
          refine ⟨deliver_preserves_valid compatible state client output synced.valid, ?_, ?_, ?_, ?_⟩
          · rw [stepped.2.2.1]
            exact synced.anchored
          · rw [admittedPositions_append, stepped.2.1]
            simp [admittedPositions, deliveryCausal, synced.admissions]
          · intro witness cursor present
            by_cases same : witness = client
            · subst witness
              have cursorEq : cursor = position + 1 :=
                Option.some.inj (present.symm.trans stepped.2.2.2.2.2.1)
              have added : deliveredPositions (events ++ [deliveryCausal client position]) client =
                  deliveredPositions events client ++ [position] := by
                rw [deliveredPositions_append]
                simp [deliveredPositions, deliveryCausal]
              rw [cursorEq, added, synced.deliveries client position oldCursor, List.range_succ]
            · have oldPresent : state.delivery.log.positions witness = some cursor := by
                rw [← stepped.2.2.2.2.2.2 witness same]
                exact present
              have unchanged : deliveredPositions (events ++ [deliveryCausal client position])
                  witness = deliveredPositions events witness := by
                rw [deliveredPositions_append]
                simp only [deliveredPositions, deliveryCausal, if_neg (Ne.symm same),
                  List.append_nil]
              rw [unchanged]
              exact synced.deliveries witness cursor oldPresent
          · intro event member
            rcases List.mem_append.mp member with earlier | later
            · exact synced.shape event earlier
            · rcases List.mem_singleton.mp later with rfl
              rfl
      | paused =>
          have eqResult : deliver compatible state client output = (.observed .paused, state) := by
            simp [deliver, ready, peekEq, SharedOccurrenceOwnership.advance,
              SharedOccurrenceOwnership.acknowledge, SharedOccurrenceOwnership.prepare,
              SharedOccurrenceLog.pull]
          rw [eqResult]
          rw [show deliveryUse? client (.observed .paused : DeliveryReply Stored) = none from rfl]
          simp only [Option.toList, List.append_nil]
          exact ⟨synced, ordered⟩
      | completed =>
          have eqResult : deliver compatible state client output = (.observed .completed, state) := by
            simp [deliver, ready, peekEq, SharedOccurrenceOwnership.advance,
              SharedOccurrenceOwnership.acknowledge, SharedOccurrenceOwnership.prepare,
              SharedOccurrenceLog.pull]
          rw [eqResult]
          rw [show deliveryUse? client (.observed .completed : DeliveryReply Stored) = none from rfl]
          simp only [Option.toList, List.append_nil]
          exact ⟨synced, ordered⟩
      | cancelled =>
          have eqResult : deliver compatible state client output = (.observed .cancelled, state) := by
            simp [deliver, ready, peekEq, SharedOccurrenceOwnership.advance,
              SharedOccurrenceOwnership.acknowledge, SharedOccurrenceOwnership.prepare,
              SharedOccurrenceLog.pull]
          rw [eqResult]
          rw [show deliveryUse? client (.observed .cancelled : DeliveryReply Stored) = none from rfl]
          simp only [Option.toList, List.append_nil]
          exact ⟨synced, ordered⟩
      | invalid =>
          have eqResult : deliver compatible state client output = (.observed .invalid, state) := by
            simp [deliver, ready, peekEq, SharedOccurrenceOwnership.advance,
              SharedOccurrenceOwnership.acknowledge, SharedOccurrenceOwnership.prepare,
              SharedOccurrenceLog.pull]
          rw [eqResult]
          rw [show deliveryUse? client (.observed .invalid : DeliveryReply Stored) = none from rfl]
          simp only [Option.toList, List.append_nil]
          exact ⟨synced, ordered⟩

/-- A second delivery does not emit the identity just consumed. The cursor is
already `position + 1`, so this refusal or later answer is a different event. -/
theorem repeated_delivery_adds_no_event (state : Cfg) (client : Fin clients) (output : Output)
    (position : Nat) (value : Stored) (ready : compatible state.context = true)
    (waiting : SharedOccurrenceLog.peek state.delivery.log client = .answer position value) :
    deliveryUse? client (deliver compatible (deliver compatible state client output).2 client
        output).1 ≠ some (deliveryCausal client position) := by
  intro repeated
  have stepped := deliver_answer_cursor compatible state client output position value ready waiting
  have moved : (deliver compatible state client output).2.delivery.log.positions client =
      some (position + 1) := stepped.2.2.2.2.2.1
  have readyNext : compatible (deliver compatible state client output).2.context = true := by
    unfold deliver
    rw [if_pos ready]
    exact ready
  let next := (deliver compatible state client output).2
  cases peekNext : SharedOccurrenceLog.peek next.delivery.log client with
  | answer found payload =>
      have cursorEq :=
        (SharedOccurrenceLog.answer_within next.delivery.log client found payload peekNext).1
      rw [moved] at cursorEq
      have foundPos : found = position + 1 := Option.some.inj cursorEq.symm
      have observed := deliver_observes_answer compatible next client output found payload
        readyNext peekNext
      rw [observed.2.1] at repeated
      have sameEvent := Option.some.inj repeated
      have ids := congrArg CausalEvent.event sameEvent
      simp only [deliveryCausal] at ids
      cases ids
      exact absurd foundPos.symm (Nat.succ_ne_self position)
  | paused =>
      have eqResult : deliver compatible next client output = (.observed .paused, next) := by
        unfold deliver
        rw [if_pos readyNext]
        simp [peekNext, SharedOccurrenceOwnership.advance,
          SharedOccurrenceOwnership.acknowledge, SharedOccurrenceOwnership.prepare,
          SharedOccurrenceLog.pull]
      rw [eqResult] at repeated
      rw [show deliveryUse? client (.observed .paused : DeliveryReply Stored) = none from rfl]
        at repeated
      cases repeated
  | completed =>
      have eqResult : deliver compatible next client output = (.observed .completed, next) := by
        unfold deliver
        rw [if_pos readyNext]
        simp [peekNext, SharedOccurrenceOwnership.advance,
          SharedOccurrenceOwnership.acknowledge, SharedOccurrenceOwnership.prepare,
          SharedOccurrenceLog.pull]
      rw [eqResult] at repeated
      rw [show deliveryUse? client (.observed .completed : DeliveryReply Stored) = none from rfl]
        at repeated
      cases repeated
  | cancelled =>
      have eqResult : deliver compatible next client output = (.observed .cancelled, next) := by
        unfold deliver
        rw [if_pos readyNext]
        simp [peekNext, SharedOccurrenceOwnership.advance,
          SharedOccurrenceOwnership.acknowledge, SharedOccurrenceOwnership.prepare,
          SharedOccurrenceLog.pull]
      rw [eqResult] at repeated
      rw [show deliveryUse? client (.observed .cancelled : DeliveryReply Stored) = none from rfl]
        at repeated
      cases repeated
  | invalid =>
      have eqResult : deliver compatible next client output = (.observed .invalid, next) := by
        unfold deliver
        rw [if_pos readyNext]
        simp [peekNext, SharedOccurrenceOwnership.advance,
          SharedOccurrenceOwnership.acknowledge, SharedOccurrenceOwnership.prepare,
          SharedOccurrenceLog.pull]
      rw [eqResult] at repeated
      rw [show deliveryUse? client (.observed .invalid : DeliveryReply Stored) = none from rfl]
        at repeated
      cases repeated

private theorem protocolSync_action (events : List Occurrence) (state : Cfg)
    (synced : ProtocolSync events state)
    (ordered : CausalReceipt.Ordered ([] : List (HistoryOccurrence clients)) events)
    (action : Action Output clients) :
    let performed := actionResult step capture capacity compatible action state
    ProtocolSync (events ++ performed.occurrence.toList) performed.next ∧
      CausalReceipt.Ordered [] (events ++ performed.occurrence.toList) := by
  cases action with
  | pump =>
      simpa [actionResult, ActionResult.occurrence, ActionResult.next] using
        protocolSync_pump step capture capacity compatible events state synced ordered
  | deliver client output =>
      simpa [actionResult, ActionResult.occurrence, ActionResult.next] using
        protocolSync_deliver compatible events state synced ordered client output

set_option backward.isDefEq.respectTransparency false in
private theorem pathOccurrences_nil (state : Cfg) :
    pathOccurrences step capture capacity compatible
        (actionPath step capture capacity compatible ([] : List (Action Output clients)) state) =
      [] := by
  let _ := actionQuiver (Output := Output) (clients := clients) step capture capacity compatible
  simp [actionPath, pathOccurrences, occurrenceAccount, pathAccount_nil, FreeMonoid.toList_one]

set_option backward.isDefEq.respectTransparency false in
private theorem pathOccurrences_append (before after : List (Action Output clients)) (state : Cfg) :
    pathOccurrences step capture capacity compatible
        (actionPath step capture capacity compatible (before ++ after) state) =
      pathOccurrences step capture capacity compatible
          (actionPath step capture capacity compatible before state) ++
        pathOccurrences step capture capacity compatible
          (actionPath step capture capacity compatible after
            (runActions step capture capacity compatible before state)) := by
  induction before generalizing state with
  | nil =>
      rw [List.nil_append, pathOccurrences_nil]
      simp [runActions]
  | cons action rest ih =>
      rw [List.cons_append, pathOccurrences_action, pathOccurrences_action]
      have tail := ih (runActions step capture capacity compatible [action] state)
      have states := runActions_append step capture capacity compatible [action] rest state
      rw [List.singleton_append] at states
      rw [tail, states, List.append_assoc]

/-- The state invariant and the accumulated order survive every finite action list.
`Ordered` is extended at each real admission or delivery from the position and
the cursor; a quiet pump or a non-answer delivery appends nothing. -/
theorem protocolSync_actions (events : List Occurrence) (state : Cfg)
    (synced : ProtocolSync events state)
    (ordered : CausalReceipt.Ordered ([] : List (HistoryOccurrence clients)) events)
    (actions : List (Action Output clients)) :
    ProtocolSync (events ++ pathOccurrences step capture capacity compatible
        (actionPath step capture capacity compatible actions state))
      (runActions step capture capacity compatible actions state) ∧
    CausalReceipt.Ordered ([] : List (HistoryOccurrence clients))
      (events ++ pathOccurrences step capture capacity compatible
        (actionPath step capture capacity compatible actions state)) := by
  induction actions generalizing events state with
  | nil =>
      rw [pathOccurrences_nil, List.append_nil]
      exact ⟨synced, ordered⟩
  | cons action rest ih =>
      have stepped := protocolSync_action step capture capacity compatible events state synced
        ordered action
      rw [pathOccurrences_action]
      have states := runActions_append step capture capacity compatible [action] rest state
      rw [List.singleton_append] at states
      rw [states]
      have nextEq := actionResult_state step capture capacity compatible action state
      have runEq := advanceAction_state step capture capacity compatible action state
      have continued := ih (events ++ (actionResult step capture capacity compatible action
        state).occurrence.toList) (runActions step capture capacity compatible [action] state)
        ((nextEq.trans runEq) ▸ stepped.1) stepped.2
      simpa [List.append_assoc] using continued

/-- Arbitrary finite source actions from a valid initial configuration project
to a well-formed admission/delivery receipt. Freshness of each admission is its
position at the end of the log then current. Each delivery cites an earlier
admission because the answered cursor lies strictly before `pastEnd`. No
delivery identity repeats, because the cursor moves to the next position and a
repeated publication or refusal contributes no event. -/
theorem protocol_from_initial (producer : Producer) (context : Context) (limit : Nat)
    (actions : List (Action Output clients)) :
    let origin := initial producer context limit
    let events := pathOccurrences step capture capacity compatible
      (actionPath step capture capacity compatible actions origin)
    let final := runActions step capture capacity compatible actions origin
    ProtocolSync events final ∧
      CausalReceipt.Ordered ([] : List (HistoryOccurrence clients)) events ∧
      CausalReceipt.WellFormed [] (protocolReceipt events) ∧
      (protocolReceipt events).roots =
        (List.range final.delivery.log.rows.length).map HistoryOccurrence.admission := by
  intro origin events final
  have started : ProtocolSync ([] : List Occurrence) origin ∧
      CausalReceipt.Ordered ([] : List (HistoryOccurrence clients)) ([] : List Occurrence) :=
    protocolSync_initial producer context limit
  have walked := protocolSync_actions step capture capacity compatible [] origin started.1
    started.2 actions
  simp only [List.nil_append] at walked
  exact ⟨walked.1, walked.2, protocolReceipt_of_ordered events walked.2,
    synced_roots_are_row_positions events final walked.1.admissions⟩

/-- Split an action history at an arbitrary prefix. The suffix receipt's events
are only the suffix projection. Prior identities appear as the explicit boundary,
not as fabricated events and not as replay authority. A suffix admission is fresh
against that boundary because its position is at least the prefix row count;
`directCauses = []` only discharges dependency availability. -/
theorem protocol_suffix_boundary (producer : Producer) (context : Context) (limit : Nat)
    (before after : List (Action Output clients)) :
    let origin := initial producer context limit
    let prefixEvents := pathOccurrences step capture capacity compatible
      (actionPath step capture capacity compatible before origin)
    let mid := runActions step capture capacity compatible before origin
    let suffixEvents := pathOccurrences step capture capacity compatible
      (actionPath step capture capacity compatible after mid)
    let boundary := prefixEvents.map CausalEvent.event
    pathOccurrences step capture capacity compatible
        (actionPath step capture capacity compatible (before ++ after) origin) =
      prefixEvents ++ suffixEvents ∧
    CausalReceipt.WellFormed boundary (protocolReceipt suffixEvents) ∧
    (protocolReceipt suffixEvents).events = suffixEvents ∧
    (∀ event ∈ prefixEvents, event ∉ suffixEvents) ∧
    (∀ event ∈ suffixEvents, ∀ position,
      event.event = HistoryOccurrence.admission position →
        event.directCauses = [] ∧
        mid.delivery.log.rows.length ≤ position ∧
        HistoryOccurrence.admission position ∉ boundary) ∧
    (recordActions step capture capacity compatible after (Prefix.initial suffixEvents.length)
      mid).1.items = suffixEvents := by
  intro origin prefixEvents mid suffixEvents boundary
  have splitEq := pathOccurrences_append step capture capacity compatible before after origin
  have prefixPacked := protocol_from_initial step capture capacity compatible producer context
    limit before
  have fullPacked := protocol_from_initial step capture capacity compatible producer context limit
    (before ++ after)
  have prefixSync : ProtocolSync prefixEvents mid := prefixPacked.1
  have prefixOrdered : CausalReceipt.Ordered [] prefixEvents := prefixPacked.2.1
  have fullOrdered : CausalReceipt.Ordered [] (prefixEvents ++ suffixEvents) := by
    rw [← splitEq]
    exact fullPacked.2.1
  have fullSync : ProtocolSync (prefixEvents ++ suffixEvents)
      (runActions step capture capacity compatible (before ++ after) origin) := by
    rw [← splitEq]
    exact fullPacked.1
  have boundaryNodup : boundary.Nodup := by
    simpa [boundary] using
      CausalReceipt.ordered_distinct [] prefixEvents List.nodup_nil prefixOrdered
  have suffixOrdered : CausalReceipt.Ordered boundary suffixEvents :=
    ((CausalReceipt.ordered_append [] prefixEvents suffixEvents).mp fullOrdered).2
  refine ⟨splitEq, ?_, rfl, ?_, ?_, ?_⟩
  · refine ⟨boundaryNodup, suffixOrdered, ?_⟩
    intro root member
    rw [CausalReceipt.known, CausalReceipt.flattenedSupport, protocolReceipt]
    exact List.mem_append_right _ (admissionIdentity_in_support suffixEvents member)
  · intro event inPrefix inSuffix
    have nodupIds := CausalReceipt.ordered_distinct [] (prefixEvents ++ suffixEvents)
      List.nodup_nil fullOrdered
    simp only [List.nil_append, List.map_append] at nodupIds
    exact absurd rfl ((List.nodup_append.mp nodupIds).2.2 event.event
      (List.mem_map_of_mem (f := CausalEvent.event) inPrefix) event.event
      (List.mem_map_of_mem (f := CausalEvent.event) inSuffix))
  · intro event inSuffix position identity
    have inFull : event ∈ prefixEvents ++ suffixEvents := List.mem_append_right _ inSuffix
    have causes := fullSync.shape event inFull
    rw [identity] at causes
    refine ⟨causes, ?_, ?_⟩
    · have admSplit : admittedPositions prefixEvents ++ admittedPositions suffixEvents =
          List.range (runActions step capture capacity compatible (before ++ after)
            origin).delivery.log.rows.length := by
        rw [← admittedPositions_append]
        exact fullSync.admissions
      rw [prefixSync.admissions] at admSplit
      have posMem : position ∈ admittedPositions suffixEvents :=
        (admission_in_support_iff suffixEvents position).mp
          (by rw [← identity]; exact List.mem_map_of_mem (f := CausalEvent.event) inSuffix)
      have nodupRange : (List.range (runActions step capture capacity compatible
          (before ++ after) origin).delivery.log.rows.length).Nodup :=
        List.nodup_range
      rw [← admSplit] at nodupRange
      have notEarlier : position ∉ List.range mid.delivery.log.rows.length := by
        intro inRange
        exact (List.nodup_append.mp nodupRange).2.2 position inRange position posMem rfl
      have inFinal : position ∈ List.range (runActions step capture capacity compatible
          (before ++ after) origin).delivery.log.rows.length := by
        rw [← admSplit]
        exact List.mem_append_right _ posMem
      have ltFinal := List.mem_range.mp inFinal
      have notLt : ¬ position < mid.delivery.log.rows.length := by
        intro lt
        exact notEarlier (List.mem_range.mpr lt)
      omega
    · intro inBoundary
      have earlier : position ∈ admittedPositions prefixEvents :=
        (admission_in_support_iff prefixEvents position).mp (by
          simpa [boundary] using inBoundary)
      rw [prefixSync.admissions, List.mem_range] at earlier
      have lower : mid.delivery.log.rows.length ≤ position := by
        have posMem : position ∈ admittedPositions suffixEvents :=
          (admission_in_support_iff suffixEvents position).mp
            (by rw [← identity]; exact List.mem_map_of_mem (f := CausalEvent.event) inSuffix)
        have admSplit : List.range mid.delivery.log.rows.length ++ admittedPositions suffixEvents =
            List.range (runActions step capture capacity compatible (before ++ after)
              origin).delivery.log.rows.length := by
          rw [← prefixSync.admissions, ← admittedPositions_append]
          exact fullSync.admissions
        have nodupRange : (List.range (runActions step capture capacity compatible
            (before ++ after) origin).delivery.log.rows.length).Nodup :=
          List.nodup_range
        rw [← admSplit] at nodupRange
        have notEarlier : position ∉ List.range mid.delivery.log.rows.length := by
          intro inRange
          exact (List.nodup_append.mp nodupRange).2.2 position inRange position posMem rfl
        have notLt : ¬ position < mid.delivery.log.rows.length := by
          intro lt
          exact notEarlier (List.mem_range.mpr lt)
        omega
      omega
  · have bounds := record_prefix_bounds step capture capacity compatible after
      (Prefix.initial suffixEvents.length) mid
    have items := bounds.1
    dsimp only [Prefix.initial, Prefix.items] at items
    rw [List.reverse_nil, List.nil_append, List.take_length] at items
    exact items

omit [DecidableEq Stored] [DecidableEq Output] in
/-- Both consumers can hold the same position. The projection keeps two delivery
identities; `duplicate_payload_stays_two_deliveries` is that identity. -/
theorem synced_equal_payloads_stay_distinct (events : List Occurrence) (state : Cfg)
    (synced : ProtocolSync events state) (client other : Fin clients) (position : Nat)
    (stored : Stored) (distinct : other ≠ client) (leftCursor rightCursor : Nat)
    (left : state.delivery.log.positions client = some leftCursor)
    (right : state.delivery.log.positions other = some rightCursor)
    (leftPast : position < leftCursor) (rightPast : position < rightCursor) :
    deliveryCausal client position ∈ events ∧
      deliveryCausal other position ∈ events ∧
      deliveryCausal client position ≠ deliveryCausal other position := by
  have clientMem : position ∈ deliveredPositions events client := by
    rw [synced.deliveries client leftCursor left, List.mem_range]
    exact leftPast
  have otherMem : position ∈ deliveredPositions events other := by
    rw [synced.deliveries other rightCursor right, List.mem_range]
    exact rightPast
  have clientEvent : deliveryCausal client position ∈ events := by
    obtain ⟨event, member, identity⟩ := List.mem_map.mp
      ((delivery_in_support_iff events client position).mpr clientMem)
    have causes := synced.shape event member
    cases event with
    | mk id causeList =>
        cases id with
        | admission _ => cases identity
        | delivery found pos =>
            cases identity
            simp at causes
            subst causes
            simpa [deliveryCausal] using member
  have otherEvent : deliveryCausal other position ∈ events := by
    obtain ⟨event, member, identity⟩ := List.mem_map.mp
      ((delivery_in_support_iff events other position).mpr otherMem)
    have causes := synced.shape event member
    cases event with
    | mk id causeList =>
        cases id with
        | admission _ => cases identity
        | delivery found pos =>
            cases identity
            simp at causes
            subst causes
            simpa [deliveryCausal] using member
  exact ⟨clientEvent, otherEvent, (duplicate_payload_stays_two_deliveries client other position
    stored distinct).2.2⟩

omit [DecidableEq Stored] [DecidableEq Output] in
/-- Cancellation is outside `Action`. It drops one cursor and leaves the
projection, the other cursors, and the accumulated order in place. -/
theorem protocolSync_retire (events : List Occurrence) (state : Cfg)
    (synced : ProtocolSync events state)
    (ordered : CausalReceipt.Ordered ([] : List (HistoryOccurrence clients)) events)
    (client : Fin clients) :
    ProtocolSync events (retireConsumer state client) ∧
      CausalReceipt.Ordered ([] : List (HistoryOccurrence clients)) events := by
  have logEq : (retireConsumer state client).delivery.log =
      SharedOccurrenceLog.cancel state.delivery.log client := by
    simp [retireConsumer, SharedOccurrenceOwnership.cancelConsumer]
  refine ⟨⟨?_, ?_, ?_, ?_, synced.shape⟩, ordered⟩
  · rw [logEq]
    exact SharedOccurrenceLog.cancel_valid state.delivery.log client synced.valid
  · rw [logEq]
    exact synced.anchored
  · rw [logEq]
    exact synced.admissions
  · intro other cursor present
    rw [logEq] at present
    by_cases same : other = client
    · subst other
      rw [SharedOccurrenceLog.cancel, SharedOccurrenceLog.setPosition_self] at present
      cases present
    · rw [SharedOccurrenceLog.cancel, SharedOccurrenceLog.setPosition_other
        state.delivery.log client other none same] at present
      exact synced.deliveries other cursor present

/-- Retiring one consumer leaves another consumer's answer and the paid
execution. The retired consumer's next delivery is not an event
(`cancellation_is_not_a_delivery`). -/
theorem retire_keeps_other_delivery_and_paid_work (state : Cfg) (retired other : Fin clients)
    (output : Output) (position : Nat) (value : Stored) (distinct : other ≠ retired)
    (ready : compatible state.context = true)
    (waiting : SharedOccurrenceLog.peek state.delivery.log other = .answer position value) :
    deliveryUse? other (deliver compatible (retireConsumer state retired) other output).1 =
        some (deliveryCausal other position) ∧
      (deliver compatible (retireConsumer state retired) other output).2.execution =
        state.execution ∧
      acceptedCount (deliver compatible (retireConsumer state retired) other output).2 =
        acceptedCount state ∧
      deliveryUse? retired (deliver compatible (retireConsumer state retired) retired output).1 =
        none := by
  have resumed := retireConsumer_resumes_other compatible state retired other output distinct ready
  have observed := deliver_observes_answer compatible state other output position value ready waiting
  refine ⟨?_, ?_, ?_, (cancellation_is_not_a_delivery compatible state retired output ready).2.1⟩
  · have replyEq : (deliver compatible (retireConsumer state retired) other output).1 =
        (deliver compatible state other output).1 := by
      rw [resumed]
    rw [replyEq, observed.2.1]
  · exact retireConsumer_resume_does_not_step_producer compatible state retired other output
  · unfold acceptedCount
    rw [retireConsumer_resume_does_not_step_producer compatible state retired other output]


/-! ### Pause before the next explicit action

`pauseOnGate` is the one runner. It is a client of `enterActionObservers` for
one supplied action list. Each permitted action is one observer call. A
recorded schedule keeps the bounded `Prefix` and account returned by that call
and does not allocate a second prefix. The source policy is `fuelBeforeGate`:
fuel `0` on a nonempty schedule is exhaustion, and the gate is not read. An
empty remainder is completion. After fuel is available, `operationGate` reads
current authorization and only then the pure stop test. Authorization denial
is `ActionStop.refused`. A stop request is `ActionStop.breakpoint`. Neither
answer runs the action or changes the account. `pauseBefore` is that runner
with authorization constantly granted, so the checked Boolean client keeps
fuel-before-guard behavior. A policy that tests authorization before fuel is
a different definition and needs its own law. Native micro-transitions are
not this fuel.

`GuardInspection` is the source image of a checked or partial guard:
`matched`, `refuted`, or `incomplete`. Those names follow the native
`CettaMatchCompletion` outcomes and do not parse C or count a native budget.
`inspectionGate` reads authorization first. Its inspected pair is an
arbitrary state and proposal. The producer schedule instantiates that pair
as `Cfg` and `Action`; the decision does not execute the producer.
`matched` is a breakpoint. `refuted` is a proved false guard and permits the
action. `incomplete` retains the proposal, leaves the account unchanged, and
is neither a breakpoint, a refusal, fuel exhaustion, nor a refutation.
`operationGate` is `inspectionGate` on `booleanInspection`, so the Boolean
helper has no second runner. Replacing an incomplete decision resumes at the
retained suffix.

The result retains the configuration, the current history and account, the
consumed count, and the exact unexecuted suffix. `consumed` is a control
index. Theorem statements recover the executed word as `actions.take consumed`.
Unrecorded mode stores `history = none` and does not retain that word.
Resumption of a permitted suffix runs it once through the same observer. The
resulting equality is internal to this functional source model. It is not
native exclusive-execution authority, and copying the source record is not a
theorem that a one-shot native effect cannot run twice. A supplied
authorization predicate does not prove native rights, and this client adds no
permission framework.

`ActionStop` records only the control choice. A pending effect or handoff is
the execution mode. `execution.pending` is a borrowed return waiting for
capture. Delivery reply `.paused` is a consumer waiting for a row. None of
those is a breakpoint or a refusal, and the gate does not turn one of them
into a get-state fault. The gate is a pure test of this schedule. It is not
an equation stepper and not a C seal. The list is the chosen schedule: this
is not schedule independence and not arbitrary higher-order analyzer coverage.
-/

omit [DecidableEq Stored] [DecidableEq Output] in
/-- Completion, fuel exhaustion, a requested breakpoint, authorization
refusal, and an incomplete guard inspection are different stops. -/
inductive ActionStop where
  | finished
  | exhausted
  | breakpoint
  | refused
  | incomplete
  deriving DecidableEq

omit [DecidableEq Stored] [DecidableEq Output] in
/-- Checked or partial guard result. `matched` and `refuted` are complete.
`incomplete` retains the proposed action. -/
inductive GuardInspection where
  | matched
  | refuted
  | incomplete
  deriving DecidableEq

omit [DecidableEq Stored] [DecidableEq Output] in
/-- Total Boolean guard on a state and a proposal. `true` is `matched` and
`false` is `refuted`. The producer schedule uses `Cfg` and `Action`. -/
def booleanInspection {State Proposal : Type} (breakOn : State → Proposal → Bool)
    (state : State) (proposal : Proposal) : GuardInspection :=
  match breakOn state proposal with
  | true => .matched
  | false => .refuted

omit [DecidableEq Stored] [DecidableEq Output] in
/-- Decision for one proposal after `fuelBeforeGate` has supplied fuel.
`permit` runs the producer action once when the proposal is that action.
`refuse` is current authorization denial. `stopBefore` is a requested
breakpoint. `incomplete` retains the proposal. A source predicate is not
native authority. -/
inductive OperationGate where
  | permit
  | refuse
  | stopBefore
  | incomplete
  deriving DecidableEq

omit [DecidableEq Stored] [DecidableEq Output] in
/-- Authorization is the first match on a state and a proposal. Only an
authorized proposal reads `inspect`. `incomplete` does not become a
breakpoint or a permit. The producer schedule instantiates the pair as
`Cfg` and `Action`. -/
def inspectionGate {State Proposal : Type} (authorized : State → Proposal → Bool)
    (inspect : State → Proposal → GuardInspection)
    (state : State) (proposal : Proposal) : OperationGate :=
  match authorized state proposal with
  | false => .refuse
  | true =>
      match inspect state proposal with
      | .matched => .stopBefore
      | .refuted => .permit
      | .incomplete => .incomplete

omit [DecidableEq Stored] [DecidableEq Output] in
/-- Boolean helper. It is `inspectionGate` on `booleanInspection`, so a
Boolean guard has no incomplete answer and no second runner. -/
def operationGate {State Proposal : Type} (authorized breakOn : State → Proposal → Bool)
    (state : State) (proposal : Proposal) : OperationGate :=
  inspectionGate authorized (booleanInspection breakOn) state proposal

omit [DecidableEq Stored] [DecidableEq Output] in
theorem operationGate_eq_checked_inspection
    (authorized breakOn : Cfg → Action Output clients → Bool)
    (state : Cfg) (action : Action Output clients) :
    operationGate authorized breakOn state action =
      inspectionGate authorized (booleanInspection breakOn) state action := rfl

omit [DecidableEq Stored] [DecidableEq Output] in
theorem operationGate_refuse (authorized breakOn : Cfg → Action Output clients → Bool)
    (state : Cfg) (action : Action Output clients) (denied : authorized state action = false) :
    operationGate authorized breakOn state action = .refuse := by
  unfold operationGate inspectionGate
  rw [denied]

omit [DecidableEq Stored] [DecidableEq Output] in
theorem operationGate_stop (authorized breakOn : Cfg → Action Output clients → Bool)
    (state : Cfg) (action : Action Output clients) (allowed : authorized state action = true)
    (hit : breakOn state action = true) :
    operationGate authorized breakOn state action = .stopBefore := by
  unfold operationGate inspectionGate booleanInspection
  rw [allowed, hit]

omit [DecidableEq Stored] [DecidableEq Output] in
theorem operationGate_permit (authorized breakOn : Cfg → Action Output clients → Bool)
    (state : Cfg) (action : Action Output clients) (allowed : authorized state action = true)
    (pass : breakOn state action = false) :
    operationGate authorized breakOn state action = .permit := by
  unfold operationGate inspectionGate booleanInspection
  rw [allowed, pass]

omit [DecidableEq Stored] [DecidableEq Output] in
/-- Retained source state, control index, and exact unexecuted suffix.
`consumed` counts actions passed to `enterActionObservers`. It is not a copy
of those actions. `history` is the existing bounded prefix, or `none`. -/
structure ObservedPause (Producer Borrowed Stored Context Output Effect Handoff : Type)
    (clients : Nat) where
  stop : ActionStop
  consumed : Nat
  suffix : List (Action Output clients)
  history : Option (Prefix (CausalEvent (HistoryOccurrence clients)))
  account : Option ProtocolAccount
  state : Configuration Producer Borrowed Stored Context Output Effect Handoff clients

/-- Run the supplied schedule until fuel runs out, the gate refuses or stops,
or the list is consumed. Fuel `0` is tested before `decide`. A refusal or a
breakpoint does not call `enterActionObservers`. -/
def pauseOnGate (history : Option (Prefix Occurrence)) (account : Option ProtocolAccount)
    (fuel : Nat) (decide : Cfg → Action Output clients → OperationGate)
    (actions : List (Action Output clients)) (state : Cfg) :
    ObservedPause Producer Borrowed Stored Context Output Effect Handoff clients :=
  match actions with
  | [] =>
      { stop := .finished, consumed := 0, suffix := [], history, account, state }
  | action :: rest =>
      match fuel with
      | 0 =>
          { stop := .exhausted, consumed := 0, suffix := action :: rest, history, account, state }
      | fuel + 1 =>
          match decide state action with
          | .refuse =>
              { stop := .refused, consumed := 0, suffix := action :: rest, history, account, state }
          | .stopBefore =>
              { stop := .breakpoint, consumed := 0, suffix := action :: rest, history, account,
                state }
          | .incomplete =>
              { stop := .incomplete, consumed := 0, suffix := action :: rest, history, account,
                state }
          | .permit =>
              let stepped := enterActionObservers step capture capacity compatible history account
                [action] state
              let later := pauseOnGate stepped.1 stepped.2.1 fuel decide rest stepped.2.2
              { later with consumed := later.consumed + 1 }

/-- Source policy `fuelBeforeGate`. The gate is not an argument of the result.
A policy that tests authorization before fuel is a different definition. -/
theorem fuelBeforeGate (history : Option (Prefix Occurrence)) (account : Option ProtocolAccount)
    (decide : Cfg → Action Output clients → OperationGate) (action : Action Output clients)
    (rest : List (Action Output clients)) (state : Cfg) :
    pauseOnGate step capture capacity compatible history account 0 decide (action :: rest) state =
      { stop := .exhausted, consumed := 0, suffix := action :: rest, history, account, state } := by
  conv_lhs => unfold pauseOnGate

theorem pauseOnGate_nil (history : Option (Prefix Occurrence)) (account : Option ProtocolAccount)
    (fuel : Nat) (decide : Cfg → Action Output clients → OperationGate) (state : Cfg) :
    pauseOnGate step capture capacity compatible history account fuel decide [] state =
      { stop := .finished, consumed := 0, suffix := [], history, account, state } := by
  conv_lhs => unfold pauseOnGate

theorem pauseOnGate_exhausted_step (history : Option (Prefix Occurrence))
    (account : Option ProtocolAccount) (decide : Cfg → Action Output clients → OperationGate)
    (action : Action Output clients) (rest : List (Action Output clients)) (state : Cfg) :
    pauseOnGate step capture capacity compatible history account 0 decide (action :: rest) state =
      { stop := .exhausted, consumed := 0, suffix := action :: rest, history, account, state } :=
  fuelBeforeGate step capture capacity compatible history account decide action rest state

theorem pauseOnGate_incomplete_step (history : Option (Prefix Occurrence))
    (account : Option ProtocolAccount) (fuel : Nat)
    (decide : Cfg → Action Output clients → OperationGate) (action : Action Output clients)
    (rest : List (Action Output clients)) (state : Cfg)
    (pending : decide state action = .incomplete) :
    pauseOnGate step capture capacity compatible history account (fuel + 1) decide
        (action :: rest) state =
      { stop := .incomplete, consumed := 0, suffix := action :: rest, history, account, state } := by
  conv_lhs => unfold pauseOnGate
  rw [pending]

theorem pauseOnGate_refuse_step (history : Option (Prefix Occurrence))
    (account : Option ProtocolAccount) (fuel : Nat)
    (decide : Cfg → Action Output clients → OperationGate) (action : Action Output clients)
    (rest : List (Action Output clients)) (state : Cfg)
    (denied : decide state action = .refuse) :
    pauseOnGate step capture capacity compatible history account (fuel + 1) decide
        (action :: rest) state =
      { stop := .refused, consumed := 0, suffix := action :: rest, history, account, state } := by
  conv_lhs => unfold pauseOnGate
  rw [denied]

theorem pauseOnGate_breakpoint_step (history : Option (Prefix Occurrence))
    (account : Option ProtocolAccount) (fuel : Nat)
    (decide : Cfg → Action Output clients → OperationGate) (action : Action Output clients)
    (rest : List (Action Output clients)) (state : Cfg)
    (hit : decide state action = .stopBefore) :
    pauseOnGate step capture capacity compatible history account (fuel + 1) decide
        (action :: rest) state =
      { stop := .breakpoint, consumed := 0, suffix := action :: rest, history, account, state } := by
  conv_lhs => unfold pauseOnGate
  rw [hit]

theorem pauseOnGate_continue (history : Option (Prefix Occurrence))
    (account : Option ProtocolAccount) (fuel : Nat)
    (decide : Cfg → Action Output clients → OperationGate) (action : Action Output clients)
    (rest : List (Action Output clients)) (state : Cfg)
    (pass : decide state action = .permit) :
    pauseOnGate step capture capacity compatible history account (fuel + 1) decide
        (action :: rest) state =
      let stepped := enterActionObservers step capture capacity compatible history account
        [action] state
      let later := pauseOnGate step capture capacity compatible stepped.1 stepped.2.1 fuel decide
        rest stepped.2.2
      { later with consumed := later.consumed + 1 } := by
  conv_lhs => unfold pauseOnGate
  rw [pass]

/-- Boolean client. Authorization is constantly granted, then `breakOn` is the
stop test. The runner is `pauseOnGate`; this definition does not recurse. -/
def pauseBefore (history : Option (Prefix Occurrence)) (account : Option ProtocolAccount)
    (fuel : Nat) (breakOn : Cfg → Action Output clients → Bool)
    (actions : List (Action Output clients)) (state : Cfg) :
    ObservedPause Producer Borrowed Stored Context Output Effect Handoff clients :=
  pauseOnGate step capture capacity compatible history account fuel
    (operationGate (fun _ _ => true) breakOn) actions state

theorem pauseBefore_eq_pauseOnGate (history : Option (Prefix Occurrence))
    (account : Option ProtocolAccount) (fuel : Nat) (breakOn : Cfg → Action Output clients → Bool)
    (actions : List (Action Output clients)) (state : Cfg) :
    pauseBefore step capture capacity compatible history account fuel breakOn actions state =
      pauseOnGate step capture capacity compatible history account fuel
        (operationGate (fun _ _ => true) breakOn) actions state := rfl

theorem pauseBefore_nil (history : Option (Prefix Occurrence)) (account : Option ProtocolAccount)
    (fuel : Nat) (breakOn : Cfg → Action Output clients → Bool) (state : Cfg) :
    pauseBefore step capture capacity compatible history account fuel breakOn [] state =
      { stop := .finished, consumed := 0, suffix := [], history, account, state } :=
  pauseOnGate_nil step capture capacity compatible history account fuel
    (operationGate (fun _ _ => true) breakOn) state

/-- Fuel exhaustion does not read the guard and does not run the action.
This is `fuelBeforeGate` for the Boolean client. -/
theorem pauseBefore_exhausted_step (history : Option (Prefix Occurrence))
    (account : Option ProtocolAccount) (breakOn : Cfg → Action Output clients → Bool)
    (action : Action Output clients) (rest : List (Action Output clients)) (state : Cfg) :
    pauseBefore step capture capacity compatible history account 0 breakOn (action :: rest) state =
      { stop := .exhausted, consumed := 0, suffix := action :: rest, history, account, state } :=
  fuelBeforeGate step capture capacity compatible history account
    (operationGate (fun _ _ => true) breakOn) action rest state

theorem pauseBefore_breakpoint_step (history : Option (Prefix Occurrence))
    (account : Option ProtocolAccount) (fuel : Nat) (breakOn : Cfg → Action Output clients → Bool)
    (action : Action Output clients) (rest : List (Action Output clients)) (state : Cfg)
    (hit : breakOn state action = true) :
    pauseBefore step capture capacity compatible history account (fuel + 1) breakOn
        (action :: rest) state =
      { stop := .breakpoint, consumed := 0, suffix := action :: rest, history, account, state } :=
  pauseOnGate_breakpoint_step step capture capacity compatible history account fuel
    (operationGate (fun _ _ => true) breakOn) action rest state
    (operationGate_stop (fun _ _ => true) breakOn state action rfl hit)

theorem pauseBefore_continue (history : Option (Prefix Occurrence))
    (account : Option ProtocolAccount) (fuel : Nat) (breakOn : Cfg → Action Output clients → Bool)
    (action : Action Output clients) (rest : List (Action Output clients)) (state : Cfg)
    (pass : breakOn state action = false) :
    pauseBefore step capture capacity compatible history account (fuel + 1) breakOn
        (action :: rest) state =
      let stepped := enterActionObservers step capture capacity compatible history account
        [action] state
      let later := pauseBefore step capture capacity compatible stepped.1 stepped.2.1 fuel
        breakOn rest stepped.2.2
      { later with consumed := later.consumed + 1 } :=
  pauseOnGate_continue step capture capacity compatible history account fuel
    (operationGate (fun _ _ => true) breakOn) action rest state
    (operationGate_permit (fun _ _ => true) breakOn state action rfl pass)

theorem enterActionObservers_nil (history : Option (Prefix Occurrence))
    (account : Option ProtocolAccount) (state : Cfg) :
    enterActionObservers step capture capacity compatible history account [] state =
      (history, account, state) := by
  cases history <;> cases account <;> rfl

/-- The executed prefix determines the retained history, account, and
configuration. The cut keeps the unexecuted suffix in its original order. -/
private theorem pauseOnGate_cut (history : Option (Prefix Occurrence))
    (account : Option ProtocolAccount) (fuel : Nat)
    (decide : Cfg → Action Output clients → OperationGate)
    (actions : List (Action Output clients)) (state : Cfg) :
    let paused := pauseOnGate step capture capacity compatible history account fuel decide actions state
    paused.suffix = actions.drop paused.consumed ∧
      actions.take paused.consumed ++ paused.suffix = actions ∧
      (paused.history, paused.account, paused.state) =
        enterActionObservers step capture capacity compatible history account
          (actions.take paused.consumed) state := by
  dsimp only
  induction actions generalizing fuel history account state with
  | nil =>
      simp only [pauseOnGate_nil, List.drop_zero, List.take_zero, List.nil_append,
        enterActionObservers_nil, and_self]
  | cons action rest ih =>
      cases fuel with
      | zero =>
          simp only [pauseOnGate_exhausted_step, List.drop_zero, List.take_zero, List.nil_append,
            enterActionObservers_nil, and_self]
      | succ fuel =>
          cases gate : decide state action with
          | refuse =>
              rw [pauseOnGate_refuse_step step capture capacity compatible history account fuel
                decide action rest state gate]
              simp only [List.drop_zero, List.take_zero, List.nil_append, enterActionObservers_nil, and_self]
          | stopBefore =>
              rw [pauseOnGate_breakpoint_step step capture capacity compatible history account fuel
                decide action rest state gate]
              simp only [List.drop_zero, List.take_zero, List.nil_append, enterActionObservers_nil, and_self]
          | incomplete =>
              rw [pauseOnGate_incomplete_step step capture capacity compatible history account fuel
                decide action rest state gate]
              simp only [List.drop_zero, List.take_zero, List.nil_append, enterActionObservers_nil, and_self]
          | permit =>
              rw [pauseOnGate_continue step capture capacity compatible history account fuel
                decide action rest state gate]
              let next := enterActionObservers step capture capacity compatible history account [action] state
              have tail := ih next.1 next.2.1 fuel next.2.2
              rw [List.drop_succ_cons, List.take_succ_cons, List.cons_append]
              refine ⟨tail.1, congrArg (List.cons action) tail.2.1, ?_⟩
              rw [tail.2.2]
              simpa only [List.singleton_append] using
                (enterActionObservers_append step capture capacity compatible history account [action]
                  (rest.take (pauseOnGate step capture capacity compatible next.1 next.2.1
                    fuel decide rest next.2.2).consumed) state).symm

theorem pauseOnGate_split (history : Option (Prefix Occurrence)) (account : Option ProtocolAccount)
    (fuel : Nat) (decide : Cfg → Action Output clients → OperationGate)
    (actions : List (Action Output clients)) (state : Cfg) :
    (pauseOnGate step capture capacity compatible history account fuel decide actions state).suffix =
        actions.drop
          (pauseOnGate step capture capacity compatible history account fuel decide actions
            state).consumed ∧
      actions.take
          (pauseOnGate step capture capacity compatible history account fuel decide actions
            state).consumed ++
        (pauseOnGate step capture capacity compatible history account fuel decide actions
          state).suffix =
        actions :=
  let cut := pauseOnGate_cut step capture capacity compatible history account fuel decide actions state
  ⟨cut.1, cut.2.1⟩

/-- History, account, and state are one observation of `actions.take consumed`.
A refused or stopped action is not part of that observation. -/
theorem pauseOnGate_observers (history : Option (Prefix Occurrence))
    (account : Option ProtocolAccount) (fuel : Nat)
    (decide : Cfg → Action Output clients → OperationGate)
    (actions : List (Action Output clients)) (state : Cfg) :
    ((pauseOnGate step capture capacity compatible history account fuel decide actions state).history,
        (pauseOnGate step capture capacity compatible history account fuel decide actions
          state).account,
        (pauseOnGate step capture capacity compatible history account fuel decide actions
          state).state) =
      enterActionObservers step capture capacity compatible history account
        (actions.take
          (pauseOnGate step capture capacity compatible history account fuel decide actions
            state).consumed)
        state :=
  (pauseOnGate_cut step capture capacity compatible history account fuel decide actions state).2.2

theorem pauseOnGate_erases (history : Option (Prefix Occurrence))
    (account : Option ProtocolAccount) (fuel : Nat)
    (decide : Cfg → Action Output clients → OperationGate)
    (actions : List (Action Output clients)) (state : Cfg) :
    (pauseOnGate step capture capacity compatible history account fuel decide actions state).state =
      runActions step capture capacity compatible
        (actions.take
          (pauseOnGate step capture capacity compatible history account fuel decide actions
            state).consumed)
        state := by
  have observed := pauseOnGate_observers step capture capacity compatible history account fuel
    decide actions state
  exact (congrArg (fun triple => triple.2.2) observed).trans
    (enterActionObservers_erases step capture capacity compatible history account
      (actions.take
        (pauseOnGate step capture capacity compatible history account fuel decide actions
          state).consumed)
      state)

theorem pauseOnGate_unexecuted_keeps_account (history : Option (Prefix Occurrence))
    (account : Option ProtocolAccount) (fuel : Nat)
    (decide : Cfg → Action Output clients → OperationGate)
    (actions : List (Action Output clients)) (state : Cfg) :
    (pauseOnGate step capture capacity compatible history account fuel decide actions state).account =
        (enterActionObservers step capture capacity compatible history account
          (actions.take
            (pauseOnGate step capture capacity compatible history account fuel decide actions
              state).consumed)
          state).2.1 ∧
      (pauseOnGate step capture capacity compatible history account fuel decide actions state).state =
        (enterActionObservers step capture capacity compatible history account
          (actions.take
            (pauseOnGate step capture capacity compatible history account fuel decide actions
              state).consumed)
          state).2.2 := by
  have observed := pauseOnGate_observers step capture capacity compatible history account fuel
    decide actions state
  exact ⟨congrArg (fun triple => triple.2.1) observed,
    congrArg (fun triple => triple.2.2) observed⟩

/-- Unrecorded mode retains no history. Refusal does not allocate an action list. -/
theorem pauseOnGate_unrecorded (fuel : Nat) (decide : Cfg → Action Output clients → OperationGate)
    (actions : List (Action Output clients)) (state : Cfg) :
    (pauseOnGate step capture capacity compatible none none fuel decide actions state).history =
      none := by
  have observed := pauseOnGate_observers step capture capacity compatible none none fuel decide
    actions state
  exact (congrArg (fun triple => triple.1) observed).trans
    (congrArg Prod.fst (enterActionObservers_neither step capture capacity compatible
      (actions.take
        (pauseOnGate step capture capacity compatible none none fuel decide actions state).consumed)
      state))

theorem pauseOnGate_disabled (history : Option (Prefix Occurrence))
    (account : Option ProtocolAccount) (actions : List (Action Output clients)) (state : Cfg) :
    (pauseOnGate step capture capacity compatible history account actions.length
        (operationGate (fun _ _ => true) (fun _ _ => false)) actions state).stop =
      ActionStop.finished ∧
      (pauseOnGate step capture capacity compatible history account actions.length
        (operationGate (fun _ _ => true) (fun _ _ => false)) actions state).suffix = [] ∧
      (pauseOnGate step capture capacity compatible history account actions.length
        (operationGate (fun _ _ => true) (fun _ _ => false)) actions state).consumed =
        actions.length ∧
      ((pauseOnGate step capture capacity compatible history account actions.length
          (operationGate (fun _ _ => true) (fun _ _ => false)) actions state).history,
        (pauseOnGate step capture capacity compatible history account actions.length
          (operationGate (fun _ _ => true) (fun _ _ => false)) actions state).account,
        (pauseOnGate step capture capacity compatible history account actions.length
          (operationGate (fun _ _ => true) (fun _ _ => false)) actions state).state) =
        enterActionObservers step capture capacity compatible history account actions state := by
  induction actions generalizing history account state with
  | nil =>
      rw [pauseOnGate_nil, enterActionObservers_nil]
      exact ⟨rfl, rfl, rfl, rfl⟩
  | cons action rest ih =>
      have pass : operationGate (fun _ _ => true) (fun _ _ => false) state action =
          OperationGate.permit :=
        operationGate_permit (fun _ _ => true) (fun _ _ => false) state action rfl rfl
      rw [List.length_cons]
      rw [pauseOnGate_continue step capture capacity compatible history account rest.length
        (operationGate (fun _ _ => true) (fun _ _ => false)) action rest state pass]
      have tail := ih
        (enterActionObservers step capture capacity compatible history account [action] state).1
        (enterActionObservers step capture capacity compatible history account [action] state).2.1
        (enterActionObservers step capture capacity compatible history account [action] state).2.2
      refine ⟨tail.1, tail.2.1, ?_, ?_⟩
      · exact congrArg (fun n => n + 1) tail.2.2.1
      · rw [tail.2.2.2]
        rw [← enterActionObservers_append step capture capacity compatible history account [action]
          rest state]
        rfl

/-- Resuming a permitted suffix with the stop test disabled runs that suffix
once. The joined observers equal one uninterrupted schedule of the actions
that were actually supplied. This equality is not native exclusive-execution
authority. -/
theorem pauseOnGate_resume_permitted (history : Option (Prefix Occurrence))
    (account : Option ProtocolAccount) (fuel : Nat)
    (decide : Cfg → Action Output clients → OperationGate)
    (actions : List (Action Output clients)) (state : Cfg) :
    let paused := pauseOnGate step capture capacity compatible history account fuel decide
      actions state
    let resumed := pauseOnGate step capture capacity compatible paused.history paused.account
      paused.suffix.length (operationGate (fun _ _ => true) (fun _ _ => false)) paused.suffix
      paused.state
    resumed.stop = ActionStop.finished ∧ resumed.suffix = [] ∧
      resumed.consumed = paused.suffix.length ∧
      (resumed.history, resumed.account, resumed.state) =
        enterActionObservers step capture capacity compatible history account actions state ∧
      resumed.state = runActions step capture capacity compatible actions state := by
  intro paused resumed
  have finished := pauseOnGate_disabled step capture capacity compatible paused.history
    paused.account paused.suffix paused.state
  have cut := pauseOnGate_cut step capture capacity compatible history account fuel decide actions state
  let taken := actions.take paused.consumed
  have observers : (paused.history, paused.account, paused.state) =
      enterActionObservers step capture capacity compatible history account taken state := cut.2.2
  have full : taken ++ paused.suffix = actions := cut.2.1
  have joined : (resumed.history, resumed.account, resumed.state) =
      enterActionObservers step capture capacity compatible history account actions state := by
    calc
      _ = enterActionObservers step capture capacity compatible paused.history paused.account
          paused.suffix paused.state := finished.2.2.2
      _ = (let earlier := enterActionObservers step capture capacity compatible history account taken state
          enterActionObservers step capture capacity compatible earlier.1 earlier.2.1
            paused.suffix earlier.2.2) := congrArg (fun earlier =>
              enterActionObservers step capture capacity compatible earlier.1 earlier.2.1
                paused.suffix earlier.2.2) observers
      _ = enterActionObservers step capture capacity compatible history account
          (taken ++ paused.suffix) state :=
        (enterActionObservers_append step capture capacity compatible history account
          taken paused.suffix state).symm
      _ = _ := by rw [full]
  exact ⟨finished.1, finished.2.1, finished.2.2.1, joined,
    (congrArg (fun triple => triple.2.2) joined).trans
      (enterActionObservers_erases step capture capacity compatible history account actions state)⟩

theorem pauseBefore_split (history : Option (Prefix Occurrence)) (account : Option ProtocolAccount)
    (fuel : Nat) (breakOn : Cfg → Action Output clients → Bool)
    (actions : List (Action Output clients)) (state : Cfg) :
    (pauseBefore step capture capacity compatible history account fuel breakOn actions state).suffix =
        actions.drop
          (pauseBefore step capture capacity compatible history account fuel breakOn actions
            state).consumed ∧
      actions.take
          (pauseBefore step capture capacity compatible history account fuel breakOn actions
            state).consumed ++
        (pauseBefore step capture capacity compatible history account fuel breakOn actions
          state).suffix =
        actions :=
  pauseOnGate_split step capture capacity compatible history account fuel
    (operationGate (fun _ _ => true) breakOn) actions state

/-- History, account, and state are one observation of `actions.take consumed`.
The suffix is not an argument of that observation. -/
theorem pauseBefore_observers (history : Option (Prefix Occurrence))
    (account : Option ProtocolAccount) (fuel : Nat)
    (breakOn : Cfg → Action Output clients → Bool) (actions : List (Action Output clients))
    (state : Cfg) :
    ((pauseBefore step capture capacity compatible history account fuel breakOn actions state).history,
        (pauseBefore step capture capacity compatible history account fuel breakOn actions
          state).account,
        (pauseBefore step capture capacity compatible history account fuel breakOn actions
          state).state) =
      enterActionObservers step capture capacity compatible history account
        (actions.take
          (pauseBefore step capture capacity compatible history account fuel breakOn actions
            state).consumed)
        state :=
  pauseOnGate_observers step capture capacity compatible history account fuel
    (operationGate (fun _ _ => true) breakOn) actions state

theorem pauseBefore_erases (history : Option (Prefix Occurrence))
    (account : Option ProtocolAccount) (fuel : Nat)
    (breakOn : Cfg → Action Output clients → Bool) (actions : List (Action Output clients))
    (state : Cfg) :
    (pauseBefore step capture capacity compatible history account fuel breakOn actions state).state =
      runActions step capture capacity compatible
        (actions.take
          (pauseBefore step capture capacity compatible history account fuel breakOn actions
            state).consumed)
        state :=
  pauseOnGate_erases step capture capacity compatible history account fuel
    (operationGate (fun _ _ => true) breakOn) actions state

/-- Unrecorded mode retains no history. The consumed count is not an action trace. -/
theorem pauseBefore_unrecorded (fuel : Nat) (breakOn : Cfg → Action Output clients → Bool)
    (actions : List (Action Output clients)) (state : Cfg) :
    (pauseBefore step capture capacity compatible none none fuel breakOn actions state).history =
      none :=
  pauseOnGate_unrecorded step capture capacity compatible fuel (operationGate (fun _ _ => true) breakOn) actions state

/-- History and account options do not change the stop, the consumed index,
the suffix, or the configuration. Refusal, a breakpoint, an incomplete
inspection, and a permitted step all stay on this law. -/
theorem pauseOnGate_recording_irrelevant
    (history otherHistory : Option (Prefix Occurrence))
    (account otherAccount : Option ProtocolAccount) (fuel : Nat)
    (decide : Cfg → Action Output clients → OperationGate)
    (actions : List (Action Output clients)) (state otherState : Cfg)
    (same : state = otherState) :
    (pauseOnGate step capture capacity compatible history account fuel decide actions state).stop =
        (pauseOnGate step capture capacity compatible otherHistory otherAccount fuel decide actions
          otherState).stop ∧
      (pauseOnGate step capture capacity compatible history account fuel decide actions state).consumed =
        (pauseOnGate step capture capacity compatible otherHistory otherAccount fuel decide actions
          otherState).consumed ∧
      (pauseOnGate step capture capacity compatible history account fuel decide actions state).suffix =
        (pauseOnGate step capture capacity compatible otherHistory otherAccount fuel decide actions
          otherState).suffix ∧
      (pauseOnGate step capture capacity compatible history account fuel decide actions state).state =
        (pauseOnGate step capture capacity compatible otherHistory otherAccount fuel decide actions
          otherState).state := by
  induction actions generalizing fuel history account otherHistory otherAccount state otherState with
  | nil =>
      cases same
      rw [pauseOnGate_nil, pauseOnGate_nil]
      exact ⟨rfl, rfl, rfl, rfl⟩
  | cons action rest ih =>
      cases same
      cases fuel with
      | zero =>
          rw [pauseOnGate_exhausted_step, pauseOnGate_exhausted_step]
          exact ⟨rfl, rfl, rfl, rfl⟩
      | succ fuel =>
          cases gate : decide state action with
          | refuse =>
              rw [pauseOnGate_refuse_step step capture capacity compatible history account fuel
                  decide action rest state gate,
                pauseOnGate_refuse_step step capture capacity compatible otherHistory otherAccount
                  fuel decide action rest state gate]
              exact ⟨rfl, rfl, rfl, rfl⟩
          | stopBefore =>
              rw [pauseOnGate_breakpoint_step step capture capacity compatible history account fuel
                  decide action rest state gate,
                pauseOnGate_breakpoint_step step capture capacity compatible otherHistory
                  otherAccount fuel decide action rest state gate]
              exact ⟨rfl, rfl, rfl, rfl⟩
          | incomplete =>
              rw [pauseOnGate_incomplete_step step capture capacity compatible history account fuel
                  decide action rest state gate,
                pauseOnGate_incomplete_step step capture capacity compatible otherHistory
                  otherAccount fuel decide action rest state gate]
              exact ⟨rfl, rfl, rfl, rfl⟩
          | permit =>
              have nextSame :=
                (enterActionObservers_erases step capture capacity compatible history account
                    [action] state).trans
                  (enterActionObservers_erases step capture capacity compatible otherHistory
                    otherAccount [action] state).symm
              have continued := ih
                (enterActionObservers step capture capacity compatible history account [action]
                  state).1
                (enterActionObservers step capture capacity compatible otherHistory otherAccount
                  [action] state).1
                (enterActionObservers step capture capacity compatible history account [action]
                  state).2.1
                (enterActionObservers step capture capacity compatible otherHistory otherAccount
                  [action] state).2.1
                fuel
                (enterActionObservers step capture capacity compatible history account [action]
                  state).2.2
                (enterActionObservers step capture capacity compatible otherHistory otherAccount
                  [action] state).2.2
                nextSame
              rw [pauseOnGate_continue step capture capacity compatible history account fuel decide
                  action rest state gate,
                pauseOnGate_continue step capture capacity compatible otherHistory otherAccount fuel
                  decide action rest state gate]
              exact ⟨continued.1, congrArg (fun n => n + 1) continued.2.1, continued.2.2.1,
                continued.2.2.2⟩

/-- Boolean client of `pauseOnGate_recording_irrelevant`. `pauseBefore` is
`pauseOnGate` with authorization constantly granted. -/
theorem pauseBefore_recording_irrelevant
    (history otherHistory : Option (Prefix Occurrence))
    (account otherAccount : Option ProtocolAccount) (fuel : Nat)
    (breakOn : Cfg → Action Output clients → Bool) (actions : List (Action Output clients))
    (state otherState : Cfg) (same : state = otherState) :
    (pauseBefore step capture capacity compatible history account fuel breakOn actions state).stop =
        (pauseBefore step capture capacity compatible otherHistory otherAccount fuel breakOn actions
          otherState).stop ∧
      (pauseBefore step capture capacity compatible history account fuel breakOn actions state).consumed =
        (pauseBefore step capture capacity compatible otherHistory otherAccount fuel breakOn actions
          otherState).consumed ∧
      (pauseBefore step capture capacity compatible history account fuel breakOn actions state).suffix =
        (pauseBefore step capture capacity compatible otherHistory otherAccount fuel breakOn actions
          otherState).suffix ∧
      (pauseBefore step capture capacity compatible history account fuel breakOn actions state).state =
        (pauseBefore step capture capacity compatible otherHistory otherAccount fuel breakOn actions
          otherState).state := by
  unfold pauseBefore
  exact pauseOnGate_recording_irrelevant step capture capacity compatible history otherHistory
    account otherAccount fuel (operationGate (fun _ _ => true) breakOn) actions state otherState same

/-- An unexecuted suffix contributes neither charge nor a configuration change.
Both are the observation of `actions.take consumed`. -/
theorem pauseBefore_unexecuted_keeps_account (history : Option (Prefix Occurrence))
    (account : Option ProtocolAccount) (fuel : Nat)
    (breakOn : Cfg → Action Output clients → Bool) (actions : List (Action Output clients))
    (state : Cfg) :
    (pauseBefore step capture capacity compatible history account fuel breakOn actions state).account =
        (enterActionObservers step capture capacity compatible history account
          (actions.take
            (pauseBefore step capture capacity compatible history account fuel breakOn actions
              state).consumed)
          state).2.1 ∧
      (pauseBefore step capture capacity compatible history account fuel breakOn actions state).state =
        (enterActionObservers step capture capacity compatible history account
          (actions.take
            (pauseBefore step capture capacity compatible history account fuel breakOn actions
              state).consumed)
          state).2.2 :=
  pauseOnGate_unexecuted_keeps_account step capture capacity compatible history account fuel
    (operationGate (fun _ _ => true) breakOn) actions state

theorem pauseBefore_disabled (history : Option (Prefix Occurrence))
    (account : Option ProtocolAccount) (actions : List (Action Output clients)) (state : Cfg) :
    (pauseBefore step capture capacity compatible history account actions.length (fun _ _ => false)
        actions state).stop = ActionStop.finished ∧
      (pauseBefore step capture capacity compatible history account actions.length (fun _ _ => false)
        actions state).suffix = [] ∧
      (pauseBefore step capture capacity compatible history account actions.length (fun _ _ => false)
        actions state).consumed = actions.length ∧
      ((pauseBefore step capture capacity compatible history account actions.length (fun _ _ => false)
          actions state).history,
        (pauseBefore step capture capacity compatible history account actions.length (fun _ _ => false)
          actions state).account,
        (pauseBefore step capture capacity compatible history account actions.length (fun _ _ => false)
          actions state).state) =
        enterActionObservers step capture capacity compatible history account actions state :=
  pauseOnGate_disabled step capture capacity compatible history account actions state

/-- Resuming with the guard disabled runs the unexecuted suffix once in this
source model. The joined observers equal one uninterrupted schedule. This
equality is not native exclusive-execution authority, and copying the source
record is not a theorem that a one-shot native effect cannot run twice. -/
theorem pauseBefore_resume (history : Option (Prefix Occurrence))
    (account : Option ProtocolAccount) (fuel : Nat)
    (breakOn : Cfg → Action Output clients → Bool) (actions : List (Action Output clients))
    (state : Cfg) :
    let paused := pauseBefore step capture capacity compatible history account fuel breakOn
      actions state
    let resumed := pauseBefore step capture capacity compatible paused.history paused.account
      paused.suffix.length (fun _ _ => false) paused.suffix paused.state
    resumed.stop = ActionStop.finished ∧ resumed.suffix = [] ∧
      resumed.consumed = paused.suffix.length ∧
      (resumed.history, resumed.account, resumed.state) =
        enterActionObservers step capture capacity compatible history account actions state ∧
      resumed.state = runActions step capture capacity compatible actions state :=
  pauseOnGate_resume_permitted step capture capacity compatible history account fuel
    (operationGate (fun _ _ => true) breakOn) actions state

set_option backward.isDefEq.respectTransparency false in
/-- The occurrence word of the schedule is the word of `actions.take consumed`
followed by the word of the suffix, started at `runActions` of that prefix.
`pauseBefore_erases` identifies that state with the retained configuration. -/
theorem pauseBefore_occurrence_word (history : Option (Prefix Occurrence))
    (account : Option ProtocolAccount) (fuel : Nat)
    (breakOn : Cfg → Action Output clients → Bool) (actions : List (Action Output clients))
    (state : Cfg) :
    pathOccurrences step capture capacity compatible
        (actionPath step capture capacity compatible actions state) =
      pathOccurrences step capture capacity compatible
          (actionPath step capture capacity compatible
            (actions.take
              (pauseBefore step capture capacity compatible history account fuel breakOn actions
                state).consumed)
            state) ++
        pathOccurrences step capture capacity compatible
          (actionPath step capture capacity compatible
            (pauseBefore step capture capacity compatible history account fuel breakOn actions
              state).suffix
            (runActions step capture capacity compatible
              (actions.take
                (pauseBefore step capture capacity compatible history account fuel breakOn actions
                  state).consumed)
              state)) := by
  have split := pauseBefore_split step capture capacity compatible history account fuel breakOn
    actions state
  have appended := pathOccurrences_append step capture capacity compatible
    (actions.take
      (pauseBefore step capture capacity compatible history account fuel breakOn actions
        state).consumed)
    (pauseBefore step capture capacity compatible history account fuel breakOn actions state).suffix
    state
  rw [split.2] at appended
  exact appended

set_option backward.isDefEq.respectTransparency false in
/-- The paused index is the existing suffix boundary. Prior identities remain
the captured boundary; this theorem does not rebuild the receipt. -/
theorem pauseBefore_respects_suffix_boundary (producer : Producer) (context : Context)
    (limit : Nat) (history : Option (Prefix Occurrence)) (account : Option ProtocolAccount)
    (fuel : Nat) (breakOn : Cfg → Action Output clients → Bool)
    (actions : List (Action Output clients)) :
    let origin := initial producer context limit
    let paused := pauseBefore step capture capacity compatible history account fuel breakOn
      actions origin
    let done := actions.take paused.consumed
    paused.suffix = actions.drop paused.consumed ∧
      done ++ paused.suffix = actions ∧
      paused.state = runActions step capture capacity compatible done origin ∧
      pathOccurrences step capture capacity compatible
          (actionPath step capture capacity compatible actions origin) =
        pathOccurrences step capture capacity compatible
            (actionPath step capture capacity compatible done origin) ++
          pathOccurrences step capture capacity compatible
            (actionPath step capture capacity compatible paused.suffix
              (runActions step capture capacity compatible done origin)) ∧
      CausalReceipt.WellFormed
        ((pathOccurrences step capture capacity compatible
            (actionPath step capture capacity compatible done origin)).map
          CausalEvent.event)
        (protocolReceipt (pathOccurrences step capture capacity compatible
          (actionPath step capture capacity compatible paused.suffix
            (runActions step capture capacity compatible done origin)))) := by
  intro origin paused done
  have split := pauseBefore_split step capture capacity compatible history account fuel breakOn
    actions origin
  have erased := pauseBefore_erases step capture capacity compatible history account fuel breakOn
    actions origin
  refine ⟨split.1, split.2, erased, ?_, ?_⟩
  · have boundary := protocol_suffix_boundary step capture capacity compatible producer context
      limit done paused.suffix
    dsimp only at boundary
    have path := boundary.1
    rw [split.2] at path
    exact path
  · have boundary := protocol_suffix_boundary step capture capacity compatible producer context
      limit done paused.suffix
    dsimp only at boundary
    exact boundary.2.1

omit [DecidableEq Stored] [DecidableEq Output] in
/-- A full prefix keeps its items and its exhausted capacity. A real occurrence
increments `omitted`; an absent one does not. -/
theorem pushOccurrence_exhausted_storage (record : Prefix Occurrence)
    (occurrence : Option Occurrence) (full : record.remaining = 0) :
    (pushOccurrence record occurrence).items = record.items ∧
      (pushOccurrence record occurrence).remaining = 0 ∧
      (pushOccurrence record occurrence).reversed = record.reversed ∧
      (pushOccurrence record occurrence).omitted =
        record.omitted + match occurrence with | none => 0 | some _ => 1 := by
  cases occurrence with
  | none => simp [pushOccurrence, Prefix.items, full]
  | some _ => simp [pushOccurrence, Prefix.push, Prefix.items, full]

/-- Later actions do not refill an exhausted prefix or put its omitted
occurrences back into `items`. -/
theorem recordActions_exhausted_keeps_items (actions : List (Action Output clients))
    (record : Prefix Occurrence) (state : Cfg) (full : record.remaining = 0) :
    (recordActions step capture capacity compatible actions record state).1.items = record.items ∧
      (recordActions step capture capacity compatible actions record state).1.remaining = 0 ∧
      (recordActions step capture capacity compatible actions record state).1.reversed =
        record.reversed := by
  induction actions generalizing record state with
  | nil => simp [recordActions, full]
  | cons action rest ih =>
      let performed := actionResult step capture capacity compatible action state
      have stored := pushOccurrence_exhausted_storage record performed.occurrence full
      have later := ih (pushOccurrence record performed.occurrence) performed.next stored.2.1
      simp only [recordActions, ActionResult.record_eq_pushOccurrence]
      exact ⟨later.1.trans stored.1, later.2.1, later.2.2.trans stored.2.2.1⟩

omit [DecidableEq Stored] [DecidableEq Output] in
theorem actionStop_reasons_differ :
    ActionStop.finished ≠ ActionStop.exhausted ∧
      ActionStop.exhausted ≠ ActionStop.breakpoint ∧
      ActionStop.breakpoint ≠ ActionStop.finished := by
  decide

/-- Fuel `0` on a nonempty schedule is exhaustion even when the guard would
accept the action. An empty schedule is completion. A disabled guard runs. -/
theorem service_pause_reasons :
    (pauseBefore serviceCohortStep (fun value => some value) (fun _ => true) (fun _ => true)
      none none 0 (fun _ _ => true) [Action.pump] serviceCohort).stop = ActionStop.exhausted ∧
    (pauseBefore serviceCohortStep (fun value => some value) (fun _ => true) (fun _ => true)
      none none 1 (fun _ _ => true) [Action.pump] serviceCohort).stop = ActionStop.breakpoint ∧
    (pauseBefore serviceCohortStep (fun value => some value) (fun _ => true) (fun _ => true)
      none none 0 (fun _ _ => true) ([] : List (Action Unit 2)) serviceCohort).stop =
      ActionStop.finished ∧
    (pauseBefore serviceCohortStep (fun value => some value) (fun _ => true) (fun _ => true)
      none none 1 (fun _ _ => false) [Action.pump] serviceCohort).stop =
      ActionStop.finished := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The breakpoint is before the production pump. The borrowed return and its
charge appear only when that pump runs. `consumed = 0` is the control index;
the action list is not retained. -/
theorem breakpoint_before_production :
    let capture := fun value : Nat => some value
    let allow := fun _ : Nat => true
    let schedule : List (Action Unit 2) := [Action.pump]
    let hit := fun (_ : Configuration Unit Nat Nat Nat Unit Unit Unit 2) (_ : Action Unit 2) => true
    let recorded := pauseBefore serviceCohortStep capture allow allow
      (some (Prefix.initial 1)) (some (1, 1)) 1 hit schedule serviceCohort
    let silent := pauseBefore serviceCohortStep capture allow allow none none 1 hit schedule
      serviceCohort
    let resumed := pauseBefore serviceCohortStep capture allow allow recorded.history
      recorded.account recorded.suffix.length (fun _ _ => false) recorded.suffix recorded.state
    recorded.stop = ActionStop.breakpoint ∧
      silent.stop = ActionStop.breakpoint ∧
      silent.history = none ∧
      recorded.consumed = 0 ∧
      recorded.suffix = schedule ∧
      schedule.take recorded.consumed = [] ∧
      recorded.state = serviceCohort ∧
      recorded.account = some (1, 1) ∧
      recorded.history = some (Prefix.initial 1) ∧
      pending recorded.state = none ∧
      resumed.stop = ActionStop.finished ∧
      resumed.suffix = [] ∧
      resumed.consumed = schedule.length ∧
      resumed.state = runActions serviceCohortStep capture allow allow schedule serviceCohort ∧
      pending resumed.state = some 2 ∧
      driverTicks (pump serviceCohortStep capture allow allow serviceCohort).1 = 1 ∧
      noticeAdmission? (clients := 2) (pump serviceCohortStep capture allow allow serviceCohort).1 =
        none ∧
      resumed.account = some (Multiplicative.ofAdd 1, 1) ∧
      recorded.account ≠ resumed.account := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  decide

/-- A pending borrowed return is source state. The same configuration can be
completed, stopped, or left by exhaustion, and only the completed pump admits. -/
theorem pending_return_is_not_a_breakpoint :
    let capture := fun value : Nat => some value
    let allow := fun _ : Nat => true
    let returned := pump serviceCohortStep capture allow allow serviceCohort
    let ran := pauseBefore serviceCohortStep capture allow allow none none 1 (fun _ _ => false)
      [Action.pump] returned.2
    let held := pauseBefore serviceCohortStep capture allow allow none none 1 (fun _ _ => true)
      [Action.pump] returned.2
    let dry := pauseBefore serviceCohortStep capture allow allow none none 0 (fun _ _ => true)
      [Action.pump] returned.2
    returned.1 = .returned 2 ∧
      pending returned.2 = some 2 ∧
      ran.stop = ActionStop.finished ∧
      ran.state.delivery.log.rows = [2] ∧
      pending ran.state = none ∧
      held.stop = ActionStop.breakpoint ∧
      held.state = returned.2 ∧
      pending held.state = some 2 ∧
      held.state.delivery.log.rows = [] ∧
      dry.stop = ActionStop.exhausted ∧
      dry.state = returned.2 ∧
      dry.stop ≠ held.stop ∧
      held.stop ≠ ran.stop := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · decide
  · decide

/-- The breakpoint is before the pump that installs the effect. Resuming runs
that pump and the following inert barrier once in this source model. -/
theorem breakpoint_before_effect :
    let effectStep := fun (_ : Unit) => (ProducerOutcome.effect () () :
        ProducerOutcome Unit Nat Unit Unit)
    let capture := fun value : Nat => some value
    let allow := fun _ : Nat => true
    let schedule : List (Action Unit 2) := [Action.pump, Action.pump]
    let paused := pauseBefore effectStep capture allow allow none (some (1, 1)) 1
      (fun _ _ => true) schedule serviceCohort
    let resumed := pauseBefore effectStep capture allow allow paused.history paused.account
      paused.suffix.length (fun _ _ => false) paused.suffix paused.state
    paused.stop = ActionStop.breakpoint ∧
      paused.consumed = 0 ∧
      paused.suffix = schedule ∧
      paused.state = serviceCohort ∧
      paused.state.execution = some ⟨(), none, 0, .active⟩ ∧
      paused.account = some (1, 1) ∧
      resumed.stop = ActionStop.finished ∧
      resumed.consumed = schedule.length ∧
      resumed.account = some (1, 1) ∧
      resumed.state = runActions effectStep capture allow allow schedule serviceCohort ∧
      resumed.state.execution = some ⟨(), none, 0, .effect ()⟩ ∧
      pump effectStep capture allow allow resumed.state = (.effect (), resumed.state) ∧
      noticeAdmission? (clients := 2)
        (pump effectStep capture allow allow resumed.state).1 = none := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The breakpoint is before the pump that installs the handoff. Resuming runs
that pump and the following inert barrier once in this source model. -/
theorem breakpoint_before_handoff :
    let handoffStep := fun (_ : Unit) => (ProducerOutcome.handoff () () :
        ProducerOutcome Unit Nat Unit Unit)
    let capture := fun value : Nat => some value
    let allow := fun _ : Nat => true
    let schedule : List (Action Unit 2) := [Action.pump, Action.pump]
    let paused := pauseBefore handoffStep capture allow allow none (some (1, 1)) 1
      (fun _ _ => true) schedule serviceCohort
    let resumed := pauseBefore handoffStep capture allow allow paused.history paused.account
      paused.suffix.length (fun _ _ => false) paused.suffix paused.state
    paused.stop = ActionStop.breakpoint ∧
      paused.consumed = 0 ∧
      paused.state = serviceCohort ∧
      paused.state.execution = some ⟨(), none, 0, .active⟩ ∧
      resumed.stop = ActionStop.finished ∧
      resumed.consumed = schedule.length ∧
      resumed.state = runActions handoffStep capture allow allow schedule serviceCohort ∧
      resumed.state.execution = some ⟨(), none, 0, .handoff ()⟩ ∧
      pump handoffStep capture allow allow resumed.state = (.handoff (), resumed.state) ∧
      noticeAdmission? (clients := 2)
        (pump handoffStep capture allow allow resumed.state).1 = none ∧
      resumed.account = some (1, 1) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- An installed effect is still an effect under exhaustion, a breakpoint, and
completion. The barrier pump leaves the mode in place and finishes. -/
theorem pending_effect_is_not_a_pause_reason :
    let effectStep := fun (_ : Unit) => (ProducerOutcome.effect () () :
        ProducerOutcome Unit Nat Unit Unit)
    let capture := fun value : Nat => some value
    let allow := fun _ : Nat => true
    let installed := (pump effectStep capture allow allow serviceCohort).2
    let dry := pauseBefore effectStep capture allow allow none (some (1, 1)) 0 (fun _ _ => true)
      [Action.pump] installed
    let held := pauseBefore effectStep capture allow allow none (some (1, 1)) 1 (fun _ _ => true)
      [Action.pump] installed
    let ran := pauseBefore effectStep capture allow allow none (some (1, 1)) 1 (fun _ _ => false)
      [Action.pump] installed
    let resumed := pauseBefore effectStep capture allow allow held.history held.account
      held.suffix.length (fun _ _ => false) held.suffix held.state
    installed.execution = some ⟨(), none, 0, .effect ()⟩ ∧
      dry.stop = ActionStop.exhausted ∧
      held.stop = ActionStop.breakpoint ∧
      ran.stop = ActionStop.finished ∧
      dry.state = installed ∧
      held.state = installed ∧
      ran.state = installed ∧
      held.account = some (1, 1) ∧
      ran.account = some (1, 1) ∧
      resumed.stop = ActionStop.finished ∧
      resumed.state = installed ∧
      resumed.account = some (1, 1) ∧
      dry.stop ≠ held.stop ∧
      held.stop ≠ ran.stop := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · decide
  · decide

/-- An installed handoff remains under every stop. The barrier finishes and
keeps the handoff mode. -/
theorem pending_handoff_is_not_a_pause_reason :
    let handoffStep := fun (_ : Unit) => (ProducerOutcome.handoff () () :
        ProducerOutcome Unit Nat Unit Unit)
    let capture := fun value : Nat => some value
    let allow := fun _ : Nat => true
    let installed := (pump handoffStep capture allow allow serviceCohort).2
    let dry := pauseBefore handoffStep capture allow allow none none 0 (fun _ _ => true)
      [Action.pump] installed
    let held := pauseBefore handoffStep capture allow allow none none 1 (fun _ _ => true)
      [Action.pump] installed
    let ran := pauseBefore handoffStep capture allow allow none none 1 (fun _ _ => false)
      [Action.pump] installed
    installed.execution = some ⟨(), none, 0, .handoff ()⟩ ∧
      dry.stop = ActionStop.exhausted ∧
      held.stop = ActionStop.breakpoint ∧
      ran.stop = ActionStop.finished ∧
      dry.state = installed ∧
      held.state = installed ∧
      ran.state = installed ∧
      dry.history = none ∧
      held.history = none ∧
      ran.history = none := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A consumer waiting for a row produces reply `.paused`. With the guard
disabled that action completes; the reply is not a breakpoint. -/
theorem source_paused_reply_is_not_a_breakpoint :
    (deliver (fun _ => true) serviceCohort (0 : Fin 2) ()).1 =
        .observed (SharedOccurrenceLog.Reply.paused : SharedOccurrenceLog.Reply Nat) ∧
      (pauseBefore serviceCohortStep (fun value => some value) (fun _ => true) (fun _ => true)
        none none 1 (fun _ _ => false) [Action.deliver (0 : Fin 2) ()] serviceCohort).stop =
        ActionStop.finished ∧
      (pauseBefore serviceCohortStep (fun value => some value) (fun _ => true) (fun _ => true)
        none none 1 (fun _ _ => false) [Action.deliver (0 : Fin 2) ()] serviceCohort).state =
        serviceCohort ∧
      pending serviceCohort = none ∧
      ActionStop.finished ≠ ActionStop.breakpoint := by
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  decide

/-- The second equal delivery is the unexecuted suffix. The executed word is
`schedule.take consumed`. Resuming delivers the suffix once in this source
model; the two cursors and the two identities stay distinct. -/
theorem breakpoint_before_second_delivery :
    let capture := fun value : Nat => some value
    let allow := fun _ : Nat => true
    let guard := fun (_ : Configuration Unit Nat Nat Nat Unit Unit Unit 2) (action : Action Unit 2) =>
      match action with
      | .pump => false
      | .deliver client _ => client == (1 : Fin 2)
    let schedule : List (Action Unit 2) :=
      [Action.pump, Action.pump, Action.deliver (0 : Fin 2) (), Action.deliver (1 : Fin 2) ()]
    let paused := pauseBefore serviceCohortStep capture allow allow
      (some (Prefix.initial 4)) (some (1, 1)) 4 guard schedule serviceCohort
    let resumed := pauseBefore serviceCohortStep capture allow allow paused.history paused.account
      paused.suffix.length (fun _ _ => false) paused.suffix paused.state
    paused.stop = ActionStop.breakpoint ∧
      paused.consumed = 3 ∧
      schedule.take paused.consumed =
        [Action.pump, Action.pump, Action.deliver (0 : Fin 2) ()] ∧
      paused.suffix = [Action.deliver (1 : Fin 2) ()] ∧
      paused.state.delivery.log.rows = [2] ∧
      paused.state.delivery.log.positions (0 : Fin 2) = some 1 ∧
      paused.state.delivery.log.positions (1 : Fin 2) = some 0 ∧
      resumed.stop = ActionStop.finished ∧
      resumed.consumed = paused.suffix.length ∧
      resumed.state = runActions serviceCohortStep capture allow allow schedule serviceCohort ∧
      resumed.state.delivery.log.positions (0 : Fin 2) = some 1 ∧
      resumed.state.delivery.log.positions (1 : Fin 2) = some 1 ∧
      deliveryCausal (0 : Fin 2) 0 ≠ deliveryCausal (1 : Fin 2) 0 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  decide

/-- A zero-capacity prefix omits the admission and does not regain it when the
unexecuted deliveries run. The source rows and a positive-capacity prefix of
the same pumps still show that admission. The omitted prefix is the only
history; the consumed count is not a second copy of the action word. -/
theorem omitted_pause_history_is_not_the_source_word :
    let capture := fun value : Nat => some value
    let allow := fun _ : Nat => true
    let guard := fun (_ : Configuration Unit Nat Nat Nat Unit Unit Unit 2) (action : Action Unit 2) =>
      match action with
      | .pump => false
      | .deliver _ _ => true
    let schedule : List (Action Unit 2) :=
      [Action.pump, Action.pump, Action.deliver (0 : Fin 2) (), Action.deliver (1 : Fin 2) ()]
    let paused := pauseBefore serviceCohortStep capture allow allow
      (some (Prefix.initial 0)) (some (1, 1)) 4 guard schedule serviceCohort
    let resumed := pauseBefore serviceCohortStep capture allow allow paused.history paused.account
      paused.suffix.length (fun _ _ => false) paused.suffix paused.state
    let kept := recordActions serviceCohortStep capture allow allow
      [Action.pump, Action.pump] (Prefix.initial 1) serviceCohort
    let silent := pauseBefore serviceCohortStep capture allow allow none none 4 guard schedule
      serviceCohort
    paused.stop = ActionStop.breakpoint ∧
      paused.consumed = 2 ∧
      schedule.take paused.consumed = [Action.pump, Action.pump] ∧
      paused.suffix = [Action.deliver (0 : Fin 2) (), Action.deliver (1 : Fin 2) ()] ∧
      paused.state.delivery.log.rows = [2] ∧
      silent.history = none ∧
      silent.state = paused.state ∧
      paused.history = some ⟨[], 0, 1⟩ ∧
      Prefix.complete? (⟨[], 0, 1⟩ : Prefix Occurrence) = none ∧
      kept.1.items = [admissionCausal (clients := 2) 0] ∧
      Prefix.complete? kept.1 = some [admissionCausal (clients := 2) 0] ∧
      resumed.history = some ⟨[], 0, 3⟩ ∧
      Prefix.complete? (⟨[], 0, 3⟩ : Prefix Occurrence) = none ∧
      resumed.state.delivery.log.rows = [2] ∧
      resumed.state.delivery.log.positions (0 : Fin 2) = some 1 ∧
      resumed.state.delivery.log.positions (1 : Fin 2) = some 1 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩



/-- The same account option is the paid account under either history option.
`pauseOnGate_recording_irrelevant` supplies the shared consumed index. -/
theorem pauseOnGate_recording_keeps_account
    (history otherHistory : Option (Prefix Occurrence))
    (account : Option ProtocolAccount) (fuel : Nat)
    (decide : Cfg → Action Output clients → OperationGate)
    (actions : List (Action Output clients)) (state : Cfg) :
    (pauseOnGate step capture capacity compatible history account fuel decide actions state).account =
      (pauseOnGate step capture capacity compatible otherHistory account fuel decide actions
        state).account := by
  have aligned := pauseOnGate_recording_irrelevant step capture capacity compatible history
    otherHistory account account fuel decide actions state state rfl
  have left := pauseOnGate_unexecuted_keeps_account step capture capacity compatible history
    account fuel decide actions state
  have right := pauseOnGate_unexecuted_keeps_account step capture capacity compatible
    otherHistory account fuel decide actions state
  have sameTake :
      actions.take
          (pauseOnGate step capture capacity compatible otherHistory account fuel decide actions
            state).consumed =
        actions.take
          (pauseOnGate step capture capacity compatible history account fuel decide actions
            state).consumed := by
    rw [aligned.2.1]
  rw [left.1, right.1, sameTake]
  exact (congrArg Prod.fst
      (enterActionObservers_projects_account step capture capacity compatible history account
        (actions.take
          (pauseOnGate step capture capacity compatible history account fuel decide actions
            state).consumed)
        state)).trans
    (congrArg Prod.fst
      (enterActionObservers_projects_account step capture capacity compatible otherHistory account
        (actions.take
          (pauseOnGate step capture capacity compatible history account fuel decide actions
            state).consumed)
        state)).symm

/-- Forgetting the paused history uses `none`. The suffix and the paid account
stay those of the recorded run. -/
theorem pauseOnGate_forget_keeps_suffix_and_account
    (history : Option (Prefix Occurrence)) (account : Option ProtocolAccount) (fuel : Nat)
    (decide : Cfg → Action Output clients → OperationGate)
    (actions : List (Action Output clients)) (state : Cfg) :
    (pauseOnGate step capture capacity compatible none account fuel decide actions state).stop =
        (pauseOnGate step capture capacity compatible history account fuel decide actions
          state).stop ∧
      (pauseOnGate step capture capacity compatible none account fuel decide actions state).consumed =
        (pauseOnGate step capture capacity compatible history account fuel decide actions
          state).consumed ∧
      (pauseOnGate step capture capacity compatible none account fuel decide actions state).suffix =
        (pauseOnGate step capture capacity compatible history account fuel decide actions
          state).suffix ∧
      (pauseOnGate step capture capacity compatible none account fuel decide actions state).account =
        (pauseOnGate step capture capacity compatible history account fuel decide actions
          state).account ∧
      (pauseOnGate step capture capacity compatible none account fuel decide actions state).state =
        (pauseOnGate step capture capacity compatible history account fuel decide actions
          state).state := by
  have aligned := pauseOnGate_recording_irrelevant step capture capacity compatible history none
    account account fuel decide actions state state rfl
  have paid := pauseOnGate_recording_keeps_account step capture capacity compatible history none
    account fuel decide actions state
  exact ⟨aligned.1.symm, aligned.2.1.symm, aligned.2.2.1.symm, paid.symm, aligned.2.2.2.symm⟩

/-- Restarting attaches `Prefix.initial` at the same run. The suffix and the
paid account stay. `record_after_unrecorded_gap` and
`fresh_record_after_unrecorded_gap_bounds` remain the suffix-diary equations. -/
theorem pauseOnGate_restart_keeps_suffix_and_account
    (history : Option (Prefix Occurrence)) (account : Option ProtocolAccount) (fuel : Nat)
    (decide : Cfg → Action Output clients → OperationGate)
    (actions : List (Action Output clients)) (state : Cfg) (bound : Nat) :
    (pauseOnGate step capture capacity compatible (some (Prefix.initial bound)) account fuel
        decide actions state).stop =
        (pauseOnGate step capture capacity compatible history account fuel decide actions
          state).stop ∧
      (pauseOnGate step capture capacity compatible (some (Prefix.initial bound)) account fuel
          decide actions state).consumed =
        (pauseOnGate step capture capacity compatible history account fuel decide actions
          state).consumed ∧
      (pauseOnGate step capture capacity compatible (some (Prefix.initial bound)) account fuel
          decide actions state).suffix =
        (pauseOnGate step capture capacity compatible history account fuel decide actions
          state).suffix ∧
      (pauseOnGate step capture capacity compatible (some (Prefix.initial bound)) account fuel
          decide actions state).account =
        (pauseOnGate step capture capacity compatible history account fuel decide actions
          state).account ∧
      (pauseOnGate step capture capacity compatible (some (Prefix.initial bound)) account fuel
          decide actions state).state =
        (pauseOnGate step capture capacity compatible history account fuel decide actions
          state).state := by
  have aligned := pauseOnGate_recording_irrelevant step capture capacity compatible history
    (some (Prefix.initial bound)) account account fuel decide actions state state rfl
  have paid := pauseOnGate_recording_keeps_account step capture capacity compatible history
    (some (Prefix.initial bound)) account fuel decide actions state
  exact ⟨aligned.1.symm, aligned.2.1.symm, aligned.2.2.1.symm, paid.symm, aligned.2.2.2.symm⟩


/-- The retained cut determines the observers below. The cause of a stop
carries separate information even when the cut is the same. -/
example (history : Option (Prefix Occurrence)) (account : Option ProtocolAccount)
    (action : Action Output clients) (state : Cfg) :
    let refused := pauseOnGate step capture capacity compatible history account 1
      (fun _ _ => .refuse) [action] state
    let stopped := pauseOnGate step capture capacity compatible history account 1
      (fun _ _ => .stopBefore) [action] state
    (refused.history, refused.account, refused.state, refused.suffix, refused.consumed) =
      (stopped.history, stopped.account, stopped.state, stopped.suffix, stopped.consumed) ∧
      refused.stop ≠ stopped.stop := by
  dsimp only
  rw [pauseOnGate_refuse_step step capture capacity compatible history account 0
        (fun _ _ => .refuse) action [] state rfl,
      pauseOnGate_breakpoint_step step capture capacity compatible history account 0
        (fun _ _ => .stopBefore) action [] state rfl]
  refine ⟨rfl, ?_⟩
  intro same
  cases same

/-- A disabled stop test still permits under constant authorization, and the
same disabled test does not turn an authorization denial into that permit.
The refusal keeps the account and the configuration. -/
theorem disabled_stop_does_not_override_refusal (history : Option (Prefix Occurrence))
    (account : Option ProtocolAccount) (fuel : Nat)
    (authorized breakOn : Cfg → Action Output clients → Bool) (action : Action Output clients)
    (rest : List (Action Output clients)) (state : Cfg)
    (disabled : breakOn state action = false) (denied : authorized state action = false) :
    pauseOnGate step capture capacity compatible history account (fuel + 1)
        (operationGate authorized breakOn) (action :: rest) state =
      pauseOnGate step capture capacity compatible history account (fuel + 1)
        (operationGate authorized (fun _ _ => true)) (action :: rest) state ∧
      (pauseOnGate step capture capacity compatible history account (fuel + 1)
        (operationGate authorized breakOn) (action :: rest) state).stop = ActionStop.refused ∧
      (pauseOnGate step capture capacity compatible history account (fuel + 1)
        (operationGate authorized breakOn) (action :: rest) state).account = account ∧
      (pauseOnGate step capture capacity compatible history account (fuel + 1)
        (operationGate authorized breakOn) (action :: rest) state).consumed = 0 ∧
      (pauseOnGate step capture capacity compatible history account (fuel + 1)
        (operationGate authorized breakOn) (action :: rest) state).state = state ∧
      operationGate (fun _ _ => true) breakOn state action = OperationGate.permit := by
  have refused := operationGate_refuse authorized breakOn state action denied
  have refusedStop := operationGate_refuse authorized (fun _ _ => true) state action denied
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [pauseOnGate_refuse_step step capture capacity compatible history account fuel
      (operationGate authorized breakOn) action rest state refused,
      pauseOnGate_refuse_step step capture capacity compatible history account fuel
      (operationGate authorized (fun _ _ => true)) action rest state refusedStop]
  · rw [pauseOnGate_refuse_step step capture capacity compatible history account fuel
      (operationGate authorized breakOn) action rest state refused]
  · rw [pauseOnGate_refuse_step step capture capacity compatible history account fuel
      (operationGate authorized breakOn) action rest state refused]
  · rw [pauseOnGate_refuse_step step capture capacity compatible history account fuel
      (operationGate authorized breakOn) action rest state refused]
  · rw [pauseOnGate_refuse_step step capture capacity compatible history account fuel
      (operationGate authorized breakOn) action rest state refused]
  · exact operationGate_permit (fun _ _ => true) breakOn state action rfl disabled

omit [DecidableEq Stored] [DecidableEq Output] in
theorem actionStop_refusal_differs :
    ActionStop.refused ≠ ActionStop.finished ∧
      ActionStop.refused ≠ ActionStop.exhausted ∧
      ActionStop.refused ≠ ActionStop.breakpoint := by
  decide

/-- Fuel `0` stays exhaustion while the gate would refuse. With fuel, a disabled
stop and an enabled stop both refuse, and neither charges the account. An
authorized stop remains a breakpoint. -/
theorem refusal_precedes_disabled_stop :
    let capture := fun value : Nat => some value
    let allowCtx := fun _ : Nat => true
    let deny := fun (_ : Configuration Unit Nat Nat Nat Unit Unit Unit 2) (_ : Action Unit 2) =>
      false
    let allowAct := fun (_ : Configuration Unit Nat Nat Nat Unit Unit Unit 2) (_ : Action Unit 2) =>
      true
    let stop := fun (_ : Configuration Unit Nat Nat Nat Unit Unit Unit 2) (_ : Action Unit 2) => true
    let pass := fun (_ : Configuration Unit Nat Nat Nat Unit Unit Unit 2) (_ : Action Unit 2) =>
      false
    let schedule : List (Action Unit 2) := [Action.pump]
    let dry := pauseOnGate serviceCohortStep capture allowCtx allowCtx none (some (1, 1)) 0
      (operationGate deny stop) schedule serviceCohort
    let refusedStop := pauseOnGate serviceCohortStep capture allowCtx allowCtx none (some (1, 1)) 1
      (operationGate deny stop) schedule serviceCohort
    let refusedPass := pauseOnGate serviceCohortStep capture allowCtx allowCtx none (some (1, 1)) 1
      (operationGate deny pass) schedule serviceCohort
    let broke := pauseOnGate serviceCohortStep capture allowCtx allowCtx none (some (1, 1)) 1
      (operationGate allowAct stop) schedule serviceCohort
    let ran := pauseOnGate serviceCohortStep capture allowCtx allowCtx none (some (1, 1)) 1
      (operationGate allowAct pass) schedule serviceCohort
    dry.stop = ActionStop.exhausted ∧
      refusedStop.stop = ActionStop.refused ∧
      refusedPass.stop = ActionStop.refused ∧
      refusedStop.stop = refusedPass.stop ∧
      refusedStop.consumed = 0 ∧
      schedule.take refusedStop.consumed = [] ∧
      refusedStop.suffix = schedule ∧
      refusedStop.state = serviceCohort ∧
      refusedStop.account = some (1, 1) ∧
      refusedPass.account = some (1, 1) ∧
      broke.stop = ActionStop.breakpoint ∧
      broke.state = serviceCohort ∧
      broke.account = some (1, 1) ∧
      ran.stop = ActionStop.finished ∧
      dry.stop ≠ refusedStop.stop ∧
      refusedStop.stop ≠ broke.stop ∧
      broke.stop ≠ ran.stop := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide

omit [DecidableEq Stored] [DecidableEq Output] in
theorem actionStop_incomplete_differs :
    ActionStop.incomplete ≠ ActionStop.finished ∧
      ActionStop.incomplete ≠ ActionStop.exhausted ∧
      ActionStop.incomplete ≠ ActionStop.breakpoint ∧
      ActionStop.incomplete ≠ ActionStop.refused := by
  decide

omit [DecidableEq Stored] [DecidableEq Output] in
/-- `refuted` permits the action. `incomplete` retains it. A denial stays a
refusal when the inspection is incomplete. -/
theorem inspection_reasons_differ (state : Cfg) (action : Action Output clients) :
    inspectionGate (fun _ _ => true) (fun _ _ => .matched) state action = .stopBefore ∧
      inspectionGate (fun _ _ => true) (fun _ _ => .refuted) state action = .permit ∧
      inspectionGate (fun _ _ => true) (fun _ _ => .incomplete) state action = .incomplete ∧
      inspectionGate (fun _ _ => false) (fun _ _ => .incomplete) state action = .refuse := by
  unfold inspectionGate
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- An incomplete inspection does not run the action or change the account.
Fuel `0` remains exhaustion and does not read that inspection. -/
theorem incomplete_inspection_keeps_action (history : Option (Prefix Occurrence))
    (account : Option ProtocolAccount) (fuel : Nat) (action : Action Output clients)
    (rest : List (Action Output clients)) (state : Cfg) :
    let decide := fun (_ : Cfg) (_ : Action Output clients) => OperationGate.incomplete
    (pauseOnGate step capture capacity compatible history account 0 decide (action :: rest)
        state).stop = ActionStop.exhausted ∧
      (pauseOnGate step capture capacity compatible history account (fuel + 1) decide
        (action :: rest) state).stop = ActionStop.incomplete ∧
      (pauseOnGate step capture capacity compatible history account (fuel + 1) decide
        (action :: rest) state).consumed = 0 ∧
      (pauseOnGate step capture capacity compatible history account (fuel + 1) decide
        (action :: rest) state).suffix = action :: rest ∧
      (pauseOnGate step capture capacity compatible history account (fuel + 1) decide
        (action :: rest) state).account = account ∧
      (pauseOnGate step capture capacity compatible history account (fuel + 1) decide
        (action :: rest) state).state = state ∧
      (pauseOnGate step capture capacity compatible history account (fuel + 1) decide
        (action :: rest) state).state =
        runActions step capture capacity compatible
          ((action :: rest).take
            (pauseOnGate step capture capacity compatible history account (fuel + 1) decide
              (action :: rest) state).consumed)
          state := by
  intro decide
  have pending : decide state action = OperationGate.incomplete := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [fuelBeforeGate step capture capacity compatible history account decide action rest state]
  · rw [pauseOnGate_incomplete_step step capture capacity compatible history account fuel decide
      action rest state pending]
  · rw [pauseOnGate_incomplete_step step capture capacity compatible history account fuel decide
      action rest state pending]
  · rw [pauseOnGate_incomplete_step step capture capacity compatible history account fuel decide
      action rest state pending]
  · rw [pauseOnGate_incomplete_step step capture capacity compatible history account fuel decide
      action rest state pending]
  · rw [pauseOnGate_incomplete_step step capture capacity compatible history account fuel decide
      action rest state pending]
  · exact pauseOnGate_erases step capture capacity compatible history account (fuel + 1) decide
      (action :: rest) state

/-- Replacing an incomplete stop resumes at the retained suffix. The second
runner receives that suffix, and `actions.take consumed` stays the already
observed prefix. -/
theorem incomplete_replacement_resumes_suffix (history : Option (Prefix Occurrence))
    (account : Option ProtocolAccount) (fuel : Nat)
    (decide : Cfg → Action Output clients → OperationGate)
    (actions : List (Action Output clients)) (state : Cfg)
    (mark : (pauseOnGate step capture capacity compatible history account fuel decide actions
      state).stop = ActionStop.incomplete) :
    let paused := pauseOnGate step capture capacity compatible history account fuel decide
      actions state
    let resumed := pauseOnGate step capture capacity compatible paused.history paused.account
      paused.suffix.length (operationGate (fun _ _ => true) (fun _ _ => false)) paused.suffix
      paused.state
    paused.stop = ActionStop.incomplete ∧
      paused.stop ≠ ActionStop.breakpoint ∧
      paused.account =
        (enterActionObservers step capture capacity compatible history account
          (actions.take paused.consumed) state).2.1 ∧
      paused.state =
        runActions step capture capacity compatible (actions.take paused.consumed) state ∧
      actions.take paused.consumed ++ paused.suffix = actions ∧
      resumed.stop = ActionStop.finished ∧
      resumed.suffix = [] ∧
      resumed.consumed = paused.suffix.length ∧
      (resumed.history, resumed.account, resumed.state) =
        enterActionObservers step capture capacity compatible history account actions state := by
  intro paused resumed
  have kept := pauseOnGate_unexecuted_keeps_account step capture capacity compatible history
    account fuel decide actions state
  have erased := pauseOnGate_erases step capture capacity compatible history account fuel decide
    actions state
  have split := pauseOnGate_split step capture capacity compatible history account fuel decide
    actions state
  have resume := pauseOnGate_resume_permitted step capture capacity compatible history account
    fuel decide actions state
  have distinct : paused.stop ≠ ActionStop.breakpoint := by
    rw [mark]
    decide
  exact ⟨mark, distinct, kept.1, erased, split.2, resume.1, resume.2.1, resume.2.2.1,
    resume.2.2.2.1⟩

/-- Incomplete inspection retains the pump. Fuel exhaustion, refusal, a
matched breakpoint, and a refuted guard stay different answers. -/
theorem incomplete_inspection_retains_service_action :
    let capture := fun value : Nat => some value
    let allowCtx := fun _ : Nat => true
    let deny := fun (_ : Configuration Unit Nat Nat Nat Unit Unit Unit 2) (_ : Action Unit 2) =>
      false
    let allowAct := fun (_ : Configuration Unit Nat Nat Nat Unit Unit Unit 2) (_ : Action Unit 2) =>
      true
    let hold := fun (_ : Configuration Unit Nat Nat Nat Unit Unit Unit 2) (_ : Action Unit 2) =>
      GuardInspection.incomplete
    let matched := fun (_ : Configuration Unit Nat Nat Nat Unit Unit Unit 2) (_ : Action Unit 2) =>
      GuardInspection.matched
    let refuted := fun (_ : Configuration Unit Nat Nat Nat Unit Unit Unit 2) (_ : Action Unit 2) =>
      GuardInspection.refuted
    let schedule : List (Action Unit 2) := [Action.pump]
    let dry := pauseOnGate serviceCohortStep capture allowCtx allowCtx none (some (1, 1)) 0
      (inspectionGate deny hold) schedule serviceCohort
    let held := pauseOnGate serviceCohortStep capture allowCtx allowCtx none (some (1, 1)) 1
      (inspectionGate allowAct hold) schedule serviceCohort
    let refused := pauseOnGate serviceCohortStep capture allowCtx allowCtx none (some (1, 1)) 1
      (inspectionGate deny hold) schedule serviceCohort
    let broke := pauseOnGate serviceCohortStep capture allowCtx allowCtx none (some (1, 1)) 1
      (inspectionGate allowAct matched) schedule serviceCohort
    let ran := pauseOnGate serviceCohortStep capture allowCtx allowCtx none (some (1, 1)) 1
      (inspectionGate allowAct refuted) schedule serviceCohort
    dry.stop = ActionStop.exhausted ∧
      held.stop = ActionStop.incomplete ∧
      held.consumed = 0 ∧
      schedule.take held.consumed = [] ∧
      held.suffix = schedule ∧
      held.state = serviceCohort ∧
      held.account = some (1, 1) ∧
      refused.stop = ActionStop.refused ∧
      refused.account = some (1, 1) ∧
      broke.stop = ActionStop.breakpoint ∧
      ran.stop = ActionStop.finished ∧
      held.stop ≠ ActionStop.breakpoint ∧
      held.stop ≠ ActionStop.refused ∧
      held.stop ≠ ActionStop.exhausted ∧
      ran.stop ≠ ActionStop.incomplete := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · decide
end InterleavedObservation

end Accounting

/-! ## Finite credit for the actual producer and delivery cursor

The optional finite profile uses the existing shared lease ledger. Its source
program sequences existing pump/delivery actions through the common primitive
cursor. The source action account prices production and delivery separately;
it is not a bound on arbitrary callbacks or the complete native service slot.
The ordinary uncounted entry and its recording selection remain unchanged.
-/

namespace Accounting.LeaseExecution

open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open Mettapedia.GSLT.Dynamics.ParallelFuelLease

variable {Producer Borrowed Stored Context Output Effect Handoff : Type} {clients : Nat}
variable [DecidableEq Stored] [DecidableEq Output]
variable (step : Producer → ProducerOutcome Producer Borrowed Effect Handoff)
variable (capture : Borrowed → Option Stored) (capacity : Stored → Bool)
variable (compatible : Context → Bool)

local notation "Cfg" =>
  Configuration Producer Borrowed Stored Context Output Effect Handoff clients

/-- A declared additive price for the existing two-coordinate account. -/
def accountPrice (production delivery : Nat) (account : ProtocolAccount) : Nat :=
  production * account.1.toAdd + delivery * account.2.toAdd

theorem accountPrice_mul (production delivery : Nat) (first second : ProtocolAccount) :
    accountPrice production delivery (first * second) =
      accountPrice production delivery first + accountPrice production delivery second := by
  simp [accountPrice, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm]

def program : List (Action Output clients) → Prog (Action Output clients) (fun _ => PUnit) PUnit
  | [] => .ret .unit
  | action :: rest => .call action fun _ => program rest

def sourceStep (state : Cfg) (action : Action Output clients) : Cfg × Except Empty PUnit :=
  ((advanceAction step capture capacity compatible action state).1, .ok .unit)

def sourcePrice (production delivery : Nat) (state : Cfg) (action : Action Output clients) : Nat :=
  accountPrice production delivery (advanceAction step capture capacity compatible action state).2

abbrev sourceProvider :
    Provider (PrimitiveProgram.protocol (Action Output clients) (fun _ => PUnit) Empty) :=
  PrimitiveProgram.provider (sourceStep (Output := Output) (clients := clients)
    step capture capacity compatible)
abbrev sourceClient := PrimitiveProgram.client (Action Output clients) (fun _ => PUnit) PUnit Empty

def sourceCharge (production delivery : Nat) :
    Charge (sourceProvider (Output := Output) (clients := clients) step capture capacity compatible) :=
  PrimitiveProgram.charge
    (sourcePrice (Output := Output) (clients := clients) step capture capacity compatible production delivery)
    (sourceStep (Output := Output) (clients := clients) step capture capacity compatible)

def sourcePacket (actions : List (Action Output clients)) (state : Cfg) :
    Packet (sourceProvider step capture capacity compatible)
      (sourceClient (Output := Output) (clients := clients)) PUnit.unit :=
  ⟨PUnit.unit, .ok (program actions), state⟩

/-- The independent primitive interpreter executes the existing uncounted
actions and obtains the independently maintained online source account. -/
theorem direct_program (production delivery : Nat) (actions : List (Action Output clients))
    (state : Cfg) :
    PrimitiveProgram.direct (sourceStep step capture capacity compatible)
      (sourcePrice step capture capacity compatible production delivery)
      (actions.length + 1) (.ok (program actions)) state =
      (accountPrice production delivery (count step capture capacity compatible actions (1, 1) state).2,
        (.inl (.ok PUnit.unit), runActions step capture capacity compatible actions state)) := by
  induction actions generalizing state with
  | nil => rfl
  | cons action rest ih =>
      change
        (sourcePrice step capture capacity compatible production delivery state action +
          (PrimitiveProgram.direct (sourceStep step capture capacity compatible)
            (sourcePrice step capture capacity compatible production delivery)
            (rest.length + 1) (.ok (program rest))
            (advanceAction step capture capacity compatible action state).1).1,
          (PrimitiveProgram.direct (sourceStep step capture capacity compatible)
            (sourcePrice step capture capacity compatible production delivery)
            (rest.length + 1) (.ok (program rest))
            (advanceAction step capture capacity compatible action state).1).2) = _
      rw [ih]
      have counted : (count step capture capacity compatible (action :: rest) (1, 1) state).2 =
          (advanceAction step capture capacity compatible action state).2 *
            (count step capture capacity compatible rest (1, 1)
              (advanceAction step capture capacity compatible action state).1).2 := by
        simpa only [count, Prod.mul_def, one_mul] using
          count_scales step capture capacity compatible rest
            (advanceAction step capture capacity compatible action state).2
            (advanceAction step capture capacity compatible action state).1
      rw [counted, accountPrice_mul]
      cases action <;> rfl

/-- The actual common cursor reaches exactly that state, paid prefix and
terminal result. Equality of the full state preserves its selected producer,
pending value, source history, delivery positions and publications. -/
theorem cursor_program (production delivery : Nat) (actions : List (Action Output clients))
    (state : Cfg) :
    let result := advance (sourceProvider step capture capacity compatible)
      (sourceClient (Output := Output) (clients := clients))
      (sourceCharge step capture capacity compatible production delivery)
      (actions.length + 1) (sourcePacket step capture capacity compatible actions state)
    (result.1, PrimitiveProgram.readOutcome (sourceStep step capture capacity compatible) result.2) =
      (accountPrice production delivery (count step capture capacity compatible actions (1, 1) state).2,
        (.inl (.ok PUnit.unit), runActions step capture capacity compatible actions state)) := by
  exact (PrimitiveProgram.advance_is_direct (sourceStep step capture capacity compatible)
    (sourcePrice step capture capacity compatible production delivery) (actions.length + 1)
    (.ok (program actions)) state).trans
      (direct_program step capture capacity compatible production delivery actions state)

/-- The charge word is derived from the actual reply-dependent cursor and
agrees with the existing independent source-path RunAccount. -/
theorem charges_are_source_account (production delivery : Nat)
    (actions : List (Action Output clients)) (state : Cfg) :
    letI := actionQuiver (Output := Output) (clients := clients) step capture capacity compatible
    (Lease.charges (sourceClient (Output := Output) (clients := clients))
      (sourceProvider step capture capacity compatible)
      (sourceCharge step capture capacity compatible production delivery)
      (actions.length + 1) (sourcePacket step capture capacity compatible actions state)).sum =
      accountPrice production delivery ((splitAccount step capture capacity compatible).of
        (actionPath step capture capacity compatible actions state)) := by
  let _ := actionQuiver (Output := Output) (clients := clients) step capture capacity compatible
  rw [Lease.charges_sum, ← count_eq_pathAccount]
  exact congrArg Prod.fst
    (cursor_program step capture capacity compatible production delivery actions state)

omit [DecidableEq Stored] in
theorem answerUnits_le_one (reply : DeliveryReply Stored) : answerUnits reply ≤ 1 := by
  cases reply with
  | contextRefused => simp [answerUnits]
  | observed reply => cases reply <;> simp [answerUnits]

/-- This is a bound on declared protocol prices, not on the work inside an
arbitrary pump, capture, compatibility, or delivery callback. -/
theorem sourcePrice_bound (production delivery : Nat) (state : Cfg)
    (action : Action Output clients) :
    sourcePrice step capture capacity compatible production delivery state action ≤
      max production delivery := by
  cases action with
  | pump =>
      change production * driverTicks (pump step capture capacity compatible state).1 + delivery * 0 ≤ _
      have bounded := Nat.mul_le_mul_left production
        (driverTicks_le_one (pump step capture capacity compatible state).1)
      simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one] at bounded ⊢
      exact bounded.trans (Nat.le_max_left _ _)
  | deliver client output =>
      change production * 0 + delivery * answerUnits (deliver compatible state client output).1 ≤ _
      have bounded := Nat.mul_le_mul_left delivery
        (answerUnits_le_one (deliver compatible state client output).1)
      simp only [Nat.mul_zero, Nat.zero_add, Nat.mul_one] at bounded ⊢
      exact bounded.trans (Nat.le_max_right _ _)

noncomputable section

/-- The actual selected provider moves every paid request to the shared spent
account. Its production/delivery valuation comes from the real source walk. -/
theorem financed_spent_is_source_account {Owner : Type} (owner : Owner)
    (ledger : Ledger Owner) (production delivery : Nat)
    (actions : List (Action Output clients)) (state : Cfg) :
    let M := sourceProvider step capture capacity compatible
    let C := sourceClient (Output := Output) (clients := clients)
    let price : Charge M := sourceCharge step capture capacity compatible production delivery
    let reached := advance (Lease.provider M price owner) C (Lease.price M price owner)
      (actions.length + 1)
      (Lease.attachPacket C M price owner ledger (sourcePacket step capture capacity compatible actions state))
    (Lease.ledgerOf C M price owner reached.2).spent =
      ledger.spent +
        (accountPrice production delivery (count step capture capacity compatible actions (1, 1) state).2 : ℤ) := by
  dsimp only
  rw [Lease.advance_spent]
  rw [congrArg Prod.fst (cursor_program step capture capacity compatible production delivery actions state)]

namespace Controls

def captureNat (value : Nat) : Option Nat := some value
def permitNat (_ : Nat) : Bool := true
def actions : List (Action Unit 2) := [.pump, .pump, .deliver 0 (), .deliver 1 ()]
abbrev M := sourceProvider (Output := Unit) (clients := 2)
  serviceCohortStep captureNat permitNat permitNat
abbrev C := sourceClient (Output := Unit) (clients := 2)
def price : Charge M := sourceCharge (Output := Unit) (clients := 2)
  serviceCohortStep captureNat permitNat permitNat 5 1
def start : Packet M C PUnit.unit :=
  sourcePacket serviceCohortStep captureNat permitNat permitNat actions serviceCohort
def first := advance M C price 2 start
def complete := resume M C price 3 first
def word := Lease.charges C M price 5 start

theorem actual_shared_production_and_split :
    word = [5, 0, 1, 1] ∧ first.1 = 5 ∧ complete.1 = 7 ∧
      Lease.suffixCharges C M price 3 first.2 = [1, 1] ∧
      complete = advance M C price 5 start ∧
      (count serviceCohortStep captureNat permitNat permitNat actions (1, 1)
        serviceCohort).2 = (Multiplicative.ofAdd 1, Multiplicative.ofAdd 2) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, rfl⟩
  exact (advance_add M C price 2 3 start).symm

/-- The one production admission is the common predecessor of two distinct
delivery occurrences. The complete ordinary state retains both cursor moves. -/
theorem actual_history_and_duplicate_deliveries :
    pathOccurrences serviceCohortStep captureNat permitNat permitNat
      (actionPath serviceCohortStep captureNat permitNat permitNat actions serviceCohort) =
        [admissionCausal 0, deliveryCausal (0 : Fin 2) 0, deliveryCausal (1 : Fin 2) 0] ∧
      (runActions serviceCohortStep captureNat permitNat permitNat actions
        serviceCohort).delivery.log.rows = [2] ∧
      (runActions serviceCohortStep captureNat permitNat permitNat actions
        serviceCohort).delivery.log.positions = (fun _ => some 1) := by
  refine ⟨rfl, rfl, ?_⟩
  funext client
  fin_cases client <;> rfl

/-- A real source interruption occurs after paid administrative work and
before any produced or delivered answer. -/
def interruptedStep (started : Bool) : ProducerOutcome Bool Nat Unit Unit :=
  if started then .interrupted true else .progress true
def interruptedStart : Configuration Bool Nat Nat Nat Unit Unit Unit 2 := initial false 8 2
abbrev interruptedM := sourceProvider (Output := Unit) (clients := 2)
  interruptedStep captureNat permitNat permitNat
def interruptedPrice : Charge interruptedM := sourceCharge (Output := Unit) (clients := 2)
  interruptedStep captureNat permitNat permitNat 3 1
def interruptedPacket : Packet interruptedM C PUnit.unit :=
  sourcePacket interruptedStep captureNat permitNat permitNat [.pump, .pump] interruptedStart

theorem successful_answers_do_not_account_for_interrupted_work :
    (advance interruptedM C interruptedPrice 3 interruptedPacket).1 = 3 ∧
      Lease.charges C interruptedM interruptedPrice 3 interruptedPacket = [3, 0] ∧
      (runActions interruptedStep captureNat permitNat permitNat [.pump, .pump]
        interruptedStart).delivery.log.rows = [] ∧
      (runActions interruptedStep captureNat permitNat permitNat [.pump, .pump]
        interruptedStart).execution.map Execution.mode = some .interrupted := by
  exact ⟨rfl, rfl, rfl, rfl⟩

def bank : Ledger Nat := ⟨Finsupp.single 0 20, 0⟩
def outer : Ledger Nat := reserved 0 1 (by decide) bank 12
def sibling : Ledger Nat := reserved 0 3 (by decide) outer 4
def inner : Ledger Nat := reserved 1 2 (by decide) sibling 6
def productionLedger : Ledger Nat :=
  Lease.ledgerOf C M price 2
    (advance (Lease.provider M price 2) C (Lease.price M price 2) 2
      (Lease.attachPacket C M price 2 inner start)).2
def nestedRefund : Ledger Nat :=
  (refundTransfer productionLedger 2 1 (by decide)).apply productionLedger
def deliveryLedger : Ledger Nat :=
  Lease.ledgerOf C M price 1
    (resume (Lease.provider M price 1) C (Lease.price M price 1) 3
      (first.1, Lease.attachOutcome C M price 1 nestedRefund first.2)).2
def outerRefund : Ledger Nat :=
  (refundTransfer deliveryLedger 1 0 (by decide)).apply deliveryLedger
def interruptionLedger : Ledger Nat :=
  Lease.ledgerOf C interruptedM interruptedPrice 3
    (advance (Lease.provider interruptedM interruptedPrice 3) C
      (Lease.price interruptedM interruptedPrice 3) 3
      (Lease.attachPacket C interruptedM interruptedPrice 3 outerRefund interruptedPacket)).2
def final : Ledger Nat :=
  (refundTransfer interruptionLedger 3 0 (by decide)).apply interruptionLedger

theorem actual_ledger_words :
    productionLedger = spendWord 2 [5, 0] inner ∧
      deliveryLedger = spendWord 1 [1, 1] nestedRefund ∧
      interruptionLedger = spendWord 3 [3, 0] outerRefund := by
  constructor
  · rw [productionLedger, Lease.advance_exact, Lease.ledgerOf_attachOutcome]
    rfl
  · constructor
    · rw [deliveryLedger, Lease.resume_exact, Lease.ledgerOf_attachOutcome]
      rfl
    · rw [interruptionLedger, Lease.advance_exact, Lease.ledgerOf_attachOutcome]
      rfl

theorem nested_shared_and_sibling_refunds_are_exact :
    productionLedger.spent = 5 ∧ productionLedger.balances 2 = 1 ∧
      nestedRefund.balances 1 = 7 ∧ deliveryLedger.spent = 7 ∧
      outerRefund.balances 0 = 9 ∧ interruptionLedger.spent = 10 ∧
      final.balances 0 = 10 ∧ final.balances 1 = 0 ∧ final.balances 2 = 0 ∧
      final.balances 3 = 0 ∧ final.spent = 10 := by
  simp only [actual_ledger_words.1, actual_ledger_words.2.1, actual_ledger_words.2.2,
    final, outerRefund, nestedRefund]
  norm_num [inner, sibling, outer, bank, reserved, reserveMovement, spendWord,
    refundTransfer, Spend.apply, Transfer.apply]

local notation "FuelRun" => Mettapedia.GSLT.Dynamics.ParallelFuelLease.Execution

private theorem reserve_funded (before : Ledger Nat) (parent child : Nat)
    (distinct : child ≠ parent) (upper : Nat) (available : (upper : ℤ) ≤ before.balances parent) :
    FuelRun before (reserved parent child distinct before upper) := by
  let receipt : Transfer.Receipt (reserveMovement parent child distinct upper) before :=
    ⟨⟨Nat.cast_nonneg _, available⟩⟩
  exact .cons (.transfer _ receipt) (.refl _)

/-- One shared balance funds nested production, two deliveries and an
interrupted sibling. Every real callback debit and each unused-credit refund
is an admitted transition, rather than an equation only about final sums. -/
theorem nested_shared_and_interrupted_execution_is_admitted :
    FuelRun bank final ∧ final.Nonnegative ∧ final.total = 20 := by
  have valid : bank.Nonnegative := by
    constructor
    · decide
    · intro owner
      by_cases same : owner = 0 <;> simp [bank, same]
  have outerRun : FuelRun bank outer :=
    reserve_funded bank 0 1 (by decide) 12 (by norm_num [bank])
  have siblingRun : FuelRun outer sibling :=
    reserve_funded outer 0 3 (by decide) 4 (by
      norm_num [outer, reserved, reserveMovement, Transfer.apply, bank])
  have innerRun : FuelRun sibling inner :=
    reserve_funded sibling 1 2 (by decide) 6 (by
      norm_num [sibling, outer, reserved, reserveMovement, Transfer.apply, bank])
  have productionRun : FuelRun inner productionLedger :=
    Lease.advance_admitted C M price 2 2 start inner (by
      rw [show (advance M C price 2 start).1 = 5 from rfl]
      norm_num [inner, sibling, outer, reserved, reserveMovement, Transfer.apply, bank])
  have productionValid := productionRun.nonnegative_preserved
    (innerRun.nonnegative_preserved (siblingRun.nonnegative_preserved
      (outerRun.nonnegative_preserved valid)))
  have nestedReturn : FuelRun productionLedger nestedRefund :=
    .cons (.transfer _ (refundReceipt productionLedger productionValid 2 1 (by decide))) (.refl _)
  have deliveryRun : FuelRun nestedRefund deliveryLedger :=
    Lease.resume_admitted C M price 1 3 first.1 first.2 nestedRefund (by
      rw [show (resume M C price 3 (first.1, first.2)).1 = 7 from rfl]
      change (7 : ℤ) - 5 ≤ nestedRefund.balances 1
      rw [nested_shared_and_sibling_refunds_are_exact.2.2.1]
      decide)
  have deliveryValid := deliveryRun.nonnegative_preserved
    (nestedReturn.nonnegative_preserved productionValid)
  have outerReturn : FuelRun deliveryLedger outerRefund :=
    .cons (.transfer _ (refundReceipt deliveryLedger deliveryValid 1 0 (by decide))) (.refl _)
  have interruptionRun : FuelRun outerRefund interruptionLedger :=
    Lease.advance_admitted C interruptedM interruptedPrice 3 3 interruptedPacket outerRefund (by
      rw [show (advance interruptedM C interruptedPrice 3 interruptedPacket).1 = 3 from rfl]
      simp only [outerRefund, actual_ledger_words.2.1, nestedRefund, actual_ledger_words.1]
      norm_num [inner, sibling, outer, reserved, reserveMovement, refundTransfer, spendWord,
        Spend.apply, Transfer.apply, bank])
  have interruptionValid := interruptionRun.nonnegative_preserved
    (outerReturn.nonnegative_preserved deliveryValid)
  have siblingReturn : FuelRun interruptionLedger final :=
    .cons (.transfer _ (refundReceipt interruptionLedger interruptionValid 3 0 (by decide))) (.refl _)
  have execution := outerRun.append (siblingRun.append (innerRun.append (productionRun.append
    (nestedReturn.append (deliveryRun.append (outerReturn.append
      (interruptionRun.append siblingReturn)))))))
  refine ⟨execution, execution.nonnegative_preserved valid, ?_⟩
  rw [execution.total_conserved]
  norm_num [bank, Ledger.total, Finsupp.sum_single_index]

theorem a_copied_positive_refund_is_refused :
    ¬ (refundTransfer productionLedger 2 1 (by decide)).Admissible nestedRefund :=
  Lease.positive_refund_not_replayable 2 productionLedger 1 (by decide)
    (by rw [nested_shared_and_sibling_refunds_are_exact.2.1]; decide)

theorem cancellation_keeps_the_surviving_delivery :
    let admitted := runActions serviceCohortStep captureNat permitNat permitNat
      [.pump, .pump] serviceCohort
    let retired := retireConsumer admitted (0 : Fin 2)
    let surviving := deliver permitNat retired (1 : Fin 2) ()
    retired.delivery.log.positions 0 = none ∧
      surviving.1 = .observed (.answer 0 2) ∧
      acceptedCount surviving.2 = 1 ∧ first.1 = 5 ∧
      productionLedger.spent = nestedRefund.spent := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

def ten : Ledger Nat := ⟨Finsupp.single 1 10, 0⟩
def once : Ledger Nat :=
  Lease.ledgerOf C M price 1
    (advance (Lease.provider M price 1) C (Lease.price M price 1) 5
      (Lease.attachPacket C M price 1 ten start)).2

theorem copied_predebit_balance_does_not_fund_a_second_run :
    Mettapedia.GSLT.Dynamics.ParallelFuelLease.Execution ten once ∧
      once.balances 1 = 3 ∧
      ¬ Mettapedia.GSLT.Dynamics.ParallelFuelLease.Execution once
        (spendWord 1 (Lease.charges C M price 5 start) once) := by
  have entered : Mettapedia.GSLT.Dynamics.ParallelFuelLease.Execution ten once :=
    Lease.advance_admitted C M price 1 5 start ten (by
      rw [show (advance M C price 5 start).1 = 7 from rfl]
      norm_num [ten])
  have balance : once.balances 1 = 3 := by
    rw [once, Lease.advance_balance]
    rw [show (advance M C price 5 start).1 = 7 from rfl]
    norm_num [ten]
  have validTen : ten.Nonnegative := by
    constructor
    · decide
    · intro owner
      by_cases same : owner = 1 <;> simp [ten, same]
  refine ⟨entered, balance, ?_⟩
  intro repeated
  have funded := (spendWord_execution_iff 1 (Lease.charges C M price 5 start) once
    (entered.nonnegative_preserved validTen)).mp repeated
  rw [balance] at funded
  change (7 : ℤ) ≤ 3 at funded
  omega

/-- Finite zero refuses the positive paid prefix. The ordinary unmetered
provider still executes it; zero is not a spelling for the unmetered profile. -/
theorem finite_zero_and_unmetered_are_distinct :
    (advance M C price 2 start).1 = 5 ∧
      ¬ Mettapedia.GSLT.Dynamics.ParallelFuelLease.Execution
        (⟨0, 0⟩ : Ledger Nat) (spendWord 1 (Lease.charges C M price 2 start) ⟨0, 0⟩) := by
  refine ⟨rfl, ?_⟩
  intro execution
  have valid : (⟨0, 0⟩ : Ledger Nat).Nonnegative := by simp [Ledger.Nonnegative]
  have funded := (spendWord_execution_iff 1 (Lease.charges C M price 2 start) ⟨0, 0⟩ valid).mp execution
  change (5 : ℤ) ≤ 0 at funded
  omega

private def trancheBank : Ledger Nat := ⟨Finsupp.single 0 7, 0⟩
private def trancheGrant : Ledger Nat := reserved 0 1 (by decide) trancheBank 5
private def tranchePrefix :=
  advance (Lease.provider M price 1) C (Lease.price M price 1) 2
    (Lease.attachPacket C M price 1 trancheGrant start)
private def trancheUsed : Ledger Nat := Lease.ledgerOf C M price 1 tranchePrefix.2
private def trancheCut := (Lease.forget M price 1).outcome C tranchePrefix.2
private def trancheMove : Transfer Nat := ⟨0, 1, by decide, 2⟩
private def trancheFunded : Ledger Nat := trancheMove.apply trancheUsed
private def trancheTail :=
  resume (Lease.provider M price 1) C (Lease.price M price 1) 3
    (tranchePrefix.1, Lease.attachOutcome C M price 1 trancheFunded trancheCut)

/-- An exhausted child can resume its exact retained source after a conserved
transfer. The first prefix is not replayed or paid twice; shared production
remains the common predecessor of both separately priced deliveries. -/
theorem conserved_tranche_resumes_the_same_execution :
    tranchePrefix.1 = 5 ∧ trancheUsed.balances 1 = 0 ∧ trancheUsed.spent = 5 ∧
      ¬ Mettapedia.GSLT.Dynamics.ParallelFuelLease.Execution trancheUsed
        (Lease.ledgerOf C M price 1
          (resume (Lease.provider M price 1) C (Lease.price M price 1) 3 tranchePrefix).2) ∧
      trancheMove.Admissible trancheUsed ∧
      trancheFunded.spent = trancheUsed.spent ∧
      trancheFunded.total = trancheUsed.total ∧
      (tranchePrefix.1, (Lease.forget M price 1).outcome C
        (Lease.attachOutcome C M price 1 trancheFunded trancheCut)) =
        (tranchePrefix.1, (Lease.forget M price 1).outcome C tranchePrefix.2) ∧
      (trancheTail.1, PrimitiveProgram.readOutcome
        (sourceStep serviceCohortStep captureNat permitNat permitNat)
        ((Lease.forget M price 1).outcome C trancheTail.2)) =
        (7, (.inl (.ok PUnit.unit),
          runActions serviceCohortStep captureNat permitNat permitNat actions serviceCohort)) ∧
      trancheTail.1 = tranchePrefix.1 + 2 ∧
      (Lease.ledgerOf C M price 1 trancheTail.2).spent = 7 ∧
      (Lease.ledgerOf C M price 1 trancheTail.2).balances 0 = 0 ∧
      (Lease.ledgerOf C M price 1 trancheTail.2).balances 1 = 0 ∧
      Mettapedia.GSLT.Dynamics.ParallelFuelLease.Execution trancheBank
        (Lease.ledgerOf C M price 1 trancheTail.2) ∧
      (Lease.ledgerOf C M price 1 trancheTail.2).total = trancheBank.total := by
  let final := Lease.ledgerOf C M price 1 trancheTail.2
  have prefixExact : tranchePrefix =
      (first.1, Lease.attachOutcome C M price 1 (spendWord 1 [5, 0] trancheGrant) first.2) := by
    rw [tranchePrefix, Lease.advance_exact]
    rfl
  have prefixPaid : tranchePrefix.1 = 5 := by rw [prefixExact]; rfl
  have usedExact : trancheUsed = spendWord 1 [5, 0] trancheGrant := by
    rw [trancheUsed, prefixExact, Lease.ledgerOf_attachOutcome]
  have cutExact : trancheCut = first.2 := by
    rw [trancheCut, prefixExact, Lease.forget_attachOutcome]
  have bankValid : trancheBank.Nonnegative := by
    constructor
    · decide
    · intro owner
      by_cases same : owner = 0 <;> simp [trancheBank, same]
  have grantReceipt : Transfer.Receipt (reserveMovement 0 1 (by decide) 5) trancheBank :=
    ⟨⟨by decide, by norm_num [trancheBank, reserveMovement]⟩⟩
  have granted : Mettapedia.GSLT.Dynamics.ParallelFuelLease.Execution trancheBank trancheGrant :=
    .cons (.transfer _ grantReceipt) (.refl _)
  have prefixRun : Mettapedia.GSLT.Dynamics.ParallelFuelLease.Execution trancheGrant trancheUsed :=
    Lease.advance_admitted C M price 1 2 start trancheGrant (by
      rw [show (advance M C price 2 start).1 = 5 from rfl]
      norm_num [trancheGrant, trancheBank, reserved, reserveMovement, Transfer.apply])
  have usedValid := prefixRun.nonnegative_preserved (granted.nonnegative_preserved bankValid)
  have exhausted : trancheUsed.balances 1 = 0 := by
    rw [usedExact]
    norm_num [trancheGrant, trancheBank, reserved, reserveMovement, spendWord, Spend.apply,
      Transfer.apply]
  have refused : ¬ Mettapedia.GSLT.Dynamics.ParallelFuelLease.Execution trancheUsed
      (Lease.ledgerOf C M price 1
        (resume (Lease.provider M price 1) C (Lease.price M price 1) 3 tranchePrefix).2) := by
    intro repeated
    have prefixRebuilt : tranchePrefix = (first.1, Lease.attachOutcome C M price 1 trancheUsed first.2) := by
      rw [prefixExact, usedExact]
    rw [prefixRebuilt, Lease.resume_exact, Lease.ledgerOf_attachOutcome] at repeated
    have affordable := (spendWord_execution_iff 1
      (Lease.suffixCharges C M price 3 first.2) trancheUsed usedValid).mp repeated
    rw [exhausted] at affordable
    change (2 : ℤ) ≤ 0 at affordable
    omega
  have transferReceipt : Transfer.Receipt trancheMove trancheUsed := by
    refine ⟨⟨by decide, ?_⟩⟩
    rw [usedExact]
    norm_num [trancheMove, trancheGrant, trancheBank, reserved, reserveMovement, spendWord,
      Spend.apply, Transfer.apply]
  have transferRun : Mettapedia.GSLT.Dynamics.ParallelFuelLease.Execution trancheUsed trancheFunded :=
    .cons (.transfer _ transferReceipt) (.refl _)
  have tailRun : Mettapedia.GSLT.Dynamics.ParallelFuelLease.Execution trancheFunded final := by
    apply Lease.resume_admitted C M price 1 3 tranchePrefix.1 trancheCut trancheFunded
    rw [prefixPaid, cutExact]
    change (7 : ℤ) - 5 ≤ trancheFunded.balances 1
    rw [trancheFunded, usedExact]
    norm_num [trancheMove, trancheGrant, trancheBank, reserved, reserveMovement, spendWord,
      Spend.apply, Transfer.apply]
  have full := granted.append (prefixRun.append (transferRun.append tailRun))
  have tailExact : trancheTail =
      (complete.1, Lease.attachOutcome C M price 1
        (spendWord 1 [1, 1] trancheFunded) complete.2) := by
    rw [trancheTail, prefixPaid, cutExact, Lease.resume_exact]
    rfl
  have finalExact : final = spendWord 1 [1, 1] trancheFunded := by
    dsimp only [final]
    rw [tailExact, Lease.ledgerOf_attachOutcome]
  refine ⟨prefixPaid, exhausted, ?_, refused, transferReceipt.admission, rfl,
    Transfer.total_apply _ _, ?_, ?_, ?_, ?_, ?_, ?_, full, full.total_conserved⟩
  · rw [usedExact]
    norm_num [trancheGrant, trancheBank, reserved, reserveMovement, spendWord, Spend.apply,
      Transfer.apply]
  · rw [Lease.forget_attachOutcome]
    rfl
  · rw [tailExact, Lease.forget_attachOutcome]
    exact (cursor_program serviceCohortStep captureNat permitNat permitNat 5 1 actions serviceCohort)
      |>.trans (by rfl)
  · rw [tailExact, prefixPaid]
    rfl
  · change final.spent = 7
    rw [finalExact, trancheFunded, usedExact]
    norm_num [trancheMove, trancheGrant, trancheBank, reserved, reserveMovement, spendWord,
      Spend.apply, Transfer.apply]
  · change final.balances 0 = 0
    rw [finalExact, trancheFunded, usedExact]
    norm_num [trancheMove, trancheGrant, trancheBank, reserved, reserveMovement, spendWord,
      Spend.apply, Transfer.apply]
  · change final.balances 1 = 0
    rw [finalExact, trancheFunded, usedExact]
    norm_num [trancheMove, trancheGrant, trancheBank, reserved, reserveMovement, spendWord,
      Spend.apply, Transfer.apply]


end Controls

end

end Accounting.LeaseExecution

end Mettapedia.Machines.Cursor.ProducerOccurrenceLog
