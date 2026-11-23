/-!
# Reusing a completed empty-queue observation

An owned gateway is the only admitted writer of its queue. Its producer
distinguishes an exhausted pending queue from an expired head: the latter
changes the queue without claiming a job, and can leave more work behind.

This model projects the ordered pending jobs, not every durable job record.
Every operation that may change the projection invalidates the observation.
Reusing a quiet observation preserves the producer's answer and pending jobs;
it cannot grant dispatch authority. Generation and ownership changes count as
invalidations even when their logical projection happens to stay equal.

These are abstract protocol contracts, not an implementation refinement proof.
-/

set_option autoImplicit false

namespace Mettapedia.Protocols.Agents.GatewayQuietPolling

structure Job where
  id : Nat
  expired : Bool
  deriving DecidableEq, Repr

inductive Observation where
  | exhausted
  | expired (id : Nat)
  | claimed (id : Nat)
  deriving DecidableEq, Repr

/-- Actual head transitions distinguish a completed absence from progress. -/
def producer : List Job → List Job × Observation
  | [] => ([], .exhausted)
  | job :: rest => (rest, if job.expired then .expired job.id else .claimed job.id)

structure State where
  pending : List Job
  generation : Nat
  quiet : Option Nat
  deriving DecidableEq, Repr

def Valid (s : State) : Prop := s.quiet = some s.generation → s.pending = []

/-- Every potentially changing operation, including reopen, invalidates first. -/
def mutate (s : State) (pending : List Job) : State :=
  { pending, generation := s.generation + 1, quiet := none }

def observe (s : State) : State × Observation :=
  match s.pending with
  | [] => ({ s with quiet := some s.generation }, .exhausted)
  | job :: rest =>
    (mutate s rest, if job.expired then .expired job.id else .claimed job.id)

def poll (s : State) : State × Observation :=
  if s.quiet = some s.generation then (s, .exhausted) else observe s

theorem exhausted_iff_empty (pending : List Job) :
    (producer pending).2 = .exhausted ↔ pending = [] := by
  cases pending with
  | nil => simp [producer]
  | cons job rest => cases h : job.expired <;> simp [producer, h]

theorem mutation_invalidates (s : State) (pending : List Job) :
    (mutate s pending).quiet = none := rfl

theorem mutation_valid (s : State) (pending : List Job) : Valid (mutate s pending) := by
  simp [Valid, mutate]

theorem observation_valid (s : State) : Valid (observe s).1 := by
  cases h : s.pending with
  | nil => simp [observe, h, Valid]
  | cons job rest => cases job.expired <;> simp [observe, h, mutate, Valid]

theorem poll_valid (s : State) (hs : Valid s) : Valid (poll s).1 := by
  by_cases h : s.quiet = some s.generation
  · simpa [poll, h] using hs
  · simpa [poll, h] using observation_valid s

theorem poll_observation_agrees (s : State) (hs : Valid s) :
    (poll s).2 = (producer s.pending).2 := by
  by_cases h : s.quiet = some s.generation
  · simp [poll, h, hs h, producer]
  · cases hp : s.pending with
    | nil => simp [poll, h, observe, hp, producer]
    | cons job rest => simp [poll, h, observe, hp, producer]

theorem poll_pending_agrees (s : State) (hs : Valid s) :
    (poll s).1.pending = (producer s.pending).1 := by
  by_cases h : s.quiet = some s.generation
  · simp [poll, h, hs h, producer]
  · cases hp : s.pending with
    | nil => simp [poll, h, observe, hp, producer]
    | cons job rest => simp [poll, h, observe, hp, producer, mutate]

def enqueue (s : State) (job : Job) : State := mutate s (s.pending ++ [job])

theorem fresh_submission_is_seen (s : State) (job : Job)
    (empty : s.pending = []) (ready : job.expired = false) :
    (poll (enqueue s job)).2 = .claimed job.id := by
  simp [poll, enqueue, mutate, empty, observe, ready]

def noClaim : Observation → Bool
  | .claimed _ => false
  | _ => true

/-- A no-claim result from expiry cannot authorize an empty-queue shortcut. -/
theorem no_claim_does_not_mean_exhausted :
    let pending := [Job.mk 1 true, Job.mk 2 false]
    noClaim (producer pending).2 = true ∧ (producer pending).1 ≠ [] := by
  decide

theorem expiry_leaves_the_next_ready_job_visible :
    let s : State := { pending := [Job.mk 1 true, Job.mk 2 false], generation := 0, quiet := none }
    (poll s).2 = .expired 1 ∧ (poll (poll s).1).2 = .claimed 2 := by
  decide

inductive Event where
  | change (pending : List Job)
  | poll

def step (s : State) : Event → State
  | .change pending => mutate s pending
  | .poll => (poll s).1

theorem step_valid (s : State) (hs : Valid s) (event : Event) : Valid (step s event) := by
  cases event with
  | change pending => exact mutation_valid s pending
  | poll => exact poll_valid s hs

theorem run_valid (s : State) (hs : Valid s) (events : List Event) :
    Valid (events.foldl step s) := by
  induction events generalizing s with
  | nil => exact hs
  | cons event rest ih => exact ih (step s event) (step_valid s hs event)

end Mettapedia.Protocols.Agents.GatewayQuietPolling

namespace Mettapedia.Protocols.Agents.GatewayQuietPolling.Metadata

/- A byte-frame shortcut is sound only after the normal decoder identified a
configuration-only read. Equality is of the entire frame, not a token found in
an effect's payload. The decoder is abstract; its agreement with a host JSON
parser is an implementation obligation, not an assumption discharged here. -/
inductive Request where
  | tools
  | submit (job : Job)
  | claim
  deriving DecidableEq

inductive Reply where
  | metadata (configuration : Nat)
  | submitted (id : Nat)
  | claimed (result : Observation)
  | invalid
  deriving DecidableEq

structure Cache where
  configuration : Nat
  frame : List UInt8

def dispatch (decode : List UInt8 → Option Request) (configuration : Nat)
    (frame : List UInt8) (s : State) : State × Reply :=
  match decode frame with
  | some .tools => (s, .metadata configuration)
  | some (.submit job) => (enqueue s job, .submitted job.id)
  | some .claim => let result := observe s; (result.1, .claimed result.2)
  | none => (s, .invalid)

def route (decode : List UInt8 → Option Request) (configuration : Nat)
    (cache : Cache) (frame : List UInt8) (s : State) : State × Reply :=
  if configuration = cache.configuration ∧ frame = cache.frame then
    (s, .metadata cache.configuration)
  else dispatch decode configuration frame s

theorem exact_validated_frame_refines (decode : List UInt8 → Option Request)
    (configuration : Nat) (cache : Cache) (frame : List UInt8) (s : State)
    (validated : decode cache.frame = some .tools) :
    route decode configuration cache frame s = dispatch decode configuration frame s := by
  by_cases h : configuration = cache.configuration ∧ frame = cache.frame
  · rcases h with ⟨hc, hf⟩
    simp [route, hc, hf, dispatch, validated]
  · simp [route, h]

theorem changed_configuration_uses_normal_dispatch (decode : List UInt8 → Option Request)
    (configuration : Nat) (cache : Cache) (frame : List UInt8) (s : State)
    (changed : configuration ≠ cache.configuration) :
    route decode configuration cache frame s = dispatch decode configuration frame s := by
  simp [route, changed]

theorem submit_cannot_hit_validated_metadata (decode : List UInt8 → Option Request)
    (configuration : Nat) (cache : Cache) (frame : List UInt8) (s : State) (job : Job)
    (validated : decode cache.frame = some .tools)
    (submitted : decode frame = some (.submit job)) :
    route decode configuration cache frame s = (enqueue s job, .submitted job.id) := by
  rw [exact_validated_frame_refines decode configuration cache frame s validated]
  simp [dispatch, submitted]

theorem truncated_frame_uses_normal_dispatch (decode : List UInt8 → Option Request)
    (configuration : Nat) (cache : Cache) (partialFrame : List UInt8) (s : State)
    (shorter : partialFrame.length < cache.frame.length) :
    route decode configuration cache partialFrame s = dispatch decode configuration partialFrame s := by
  have different : partialFrame ≠ cache.frame := by
    intro equal
    subst partialFrame
    exact Nat.lt_irrefl _ shorter
  simp [route, different]

end Mettapedia.Protocols.Agents.GatewayQuietPolling.Metadata
