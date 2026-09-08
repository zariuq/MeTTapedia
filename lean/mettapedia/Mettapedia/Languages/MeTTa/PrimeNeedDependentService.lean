import Mettapedia.Languages.MeTTa.PrimeNeedCacheLaws
import Mettapedia.Languages.MeTTa.PrimeNeedExecutionMachine
import Mettapedia.TypeTheory.DisplayedEvidenceNeed

/-!
# Dependent services on the Prime Need machine

A service produces a reply in the family indexed by its complete immutable
request. Its first force uses the existing owned Need machine to evaluate and
commit a packed reply. A consumer resumes through that same machine, checks
the packet index, and only then exposes the reply at the requested fibre.
Subsequent demands observe the existing cache without invoking the producer.

The client supplies the full raw request, including any authority, revision,
context, and query coordinates on which its meaning depends. No key-only
sharing or transport across unequal requests is introduced. A finite check's
accepted and refused candidate outcomes can both be data in its reply family;
refusing a candidate is not a refutation of a logical proposition.

The producer is a total deterministic local action, not an unbounded search
oracle. The exact transition counts describe the surrounding Need protocol,
not the native cost of producing a reply. No evaluator or type profile is
replaced by this instance.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeNeedDependentService

open PrimeNeedReference
open Mettapedia.TypeTheory.DisplayedEvidence

universe uRaw uExact

variable (family : Family.{uRaw, uExact})

/-- Reuse the existing displayed-evidence packet, including its exact index. -/
abbrev Packet := Mettapedia.TypeTheory.DisplayedEvidenceNeed.PackedEvidence family

/-- An operational request mismatch, not a logical refutation. -/
structure IndexMismatch where
  expected : family.Raw
  actual : family.Raw

abbrev Outcome := Produced (Packet family) Empty (IndexMismatch family)

/-- Project only after the complete request indices agree. -/
def project? [DecidableEq family.Raw] (expected : family.Raw)
    (packet : Packet family) : Option (family.Exact expected) :=
  if same : packet.1 = expected then
    some (cast (congrArg family.Exact same) packet.2)
  else none

@[simp] theorem project?_matching [DecidableEq family.Raw]
    (request : family.Raw) (reply : family.Exact request) :
    project? family request ⟨request, reply⟩ = some reply := by
  simp [project?]

theorem project?_mismatched [DecidableEq family.Raw]
    {expected actual : family.Raw} (different : actual ≠ expected)
    (reply : family.Exact actual) :
    project? family expected ⟨actual, reply⟩ = none := by
  simp [project?, different]

/-- Successful projection retains the exact dependent packet, not only its tag. -/
theorem project?_sound [DecidableEq family.Raw]
    {expected : family.Raw} {packet : Packet family} {reply : family.Exact expected}
    (projected : project? family expected packet = some reply) :
    packet = ⟨expected, reply⟩ := by
  rcases packet with ⟨actual, value⟩
  unfold project? at projected
  split at projected
  · rename_i same
    change actual = expected at same
    subst actual
    simp only [cast_eq, Option.some.injEq] at projected
    subst reply
    rfl
  · cases projected

/-- A resumed consumer validates the packet before returning its dependent reply. -/
def consumeOutcome [DecidableEq family.Raw] (expected : family.Raw) :
    Outcome family → Outcome family
  | .value packet =>
      match project? family expected packet with
      | some reply => .value ⟨expected, reply⟩
      | none => .retryableFault (.domain ⟨expected, packet.1⟩)
  | .stableFault impossible => nomatch impossible
  | .retryableFault reason => .retryableFault reason

@[simp] theorem consumeOutcome_matching [DecidableEq family.Raw]
    (request : family.Raw) (reply : family.Exact request) :
    consumeOutcome family request (.value ⟨request, reply⟩) =
      .value ⟨request, reply⟩ := by
  simp [consumeOutcome]

theorem consumeOutcome_mismatched [DecidableEq family.Raw]
    {expected actual : family.Raw} (different : actual ≠ expected)
    (reply : family.Exact actual) :
    consumeOutcome family expected (.value ⟨actual, reply⟩) =
      .retryableFault (.domain ⟨expected, actual⟩) := by
  simp [consumeOutcome, project?_mismatched family different reply]

inductive Rule where
  | produce
  deriving DecidableEq, Repr

/-- Service entry and consumption are states of the existing Need machine. -/
inductive Local where
  | produce (request : family.Raw)
  | demand (expected : family.Raw) (cell : CellId)
  | output (outcome : Outcome family)

abbrev ServiceWorld :=
  World family.Raw Rule (Packet family) Empty (IndexMismatch family) Empty

abbrev ServiceMachine :=
  Machine family.Raw (Local family) family.Raw Rule (Packet family) Empty
    (IndexMismatch family) Empty

/-- The only producer invocation is the local `produce` action. The core
machine owns allocation, the evaluating owner, commit, cache lookup and receipts. -/
def spec [DecidableEq family.Raw] (producer : (request : family.Raw) → family.Exact request) :
    Spec family.Raw (Local family) family.Raw Rule (Packet family) Empty
      (IndexMismatch family) Empty where
  alternatives request := [(.produce, .produce request)]
  action
    | .produce request => .done (.value ⟨request, producer request⟩)
    | .demand expected cell => .demand cell expected
    | .output outcome => .done outcome
  afterDemand expected outcome := .output (consumeOutcome family expected outcome)
  afterAllocation expected cell := .demand expected cell

/-- The exact world at the unique suspended-force successor. -/
def forceWorld (world : ServiceWorld family) (cell : CellId) (request : family.Raw) :
    ServiceWorld family :=
  let base := { world with nextEvaluator := world.nextEvaluator + 1 }
  recorded
    (recorded
      ((base.fork 0).setKnownCache cell ⟨request, .suspended⟩
        (.evaluating world.nextEvaluator))
      (.evaluate cell world.nextEvaluator))
    (.chooseRule cell .produce)

/-- The exact owner-matched commit-and-observe world. -/
def commitWorld (world : ServiceWorld family) (cell : CellId) (request : family.Raw)
    (owner : EvaluatorId) (packet : Packet family) : ServiceWorld family :=
  recorded (world.setKnownCache cell ⟨request, .evaluating owner⟩ (.value packet))
    (.observe cell (.value packet))

def producedWorld (producer : (request : family.Raw) → family.Exact request)
    (world : ServiceWorld family) (cell : CellId) (request : family.Raw) :
    ServiceWorld family :=
  commitWorld family (forceWorld family world cell request) cell request world.nextEvaluator
    ⟨request, producer request⟩

def freshForceWork (work : Work) : Work :=
  ((work.bump 1 1 2 0).bump 0 0 0 0).bump 1 1 1 0

def consumerFinishWork (work : Work) : Work :=
  ((work.bump 0 0 0 0).bump 0 0 0 0).bump 0 0 0 0

@[simp] theorem forceWorld_lookup (world : ServiceWorld family) (cell : CellId)
    (request : family.Raw) :
    (forceWorld family world cell request).heap.lookup cell =
      some ⟨request, .evaluating world.nextEvaluator⟩ := by
  simp only [forceWorld, PrimeNeedCacheLaws.recorded_heap, World.setKnownCache,
    Heap.setKnownCache_lookup_same]

@[simp] theorem producedWorld_lookup
    (producer : (request : family.Raw) → family.Exact request)
    (world : ServiceWorld family) (cell : CellId) (request : family.Raw) :
    (producedWorld family producer world cell request).heap.lookup cell =
      some ⟨request, .value ⟨request, producer request⟩⟩ := by
  simp only [producedWorld, commitWorld, PrimeNeedCacheLaws.recorded_heap,
    World.setKnownCache, Heap.setKnownCache_lookup_same]

section Runs

variable [DecidableEq family.Raw]
    (producer : (request : family.Raw) → family.Exact request)

theorem step_force_suspended {world : ServiceWorld family} {cell : CellId}
    {request : family.Raw} {stack : List (Frame family.Raw)} {work : Work}
    (suspended : world.heap.lookup cell = some ⟨request, .suspended⟩) :
    step (spec family producer) (⟨world, .force cell stack, work⟩ : ServiceMachine family) =
      [⟨forceWorld family world cell request,
        .run (.produce request) (.commit cell world.nextEvaluator :: stack),
        work.bump 1 1 2 0⟩] := by
  simp [step, spec, suspended, branchAlternatives, forceWorld, finished]

theorem step_produce (world : ServiceWorld family) (request : family.Raw)
    (stack : List (Frame family.Raw)) (work : Work) :
    step (spec family producer) (⟨world, .run (.produce request) stack, work⟩ :
      ServiceMachine family) =
      [⟨world, .returned (.value ⟨request, producer request⟩) stack,
        work.bump 0 0 0 0⟩] := rfl

theorem step_commit {world : ServiceWorld family} {cell : CellId} {request : family.Raw}
    {owner : EvaluatorId} {packet : Packet family} {stack : List (Frame family.Raw)}
    {work : Work} (owned : world.heap.lookup cell = some ⟨request, .evaluating owner⟩) :
    step (spec family producer)
      (⟨world, .returned (.value packet) (.commit cell owner :: stack), work⟩ :
        ServiceMachine family) =
      [⟨commitWorld family world cell request owner packet,
        .returned (.value packet) stack, work.bump 1 1 1 0⟩] := by
  simp [step, owned, commitWorld, finished]

/-- Every suspended service cell returns and caches the exact producer packet
in three actual machine transitions, under an arbitrary continuation stack. -/
theorem fresh_force_returns {world : ServiceWorld family} {cell : CellId}
    {request : family.Raw} (stack : List (Frame family.Raw)) (work : Work)
    (suspended : world.heap.lookup cell = some ⟨request, .suspended⟩) :
    UniqueSteps (spec family producer) 3
      (⟨world, .force cell stack, work⟩ : ServiceMachine family)
      ⟨producedWorld family producer world cell request,
        .returned (.value ⟨request, producer request⟩) stack, freshForceWork work⟩ := by
  apply UniqueSteps.cons (step_force_suspended family producer suspended)
  apply UniqueSteps.cons (step_produce family producer _ _ _ _)
  apply UniqueSteps.cons (step_commit family producer (forceWorld_lookup family world cell request))
  exact UniqueSteps.refl _

/-- Forcing an already cached reply observes it in one transition. In
particular the producer and its local action are not invoked. -/
theorem cached_force_returns {world : ServiceWorld family} {cell : CellId}
    {origin : family.Raw} {packet : Packet family}
    (stack : List (Frame family.Raw)) (work : Work)
    (cached : world.heap.lookup cell = some ⟨origin, .value packet⟩) :
    UniqueSteps (spec family producer) 1
      (⟨world, .force cell stack, work⟩ : ServiceMachine family)
      ⟨recorded world (.observe cell (.value packet)),
        .returned (.value packet) stack, work.bump 1 0 1 0⟩ := by
  apply UniqueSteps.cons
    (PrimeNeedCacheLaws.force_cached_value_step (spec family producer) _ rfl cached)
  exact UniqueSteps.refl _

/-- The consumer index check is executed by the machine's resume path. -/
theorem resume_and_halt (world : ServiceWorld family) (expected : family.Raw)
    (outcome : Outcome family) (work : Work) :
    UniqueSteps (spec family producer) 3
      (⟨world, .returned outcome [.resume expected], work⟩ : ServiceMachine family)
      ⟨world, .halted (consumeOutcome family expected outcome), consumerFinishWork work⟩ := by
  apply UniqueSteps.cons (by rfl)
  apply UniqueSteps.cons (by rfl)
  apply UniqueSteps.cons (by rfl)
  exact UniqueSteps.refl _

/-- A first demanded consumer checks, caches, projects and returns the reply. -/
theorem fresh_consumer_run {world : ServiceWorld family} {cell : CellId}
    {request : family.Raw} (work : Work)
    (suspended : world.heap.lookup cell = some ⟨request, .suspended⟩) :
    UniqueSteps (spec family producer) 7
      (⟨world, .run (.demand request cell) [], work⟩ : ServiceMachine family)
      ⟨producedWorld family producer world cell request,
        .halted (.value ⟨request, producer request⟩),
        consumerFinishWork (freshForceWork (work.bump 0 0 0 0))⟩ := by
  apply UniqueSteps.cons (by rfl)
  have forced := fresh_force_returns family producer [.resume request]
    (work.bump 0 0 0 0) suspended
  have resumed := resume_and_halt family producer
    (producedWorld family producer world cell request) request
    (.value ⟨request, producer request⟩) (freshForceWork (work.bump 0 0 0 0))
  simpa only [consumeOutcome_matching, finished] using
    UniqueSteps.trans (spec family producer) forced resumed

/-- All cached consumer outcomes are exact, including request-index failures. -/
theorem cached_consumer_run {world : ServiceWorld family} {cell : CellId}
    {origin : family.Raw} {packet : Packet family} (expected : family.Raw) (work : Work)
    (cached : world.heap.lookup cell = some ⟨origin, .value packet⟩) :
    UniqueSteps (spec family producer) 5
      (⟨world, .run (.demand expected cell) [], work⟩ : ServiceMachine family)
      ⟨recorded world (.observe cell (.value packet)),
        .halted (consumeOutcome family expected (.value packet)),
        consumerFinishWork ((work.bump 0 0 0 0).bump 1 0 1 0)⟩ := by
  apply UniqueSteps.cons (by rfl)
  exact UniqueSteps.trans (spec family producer)
    (cached_force_returns family producer [.resume expected] (work.bump 0 0 0 0) cached)
    (resume_and_halt family producer _ expected (.value packet) _)

/-- Exact frontier equality for a first consumer demand, not only reachability. -/
theorem fresh_consumer_runFrontier {world : ServiceWorld family} {cell : CellId}
    {request : family.Raw} (work : Work)
    (suspended : world.heap.lookup cell = some ⟨request, .suspended⟩) :
    runFrontier (spec family producer) 7
      [(⟨world, .run (.demand request cell) [], work⟩ : ServiceMachine family)] =
      [⟨producedWorld family producer world cell request,
        .halted (.value ⟨request, producer request⟩),
        consumerFinishWork (freshForceWork (work.bump 0 0 0 0))⟩] :=
  UniqueSteps.runFrontier_eq (spec family producer)
    (fresh_consumer_run family producer work suspended)

theorem cached_consumer_runFrontier {world : ServiceWorld family} {cell : CellId}
    {origin : family.Raw} {packet : Packet family} (expected : family.Raw) (work : Work)
    (cached : world.heap.lookup cell = some ⟨origin, .value packet⟩) :
    runFrontier (spec family producer) 5
      [(⟨world, .run (.demand expected cell) [], work⟩ : ServiceMachine family)] =
      [⟨recorded world (.observe cell (.value packet)),
        .halted (consumeOutcome family expected (.value packet)),
        consumerFinishWork ((work.bump 0 0 0 0).bump 1 0 1 0)⟩] :=
  UniqueSteps.runFrontier_eq (spec family producer)
    (cached_consumer_run family producer expected work cached)

/-- A cached packet from another complete request is not silently projected. -/
theorem mismatched_consumer_run {world : ServiceWorld family} {cell : CellId}
    {origin expected actual : family.Raw} (reply : family.Exact actual) (work : Work)
    (different : actual ≠ expected)
    (cached : world.heap.lookup cell = some ⟨origin, .value ⟨actual, reply⟩⟩) :
    runFrontier (spec family producer) 5
      [(⟨world, .run (.demand expected cell) [], work⟩ : ServiceMachine family)] =
      [⟨recorded world (.observe cell (.value ⟨actual, reply⟩)),
        .halted (.retryableFault (.domain ⟨expected, actual⟩)),
        consumerFinishWork ((work.bump 0 0 0 0).bump 1 0 1 0)⟩] := by
  simpa only [consumeOutcome_mismatched family different reply] using
    cached_consumer_runFrontier family producer expected work cached

/-- Completed packets remain unchanged through every subsequent execution. -/
theorem completed_packet_retained {length : Nat} {initial final : ServiceMachine family}
    (execution : Steps (spec family producer) length initial final)
    {cell : CellId} {origin : family.Raw} {packet : Packet family}
    (cached : initial.world.heap.lookup cell = some ⟨origin, .value packet⟩) :
    final.world.heap.lookup cell = some ⟨origin, .value packet⟩ :=
  PrimeNeedCacheLaws.steps_preserve_completed (spec family producer) execution cached (.value packet)

/-- The answer-only execution carrier inherits the exact service answer bag. -/
theorem answers_erasure (fuel : Nat) (machine : ServiceMachine family) :
    PrimeNeedExecution.answers (spec family producer) fuel
        (PrimeNeedExecution.eraseMachine machine) =
      answers (spec family producer) fuel machine :=
  PrimeNeedExecution.answers_commute (spec family producer) fuel machine

end Runs

/-- Cached consumption is independent of the producer function. This is the
saved-invocation boundary, not a constant-time native checking claim. -/
theorem cached_consumer_independent_of_producer [DecidableEq family.Raw]
    (first second : (request : family.Raw) → family.Exact request)
    {world : ServiceWorld family} {cell : CellId} {origin : family.Raw}
    {packet : Packet family} (expected : family.Raw) (work : Work)
    (cached : world.heap.lookup cell = some ⟨origin, .value packet⟩) :
    runFrontier (spec family first) 5
        [(⟨world, .run (.demand expected cell) [], work⟩ : ServiceMachine family)] =
      runFrontier (spec family second) 5
        [(⟨world, .run (.demand expected cell) [], work⟩ : ServiceMachine family)] := by
  rw [cached_consumer_runFrontier family first expected work cached,
    cached_consumer_runFrontier family second expected work cached]

#print axioms project?_sound
#print axioms project?_mismatched
#print axioms fresh_force_returns
#print axioms fresh_consumer_runFrontier
#print axioms cached_consumer_runFrontier
#print axioms mismatched_consumer_run
#print axioms completed_packet_retained
#print axioms answers_erasure
#print axioms cached_consumer_independent_of_producer

end Mettapedia.Languages.MeTTa.PrimeNeedDependentService
