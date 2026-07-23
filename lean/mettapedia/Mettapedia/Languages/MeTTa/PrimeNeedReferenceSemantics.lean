import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
# Prime Need reference semantics

This module gives the theorem-bearing core of Prime's call-by-need machine.
It is intentionally smaller than the full language evaluator, but the
semantic mechanisms that must not be delegated to a host-language oracle are
already explicit:

* stable Need-cell identity, including allocation lineage and generation;
* persistent branch-local heaps with immutable origins;
* call-time choice as branching while a cell is being evaluated;
* cached values and stable faults versus uncached retryable faults;
* deliberate resampling into a fresh cell;
* exact list multiplicity of alternatives;
* effect and observation events in a causal receipt DAG; and
* an explicit machine-work account.

The language-facing `Spec` supplies rule alternatives and deterministic local
actions.  It does not choose worlds, allocate cells, cache outcomes, classify
machine faults, or construct receipts.  Consequently a language instance
cannot accidentally implement run-time choice while claiming call-time
choice, nor can it hide multiplicity in a set-valued oracle.

`Heap.current` is an abstract finite-map observation and `Heap.spine` is its
explicit persistent update history.  A native implementation may refine the
current map to a hash table, trie, or compact arena index; the reference
machine therefore counts one semantic lookup rather than assuming that a
particular linked representation is constant-time.
-/

namespace Mettapedia.Languages.MeTTa.PrimeNeedReference

abbrev WorldPath := List Nat
abbrev LineageId := Nat
abbrev EvaluatorId := Nat

/-- Cells allocated before a branch retain their identity in all descendants.
Cells allocated after a branch include that branch in `birth`, so sibling
allocations cannot be confused.  `generation` distinguishes deliberate
resampling from ordinary sharing. -/
structure CellId where
  lineage : LineageId
  birth : WorldPath
  slot : Nat
  generation : Nat
deriving DecidableEq, Repr

/-- Event identifiers are local to a branch path.  Equal inherited events keep
their identifiers; new events in sibling branches are necessarily distinct. -/
structure ReceiptId where
  world : WorldPath
  serial : Nat
deriving DecidableEq, Repr

/-- Machine-owned retry causes.  Domain-specific retryable failures occupy
only the `domain` constructor; blackholes and scope failures cannot be hidden
inside a language instance. -/
inductive RetryReason (RetryableFault : Type*) where
  | domain (fault : RetryableFault)
  | blackhole (cell : CellId)
  | outOfScope (cell : CellId)
  | noRule (cell : CellId)
  | ownershipLost (cell : CellId) (expected actual : EvaluatorId)
  | allocationCollision (cell : CellId)
deriving DecidableEq, Repr

/-- Outcomes preserve the stable/retryable distinction.  Only values and
stable faults may enter a Need-cell cache. -/
inductive Produced (Value StableFault RetryableFault : Type*) where
  | value (value : Value)
  | stableFault (fault : StableFault)
  | retryableFault (reason : RetryReason RetryableFault)
deriving DecidableEq, Repr

/-- A cell cache mirrors the native four-state protocol. -/
inductive Cache (Value StableFault : Type*) where
  | suspended
  | evaluating (owner : EvaluatorId)
  | value (value : Value)
  | stableFault (fault : StableFault)
deriving DecidableEq, Repr

structure CellRecord (Origin Value StableFault : Type*) where
  origin : Origin
  cache : Cache Value StableFault
deriving DecidableEq, Repr

/-- The update history is semantic data rather than an implementation trace:
it records which stable cell was allocated or had its cache changed. -/
inductive HeapUpdate (Origin Value StableFault : Type*) where
  | allocate (cell : CellId) (origin : Origin)
  | cache (cell : CellId) (state : Cache Value StableFault)
deriving DecidableEq, Repr

/-- Persistent heap state.  `current` is the extensional map used by the
machine; `spine` retains the newest-first update history needed by the later
cost/refinement proof. -/
structure Heap (Origin Value StableFault : Type*) where
  current : CellId → Option (CellRecord Origin Value StableFault)
  spine : List (HeapUpdate Origin Value StableFault)

namespace Heap

variable {Origin Value StableFault : Type*}

def empty : Heap Origin Value StableFault where
  current := fun _ => none
  spine := []

def lookup (heap : Heap Origin Value StableFault) (cell : CellId) :
    Option (CellRecord Origin Value StableFault) :=
  heap.current cell

/-- Allocation is fail-closed.  It cannot shadow a live cell identifier. -/
def allocate? (heap : Heap Origin Value StableFault) (cell : CellId)
    (origin : Origin) : Option (Heap Origin Value StableFault) :=
  match heap.lookup cell with
  | some _ => none
  | none =>
      let record : CellRecord Origin Value StableFault :=
        { origin := origin, cache := .suspended }
      some
        { current := Function.update heap.current cell (some record)
          spine := .allocate cell origin :: heap.spine }

/-- Internal cache replacement takes the record obtained by the preceding
lookup.  Reusing that record is what makes origin immutability structural. -/
def setKnownCache (heap : Heap Origin Value StableFault) (cell : CellId)
    (record : CellRecord Origin Value StableFault)
    (state : Cache Value StableFault) :
    Heap Origin Value StableFault :=
  { current :=
      Function.update heap.current cell
        (some { record with cache := state })
    spine := .cache cell state :: heap.spine }

@[simp] theorem empty_lookup (cell : CellId) :
    (empty : Heap Origin Value StableFault).lookup cell = none :=
  rfl

theorem allocate?_lookup_same
    {heap next : Heap Origin Value StableFault}
    {cell : CellId} {origin : Origin}
    (h : heap.allocate? cell origin = some next) :
    next.lookup cell =
      some { origin := origin, cache := Cache.suspended } := by
  unfold allocate? at h
  split at h
  · contradiction
  · simp only [Option.some.injEq] at h
    subst next
    simp [lookup]

theorem allocate?_preserves_other
    {heap next : Heap Origin Value StableFault}
    {cell other : CellId} {origin : Origin}
    (hAllocate : heap.allocate? cell origin = some next)
    (hOther : other ≠ cell) :
    next.lookup other = heap.lookup other := by
  unfold allocate? at hAllocate
  split at hAllocate
  · contradiction
  · simp only [Option.some.injEq] at hAllocate
    subst next
    simp [lookup, hOther]

@[simp] theorem setKnownCache_lookup_same
    (heap : Heap Origin Value StableFault) (cell : CellId)
    (record : CellRecord Origin Value StableFault)
    (state : Cache Value StableFault) :
    (heap.setKnownCache cell record state).lookup cell =
      some { record with cache := state } := by
  simp [setKnownCache, lookup]

/-- Cache updates cannot rewrite a cell origin. -/
theorem setKnownCache_preserves_origin
    (heap : Heap Origin Value StableFault) (cell : CellId)
    (record : CellRecord Origin Value StableFault)
    (state : Cache Value StableFault) :
    ((heap.setKnownCache cell record state).lookup cell).map
        CellRecord.origin =
      some record.origin := by
  simp

theorem setKnownCache_preserves_other
    (heap : Heap Origin Value StableFault) {cell other : CellId}
    (record : CellRecord Origin Value StableFault)
    (state : Cache Value StableFault) (hOther : other ≠ cell) :
    (heap.setKnownCache cell record state).lookup other =
      heap.lookup other := by
  simp [setKnownCache, lookup, hOther]

end Heap

/-- Receipt payloads are semantic observations and effects, not every
evaluator instruction. -/
inductive ReceiptPayload
    (Origin Rule Value StableFault RetryableFault Effect : Type*) where
  | allocate (cell : CellId) (origin : Origin)
  | evaluate (cell : CellId) (owner : EvaluatorId)
  | chooseRule (cell : CellId) (rule : Rule)
  | observe (cell : CellId)
      (outcome : Produced Value StableFault RetryableFault)
  | retry (cell : CellId) (reason : RetryReason RetryableFault)
  | resample (source fresh : CellId)
  | effect (effect : Effect)
deriving DecidableEq, Repr

structure ReceiptNode
    (Origin Rule Value StableFault RetryableFault Effect : Type*) where
  id : ReceiptId
  parents : List ReceiptId
  payload :
    ReceiptPayload Origin Rule Value StableFault RetryableFault Effect
deriving DecidableEq, Repr

/-- `roots` is the exact current causal frontier.  Appending a node makes the
old roots its parents; inherited nodes remain shared across branch worlds. -/
structure ReceiptGraph
    (Origin Rule Value StableFault RetryableFault Effect : Type*) where
  nodes :
    List (ReceiptNode Origin Rule Value StableFault RetryableFault Effect)
  roots : List ReceiptId
  nextSerial : Nat
deriving DecidableEq, Repr

namespace ReceiptGraph

variable {Origin Rule Value StableFault RetryableFault Effect : Type*}

def empty :
    ReceiptGraph Origin Rule Value StableFault RetryableFault Effect where
  nodes := []
  roots := []
  nextSerial := 0

def append
    (graph :
      ReceiptGraph Origin Rule Value StableFault RetryableFault Effect)
    (path : WorldPath)
    (payload :
      ReceiptPayload Origin Rule Value StableFault RetryableFault Effect) :
    ReceiptGraph Origin Rule Value StableFault RetryableFault Effect ×
      ReceiptId :=
  let id : ReceiptId := { world := path, serial := graph.nextSerial }
  let node :
      ReceiptNode Origin Rule Value StableFault RetryableFault Effect :=
    { id := id, parents := graph.roots, payload := payload }
  ( { nodes := node :: graph.nodes
      roots := [id]
      nextSerial := graph.nextSerial + 1 },
    id )

@[simp] theorem append_roots
    (graph :
      ReceiptGraph Origin Rule Value StableFault RetryableFault Effect)
    (path : WorldPath)
    (payload :
      ReceiptPayload Origin Rule Value StableFault RetryableFault Effect) :
    (graph.append path payload).1.roots = [(graph.append path payload).2] := by
  rfl

@[simp] theorem append_serial
    (graph :
      ReceiptGraph Origin Rule Value StableFault RetryableFault Effect)
    (path : WorldPath)
    (payload :
      ReceiptPayload Origin Rule Value StableFault RetryableFault Effect) :
    (graph.append path payload).2.serial = graph.nextSerial := by
  rfl

@[simp] theorem append_parents
    (graph :
      ReceiptGraph Origin Rule Value StableFault RetryableFault Effect)
    (path : WorldPath)
    (payload :
      ReceiptPayload Origin Rule Value StableFault RetryableFault Effect) :
    (graph.append path payload).1.nodes.head?.map ReceiptNode.parents =
      some graph.roots := by
  rfl

end ReceiptGraph

/-- A branch world owns a persistent heap and receipt frontier. -/
structure World
    (Origin Rule Value StableFault RetryableFault Effect : Type*) where
  lineage : LineageId
  path : WorldPath
  heap : Heap Origin Value StableFault
  receipts :
    ReceiptGraph Origin Rule Value StableFault RetryableFault Effect
  nextCell : Nat
  nextEvaluator : EvaluatorId

namespace World

variable {Origin Rule Value StableFault RetryableFault Effect : Type*}

def fork
    (world : World Origin Rule Value StableFault RetryableFault Effect)
    (branch : Nat) :
    World Origin Rule Value StableFault RetryableFault Effect :=
  { world with path := world.path ++ [branch] }

def record
    (world : World Origin Rule Value StableFault RetryableFault Effect)
    (payload :
      ReceiptPayload Origin Rule Value StableFault RetryableFault Effect) :
    World Origin Rule Value StableFault RetryableFault Effect × ReceiptId :=
  let appended := world.receipts.append world.path payload
  ({ world with receipts := appended.1 }, appended.2)

def setKnownCache
    (world : World Origin Rule Value StableFault RetryableFault Effect)
    (cell : CellId) (record : CellRecord Origin Value StableFault)
    (state : Cache Value StableFault) :
    World Origin Rule Value StableFault RetryableFault Effect :=
  { world with heap := world.heap.setKnownCache cell record state }

def freshCell
    (world : World Origin Rule Value StableFault RetryableFault Effect)
    (generation : Nat) : CellId :=
  { lineage := world.lineage
    birth := world.path
    slot := world.nextCell
    generation := generation }

/-- Allocate a fresh cell in this branch and record the occurrence. -/
def allocate?
    (world : World Origin Rule Value StableFault RetryableFault Effect)
    (origin : Origin) (generation : Nat := 0) :
    Option
      (World Origin Rule Value StableFault RetryableFault Effect × CellId) :=
  let cell := world.freshCell generation
  match world.heap.allocate? cell origin with
  | none => none
  | some heap =>
      let advanced := { world with heap := heap, nextCell := world.nextCell + 1 }
      let recorded := advanced.record (.allocate cell origin)
      some (recorded.1, cell)

theorem fork_preserves_heap
    (world : World Origin Rule Value StableFault RetryableFault Effect)
    (branch : Nat) :
    (world.fork branch).heap = world.heap :=
  rfl

theorem fork_preserves_existing_cell
    (world : World Origin Rule Value StableFault RetryableFault Effect)
    (branch : Nat) (cell : CellId) :
    (world.fork branch).heap.lookup cell = world.heap.lookup cell :=
  rfl

theorem freshCell_sibling_ne
    (world : World Origin Rule Value StableFault RetryableFault Effect)
    {left right : Nat} (h : left ≠ right) (generation : Nat) :
    (world.fork left).freshCell generation ≠
      (world.fork right).freshCell generation := by
  intro hCells
  have hBirth :
      world.path ++ [left] = world.path ++ [right] :=
    congrArg CellId.birth hCells
  have hSingleton : [left] = [right] := List.append_cancel_left hBirth
  exact h (by simpa using hSingleton)

theorem allocate?_fresh_generation
    {world next :
      World Origin Rule Value StableFault RetryableFault Effect}
    {origin : Origin} {generation : Nat} {cell : CellId}
    (h : world.allocate? origin generation = some (next, cell)) :
    cell.generation = generation := by
  let candidate := world.freshCell generation
  change
    (match world.heap.allocate? candidate origin with
      | none => none
      | some heap =>
          let advanced :=
            { world with heap := heap, nextCell := world.nextCell + 1 }
          let recorded := advanced.record (.allocate candidate origin)
          some (recorded.1, candidate)) =
      some (next, cell) at h
  split at h
  · contradiction
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]
    change candidate.generation = generation
    simp [candidate, freshCell]

theorem allocate?_fresh_cell
    {world next :
      World Origin Rule Value StableFault RetryableFault Effect}
    {origin : Origin} {generation : Nat} {cell : CellId}
    (h : world.allocate? origin generation = some (next, cell)) :
    cell = world.freshCell generation := by
  let candidate := world.freshCell generation
  change
    (match world.heap.allocate? candidate origin with
      | none => none
      | some heap =>
          let advanced :=
            { world with heap := heap, nextCell := world.nextCell + 1 }
          let recorded := advanced.record (.allocate candidate origin)
          some (recorded.1, candidate)) =
      some (next, cell) at h
  split at h
  · contradiction
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact h.2.symm

theorem allocate?_lookup_same
    {world next :
      World Origin Rule Value StableFault RetryableFault Effect}
    {origin : Origin} {generation : Nat} {cell : CellId}
    (h : world.allocate? origin generation = some (next, cell)) :
    next.heap.lookup cell =
      some { origin := origin, cache := Cache.suspended } := by
  let candidate := world.freshCell generation
  change
    (match world.heap.allocate? candidate origin with
      | none => none
      | some heap =>
          let advanced :=
            { world with heap := heap, nextCell := world.nextCell + 1 }
          let recorded := advanced.record (.allocate candidate origin)
          some (recorded.1, candidate)) =
      some (next, cell) at h
  cases hHeap : world.heap.allocate? candidate origin with
  | none => simp [hHeap] at h
  | some heap =>
      simp only [hHeap, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1, ← h.2]
      exact Heap.allocate?_lookup_same hHeap

theorem allocate?_preserves_other
    {world next :
      World Origin Rule Value StableFault RetryableFault Effect}
    {origin : Origin} {generation : Nat} {cell other : CellId}
    (h : world.allocate? origin generation = some (next, cell))
    (hOther : other ≠ cell) :
    next.heap.lookup other = world.heap.lookup other := by
  let candidate := world.freshCell generation
  change
    (match world.heap.allocate? candidate origin with
      | none => none
      | some heap =>
          let advanced :=
            { world with heap := heap, nextCell := world.nextCell + 1 }
          let recorded := advanced.record (.allocate candidate origin)
          some (recorded.1, candidate)) =
      some (next, cell) at h
  cases hHeap : world.heap.allocate? candidate origin with
  | none => simp [hHeap] at h
  | some heap =>
      simp only [hHeap, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1]
      apply Heap.allocate?_preserves_other hHeap
      rwa [h.2]

theorem allocate?_nextCell
    {world next :
      World Origin Rule Value StableFault RetryableFault Effect}
    {origin : Origin} {generation : Nat} {cell : CellId}
    (h : world.allocate? origin generation = some (next, cell)) :
    next.nextCell = world.nextCell + 1 := by
  let candidate := world.freshCell generation
  change
    (match world.heap.allocate? candidate origin with
      | none => none
      | some heap =>
          let advanced :=
            { world with heap := heap, nextCell := world.nextCell + 1 }
          let recorded := advanced.record (.allocate candidate origin)
          some (recorded.1, candidate)) =
      some (next, cell) at h
  split at h
  · contradiction
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]
    rfl

theorem allocate?_lineage
    {world next :
      World Origin Rule Value StableFault RetryableFault Effect}
    {origin : Origin} {generation : Nat} {cell : CellId}
    (h : world.allocate? origin generation = some (next, cell)) :
    next.lineage = world.lineage := by
  let candidate := world.freshCell generation
  change
    (match world.heap.allocate? candidate origin with
      | none => none
      | some heap =>
          let advanced :=
            { world with heap := heap, nextCell := world.nextCell + 1 }
          let recorded := advanced.record (.allocate candidate origin)
          some (recorded.1, candidate)) =
      some (next, cell) at h
  split at h
  · contradiction
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]
    rfl

end World

/-- Work is counted in semantic machine operations.  Representation-specific
costs, such as probing a hash table or shortening an indirection, belong to a
later refinement theorem. -/
structure Work where
  transitions : Nat := 0
  heapLookups : Nat := 0
  heapUpdates : Nat := 0
  receiptAppends : Nat := 0
  allocations : Nat := 0
deriving DecidableEq, Repr

namespace Work

def add (left right : Work) : Work :=
  { transitions := left.transitions + right.transitions
    heapLookups := left.heapLookups + right.heapLookups
    heapUpdates := left.heapUpdates + right.heapUpdates
    receiptAppends := left.receiptAppends + right.receiptAppends
    allocations := left.allocations + right.allocations }

def operation
    (lookups updates receipts allocations : Nat) : Work :=
  { transitions := 1
    heapLookups := lookups
    heapUpdates := updates
    receiptAppends := receipts
    allocations := allocations }

def bump (work : Work) (lookups updates receipts allocations : Nat) : Work :=
  { transitions := work.transitions + 1
    heapLookups := work.heapLookups + lookups
    heapUpdates := work.heapUpdates + updates
    receiptAppends := work.receiptAppends + receipts
    allocations := work.allocations + allocations }

@[simp] theorem bump_transitions
    (work : Work) (lookups updates receipts allocations : Nat) :
    (work.bump lookups updates receipts allocations).transitions =
      work.transitions + 1 :=
  rfl

@[simp] theorem add_zero (work : Work) :
    work.add {} = work := by
  cases work
  rfl

@[simp] theorem zero_add (work : Work) :
    ({} : Work).add work = work := by
  cases work
  simp [add]

theorem add_assoc (left middle right : Work) :
    (left.add middle).add right = left.add (middle.add right) := by
  cases left
  cases middle
  cases right
  simp [add, Nat.add_assoc]

@[simp] theorem bump_eq_add_operation
    (work : Work) (lookups updates receipts allocations : Nat) :
    work.bump lookups updates receipts allocations =
      work.add (operation lookups updates receipts allocations) := by
  rfl

end Work

/-- The deterministic action exposed by a language-local state. -/
inductive Action
    (Origin Local Resume Value StableFault RetryableFault Effect : Type*) where
  | done (outcome : Produced Value StableFault RetryableFault)
  | demand (cell : CellId) (resume : Resume)
  | allocate (origin : Origin) (resume : Resume)
  | resample (source : CellId) (resume : Resume)
  | perform (effect : Effect) (next : Local)

/-- Tight language interface.  The list of alternatives is occurrence
sensitive.  The core machine, rather than the instance, owns all branching. -/
structure Spec
    (Origin Local Resume Rule Value StableFault RetryableFault Effect : Type*)
    where
  alternatives : Origin → List (Rule × Local)
  action :
    Local →
      Action Origin Local Resume Value StableFault RetryableFault Effect
  afterDemand :
    Resume → Produced Value StableFault RetryableFault → Local
  afterAllocation : Resume → CellId → Local

inductive Frame (Resume : Type*) where
  | commit (cell : CellId) (owner : EvaluatorId)
  | resume (token : Resume)

inductive Control
    (Local Resume Value StableFault RetryableFault : Type*) where
  | force (cell : CellId) (stack : List (Frame Resume))
  | run (state : Local) (stack : List (Frame Resume))
  | returned (outcome : Produced Value StableFault RetryableFault)
      (stack : List (Frame Resume))
  | halted (outcome : Produced Value StableFault RetryableFault)

structure Machine
    (Origin Local Resume Rule Value StableFault RetryableFault Effect : Type*)
    where
  world : World Origin Rule Value StableFault RetryableFault Effect
  control : Control Local Resume Value StableFault RetryableFault
  work : Work := {}

section Dynamics

variable {Origin Local Resume Rule Value StableFault RetryableFault Effect :
  Type*}

def finished
    (machine :
      Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (world :
      World Origin Rule Value StableFault RetryableFault Effect)
    (control : Control Local Resume Value StableFault RetryableFault)
    (lookups updates receipts allocations : Nat) :
    Machine Origin Local Resume Rule Value StableFault RetryableFault Effect :=
  { world := world
    control := control
    work := machine.work.bump lookups updates receipts allocations }

def recorded
    (world :
      World Origin Rule Value StableFault RetryableFault Effect)
    (payload :
      ReceiptPayload Origin Rule Value StableFault RetryableFault Effect) :
    World Origin Rule Value StableFault RetryableFault Effect :=
  (world.record payload).1

def retryMachine
    (machine :
      Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (world :
      World Origin Rule Value StableFault RetryableFault Effect)
    (cell : CellId) (reason : RetryReason RetryableFault)
    (stack : List (Frame Resume))
    (lookups updates receipts allocations : Nat) :
    Machine Origin Local Resume Rule Value StableFault RetryableFault Effect :=
  let world := recorded world (.retry cell reason)
  finished machine world (.returned (.retryableFault reason) stack)
    lookups updates (receipts + 1) allocations

def branchAlternatives
    (machine :
      Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (base : World Origin Rule Value StableFault RetryableFault Effect)
    (cell : CellId) (record : CellRecord Origin Value StableFault)
    (owner : EvaluatorId) (stack : List (Frame Resume)) :
    Nat → List (Rule × Local) →
      List
        (Machine Origin Local Resume Rule Value StableFault RetryableFault
          Effect)
  | _, [] => []
  | index, (rule, state) :: rest =>
      let world := (base.fork index).setKnownCache cell record (.evaluating owner)
      let world := recorded world (.evaluate cell owner)
      let world := recorded world (.chooseRule cell rule)
      finished machine world
          (.run state (.commit cell owner :: stack))
          1 1 2 0 ::
        branchAlternatives machine base cell record owner stack
          (index + 1) rest

@[simp] theorem branchAlternatives_length
    (machine :
      Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (base : World Origin Rule Value StableFault RetryableFault Effect)
    (cell : CellId) (record : CellRecord Origin Value StableFault)
    (owner : EvaluatorId) (stack : List (Frame Resume))
    (index : Nat) (alternatives : List (Rule × Local)) :
    (branchAlternatives machine base cell record owner stack
      index alternatives).length = alternatives.length := by
  induction alternatives generalizing index with
  | nil => rfl
  | cons head tail ih =>
      simp [branchAlternatives, ih]

theorem branchAlternatives_transitions
    (machine :
      Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (base : World Origin Rule Value StableFault RetryableFault Effect)
    (cell : CellId) (record : CellRecord Origin Value StableFault)
    (owner : EvaluatorId) (stack : List (Frame Resume))
    (index : Nat) (alternatives : List (Rule × Local))
    {candidate :
      Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    (hCandidate :
      candidate ∈
        branchAlternatives machine base cell record owner stack
          index alternatives) :
    candidate.work.transitions = machine.work.transitions + 1 := by
  induction alternatives generalizing index candidate with
  | nil => simp [branchAlternatives] at hCandidate
  | cons head tail ih =>
      simp only [branchAlternatives, List.mem_cons] at hCandidate
      rcases hCandidate with rfl | hCandidate
      · rfl
      · exact ih (index := index + 1) hCandidate

/-- One small step.  A list is used deliberately: list position and duplicate
entries retain exact rule-occurrence multiplicity. -/
def step
    (spec :
      Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (machine :
      Machine Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    List
      (Machine Origin Local Resume Rule Value StableFault RetryableFault
        Effect) :=
  match machine.control with
  | .halted _ => []
  | .force cell stack =>
      match machine.world.heap.lookup cell with
      | none =>
          [retryMachine machine machine.world cell (.outOfScope cell) stack
            1 0 0 0]
      | some record =>
          match record.cache with
          | .value value =>
              let outcome : Produced Value StableFault RetryableFault :=
                .value value
              let world := recorded machine.world (.observe cell outcome)
              [finished machine world (.returned outcome stack) 1 0 1 0]
          | .stableFault fault =>
              let outcome : Produced Value StableFault RetryableFault :=
                .stableFault fault
              let world := recorded machine.world (.observe cell outcome)
              [finished machine world (.returned outcome stack) 1 0 1 0]
          | .evaluating _ =>
              [retryMachine machine machine.world cell (.blackhole cell) stack
                1 0 0 0]
          | .suspended =>
              let owner := machine.world.nextEvaluator
              let base := { machine.world with nextEvaluator := owner + 1 }
              match spec.alternatives record.origin with
              | [] =>
                  let world := recorded base (.evaluate cell owner)
                  [retryMachine machine world cell (.noRule cell) stack
                    1 0 1 0]
              | alternatives =>
                  branchAlternatives machine base cell record owner stack
                    0 alternatives
  | .run state stack =>
      match spec.action state with
      | .done outcome =>
          [finished machine machine.world (.returned outcome stack) 0 0 0 0]
      | .demand cell resume =>
          [finished machine machine.world
            (.force cell (.resume resume :: stack)) 0 0 0 0]
      | .allocate origin resume =>
          let candidate := machine.world.freshCell 0
          match machine.world.allocate? origin with
          | none =>
              [retryMachine machine machine.world candidate
                (.allocationCollision candidate) stack 1 0 0 0]
          | some (world, cell) =>
              [finished machine world
                (.run (spec.afterAllocation resume cell) stack)
                1 1 1 1]
      | .resample source resume =>
          match machine.world.heap.lookup source with
          | none =>
              [retryMachine machine machine.world source (.outOfScope source)
                stack 1 0 0 0]
          | some sourceRecord =>
              let candidate :=
                machine.world.freshCell (source.generation + 1)
              match machine.world.allocate? sourceRecord.origin
                  (source.generation + 1) with
              | none =>
                  [retryMachine machine machine.world candidate
                    (.allocationCollision candidate) stack 2 0 0 0]
              | some (world, fresh) =>
                  let world := recorded world (.resample source fresh)
                  [finished machine world
                    (.run (spec.afterAllocation resume fresh) stack)
                    2 1 2 1]
      | .perform effect next =>
          let world := recorded machine.world (.effect effect)
          [finished machine world (.run next stack) 0 0 1 0]
  | .returned outcome stack =>
      match stack with
      | [] =>
          [finished machine machine.world (.halted outcome) 0 0 0 0]
      | .resume token :: rest =>
          [finished machine machine.world
            (.run (spec.afterDemand token outcome) rest) 0 0 0 0]
      | .commit cell owner :: rest =>
          match machine.world.heap.lookup cell with
          | none =>
              [retryMachine machine machine.world cell (.outOfScope cell)
                rest 1 0 0 0]
          | some record =>
              match record.cache with
              | .evaluating actual =>
                  if _hOwner : actual = owner then
                    let state : Cache Value StableFault :=
                      match outcome with
                      | .value value => .value value
                      | .stableFault fault => .stableFault fault
                      | .retryableFault _ => .suspended
                    let world :=
                      machine.world.setKnownCache cell record state
                    match outcome with
                    | .retryableFault reason =>
                        [retryMachine machine world cell reason rest 1 1 0 0]
                    | _ =>
                        let world := recorded world (.observe cell outcome)
                        [finished machine world (.returned outcome rest)
                          1 1 1 0]
                  else
                    [retryMachine machine machine.world cell
                      (.ownershipLost cell owner actual) rest 1 0 0 0]
              | _ =>
                  [retryMachine machine machine.world cell
                    (.ownershipLost cell owner 0) rest 1 0 0 0]

/-- A halted state remains in a bounded frontier rather than disappearing. -/
def advance
    (spec :
      Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (machine :
      Machine Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    List
      (Machine Origin Local Resume Rule Value StableFault RetryableFault
        Effect) :=
  match step spec machine with
  | [] => [machine]
  | next => next

def isHalted
    (machine :
      Machine Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    Bool :=
  match machine.control with
  | .halted _ => true
  | _ => false

def runFrontier
    (spec :
      Spec Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    Nat →
      List
        (Machine Origin Local Resume Rule Value StableFault RetryableFault
          Effect) →
      List
        (Machine Origin Local Resume Rule Value StableFault RetryableFault
          Effect)
  | 0, states => states
  | fuel + 1, states =>
      if states.all isHalted then
        states
      else
        runFrontier spec fuel (states.flatMap (advance spec))

def haltedOutcome
    (machine :
      Machine Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    Option (Produced Value StableFault RetryableFault) :=
  match machine.control with
  | .halted outcome => some outcome
  | _ => none

def answers
    (spec :
      Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (fuel : Nat)
    (machine :
      Machine Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    List (Produced Value StableFault RetryableFault) :=
  (runFrontier spec fuel [machine]).filterMap haltedOutcome

/-! ## Generic laws -/

/-- For a suspended cell with at least one rule, one force step has exactly one
successor per rule occurrence. -/
theorem suspended_step_preserves_multiplicity
    (spec :
      Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (machine :
      Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (cell : CellId) (stack : List (Frame Resume))
    (record : CellRecord Origin Value StableFault)
    (hControl : machine.control = .force cell stack)
    (hLookup : machine.world.heap.lookup cell = some record)
    (hSuspended : record.cache = .suspended)
    (hNonempty : spec.alternatives record.origin ≠ []) :
    (step spec machine).length =
      (spec.alternatives record.origin).length := by
  cases hRules : spec.alternatives record.origin with
  | nil => exact (hNonempty hRules).elim
  | cons head tail =>
      simp only [step, hControl, hLookup, hSuspended, hRules]
      exact branchAlternatives_length _ _ _ _ _ _ _ _

/-- Duplicate rule occurrences are not silently deduplicated. -/
theorem duplicate_rules_have_two_successors
    (spec :
      Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (machine :
      Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (cell : CellId) (stack : List (Frame Resume))
    (record : CellRecord Origin Value StableFault)
    (rule : Rule) (state : Local)
    (hControl : machine.control = .force cell stack)
    (hLookup : machine.world.heap.lookup cell = some record)
    (hSuspended : record.cache = .suspended)
    (hRules :
      spec.alternatives record.origin = [(rule, state), (rule, state)]) :
    (step spec machine).length = 2 := by
  calc
    (step spec machine).length =
        (spec.alternatives record.origin).length :=
      suspended_step_preserves_multiplicity spec machine cell stack record
        hControl hLookup hSuspended (by simp [hRules])
    _ = 2 := by simp [hRules]

/-- Cached outcomes have one successor and do not branch through the rule
interface again. -/
theorem cached_value_has_one_successor
    (spec :
      Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (machine :
      Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (cell : CellId) (stack : List (Frame Resume))
    (record : CellRecord Origin Value StableFault) (value : Value)
    (hControl : machine.control = .force cell stack)
    (hLookup : machine.world.heap.lookup cell = some record)
    (hCached : record.cache = .value value) :
    (step spec machine).length = 1 := by
  simp [step, hControl, hLookup, hCached]

/-- Every successor accounts for exactly one abstract transition. -/
theorem step_increments_transition
    (spec :
      Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (machine next :
      Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (hNext : next ∈ step spec machine) :
    next.work.transitions = machine.work.transitions + 1 := by
  rcases machine with ⟨world, control, work⟩
  cases control with
  | halted outcome =>
      simp [step] at hNext
  | force cell stack =>
      simp only [step] at hNext
      split at hNext
      · simp only [List.mem_singleton] at hNext
        subst next
        rfl
      · rename_i record hRecord
        split at hNext
        · simp only [List.mem_singleton] at hNext
          subst next
          rfl
        · simp only [List.mem_singleton] at hNext
          subst next
          rfl
        · simp only [List.mem_singleton] at hNext
          subst next
          rfl
        · split at hNext
          · simp only [List.mem_singleton] at hNext
            subst next
            rfl
          ·
            simpa using
              branchAlternatives_transitions
                ({ world := world, control := .force cell stack,
                   work := work } :
                  Machine Origin Local Resume Rule Value StableFault
                    RetryableFault Effect)
                { world with
                  nextEvaluator := world.nextEvaluator + 1 }
                cell record world.nextEvaluator stack 0
                (spec.alternatives record.origin) hNext
  | run state stack =>
      simp only [step] at hNext
      split at hNext <;>
        repeat' first
          | split at hNext
          | simp only [List.mem_singleton] at hNext
            subst next
            rfl
  | returned outcome stack =>
      simp only [step] at hNext
      split at hNext <;>
        repeat' first
          | split at hNext
          | simp only [List.mem_singleton] at hNext
            subst next
            rfl

/-- One occurrence of a successor in the list-valued transition.  The index
is semantic: two equal successor values produced by duplicate rules remain
two distinct occurrences. -/
structure StepOccurrence
    (spec :
      Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (machine next :
      Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    where
  index : Nat
  successorAt : (step spec machine)[index]? = some next

namespace StepOccurrence

theorem mem
    (spec :
      Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    {machine next :
      Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    (occurrence : StepOccurrence spec machine next) :
    next ∈ step spec machine := by
  rw [List.mem_iff_getElem]
  rcases List.getElem?_eq_some_iff.mp occurrence.successorAt with
    ⟨hIndex, hNext⟩
  exact ⟨occurrence.index, hIndex, hNext⟩

end StepOccurrence

/-- A finite execution path through the occurrence-sensitive transition
relation. -/
inductive Steps
    (spec :
      Spec Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    Nat →
      Machine Origin Local Resume Rule Value StableFault RetryableFault Effect →
      Machine Origin Local Resume Rule Value StableFault RetryableFault Effect →
      Prop where
  | refl (machine) : Steps spec 0 machine machine
  | cons {length machine next final}
      (hNext : StepOccurrence spec machine next)
      (hRest : Steps spec length next final) :
      Steps spec (Nat.succ length) machine final

namespace Steps

theorem trans
    (spec :
      Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    {left middle right :
      Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    {leftLength rightLength : Nat}
    (hLeft : Steps spec leftLength left middle)
    (hRight : Steps spec rightLength middle right) :
    Steps spec (leftLength + rightLength) left right := by
  induction hLeft with
  | refl => simpa using hRight
  | cons hNext _ ih =>
      simpa [Nat.succ_add] using Steps.cons hNext (ih hRight)

/-- The abstract transition counter is an exact clock for `Steps`, rather
than a separately asserted cost recurrence. -/
theorem transitions_eq
    (spec :
      Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    {length : Nat}
    {initial final :
      Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    (execution : Steps spec length initial final) :
    final.work.transitions = initial.work.transitions + length := by
  induction execution with
  | refl => rfl
  | cons hNext _ ih =>
      rw [ih, step_increments_transition spec _ _ (hNext.mem spec)]
      omega

end Steps

/-- A deterministic finite path.  Unlike `Steps`, every transition is proved
to have exactly one successor occurrence. -/
inductive UniqueSteps
    (spec :
      Spec Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    Nat →
      Machine Origin Local Resume Rule Value StableFault RetryableFault Effect →
      Machine Origin Local Resume Rule Value StableFault RetryableFault Effect →
      Prop where
  | refl (machine) : UniqueSteps spec 0 machine machine
  | cons {length machine next final}
      (hNext : step spec machine = [next])
      (hRest : UniqueSteps spec length next final) :
      UniqueSteps spec (Nat.succ length) machine final

namespace UniqueSteps

theorem toSteps
    (spec :
      Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    {length : Nat}
    {initial final :
      Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    (execution : UniqueSteps spec length initial final) :
    Steps spec length initial final := by
  induction execution with
  | refl => exact Steps.refl _
  | @cons length machine next final hNext _ ih =>
      have occurrence : StepOccurrence spec machine next :=
        { index := 0
          successorAt := by simp [hNext] }
      exact Steps.cons occurrence ih

theorem trans
    (spec :
      Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    {left middle right :
      Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    {leftLength rightLength : Nat}
    (hLeft : UniqueSteps spec leftLength left middle)
    (hRight : UniqueSteps spec rightLength middle right) :
    UniqueSteps spec (leftLength + rightLength) left right := by
  induction hLeft with
  | refl => simpa using hRight
  | cons hNext _ ih =>
      simpa [Nat.succ_add] using UniqueSteps.cons hNext (ih hRight)

theorem runFrontier_eq
    (spec :
      Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    {length : Nat}
    {initial final :
      Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    (execution : UniqueSteps spec length initial final) :
    runFrontier spec length [initial] = [final] := by
  induction execution with
  | refl => rfl
  | @cons length machine next final hNext _ ih =>
      have hRunning : isHalted machine = false := by
        cases hControl : machine.control with
        | force => simp [isHalted, hControl]
        | run => simp [isHalted, hControl]
        | returned => simp [isHalted, hControl]
        | halted =>
            simp [step, hControl] at hNext
      simp [runFrontier, hRunning, advance, hNext, ih]

end UniqueSteps

end Dynamics

/-! ## Positive and negative boundary examples -/

example :
    ({ lineage := 4, birth := [0], slot := 2, generation := 0 } : CellId) ≠
      { lineage := 4, birth := [1], slot := 2, generation := 0 } := by
  decide

/-- A resampled generation is not the cell it was sampled from. -/
example :
    ({ lineage := 4, birth := [], slot := 2, generation := 0 } : CellId) ≠
      { lineage := 4, birth := [], slot := 3, generation := 1 } := by
  decide

end Mettapedia.Languages.MeTTa.PrimeNeedReference
