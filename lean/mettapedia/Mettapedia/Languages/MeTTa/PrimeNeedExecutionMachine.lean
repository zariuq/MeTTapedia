import Mettapedia.Languages.MeTTa.PrimeNeedReferenceSemantics

/-!
# Receipt-erased Prime Need execution machine

The rich Prime Need reference machine carries a causal receipt DAG in every
world.  This module derives the answer-only execution carrier by erasing that
DAG and independently defining its transition function.  Cell identity,
branch worlds, exact alternative multiplicity, cache states, retry behavior,
control frames, and work counters remain unchanged.

The central theorem is `step_commutes`: mapping erasure over every rich
successor gives exactly the list produced by the execution transition.
Because the equality is list-valued, it preserves order and duplicate
occurrences rather than merely proving set-level reachability.  The two
membership corollaries state forward simulation and backward lifting.

This is the refinement seam for an answer-only interpreter, compiled tier, or
JIT.  Such a tier may omit receipt storage; it may not alter worlds, cells,
outcomes, multiplicity, or the receipt-operation cost account justified by
the rich semantics.
-/

namespace Mettapedia.Languages.MeTTa.PrimeNeedExecution

open PrimeNeedReference

/-- Receipt-erased world. -/
structure CoreWorld
    (Origin Rule Value StableFault RetryableFault Effect : Type*) where
  lineage : LineageId
  path : WorldPath
  heap : Heap Origin Value StableFault
  nextCell : Nat
  nextEvaluator : EvaluatorId

namespace CoreWorld

variable {Origin Rule Value StableFault RetryableFault Effect : Type*}

def fork
    (world : CoreWorld Origin Rule Value StableFault RetryableFault Effect)
    (branch : Nat) :
    CoreWorld Origin Rule Value StableFault RetryableFault Effect :=
  { world with path := world.path ++ [branch] }

def setKnownCache
    (world : CoreWorld Origin Rule Value StableFault RetryableFault Effect)
    (cell : CellId) (record : CellRecord Origin Value StableFault)
    (state : Cache Value StableFault) :
    CoreWorld Origin Rule Value StableFault RetryableFault Effect :=
  { world with heap := world.heap.setKnownCache cell record state }

def freshCell
    (world : CoreWorld Origin Rule Value StableFault RetryableFault Effect)
    (generation : Nat) : CellId :=
  { lineage := world.lineage
    birth := world.path
    slot := world.nextCell
    generation := generation }

def allocate?
    (world : CoreWorld Origin Rule Value StableFault RetryableFault Effect)
    (origin : Origin) (generation : Nat := 0) :
    Option
      (CoreWorld Origin Rule Value StableFault RetryableFault Effect ×
        CellId) :=
  let cell := world.freshCell generation
  match world.heap.allocate? cell origin with
  | none => none
  | some heap =>
      some ({ world with heap := heap, nextCell := world.nextCell + 1 }, cell)

end CoreWorld

def eraseWorld
    {Origin Rule Value StableFault RetryableFault Effect : Type*}
    (world : World Origin Rule Value StableFault RetryableFault Effect) :
    CoreWorld Origin Rule Value StableFault RetryableFault Effect where
  lineage := world.lineage
  path := world.path
  heap := world.heap
  nextCell := world.nextCell
  nextEvaluator := world.nextEvaluator

structure CoreMachine
    (Origin Local Resume Rule Value StableFault RetryableFault Effect : Type*)
    where
  world : CoreWorld Origin Rule Value StableFault RetryableFault Effect
  control : Control Local Resume Value StableFault RetryableFault
  work : Work := {}

def eraseMachine
    {Origin Local Resume Rule Value StableFault RetryableFault Effect : Type*}
    (machine :
      Machine Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    CoreMachine Origin Local Resume Rule Value StableFault RetryableFault
      Effect where
  world := eraseWorld machine.world
  control := machine.control
  work := machine.work

section ErasureLaws

variable {Origin Rule Value StableFault RetryableFault Effect : Type*}

@[simp] theorem eraseWorld_fork
    (world : World Origin Rule Value StableFault RetryableFault Effect)
    (branch : Nat) :
    eraseWorld (world.fork branch) = (eraseWorld world).fork branch :=
  rfl

@[simp] theorem eraseWorld_setKnownCache
    (world : World Origin Rule Value StableFault RetryableFault Effect)
    (cell : CellId) (record : CellRecord Origin Value StableFault)
    (state : Cache Value StableFault) :
    eraseWorld (world.setKnownCache cell record state) =
      (eraseWorld world).setKnownCache cell record state :=
  rfl

@[simp] theorem eraseWorld_record
    (world : World Origin Rule Value StableFault RetryableFault Effect)
    (payload :
      ReceiptPayload Origin Rule Value StableFault RetryableFault Effect) :
    eraseWorld (world.record payload).1 = eraseWorld world :=
  rfl

@[simp] theorem eraseWorld_freshCell
    (world : World Origin Rule Value StableFault RetryableFault Effect)
    (generation : Nat) :
    (eraseWorld world).freshCell generation = world.freshCell generation :=
  rfl

theorem eraseWorld_allocate?
    (world : World Origin Rule Value StableFault RetryableFault Effect)
    (origin : Origin) (generation : Nat := 0) :
    (world.allocate? origin generation).map
        (fun result => (eraseWorld result.1, result.2)) =
      (eraseWorld world).allocate? origin generation := by
  simp only [World.allocate?, CoreWorld.allocate?, eraseWorld_freshCell]
  split
  · rfl
  · simp [World.record, ReceiptGraph.append, eraseWorld]

end ErasureLaws

section Dynamics

variable {Origin Local Resume Rule Value StableFault RetryableFault Effect :
  Type*}

private def finished
    (machine :
      CoreMachine Origin Local Resume Rule Value StableFault RetryableFault
        Effect)
    (world :
      CoreWorld Origin Rule Value StableFault RetryableFault Effect)
    (control : Control Local Resume Value StableFault RetryableFault)
    (lookups updates receipts allocations : Nat) :
    CoreMachine Origin Local Resume Rule Value StableFault RetryableFault
      Effect :=
  { world := world
    control := control
    work := machine.work.bump lookups updates receipts allocations }

private def retryMachine
    (machine :
      CoreMachine Origin Local Resume Rule Value StableFault RetryableFault
        Effect)
    (world :
      CoreWorld Origin Rule Value StableFault RetryableFault Effect)
    (reason : RetryReason RetryableFault)
    (stack : List (Frame Resume))
    (lookups updates priorReceipts allocations : Nat) :
    CoreMachine Origin Local Resume Rule Value StableFault RetryableFault
      Effect :=
  finished machine world (.returned (.retryableFault reason) stack)
    lookups updates (priorReceipts + 1) allocations

@[simp] theorem erase_finished
    (machine :
      Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (world : World Origin Rule Value StableFault RetryableFault Effect)
    (control : Control Local Resume Value StableFault RetryableFault)
    (lookups updates receipts allocations : Nat) :
    eraseMachine
        (PrimeNeedReference.finished machine world control
          lookups updates receipts allocations) =
      finished (eraseMachine machine) (eraseWorld world) control
        lookups updates receipts allocations := by
  rfl

@[simp] theorem erase_recorded
    (world : World Origin Rule Value StableFault RetryableFault Effect)
    (payload :
      ReceiptPayload Origin Rule Value StableFault RetryableFault Effect) :
    eraseWorld (PrimeNeedReference.recorded world payload) =
      eraseWorld world := by
  rfl

@[simp] theorem erase_retryMachine
    (machine :
      Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (world : World Origin Rule Value StableFault RetryableFault Effect)
    (cell : CellId) (reason : RetryReason RetryableFault)
    (stack : List (Frame Resume))
    (lookups updates priorReceipts allocations : Nat) :
    eraseMachine
        (PrimeNeedReference.retryMachine machine world cell reason stack
          lookups updates priorReceipts allocations) =
      retryMachine (eraseMachine machine) (eraseWorld world) reason stack
        lookups updates priorReceipts allocations := by
  rfl

def branchAlternatives
    (machine :
      CoreMachine Origin Local Resume Rule Value StableFault RetryableFault
        Effect)
    (base : CoreWorld Origin Rule Value StableFault RetryableFault Effect)
    (cell : CellId) (record : CellRecord Origin Value StableFault)
    (owner : EvaluatorId) (stack : List (Frame Resume)) :
    Nat → List (Rule × Local) →
      List
        (CoreMachine Origin Local Resume Rule Value StableFault RetryableFault
          Effect)
  | _, [] => []
  | index, (_, state) :: rest =>
      let world :=
        (base.fork index).setKnownCache cell record (.evaluating owner)
      finished machine world
          (.run state (.commit cell owner :: stack))
          1 1 2 0 ::
        branchAlternatives machine base cell record owner stack
          (index + 1) rest

/-- Independently defined answer-only execution transition.  Receipt counts
remain in `Work` even though receipt nodes themselves are erased. -/
def step
    (spec :
      Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (machine :
      CoreMachine Origin Local Resume Rule Value StableFault RetryableFault
        Effect) :
    List
      (CoreMachine Origin Local Resume Rule Value StableFault RetryableFault
        Effect) :=
  match machine.control with
  | .halted _ => []
  | .force cell stack =>
      match machine.world.heap.lookup cell with
      | none =>
          [retryMachine machine machine.world (.outOfScope cell) stack
            1 0 0 0]
      | some record =>
          match record.cache with
          | .value value =>
              let outcome : Produced Value StableFault RetryableFault :=
                .value value
              [finished machine machine.world (.returned outcome stack)
                1 0 1 0]
          | .stableFault fault =>
              let outcome : Produced Value StableFault RetryableFault :=
                .stableFault fault
              [finished machine machine.world (.returned outcome stack)
                1 0 1 0]
          | .evaluating _ =>
              [retryMachine machine machine.world (.blackhole cell) stack
                1 0 0 0]
          | .suspended =>
              let owner := machine.world.nextEvaluator
              let base := { machine.world with nextEvaluator := owner + 1 }
              match spec.alternatives record.origin with
              | [] =>
                  [retryMachine machine base (.noRule cell) stack
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
              [retryMachine machine machine.world
                (.allocationCollision candidate) stack 1 0 0 0]
          | some (world, cell) =>
              [finished machine world
                (.run (spec.afterAllocation resume cell) stack)
                1 1 1 1]
      | .resample source resume =>
          match machine.world.heap.lookup source with
          | none =>
              [retryMachine machine machine.world (.outOfScope source)
                stack 1 0 0 0]
          | some sourceRecord =>
              let candidate :=
                machine.world.freshCell (source.generation + 1)
              match machine.world.allocate? sourceRecord.origin
                  (source.generation + 1) with
              | none =>
                  [retryMachine machine machine.world
                    (.allocationCollision candidate) stack 2 0 0 0]
              | some (world, fresh) =>
                  [finished machine world
                    (.run (spec.afterAllocation resume fresh) stack)
                    2 1 2 1]
      | .perform _ next =>
          [finished machine machine.world (.run next stack) 0 0 1 0]
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
              [retryMachine machine machine.world (.outOfScope cell)
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
                        [retryMachine machine world reason rest 1 1 0 0]
                    | _ =>
                        [finished machine world (.returned outcome rest)
                          1 1 1 0]
                  else
                    [retryMachine machine machine.world
                      (.ownershipLost cell owner actual) rest 1 0 0 0]
              | _ =>
                  [retryMachine machine machine.world
                    (.ownershipLost cell owner 0) rest 1 0 0 0]

private theorem erase_branchAlternatives
    (machine :
      Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (base : World Origin Rule Value StableFault RetryableFault Effect)
    (cell : CellId) (record : CellRecord Origin Value StableFault)
    (owner : EvaluatorId) (stack : List (Frame Resume))
    (index : Nat) (alternatives : List (Rule × Local)) :
    (PrimeNeedReference.branchAlternatives machine base cell record owner
        stack index alternatives).map eraseMachine =
      branchAlternatives (eraseMachine machine) (eraseWorld base) cell record
        owner stack index alternatives := by
  induction alternatives generalizing index with
  | nil => rfl
  | cons head tail ih =>
      rcases head with ⟨rule, state⟩
      simp only [PrimeNeedReference.branchAlternatives, branchAlternatives,
        List.map_cons, List.cons.injEq]
      constructor
      · rfl
      · exact ih (index + 1)

/-- Exact one-step commuting square.  This is stronger than reachability
soundness: list order and duplicate alternatives are preserved. -/
theorem step_commutes
    (spec :
      Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (machine :
      Machine Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    (PrimeNeedReference.step spec machine).map eraseMachine =
      step spec (eraseMachine machine) := by
  rcases machine with ⟨world, control, work⟩
  cases control with
  | halted outcome =>
      rfl
  | force cell stack =>
      simp only [PrimeNeedReference.step, step, eraseMachine, eraseWorld]
      split
      · rfl
      · rename_i record hRecord
        split
        · rfl
        · rfl
        · rfl
        · split
          · rfl
          · exact erase_branchAlternatives
              ({ world := world, control := .force cell stack, work := work })
              { world with nextEvaluator := world.nextEvaluator + 1 }
              cell record world.nextEvaluator stack 0
              (spec.alternatives record.origin)
  | run state stack =>
      simp only [PrimeNeedReference.step, step, eraseMachine, eraseWorld]
      split
      · rfl
      · rfl
      · split
        · rfl
        · rename_i worldAndCell hAllocation
          rcases worldAndCell with ⟨nextWorld, nextCell⟩
          have hErase := eraseWorld_allocate? world
            (match spec.action state with
              | .allocate origin _ => origin
              | _ => by contradiction)
          simp only [hAllocation, Option.map_some] at hErase
          rw [← hErase]
          rfl
      · split
        · rfl
        · rename_i sourceRecord hSource
          split
          · rfl
          · rename_i worldAndCell hAllocation
            rcases worldAndCell with ⟨nextWorld, nextCell⟩
            have hErase := eraseWorld_allocate? world sourceRecord.origin
              (match spec.action state with
                | .resample source _ => source.generation + 1
                | _ => by contradiction)
            simp only [hAllocation, Option.map_some] at hErase
            rw [← hErase]
            rfl
      · rfl
  | returned outcome stack =>
      simp only [PrimeNeedReference.step, step, eraseMachine, eraseWorld]
      split
      · rfl
      · rfl
      · split
        · rfl
        · rename_i record hRecord
          split
          · split <;> rfl
          · rfl

/-- Forward simulation from the rich reference machine. -/
theorem rich_step_sound
    (spec :
      Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    {machine next :
      Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    (hNext : next ∈ PrimeNeedReference.step spec machine) :
    eraseMachine next ∈ step spec (eraseMachine machine) := by
  rw [← step_commutes spec machine]
  exact List.mem_map.mpr ⟨next, hNext, rfl⟩

/-- Backward lifting: every answer-only successor is the erasure of a rich
successor.  Thus the execution machine cannot invent an unreceipted branch. -/
theorem core_step_lifts
    (spec :
      Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    {machine :
      Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    {next :
      CoreMachine Origin Local Resume Rule Value StableFault RetryableFault
        Effect}
    (hNext : next ∈ step spec (eraseMachine machine)) :
    ∃ richNext ∈ PrimeNeedReference.step spec machine,
      eraseMachine richNext = next := by
  rw [← step_commutes spec machine] at hNext
  rcases List.mem_map.mp hNext with ⟨richNext, hRich, hErase⟩
  exact ⟨richNext, hRich, hErase⟩

end Dynamics

end Mettapedia.Languages.MeTTa.PrimeNeedExecution
