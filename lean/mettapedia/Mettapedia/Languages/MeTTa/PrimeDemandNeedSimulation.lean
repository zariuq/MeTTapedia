import Mettapedia.Languages.MeTTa.PrimeNeedCacheLaws
import Mettapedia.Languages.MeTTa.DemandSemantics


/-!
# Demand fragment as a Need-machine instance

This module instantiates the `PrimeNeedReference` machine with the
`DemandSemantics` fragment (numbers, pairs, `add`, `rcar`, `rcdr`) and
proves the **forward simulation**: every relational evaluation
`Eval t v` is realizable as a deterministic machine execution which
forces a fresh cell holding `t` and returns `.value v`.

The encoding is one-subcell-per-subterm, in the style of
`PrimeRecursionReference`: reducible positions allocate a fresh cell
for each demanded subterm and force it, so every demand flows through
the same cache discipline the four laws apply to.  There is no choice
here: each origin has exactly one rule, so machine executions are
unique (`UniqueSteps`), and `UniqueSteps.runFrontier_eq` turns them
into exact `runFrontier` equalities for the top-level `answers`
corollary.

Stable faults stand for the relational language's stuck positions
(`add` of a non-numeral, `rcar`/`rcdr` of a non-pair): the machine
never masquerades a stuck position as a finished value, matching the
status-partition law of the canary layer.  The fragment never hits
retryable causes in well-formed runs — each cell is forced exactly
once — but the states pass them through honestly rather than making
false claims about them.

## Structure of the instance

`alternatives` carries one rule per origin and starts an
allocate–demand chain for each reducible origin.  `.pair` completes as
`.value (.pair a b)` with **no** demand of the components — the
laziness axiom of the relational semantics follows from the instance,
not from a special case.  `rcar` of a demanded pair allocates a fresh
cell for the *first* component only and demands it: one layer at a
time, exactly the `Eval.rcar` rule.
-/

namespace Mettapedia.Languages.MeTTa.PrimeDemandNeedSimulation

open PrimeNeedReference
open Mettapedia.Languages.MeTTa.DemandSemantics (Term Eval)

/-- The one rule each origin carries: the fragment is deterministic. -/
inductive Rule where
  | evaluate
  deriving Repr, DecidableEq

/-- Local machine states of the demand fragment. -/
inductive Local where
  /-- Terminal state: hand an outcome back through the stack. -/
  | output (outcome : Produced Term Unit Nat)
  /-- `add`, stage 1: allocate a cell for the left argument. -/
  | addAllocLeft (a b : Term)
  /-- `add`, stage 2: allocate a cell for the right argument. -/
  | addAllocRight (cellA : CellId) (b : Term)
  /-- `add`, stage 3: demand the left cell. -/
  | addDemandLeft (cellA cellB : CellId)
  /-- `add`, stage 4: demand the right cell. -/
  | addDemandRight (x : Nat) (cellB : CellId)
  /-- `rcar`, stage 1: allocate a cell for the outer term. -/
  | rcarAlloc (t : Term)
  /-- `rcar`, stage 2: demand that cell to WHNF. -/
  | rcarDemand (cellT : CellId)
  /-- `rcar`, stage 3: allocate a cell for the first component. -/
  | rcarAllocComponent (a : Term)
  /-- `rcar`, stage 4: demand the first component. -/
  | rcarDemandComponent (cellComponent : CellId)
  /-- `rcdr`, stage 1: allocate a cell for the outer term. -/
  | rcdrAlloc (t : Term)
  /-- `rcdr`, stage 2: demand that cell to WHNF. -/
  | rcdrDemand (cellT : CellId)
  /-- `rcdr`, stage 3: allocate a cell for the second component. -/
  | rcdrAllocComponent (b : Term)
  /-- `rcdr`, stage 4: demand the second component. -/
  | rcdrDemandComponent (cellComponent : CellId)
  deriving Repr, DecidableEq

/-- Resumption tokens carry exactly the data the continuation needs. -/
inductive Resume where
  | addLeftAllocated (b : Term)
  | addRightAllocated (cellA : CellId)
  | addLeftReturned (cellB : CellId)
  | addRightReturned (x : Nat)
  | rcarAllocated
  | rcarReturned
  | rcarComponentAllocated
  | rcarComponentReturned
  | rcdrAllocated
  | rcdrReturned
  | rcdrComponentAllocated
  | rcdrComponentReturned
  deriving Repr, DecidableEq

abbrev Outcome := Produced Term Unit Nat

/-- Continue an `add` sub-demand: numerals advance the chain; any other
value is a stuck position (a stable fault); faults propagate. -/
private def continueNumeral (outcome : Outcome) (next : Nat → Local) :
    Local :=
  match outcome with
  | .value v =>
      match v with
      | .num x => next x
      | _ => .output (.stableFault ())
  | .stableFault () => .output (.stableFault ())
  | .retryableFault reason => .output (.retryableFault reason)

/-- Rule alternatives: one rule per origin, starting its
allocate–demand chain (or, for data, producing immediately). -/
def alternatives : Term → List (Rule × Local)
  | .num n => [(.evaluate, .output (.value (.num n)))]
  | .pair a b => [(.evaluate, .output (.value (.pair a b)))]
  | .add a b => [(.evaluate, .addAllocLeft a b)]
  | .rcar t => [(.evaluate, .rcarAlloc t)]
  | .rcdr t => [(.evaluate, .rcdrAlloc t)]

/-- Deterministic local actions of each machine state. -/
def action : Local → Action Term Local Resume Term Unit Nat Nat
  | .output outcome => .done outcome
  | .addAllocLeft a b => .allocate a (.addLeftAllocated b)
  | .addAllocRight cellA b => .allocate b (.addRightAllocated cellA)
  | .addDemandLeft cellA cellB => .demand cellA (.addLeftReturned cellB)
  | .addDemandRight x cellB => .demand cellB (.addRightReturned x)
  | .rcarAlloc t => .allocate t .rcarAllocated
  | .rcarDemand cellT => .demand cellT .rcarReturned
  | .rcarAllocComponent a => .allocate a .rcarComponentAllocated
  | .rcarDemandComponent cellC => .demand cellC .rcarComponentReturned
  | .rcdrAlloc t => .allocate t .rcdrAllocated
  | .rcdrDemand cellT => .demand cellT .rcdrReturned
  | .rcdrAllocComponent b => .allocate b .rcdrComponentAllocated
  | .rcdrDemandComponent cellC => .demand cellC .rcdrComponentReturned

/-- Continua after a demand returns: `add` chains numerals, `rcar` /
`rcdr` penetrate one layer and chain one more demand; faults
propagate unchanged. -/
def afterDemand : Resume → Outcome → Local
  | .addLeftReturned cellB, outcome =>
      continueNumeral outcome fun x => .addDemandRight x cellB
  | .addRightReturned x, outcome =>
      continueNumeral outcome fun y => .output (.value (.num (x + y)))
  | .rcarReturned, outcome =>
      match outcome with
      | .value v =>
          match v with
          | .pair a _ => .rcarAllocComponent a
          | _ => .output (.stableFault ())
      | .stableFault () => .output (.stableFault ())
      | .retryableFault reason => .output (.retryableFault reason)
  | .rcarComponentReturned, outcome => .output outcome
  | .rcdrReturned, outcome =>
      match outcome with
      | .value v =>
          match v with
          | .pair _ b => .rcdrAllocComponent b
          | _ => .output (.stableFault ())
      | .stableFault () => .output (.stableFault ())
      | .retryableFault reason => .output (.retryableFault reason)
  | .rcdrComponentReturned, outcome => .output outcome
  | _resumption, _ =>
      .output (.retryableFault (.domain 0))

/-- Continua after an allocation returns its fresh cell identifier. -/
def afterAllocation : Resume → CellId → Local
  | (.addLeftAllocated b), cellA => .addAllocRight cellA b
  | (.addRightAllocated cellA), cellB => .addDemandLeft cellA cellB
  | .rcarAllocated, cellT => .rcarDemand cellT
  | .rcarComponentAllocated, cellC => .rcarDemandComponent cellC
  | .rcdrAllocated, cellT => .rcdrDemand cellT
  | .rcdrComponentAllocated, cellC => .rcdrDemandComponent cellC
  | _, _ => .output (.retryableFault (.domain 0))

/-- The need-machine instance of the demand fragment. -/
def demandSpec : Spec Term Local Resume Rule Term Unit Nat Nat where
  alternatives := alternatives
  action := action
  afterDemand := afterDemand
  afterAllocation := afterAllocation

/-! ## Initial machine and witnesses -/

/-- The distinguished root cell of a run: it holds the whole term as its
origin and is what `initialMachine` forces. -/
def rootCell (lineage : LineageId := 1) : CellId :=
  { lineage := lineage, birth := [], slot := 0, generation := 0 }

/-- The initial heap of one suspended root cell, ready to be forced. -/
def initialHeap (lineage : LineageId) (t : Term) : Heap Term Term Unit :=
  let root := rootCell lineage
  let record : CellRecord Term Term Unit :=
    { origin := t, cache := .suspended }
  { current := fun cell => if cell = root then some record else none
    spine := [.allocate root t] }

/-- The initial branch world of a run. -/
def initialWorld (t : Term) (lineage : LineageId := 1) :
    World Term Rule Term Unit Nat Nat where
  lineage := lineage
  path := []
  heap := initialHeap lineage t
  receipts := ReceiptGraph.empty
  nextCell := 1
  nextEvaluator := 1

/-- The initial machine of a run: force the root cell. -/
def initialMachine (t : Term) (lineage : LineageId := 1) :
    Machine Term Local Resume Rule Term Unit Nat Nat where
  world := initialWorld t lineage
  control := .force (rootCell lineage) []

@[simp] theorem initial_lookup (t : Term) (lineage : LineageId) :
    (initialWorld t lineage).heap.lookup (rootCell lineage) =
      some { origin := t, cache := Cache.suspended } := by
  simp [initialWorld, initialHeap, rootCell, Heap.lookup]

/-- Completed answer bag after a bounded number of machine steps. -/
def runAnswers (fuel : Nat) (t : Term) : List Outcome :=
  PrimeNeedReference.answers demandSpec fuel (initialMachine t)

set_option maxRecDepth 100000
set_option maxHeartbeats 400000

/-- Numerals evaluate to themselves in a handful of steps. -/
example : runAnswers 10 (.num 5) = [.value (.num 5)] := by
  decide

/-- Pairs are inert data: they complete with no further demand. -/
example : runAnswers 10 (.pair (.num 1) (.num 2)) =
    [.value (.pair (.num 1) (.num 2))] := by
  decide

/-- The `pair` rule never evaluates components, even nonterminating-
looking or stuck ones: this is the laziness axiom in machine form. -/
example : runAnswers 10 (.pair (.rcar (.num 1)) (.num 2)) =
    [.value (.pair (.rcar (.num 1)) (.num 2))] := by
  decide

/-- Addition of numerals computes through two subcell demands. -/
example : runAnswers 40 (.add (.num 1) (.num 2)) = [.value (.num 3)] := by
  decide

/-- `rcar` of a demanded pair penetrates the first component. -/
example : runAnswers 40 (.rcar (.pair (.add (.num 1) (.num 2)) (.num 9))) =
    [.value (.num 3)] := by
  decide

/-- `rcdr` of a demanded pair penetrates the second component. -/
example : runAnswers 40 (.rcdr (.pair (.num 9) (.add (.num 1) (.num 2)))) =
    [.value (.num 3)] := by
  decide

/-- Stuck is a stable fault, never a value: `rcar` of a numeral cannot
penetrate a constructor. -/
example : runAnswers 40 (.rcar (.num 7)) = [.stableFault ()] := by
  decide

/-! ## Well-formed worlds: allocation never collides

The simulation allocates fresh cells inside a lineage.  Collision is
impossible precisely because every cell present in the heap has a slot
strictly below the world's `nextCell` counter: the fresh cell at
`nextCell` can therefore never be present, so `allocate?` always
succeeds and the invariant is preserved. -/

/-- A world is *slot-bounded* when every populated cell id has slot
strictly below `nextCell`.  Allocation then always succeeds at the next
free slot. -/
def WellFormedWorld (world : World Term Rule Term Unit Nat Nat) : Prop :=
  ∀ cell : CellId, (world.heap.lookup cell).isSome = true →
    cell.slot < world.nextCell

/-- The initial world is slot-bounded (only slot 0 is populated). -/
theorem wellFormedWorld_initial (t : Term) (lineage : LineageId) :
    WellFormedWorld (initialWorld t lineage) := by
  intro cell hPresent
  simp only [initialWorld, initialHeap, rootCell, Heap.lookup] at hPresent
  split at hPresent
  · rename_i hEq
    subst hEq
    exact Nat.zero_lt_one
  · simp at hPresent

/-- The fresh cell of a slot-bounded world is absent from its heap. -/
theorem freshCell_absent_of_wellFormed
    {world : World Term Rule Term Unit Nat Nat}
    (hWF : WellFormedWorld world) (generation : Nat) :
    world.heap.lookup (world.freshCell generation) = none := by
  cases hL : world.heap.lookup (world.freshCell generation) with
  | none => rfl
  | some record =>
      exfalso
      have hSome :
          (world.heap.lookup (world.freshCell generation)).isSome =
            true := by
        simp [hL]
      have hSlot := hWF _ hSome
      simp [World.freshCell] at hSlot

/-- World-level allocation always succeeds in a slot-bounded world. -/
theorem allocate?_succeeds_of_wellFormed
    {world : World Term Rule Term Unit Nat Nat}
    (hWF : WellFormedWorld world) (origin : Term) (generation : Nat) :
    ∃ worldNext cell, world.allocate? origin generation =
      some (worldNext, cell) := by
  have hAbsent := freshCell_absent_of_wellFormed hWF generation
  have hInner : world.heap.allocate? (world.freshCell generation)
      origin =
      some
        { current :=
            Function.update world.heap.current
              (world.freshCell generation) (some ⟨origin, .suspended⟩)
          spine := .allocate (world.freshCell generation) origin ::
            world.heap.spine } := by
    simp [Heap.allocate?, hAbsent]
  exact
    ⟨({ world with
          heap :=
            { current :=
                Function.update world.heap.current
                  (world.freshCell generation) (some ⟨origin, .suspended⟩)
              spine := .allocate (world.freshCell generation) origin ::
                world.heap.spine }
          nextCell := world.nextCell + 1 }.record
          (.allocate (world.freshCell generation) origin)).1,
      world.freshCell generation, by
        simp [World.allocate?, hInner]⟩

/-- The slot invariant survives a world allocation. -/
theorem wellFormedWorld_allocate?
    {world worldNext : World Term Rule Term Unit Nat Nat}
    {origin : Term} {generation : Nat} {cell : CellId}
    (hWF : WellFormedWorld world)
    (hAlloc : world.allocate? origin generation = some (worldNext, cell)) :
    WellFormedWorld worldNext := by
  intro other hPresent
  have hNextCell := World.allocate?_nextCell hAlloc
  by_cases hSame : other = cell
  · subst other
    have hFresh := World.allocate?_fresh_cell hAlloc
    have hSlot : cell.slot = world.nextCell := by
      rw [hFresh]
      rfl
    omega
  · have hEq := World.allocate?_preserves_other hAlloc hSame
    rw [hEq] at hPresent
    have hBound := hWF other hPresent
    omega

/-- The slot invariant survives a cache update (`setKnownCache`) of a
cell that was already populated: `setKnownCache` changes only the
cache field of that record, so the populated set gains nothing and
`nextCell` is unchanged.  The prior-population hypothesis `hKnown` is
the machine's own discipline — cache replacement always reuses the
record from the preceding lookup (see `Heap.setKnownCache`). -/
theorem wellFormedWorld_setKnownCache
    {world : World Term Rule Term Unit Nat Nat}
    {cell : CellId} {record : CellRecord Term Term Unit}
    {state : Cache Term Unit}
    (hWF : WellFormedWorld world)
    (hKnown : world.heap.lookup cell = some record) :
    WellFormedWorld (world.setKnownCache cell record state) := by
  intro other hPresent
  have hNext : (world.setKnownCache cell record state).nextCell =
      world.nextCell := rfl
  rw [hNext]
  by_cases hSame : other = cell
  · subst other
    exact hWF cell (by simp [hKnown])
  · have hEq : (world.setKnownCache cell record state).heap.lookup other =
        world.heap.lookup other := by
      simp only [World.setKnownCache]
      exact Heap.setKnownCache_preserves_other world.heap record state hSame
    rw [hEq] at hPresent
    exact hWF other hPresent

/-! ## The forward simulation

`Eval t v` is realizable as a deterministic machine execution: forcing a
fresh suspended cell holding `t` reaches `.returned (.value v)` along a
unique path (`eval_force_completes`), and the top-level run therefore has
exactly one answer, `runAnswers_eq_singleton_of_eval`.

The fragment's executions are *forcing chains*: force a suspended cell,
run its one rule, commit the outcome to the cache, pop the stack.  Each
primitive transition is packaged as a symbolic singleton-step theorem
with universally quantified world, stack and work counters, so the
induction composes them at named junctions without ever unfolding the
receipt-laden intermediate worlds. -/

/-- The single local state each origin starts in.  (Every origin has
exactly one rule, `.evaluate`; see `alternatives_eq`.) -/
def initialState : Term → Local
  | .num n => .output (.value (.num n))
  | .pair a b => .output (.value (.pair a b))
  | .add a b => .addAllocLeft a b
  | .rcar t => .rcarAlloc t
  | .rcdr t => .rcdrAlloc t

@[simp] theorem alternatives_eq (t : Term) :
    alternatives t = [(.evaluate, initialState t)] := by
  cases t <;> rfl

/-- The base world of a forcing step: only the evaluator counter
advances. -/
def forceBase (world : World Term Rule Term Unit Nat Nat) :
    World Term Rule Term Unit Nat Nat :=
  { world with nextEvaluator := world.nextEvaluator + 1 }

/-- The world produced by forcing a suspended cell: the cell is marked
`.evaluating` under its new owner and the two receipts (evaluation
begun, rule chosen) are recorded.  This is exactly the world of the
suspended branch of `step` specialized to the single-rule fragment. -/
def forceWorld
    (world : World Term Rule Term Unit Nat Nat) (cell : CellId) (t : Term) :
    World Term Rule Term Unit Nat Nat :=
  recorded
    (recorded
      (((forceBase world).fork 0).setKnownCache cell ⟨t, .suspended⟩
        (.evaluating world.nextEvaluator))
      (.evaluate cell world.nextEvaluator))
    (.chooseRule cell .evaluate)

/-- The world produced by committing a successful outcome at a cell
whose cache is `.evaluating owner`: the cache becomes `.value v` and the
observation receipt is recorded. -/
def commitWorld
    (world : World Term Rule Term Unit Nat Nat) (cell : CellId) (t : Term)
    (owner : EvaluatorId) (v : Term) :
    World Term Rule Term Unit Nat Nat :=
  recorded
    (world.setKnownCache cell ⟨t, .evaluating owner⟩ (.value v))
    (.observe cell (.value v))

/-- Forcing a suspended cell is deterministic: it starts the unique rule
under the fresh evaluator and pushes the commit frame. -/
theorem step_force_suspended
    {world : World Term Rule Term Unit Nat Nat} {cell : CellId} {t : Term}
    {stack : List (Frame Resume)} {work : Work}
    (h : world.heap.lookup cell = some ⟨t, .suspended⟩) :
    step demandSpec ⟨world, .force cell stack, work⟩ =
      [⟨forceWorld world cell t,
        .run (initialState t) (.commit cell world.nextEvaluator :: stack),
        work.bump 1 1 2 0⟩] := by
  simp [step, h, demandSpec, alternatives_eq, branchAlternatives, forceWorld,
    initialState, forceBase, finished]

/-- A completed computation returns its outcome to the stack. -/
theorem step_run_of_done
    {world : World Term Rule Term Unit Nat Nat} {state : Local}
    {outcome : Outcome} {stack : List (Frame Resume)} {work : Work}
    (h : action state = .done outcome) :
    step demandSpec ⟨world, .run state stack, work⟩ =
      [⟨world, .returned outcome stack, work.bump 0 0 0 0⟩] := by
  simp [step, demandSpec, h, finished]

/-- A demand pushes the resume frame and forces the demanded cell. -/
theorem step_run_of_demand
    {world : World Term Rule Term Unit Nat Nat} {state : Local}
    {cell : CellId} {token : Resume} {stack : List (Frame Resume)}
    {work : Work}
    (h : action state = .demand cell token) :
    step demandSpec ⟨world, .run state stack, work⟩ =
      [⟨world, .force cell (.resume token :: stack), work.bump 0 0 0 0⟩] := by
  simp [step, demandSpec, h, finished]

/-- A successful allocation advances the chain with the fresh cell. -/
theorem step_run_of_allocate
    {world world' : World Term Rule Term Unit Nat Nat} {state : Local}
    {origin : Term} {token : Resume} {cell : CellId}
    {stack : List (Frame Resume)} {work : Work}
    (hAction : action state = .allocate origin token)
    (hAlloc : world.allocate? origin = some (world', cell)) :
    step demandSpec ⟨world, .run state stack, work⟩ =
      [⟨world', .run (demandSpec.afterAllocation token cell) stack,
        work.bump 1 1 1 1⟩] := by
  simp [step, demandSpec, hAction, hAlloc, finished]

/-- A returned outcome resumes the waiting continuation. -/
theorem step_returned_resume
    {world : World Term Rule Term Unit Nat Nat} {outcome : Outcome}
    {token : Resume} {stack : List (Frame Resume)} {work : Work} :
    step demandSpec ⟨world, .returned outcome (.resume token :: stack),
        work⟩ =
      [⟨world, .run (demandSpec.afterDemand token outcome) stack,
        work.bump 0 0 0 0⟩] := by
  simp [step, demandSpec, finished]

/-- A successful outcome commits to the cache of the cell it came from
(owner check passes when the cache is the evaluating one issued by the
forcing step). -/
theorem step_returned_commit_value
    {world : World Term Rule Term Unit Nat Nat} {cell : CellId} {t : Term}
    {owner : EvaluatorId} {v : Term} {stack : List (Frame Resume)}
    {work : Work}
    (h : world.heap.lookup cell = some ⟨t, .evaluating owner⟩) :
    step demandSpec
        ⟨world, .returned (.value v) (.commit cell owner :: stack), work⟩ =
      [⟨commitWorld world cell t owner v, .returned (.value v) stack,
        work.bump 1 1 1 0⟩] := by
  simp [step, h, commitWorld, finished]

/-- An empty stack halts with the returned outcome. -/
theorem step_returned_empty
    {world : World Term Rule Term Unit Nat Nat} {outcome : Outcome}
    {work : Work} :
    step demandSpec ⟨world, .returned outcome [], work⟩ =
      [⟨world, .halted outcome, work.bump 0 0 0 0⟩] := by
  simp [step, finished]

/-! ### Companion properties of the forced and committed worlds -/

/-- Forcing marks the forced cell `.evaluating` under its new owner. -/
theorem forceWorld_lookup_self
    {world : World Term Rule Term Unit Nat Nat} {cell : CellId} {t : Term}
    (_h : world.heap.lookup cell = some ⟨t, .suspended⟩) :
    (forceWorld world cell t).heap.lookup cell =
      some ⟨t, .evaluating world.nextEvaluator⟩ := by
  simp [forceWorld]

/-- Forcing touches no other cell. -/
theorem forceWorld_lookup_other
    {world : World Term Rule Term Unit Nat Nat} {cell other : CellId}
    {t : Term} (hOther : other ≠ cell) :
    (forceWorld world cell t).heap.lookup other =
      world.heap.lookup other := by
  have hHeap : (forceWorld world cell t).heap =
      ((forceBase world).fork 0).heap.setKnownCache cell ⟨t, .suspended⟩
        (.evaluating world.nextEvaluator) := by
    simp [forceWorld]
  rw [hHeap,
    Heap.setKnownCache_preserves_other _ _ _ hOther,
    World.fork_preserves_heap]
  rfl

/-- Forcing preserves the slot bound: only the forced cell's cache
changes, and `nextCell` is untouched. -/
theorem forceWorld_wellFormed
    {world : World Term Rule Term Unit Nat Nat} {cell : CellId} {t : Term}
    (hWF : WellFormedWorld world)
    (h : world.heap.lookup cell = some ⟨t, .suspended⟩) :
    WellFormedWorld (forceWorld world cell t) := by
  have hWF' : WellFormedWorld ((forceBase world).fork 0) := hWF
  have hKnown : ((forceBase world).fork 0).heap.lookup cell =
      some ⟨t, .suspended⟩ := h
  exact wellFormedWorld_setKnownCache hWF' hKnown

/-- Forcing leaves the allocation counter alone. -/
theorem forceWorld_nextCell
    {world : World Term Rule Term Unit Nat Nat} {cell : CellId} {t : Term} :
    (forceWorld world cell t).nextCell = world.nextCell :=
  rfl

/-- A cell present before an allocation is never the allocated one:
presence bounds its slot below `nextCell`, while the fresh cell's slot
is exactly `nextCell`. -/
theorem present_ne_fresh_of_allocate
    {world world' : World Term Rule Term Unit Nat Nat} {origin : Term}
    {generation : Nat} {cell c : CellId}
    (hWF : WellFormedWorld world)
    (hAlloc : world.allocate? origin generation = some (world', cell))
    (hPresent : (world.heap.lookup c).isSome = true) :
    c ≠ cell := by
  intro hEq
  have hSlot := hWF c hPresent
  rw [hEq, World.allocate?_fresh_cell hAlloc] at hSlot
  simp [World.freshCell] at hSlot

/-- Committing sets the committed cell's cache to the returned value. -/
theorem commitWorld_lookup_self
    {world : World Term Rule Term Unit Nat Nat} {cell : CellId} {t : Term}
    {owner : EvaluatorId} {v : Term} :
    (commitWorld world cell t owner v).heap.lookup cell =
      some ⟨t, .value v⟩ := by
  simp [commitWorld]

/-- Committing touches no other cell. -/
theorem commitWorld_lookup_other
    {world : World Term Rule Term Unit Nat Nat} {cell other : CellId}
    {t : Term} {owner : EvaluatorId} {v : Term} (hOther : other ≠ cell) :
    (commitWorld world cell t owner v).heap.lookup other =
      world.heap.lookup other := by
  have hHeap : (commitWorld world cell t owner v).heap =
      world.heap.setKnownCache cell ⟨t, .evaluating owner⟩ (.value v) := by
    simp [commitWorld]
  rw [hHeap,
    Heap.setKnownCache_preserves_other _ _ _ hOther]

/-- Committing preserves the slot bound. -/
theorem commitWorld_wellFormed
    {world : World Term Rule Term Unit Nat Nat} {cell : CellId} {t : Term}
    {owner : EvaluatorId} {v : Term}
    (hWF : WellFormedWorld world)
    (h : world.heap.lookup cell = some ⟨t, .evaluating owner⟩) :
    WellFormedWorld (commitWorld world cell t owner v) :=
  wellFormedWorld_setKnownCache hWF h

/-- **Forward simulation.**  Forcing a suspended cell holding `t`
reaches `.returned (.value v)` along the unique deterministic path
whenever `Eval t v`.  The conclusion carries everything the recursive
cases need: the forced cell ends committed to `v`, the slot invariant
survives, and cells older than the forced one keep their records
(bit-for-bit) — the machine never clobbers work it did not allocate. -/
theorem eval_force_completes {t v : Term} (h : Eval t v) :
    ∀ (world : World Term Rule Term Unit Nat Nat) (cell : CellId)
      (stack : List (Frame Resume)) (work : Work),
      WellFormedWorld world →
      world.heap.lookup cell = some ⟨t, .suspended⟩ →
      ∃ (length : Nat) (world' : World Term Rule Term Unit Nat Nat)
        (work' : Work),
        UniqueSteps demandSpec length
          ⟨world, .force cell stack, work⟩
          ⟨world', .returned (.value v) stack, work'⟩ ∧
        world'.heap.lookup cell = some ⟨t, .value v⟩ ∧
        WellFormedWorld world' ∧
        ∀ c : CellId, c ≠ cell → (world.heap.lookup c).isSome = true →
          world'.heap.lookup c = world.heap.lookup c := by
  induction h with
  | num n =>
      intro world cell stack work hWF hLookup
      refine ⟨_, commitWorld (forceWorld world cell (.num n)) cell (.num n)
        world.nextEvaluator (.num n), _,
        UniqueSteps.trans demandSpec
          (UniqueSteps.cons (by rw [step_force_suspended hLookup])
            (UniqueSteps.refl _))
          (UniqueSteps.trans demandSpec
            (UniqueSteps.cons (by rw [step_run_of_done rfl])
              (UniqueSteps.refl _))
            (UniqueSteps.cons
              (by rw [step_returned_commit_value
                (forceWorld_lookup_self hLookup)])
              (UniqueSteps.refl _))), ?_, ?_, ?_⟩
      · exact commitWorld_lookup_self
      · exact commitWorld_wellFormed
          (forceWorld_wellFormed hWF hLookup)
          (forceWorld_lookup_self hLookup)
      · intro c hc _
        rw [commitWorld_lookup_other hc, forceWorld_lookup_other hc]
  | pair a b =>
      intro world cell stack work hWF hLookup
      refine ⟨_, commitWorld (forceWorld world cell (.pair a b)) cell
        (.pair a b) world.nextEvaluator (.pair a b), _,
        UniqueSteps.trans demandSpec
          (UniqueSteps.cons (by rw [step_force_suspended hLookup])
            (UniqueSteps.refl _))
          (UniqueSteps.trans demandSpec
            (UniqueSteps.cons (by rw [step_run_of_done rfl])
              (UniqueSteps.refl _))
            (UniqueSteps.cons
              (by rw [step_returned_commit_value
                (forceWorld_lookup_self hLookup)])
              (UniqueSteps.refl _))), ?_, ?_, ?_⟩
      · exact commitWorld_lookup_self
      · exact commitWorld_wellFormed
          (forceWorld_wellFormed hWF hLookup)
          (forceWorld_lookup_self hLookup)
      · intro c hc _
        rw [commitWorld_lookup_other hc, forceWorld_lookup_other hc]
  | add ha hb iha ihb =>
      rename_i a b x y
      intro world cell stack work hWF hLookup
      -- The two fresh subcells and their slot facts.
      have hFW_wf := forceWorld_wellFormed hWF hLookup
      obtain ⟨worldA, cellA, hAllocA⟩ :=
        allocate?_succeeds_of_wellFormed hFW_wf a 0
      have hA_wf := wellFormedWorld_allocate? hFW_wf hAllocA
      obtain ⟨worldB, cellB, hAllocB⟩ :=
        allocate?_succeeds_of_wellFormed hA_wf b 0
      have hB_wf := wellFormedWorld_allocate? hA_wf hAllocB
      have hLookupA : worldA.heap.lookup cellA = some ⟨a, .suspended⟩ :=
        World.allocate?_lookup_same hAllocA
      have hSlotA : cellA.slot = world.nextCell := by
        rw [World.allocate?_fresh_cell hAllocA]; rfl
      have hNextA : worldA.nextCell = world.nextCell + 1 := by
        rw [World.allocate?_nextCell hAllocA, forceWorld_nextCell]
      have hSlotB : cellB.slot = world.nextCell + 1 := by
        rw [← hNextA, World.allocate?_fresh_cell hAllocB]; rfl
      have hB_ne_A : cellB ≠ cellA := by
        intro hEq; rw [hEq, hSlotA] at hSlotB; omega
      -- The root cell is evaluating in the forced world, and fresh cells
      -- are never cells that existed before their allocation.
      have hCellInFW :
          ((forceWorld world cell (.add a b)).heap.lookup cell).isSome =
            true := by
        rw [forceWorld_lookup_self hLookup]; rfl
      have hNA : cell ≠ cellA :=
        present_ne_fresh_of_allocate hFW_wf hAllocA hCellInFW
      have hCellInA : (worldA.heap.lookup cell).isSome = true := by
        rw [World.allocate?_preserves_other hAllocA hNA]; exact hCellInFW
      have hNB : cell ≠ cellB :=
        present_ne_fresh_of_allocate hA_wf hAllocB hCellInA
      have hCellW_B : worldB.heap.lookup cell =
          some ⟨.add a b, .evaluating world.nextEvaluator⟩ := by
        rw [World.allocate?_preserves_other hAllocB hNB,
          World.allocate?_preserves_other hAllocA hNA,
          forceWorld_lookup_self hLookup]
      have hCellInB : (worldB.heap.lookup cell).isSome = true := by
        rw [hCellW_B]; rfl
      -- Forcing the two subcells, in order, by the induction hypotheses.
      have hLookupB : worldB.heap.lookup cellB = some ⟨b, .suspended⟩ :=
        World.allocate?_lookup_same hAllocB
      have hLookupA_in_B : worldB.heap.lookup cellA =
          some ⟨a, .suspended⟩ := by
        rw [World.allocate?_preserves_other hAllocB hB_ne_A.symm]
        exact hLookupA
      have hPre : UniqueSteps demandSpec 4
          ⟨world, .force cell stack, work⟩
          ⟨worldB, .force cellA
            (.resume (.addLeftReturned cellB) ::
              .commit cell world.nextEvaluator :: stack),
            (((work.bump 1 1 2 0).bump 1 1 1 1).bump 1 1 1 1).bump
              0 0 0 0⟩ :=
        UniqueSteps.cons (by rw [step_force_suspended hLookup])
          (UniqueSteps.cons (by rw [step_run_of_allocate rfl hAllocA])
            (UniqueSteps.cons (by rw [step_run_of_allocate rfl hAllocB])
              (UniqueSteps.cons (by rw [step_run_of_demand rfl])
                (UniqueSteps.refl _))))
      obtain ⟨lenA, worldA', workA', hStepsA, _hCellA_val, hWF_A',
          hFrameA⟩ :=
        iha worldB cellA
          (.resume (.addLeftReturned cellB) ::
            .commit cell world.nextEvaluator :: stack)
          (((((work.bump 1 1 2 0).bump 1 1 1 1).bump 1 1 1 1).bump
              0 0 0 0 : Work)) hB_wf hLookupA_in_B
      -- The left evaluation preserves the right cell and the root.
      have hCellB_in_A' : worldA'.heap.lookup cellB =
          some ⟨b, .suspended⟩ := by
        rw [hFrameA cellB hB_ne_A (by rw [hLookupB]; rfl)]
        exact hLookupB
      have hCellW_A' : worldA'.heap.lookup cell =
          some ⟨.add a b, .evaluating world.nextEvaluator⟩ := by
        rw [hFrameA cell hNA hCellInB]; exact hCellW_B
      have hCellInA' : (worldA'.heap.lookup cell).isSome = true := by
        rw [hCellW_A']; rfl
      have hPost1 : UniqueSteps demandSpec 2
          ⟨worldA', .returned (.value (.num x))
            (.resume (.addLeftReturned cellB) ::
              .commit cell world.nextEvaluator :: stack), workA'⟩
          ⟨worldA', .force cellB
            (.resume (.addRightReturned x) ::
              .commit cell world.nextEvaluator :: stack),
            (workA'.bump 0 0 0 0).bump 0 0 0 0⟩ :=
        UniqueSteps.cons (by rw [step_returned_resume])
          (UniqueSteps.cons (by rw [step_run_of_demand rfl])
            (UniqueSteps.refl _))
      obtain ⟨lenB, worldB', workB', hStepsB, _hCellB_val, hWF_B',
          hFrameB⟩ :=
        ihb worldA' cellB
          (.resume (.addRightReturned x) ::
            .commit cell world.nextEvaluator :: stack)
          ((workA'.bump 0 0 0 0).bump 0 0 0 0)
          hWF_A' hCellB_in_A'
      -- The right evaluation preserves the root as well.
      have hCellW' : worldB'.heap.lookup cell =
          some ⟨.add a b, .evaluating world.nextEvaluator⟩ := by
        rw [hFrameB cell hNB hCellInA']; exact hCellW_A'
      have hPost2 : UniqueSteps demandSpec 3
          ⟨worldB', .returned (.value (.num y))
            (.resume (.addRightReturned x) ::
              .commit cell world.nextEvaluator :: stack), workB'⟩
          ⟨commitWorld worldB' cell (.add a b) world.nextEvaluator
              (.num (x + y)),
            .returned (.value (.num (x + y))) stack,
            ((workB'.bump 0 0 0 0).bump 0 0 0 0).bump 1 1 1 0⟩ :=
        UniqueSteps.cons (by rw [step_returned_resume])
          (UniqueSteps.cons (by rw [step_run_of_done rfl])
            (UniqueSteps.cons (by rw [step_returned_commit_value hCellW'])
              (UniqueSteps.refl _)))
      refine ⟨_, _, _,
        UniqueSteps.trans demandSpec hPre
          (UniqueSteps.trans demandSpec hStepsA
            (UniqueSteps.trans demandSpec hPost1
              (UniqueSteps.trans demandSpec hStepsB hPost2))),
        commitWorld_lookup_self,
        commitWorld_wellFormed hWF_B' hCellW', ?_⟩
      intro c hc hPresent
      have hPresentFW : ((forceWorld world cell
          (.add a b)).heap.lookup c).isSome = true := by
        rw [forceWorld_lookup_other hc]; exact hPresent
      have hCA : c ≠ cellA :=
        present_ne_fresh_of_allocate hFW_wf hAllocA hPresentFW
      have hPresentA : (worldA.heap.lookup c).isSome = true := by
        rw [World.allocate?_preserves_other hAllocA hCA]; exact hPresentFW
      have hCB : c ≠ cellB :=
        present_ne_fresh_of_allocate hA_wf hAllocB hPresentA
      have hPresentB : (worldB.heap.lookup c).isSome = true := by
        rw [World.allocate?_preserves_other hAllocB hCB]; exact hPresentA
      have hPresentA' : (worldA'.heap.lookup c).isSome = true := by
        rw [hFrameA c hCA hPresentB]; exact hPresentB
      rw [commitWorld_lookup_other hc, hFrameB c hCB hPresentA',
        hFrameA c hCA hPresentB,
        World.allocate?_preserves_other hAllocB hCB,
        World.allocate?_preserves_other hAllocA hCA,
        forceWorld_lookup_other hc]
  | rcar ht ha iht iha =>
      rename_i u p q w
      intro world cell stack work hWF hLookup
      -- The demanded outer cell.
      have hFW_wf := forceWorld_wellFormed hWF hLookup
      obtain ⟨worldT, cellT, hAllocT⟩ :=
        allocate?_succeeds_of_wellFormed hFW_wf u 0
      have hT_wf := wellFormedWorld_allocate? hFW_wf hAllocT
      have hLookupT : worldT.heap.lookup cellT = some ⟨u, .suspended⟩ :=
        World.allocate?_lookup_same hAllocT
      have hCellInFW :
          ((forceWorld world cell (.rcar u)).heap.lookup cell).isSome =
            true := by
        rw [forceWorld_lookup_self hLookup]; rfl
      have hNT : cell ≠ cellT :=
        present_ne_fresh_of_allocate hFW_wf hAllocT hCellInFW
      have hCellW_T : worldT.heap.lookup cell =
          some ⟨.rcar u, .evaluating world.nextEvaluator⟩ := by
        rw [World.allocate?_preserves_other hAllocT hNT,
          forceWorld_lookup_self hLookup]
      have hCellInT : (worldT.heap.lookup cell).isSome = true := by
        rw [hCellW_T]; rfl
      have hPre : UniqueSteps demandSpec 3
          ⟨world, .force cell stack, work⟩
          ⟨worldT, .force cellT
            (.resume .rcarReturned ::
              .commit cell world.nextEvaluator :: stack),
            ((work.bump 1 1 2 0).bump 1 1 1 1).bump 0 0 0 0⟩ :=
        UniqueSteps.cons (by rw [step_force_suspended hLookup])
          (UniqueSteps.cons (by rw [step_run_of_allocate rfl hAllocT])
            (UniqueSteps.cons (by rw [step_run_of_demand rfl])
              (UniqueSteps.refl _)))
      obtain ⟨lenT, worldT', workT', hStepsT, _hT_val, hWF_T',
          hFrameT⟩ :=
        iht worldT cellT
          (.resume .rcarReturned ::
            .commit cell world.nextEvaluator :: stack)
          ((((work.bump 1 1 2 0).bump 1 1 1 1).bump 0 0 0 0 : Work))
          hT_wf hLookupT
      -- The demanded pair penetrates one layer: allocate the first
      -- component in the post-demand world.
      have hCellW_T' : worldT'.heap.lookup cell =
          some ⟨.rcar u, .evaluating world.nextEvaluator⟩ := by
        rw [hFrameT cell hNT hCellInT]; exact hCellW_T
      have hCellInT' : (worldT'.heap.lookup cell).isSome = true := by
        rw [hCellW_T']; rfl
      obtain ⟨worldC, cellC, hAllocC⟩ :=
        allocate?_succeeds_of_wellFormed hWF_T' p 0
      have hC_wf := wellFormedWorld_allocate? hWF_T' hAllocC
      have hNC : cell ≠ cellC :=
        present_ne_fresh_of_allocate hWF_T' hAllocC hCellInT'
      have hLookupC : worldC.heap.lookup cellC = some ⟨p, .suspended⟩ :=
        World.allocate?_lookup_same hAllocC
      have hPost1 : UniqueSteps demandSpec 3
          ⟨worldT', .returned (.value (.pair p q))
            (.resume .rcarReturned ::
              .commit cell world.nextEvaluator :: stack), workT'⟩
          ⟨worldC, .force cellC
            (.resume .rcarComponentReturned ::
              .commit cell world.nextEvaluator :: stack),
            ((workT'.bump 0 0 0 0).bump 1 1 1 1).bump 0 0 0 0⟩ :=
        UniqueSteps.cons (by rw [step_returned_resume])
          (UniqueSteps.cons (by rw [step_run_of_allocate rfl hAllocC])
            (UniqueSteps.cons (by rw [step_run_of_demand rfl])
              (UniqueSteps.refl _)))
      have hCellW_C : worldC.heap.lookup cell =
          some ⟨.rcar u, .evaluating world.nextEvaluator⟩ := by
        rw [World.allocate?_preserves_other hAllocC hNC]
        exact hCellW_T'
      have hCellInC : (worldC.heap.lookup cell).isSome = true := by
        rw [hCellW_C]; rfl
      obtain ⟨lenC, worldC', workC', hStepsC, _hC_val, hWF_C',
          hFrameC⟩ :=
        iha worldC cellC
          (.resume .rcarComponentReturned ::
            .commit cell world.nextEvaluator :: stack)
          ((((workT'.bump 0 0 0 0).bump 1 1 1 1).bump 0 0 0 0 : Work))
          hC_wf hLookupC
      have hCellW' : worldC'.heap.lookup cell =
          some ⟨.rcar u, .evaluating world.nextEvaluator⟩ := by
        rw [hFrameC cell hNC hCellInC]; exact hCellW_C
      have hPost2 : UniqueSteps demandSpec 3
          ⟨worldC', .returned (.value w)
            (.resume .rcarComponentReturned ::
              .commit cell world.nextEvaluator :: stack), workC'⟩
          ⟨commitWorld worldC' cell (.rcar u) world.nextEvaluator w,
            .returned (.value w) stack,
            ((workC'.bump 0 0 0 0).bump 0 0 0 0).bump 1 1 1 0⟩ :=
        UniqueSteps.cons (by rw [step_returned_resume])
          (UniqueSteps.cons (by rw [step_run_of_done rfl])
            (UniqueSteps.cons (by rw [step_returned_commit_value hCellW'])
              (UniqueSteps.refl _)))
      refine ⟨_, _, _,
        UniqueSteps.trans demandSpec hPre
          (UniqueSteps.trans demandSpec hStepsT
            (UniqueSteps.trans demandSpec hPost1
              (UniqueSteps.trans demandSpec hStepsC hPost2))),
        commitWorld_lookup_self,
        commitWorld_wellFormed hWF_C' hCellW', ?_⟩
      intro c hc hPresent
      have hPresentFW : ((forceWorld world cell
          (.rcar u)).heap.lookup c).isSome = true := by
        rw [forceWorld_lookup_other hc]; exact hPresent
      have hCT : c ≠ cellT :=
        present_ne_fresh_of_allocate hFW_wf hAllocT hPresentFW
      have hPresentT : (worldT.heap.lookup c).isSome = true := by
        rw [World.allocate?_preserves_other hAllocT hCT]; exact hPresentFW
      have hPresentT' : (worldT'.heap.lookup c).isSome = true := by
        rw [hFrameT c hCT hPresentT]; exact hPresentT
      have hCC : c ≠ cellC :=
        present_ne_fresh_of_allocate hWF_T' hAllocC hPresentT'
      have hPresentC : (worldC.heap.lookup c).isSome = true := by
        rw [World.allocate?_preserves_other hAllocC hCC]; exact hPresentT'
      rw [commitWorld_lookup_other hc, hFrameC c hCC hPresentC,
        World.allocate?_preserves_other hAllocC hCC,
        hFrameT c hCT hPresentT,
        World.allocate?_preserves_other hAllocT hCT,
        forceWorld_lookup_other hc]
  | rcdr ht hb iht ihb =>
      rename_i u p q w
      intro world cell stack work hWF hLookup
      -- The demanded outer cell.
      have hFW_wf := forceWorld_wellFormed hWF hLookup
      obtain ⟨worldT, cellT, hAllocT⟩ :=
        allocate?_succeeds_of_wellFormed hFW_wf u 0
      have hT_wf := wellFormedWorld_allocate? hFW_wf hAllocT
      have hLookupT : worldT.heap.lookup cellT = some ⟨u, .suspended⟩ :=
        World.allocate?_lookup_same hAllocT
      have hCellInFW :
          ((forceWorld world cell (.rcdr u)).heap.lookup cell).isSome =
            true := by
        rw [forceWorld_lookup_self hLookup]; rfl
      have hNT : cell ≠ cellT :=
        present_ne_fresh_of_allocate hFW_wf hAllocT hCellInFW
      have hCellW_T : worldT.heap.lookup cell =
          some ⟨.rcdr u, .evaluating world.nextEvaluator⟩ := by
        rw [World.allocate?_preserves_other hAllocT hNT,
          forceWorld_lookup_self hLookup]
      have hCellInT : (worldT.heap.lookup cell).isSome = true := by
        rw [hCellW_T]; rfl
      have hPre : UniqueSteps demandSpec 3
          ⟨world, .force cell stack, work⟩
          ⟨worldT, .force cellT
            (.resume .rcdrReturned ::
              .commit cell world.nextEvaluator :: stack),
            ((work.bump 1 1 2 0).bump 1 1 1 1).bump 0 0 0 0⟩ :=
        UniqueSteps.cons (by rw [step_force_suspended hLookup])
          (UniqueSteps.cons (by rw [step_run_of_allocate rfl hAllocT])
            (UniqueSteps.cons (by rw [step_run_of_demand rfl])
              (UniqueSteps.refl _)))
      obtain ⟨lenT, worldT', workT', hStepsT, _hT_val, hWF_T',
          hFrameT⟩ :=
        iht worldT cellT
          (.resume .rcdrReturned ::
            .commit cell world.nextEvaluator :: stack)
          ((((work.bump 1 1 2 0).bump 1 1 1 1).bump 0 0 0 0 : Work))
          hT_wf hLookupT
      -- The demanded pair penetrates one layer: allocate the second
      -- component in the post-demand world.
      have hCellW_T' : worldT'.heap.lookup cell =
          some ⟨.rcdr u, .evaluating world.nextEvaluator⟩ := by
        rw [hFrameT cell hNT hCellInT]; exact hCellW_T
      have hCellInT' : (worldT'.heap.lookup cell).isSome = true := by
        rw [hCellW_T']; rfl
      obtain ⟨worldC, cellC, hAllocC⟩ :=
        allocate?_succeeds_of_wellFormed hWF_T' q 0
      have hC_wf := wellFormedWorld_allocate? hWF_T' hAllocC
      have hNC : cell ≠ cellC :=
        present_ne_fresh_of_allocate hWF_T' hAllocC hCellInT'
      have hLookupC : worldC.heap.lookup cellC = some ⟨q, .suspended⟩ :=
        World.allocate?_lookup_same hAllocC
      have hPost1 : UniqueSteps demandSpec 3
          ⟨worldT', .returned (.value (.pair p q))
            (.resume .rcdrReturned ::
              .commit cell world.nextEvaluator :: stack), workT'⟩
          ⟨worldC, .force cellC
            (.resume .rcdrComponentReturned ::
              .commit cell world.nextEvaluator :: stack),
            ((workT'.bump 0 0 0 0).bump 1 1 1 1).bump 0 0 0 0⟩ :=
        UniqueSteps.cons (by rw [step_returned_resume])
          (UniqueSteps.cons (by rw [step_run_of_allocate rfl hAllocC])
            (UniqueSteps.cons (by rw [step_run_of_demand rfl])
              (UniqueSteps.refl _)))
      have hCellW_C : worldC.heap.lookup cell =
          some ⟨.rcdr u, .evaluating world.nextEvaluator⟩ := by
        rw [World.allocate?_preserves_other hAllocC hNC]
        exact hCellW_T'
      have hCellInC : (worldC.heap.lookup cell).isSome = true := by
        rw [hCellW_C]; rfl
      obtain ⟨lenC, worldC', workC', hStepsC, _hC_val, hWF_C',
          hFrameC⟩ :=
        ihb worldC cellC
          (.resume .rcdrComponentReturned ::
            .commit cell world.nextEvaluator :: stack)
          ((((workT'.bump 0 0 0 0).bump 1 1 1 1).bump 0 0 0 0 : Work))
          hC_wf hLookupC
      have hCellW' : worldC'.heap.lookup cell =
          some ⟨.rcdr u, .evaluating world.nextEvaluator⟩ := by
        rw [hFrameC cell hNC hCellInC]; exact hCellW_C
      have hPost2 : UniqueSteps demandSpec 3
          ⟨worldC', .returned (.value w)
            (.resume .rcdrComponentReturned ::
              .commit cell world.nextEvaluator :: stack), workC'⟩
          ⟨commitWorld worldC' cell (.rcdr u) world.nextEvaluator w,
            .returned (.value w) stack,
            ((workC'.bump 0 0 0 0).bump 0 0 0 0).bump 1 1 1 0⟩ :=
        UniqueSteps.cons (by rw [step_returned_resume])
          (UniqueSteps.cons (by rw [step_run_of_done rfl])
            (UniqueSteps.cons (by rw [step_returned_commit_value hCellW'])
              (UniqueSteps.refl _)))
      refine ⟨_, _, _,
        UniqueSteps.trans demandSpec hPre
          (UniqueSteps.trans demandSpec hStepsT
            (UniqueSteps.trans demandSpec hPost1
              (UniqueSteps.trans demandSpec hStepsC hPost2))),
        commitWorld_lookup_self,
        commitWorld_wellFormed hWF_C' hCellW', ?_⟩
      intro c hc hPresent
      have hPresentFW : ((forceWorld world cell
          (.rcdr u)).heap.lookup c).isSome = true := by
        rw [forceWorld_lookup_other hc]; exact hPresent
      have hCT : c ≠ cellT :=
        present_ne_fresh_of_allocate hFW_wf hAllocT hPresentFW
      have hPresentT : (worldT.heap.lookup c).isSome = true := by
        rw [World.allocate?_preserves_other hAllocT hCT]; exact hPresentFW
      have hPresentT' : (worldT'.heap.lookup c).isSome = true := by
        rw [hFrameT c hCT hPresentT]; exact hPresentT
      have hCC : c ≠ cellC :=
        present_ne_fresh_of_allocate hWF_T' hAllocC hPresentT'
      have hPresentC : (worldC.heap.lookup c).isSome = true := by
        rw [World.allocate?_preserves_other hAllocC hCC]; exact hPresentT'
      rw [commitWorld_lookup_other hc, hFrameC c hCC hPresentC,
        World.allocate?_preserves_other hAllocC hCC,
        hFrameT c hCT hPresentT,
        World.allocate?_preserves_other hAllocT hCT,
        forceWorld_lookup_other hc]

/-- The relational evaluation of a closed term runs to a halted machine
on the heap need-machine: force the root cell, compute, halt. -/
theorem eval_steps_to_halted {t v : Term} (h : Eval t v) :
    ∃ (length : Nat) (world' : World Term Rule Term Unit Nat Nat)
      (work' : Work),
      UniqueSteps demandSpec length (initialMachine t)
        ⟨world', .halted (.value v), work'⟩ := by
  obtain ⟨len, world', work', hSteps, -, -, -⟩ :=
    eval_force_completes h (initialWorld t 1) (rootCell 1) [] {}
      (wellFormedWorld_initial t 1) (initial_lookup t 1)
  have hSnoc : UniqueSteps demandSpec 1
      ⟨world', .returned (.value v) [], work'⟩
      ⟨world', .halted (.value v), work'.bump 0 0 0 0⟩ :=
    UniqueSteps.cons (by rw [step_returned_empty]) (UniqueSteps.refl _)
  exact ⟨_, _, _, UniqueSteps.trans demandSpec hSteps hSnoc⟩

/-- **The simulation made observable.**  A terminating bounded run of the
machine on a relational value has exactly one answer, and it is that
value: the machine connects to the demand semantics with no observational
wiggle room. -/
theorem runAnswers_eq_singleton_of_eval {t v : Term} (h : Eval t v) :
    ∃ fuel : Nat, runAnswers fuel t = [.value v] := by
  obtain ⟨len, world', work', hExec⟩ := eval_steps_to_halted h
  refine ⟨len, ?_⟩
  unfold runAnswers answers
  rw [UniqueSteps.runFrontier_eq demandSpec hExec]
  rfl

/-- The heap machine and the fuel-bounded evaluator agree on values:
any `done` of `evalF` is the machine's unique answer.  This closes the
triangle `evalF` (functional canary) ↔ `Eval` (relational semantics,
`evalF_agrees`) ↔ machine executions (this module). -/
theorem runAnswers_eq_singleton_of_evalF_done {t v : Term} {n : Nat}
    (h : DemandSemantics.evalF n t = .done v) :
    ∃ fuel : Nat, runAnswers fuel t = [.value v] :=
  runAnswers_eq_singleton_of_eval
    (DemandSemantics.evalF_agrees_backward n t v h)

end Mettapedia.Languages.MeTTa.PrimeDemandNeedSimulation

