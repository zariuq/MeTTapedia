import Mettapedia.Languages.MeTTa.PrimeNeedReferenceSemantics

/-!
# Representation changes of the owned Need machine

Language data may change representation while machine-owned cell identities,
owners, branch occurrences, receipts and work remain fixed. Exact compatibility
with the language-local specification entails commutation of the actual machine
transition and bounded execution, including faults, resampling and duplicate
alternatives. No logical validity or effect erasure follows from these laws.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeNeedRepresentation

open PrimeNeedReference

variable {Origin Local Resume Rule Value StableFault RetryableFault Effect : Type*}
  {Origin' Local' Resume' Rule' Value' StableFault' RetryableFault' Effect' : Type*}

/-- Only language data is mapped. Machine-owned coordinates are unchanged. -/
structure Mapping (Origin Local Resume Rule Value StableFault RetryableFault Effect
    Origin' Local' Resume' Rule' Value' StableFault' RetryableFault' Effect' : Type*) where
  origin : Origin → Origin'
  state : Local → Local'
  resume : Resume → Resume'
  rule : Rule → Rule'
  value : Value → Value'
  stableFault : StableFault → StableFault'
  retryableFault : RetryableFault → RetryableFault'
  effect : Effect → Effect'

namespace Mapping

variable (mapping : Mapping Origin Local Resume Rule Value StableFault RetryableFault Effect
  Origin' Local' Resume' Rule' Value' StableFault' RetryableFault' Effect')

def mapRetry : RetryReason RetryableFault → RetryReason RetryableFault'
  | .domain fault => .domain (mapping.retryableFault fault)
  | .blackhole cell => .blackhole cell
  | .outOfScope cell => .outOfScope cell
  | .noRule cell => .noRule cell
  | .ownershipLost cell expected actual => .ownershipLost cell expected actual
  | .allocationCollision cell => .allocationCollision cell

def mapOutcome : Produced Value StableFault RetryableFault →
    Produced Value' StableFault' RetryableFault'
  | .value value => .value (mapping.value value)
  | .stableFault fault => .stableFault (mapping.stableFault fault)
  | .retryableFault reason => .retryableFault (mapping.mapRetry reason)

def mapCache : Cache Value StableFault → Cache Value' StableFault'
  | .suspended => .suspended
  | .evaluating owner => .evaluating owner
  | .value value => .value (mapping.value value)
  | .stableFault fault => .stableFault (mapping.stableFault fault)

def mapRecord (record : CellRecord Origin Value StableFault) :
    CellRecord Origin' Value' StableFault' :=
  ⟨mapping.origin record.origin, mapping.mapCache record.cache⟩

def mapUpdate : HeapUpdate Origin Value StableFault → HeapUpdate Origin' Value' StableFault'
  | .allocate cell origin => .allocate cell (mapping.origin origin)
  | .cache cell state => .cache cell (mapping.mapCache state)

def mapHeap (heap : Heap Origin Value StableFault) : Heap Origin' Value' StableFault' where
  current cell := (heap.current cell).map mapping.mapRecord
  spine := heap.spine.map mapping.mapUpdate

def mapPayload : ReceiptPayload Origin Rule Value StableFault RetryableFault Effect →
    ReceiptPayload Origin' Rule' Value' StableFault' RetryableFault' Effect'
  | .allocate cell origin => .allocate cell (mapping.origin origin)
  | .evaluate cell owner => .evaluate cell owner
  | .chooseRule cell rule => .chooseRule cell (mapping.rule rule)
  | .observe cell outcome => .observe cell (mapping.mapOutcome outcome)
  | .retry cell reason => .retry cell (mapping.mapRetry reason)
  | .resample source fresh => .resample source fresh
  | .effect effect => .effect (mapping.effect effect)

def mapNode (node : ReceiptNode Origin Rule Value StableFault RetryableFault Effect) :
    ReceiptNode Origin' Rule' Value' StableFault' RetryableFault' Effect' :=
  ⟨node.id, node.parents, mapping.mapPayload node.payload⟩

def mapReceipts (graph : ReceiptGraph Origin Rule Value StableFault RetryableFault Effect) :
    ReceiptGraph Origin' Rule' Value' StableFault' RetryableFault' Effect' :=
  ⟨graph.nodes.map mapping.mapNode, graph.roots, graph.nextSerial⟩

def mapWorld (world : World Origin Rule Value StableFault RetryableFault Effect) :
    World Origin' Rule' Value' StableFault' RetryableFault' Effect' :=
  ⟨world.lineage, world.path, mapping.mapHeap world.heap, mapping.mapReceipts world.receipts,
    world.nextCell, world.nextEvaluator⟩

def mapFrame : Frame Resume → Frame Resume'
  | .commit cell owner => .commit cell owner
  | .resume token => .resume (mapping.resume token)

def mapControl : Control Local Resume Value StableFault RetryableFault →
    Control Local' Resume' Value' StableFault' RetryableFault'
  | .force cell stack => .force cell (stack.map mapping.mapFrame)
  | .run state stack => .run (mapping.state state) (stack.map mapping.mapFrame)
  | .returned outcome stack => .returned (mapping.mapOutcome outcome) (stack.map mapping.mapFrame)
  | .halted outcome => .halted (mapping.mapOutcome outcome)

def mapMachine (machine : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    Machine Origin' Local' Resume' Rule' Value' StableFault' RetryableFault' Effect' :=
  ⟨mapping.mapWorld machine.world, mapping.mapControl machine.control, machine.work⟩

def mapAction : Action Origin Local Resume Value StableFault RetryableFault Effect →
    Action Origin' Local' Resume' Value' StableFault' RetryableFault' Effect'
  | .done outcome => .done (mapping.mapOutcome outcome)
  | .demand cell resume => .demand cell (mapping.resume resume)
  | .allocate origin resume => .allocate (mapping.origin origin) (mapping.resume resume)
  | .resample cell resume => .resample cell (mapping.resume resume)
  | .perform effect next => .perform (mapping.effect effect) (mapping.state next)

@[simp] theorem mapHeap_lookup (heap : Heap Origin Value StableFault) (cell : CellId) :
    (mapping.mapHeap heap).lookup cell = (heap.lookup cell).map mapping.mapRecord := rfl

private theorem option_map_update {α β γ : Type*} [DecidableEq α]
    (f : β → γ) (current : α → Option β) (selected : α) (replacement : Option β) :
    (fun key => (Function.update current selected replacement key).map f) =
      Function.update (fun key => (current key).map f) selected (replacement.map f) := by
  funext key
  by_cases equal : key = selected <;> simp [equal]

@[simp] theorem mapHeap_setKnownCache (heap : Heap Origin Value StableFault) (cell : CellId)
    (record : CellRecord Origin Value StableFault) (state : Cache Value StableFault) :
    mapping.mapHeap (heap.setKnownCache cell record state) =
      (mapping.mapHeap heap).setKnownCache cell (mapping.mapRecord record) (mapping.mapCache state) := by
  simp only [mapHeap, Heap.setKnownCache, List.map_cons, mapUpdate]
  congr 1
  exact option_map_update _ _ _ _

@[simp] theorem mapHeap_allocate (heap : Heap Origin Value StableFault) (cell : CellId)
    (origin : Origin) :
    (heap.allocate? cell origin).map mapping.mapHeap =
      (mapping.mapHeap heap).allocate? cell (mapping.origin origin) := by
  cases found : heap.lookup cell with
  | some record => simp only [Heap.allocate?, mapHeap_lookup, found, Option.map_some, Option.map_none]
  | none =>
      simp only [Heap.allocate?, mapHeap_lookup, found, Option.map_none, Option.map_some]
      congr 1
      simp only [mapHeap, List.map_cons, mapUpdate]
      congr 1
      exact option_map_update _ _ _ _

@[simp] theorem mapWorld_fork (world : World Origin Rule Value StableFault RetryableFault Effect)
    (branch : Nat) : mapping.mapWorld (world.fork branch) = (mapping.mapWorld world).fork branch := rfl

@[simp] theorem mapWorld_recorded
    (world : World Origin Rule Value StableFault RetryableFault Effect)
    (payload : ReceiptPayload Origin Rule Value StableFault RetryableFault Effect) :
    mapping.mapWorld (recorded world payload) =
      recorded (mapping.mapWorld world) (mapping.mapPayload payload) := rfl

@[simp] theorem mapWorld_setKnownCache
    (world : World Origin Rule Value StableFault RetryableFault Effect)
    (cell : CellId) (record : CellRecord Origin Value StableFault) (state : Cache Value StableFault) :
    mapping.mapWorld (world.setKnownCache cell record state) =
      (mapping.mapWorld world).setKnownCache cell (mapping.mapRecord record) (mapping.mapCache state) := by
  simp only [World.setKnownCache, mapWorld, mapHeap_setKnownCache]

@[simp] theorem mapWorld_freshCell
    (world : World Origin Rule Value StableFault RetryableFault Effect) (generation : Nat) :
    (mapping.mapWorld world).freshCell generation = world.freshCell generation := rfl

@[simp] theorem mapWorld_heap
    (world : World Origin Rule Value StableFault RetryableFault Effect) :
    (mapping.mapWorld world).heap = mapping.mapHeap world.heap := rfl

@[simp] theorem mapWorld_nextEvaluator
    (world : World Origin Rule Value StableFault RetryableFault Effect) :
    (mapping.mapWorld world).nextEvaluator = world.nextEvaluator := rfl

@[simp] theorem mapWorld_advanceEvaluator
    (world : World Origin Rule Value StableFault RetryableFault Effect) (owner : EvaluatorId) :
    mapping.mapWorld { world with nextEvaluator := owner } =
      { mapping.mapWorld world with nextEvaluator := owner } := rfl

@[simp] theorem mapWorld_allocate
    (world : World Origin Rule Value StableFault RetryableFault Effect)
    (origin : Origin) (generation : Nat) :
    (world.allocate? origin generation).map (fun pair => (mapping.mapWorld pair.1, pair.2)) =
      (mapping.mapWorld world).allocate? (mapping.origin origin) generation := by
  unfold World.allocate?
  simp only [mapWorld_freshCell, mapWorld_heap]
  simp only [← mapHeap_allocate]
  cases world.heap.allocate? (world.freshCell generation) origin <;> rfl

@[simp] theorem mapMachine_world
    (machine : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    (mapping.mapMachine machine).world = mapping.mapWorld machine.world := rfl

@[simp] theorem mapMachine_control
    (machine : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    (mapping.mapMachine machine).control = mapping.mapControl machine.control := rfl

@[simp] theorem mapMachine_work
    (machine : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    (mapping.mapMachine machine).work = machine.work := rfl

@[simp] theorem map_finished
    (machine : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (world : World Origin Rule Value StableFault RetryableFault Effect)
    (control : Control Local Resume Value StableFault RetryableFault)
    (lookups updates receipts allocations : Nat) :
    mapping.mapMachine (finished machine world control lookups updates receipts allocations) =
      finished (mapping.mapMachine machine) (mapping.mapWorld world) (mapping.mapControl control)
        lookups updates receipts allocations := rfl

@[simp] theorem map_retryMachine
    (machine : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (world : World Origin Rule Value StableFault RetryableFault Effect)
    (cell : CellId) (reason : RetryReason RetryableFault) (stack : List (Frame Resume))
    (lookups updates receipts allocations : Nat) :
    mapping.mapMachine (retryMachine machine world cell reason stack lookups updates receipts allocations) =
      retryMachine (mapping.mapMachine machine) (mapping.mapWorld world) cell (mapping.mapRetry reason)
        (stack.map mapping.mapFrame) lookups updates receipts allocations := rfl

@[simp] theorem map_branchAlternatives
    (machine : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (world : World Origin Rule Value StableFault RetryableFault Effect)
    (cell : CellId) (record : CellRecord Origin Value StableFault) (owner : EvaluatorId)
    (stack : List (Frame Resume)) (index : Nat) (alternatives : List (Rule × Local)) :
    (branchAlternatives machine world cell record owner stack index alternatives).map mapping.mapMachine =
      branchAlternatives (mapping.mapMachine machine) (mapping.mapWorld world) cell
        (mapping.mapRecord record) owner (stack.map mapping.mapFrame) index
        (alternatives.map (fun pair => (mapping.rule pair.1, mapping.state pair.2))) := by
  induction alternatives generalizing index with
  | nil => rfl
  | cons head tail ih =>
      rcases head with ⟨rule, state⟩
      simp only [branchAlternatives, List.map_cons, map_finished, mapWorld_recorded,
        mapWorld_setKnownCache, mapWorld_fork, mapPayload, mapCache, mapControl,
        List.map_cons, mapFrame, ih]

end Mapping

/-- These four independent equations retain the entire alternatives list,
not only its support or the existence of one matching successor. -/
structure Compatible
    (mapping : Mapping Origin Local Resume Rule Value StableFault RetryableFault Effect
      Origin' Local' Resume' Rule' Value' StableFault' RetryableFault' Effect')
    (source : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (target : Spec Origin' Local' Resume' Rule' Value' StableFault' RetryableFault' Effect') : Prop where
  alternatives : ∀ origin, target.alternatives (mapping.origin origin) =
    (source.alternatives origin).map (fun pair => (mapping.rule pair.1, mapping.state pair.2))
  action : ∀ state, target.action (mapping.state state) = mapping.mapAction (source.action state)
  afterDemand : ∀ resume outcome, target.afterDemand (mapping.resume resume) (mapping.mapOutcome outcome) =
    mapping.state (source.afterDemand resume outcome)
  afterAllocation : ∀ resume cell, target.afterAllocation (mapping.resume resume) cell =
    mapping.state (source.afterAllocation resume cell)

namespace Compatible

variable {mapping : Mapping Origin Local Resume Rule Value StableFault RetryableFault Effect
  Origin' Local' Resume' Rule' Value' StableFault' RetryableFault' Effect'}
  {source : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect}
  {target : Spec Origin' Local' Resume' Rule' Value' StableFault' RetryableFault' Effect'}
  (compatible : Compatible mapping source target)

open Mapping

attribute [local simp] mapRetry mapOutcome mapCache mapRecord mapPayload mapControl mapFrame mapAction

include compatible

/-- Every successor occurrence, its exact world, and its semantic work commute
with a compatible change of language representation. -/
theorem step_map
    (machine : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    (step source machine).map mapping.mapMachine = step target (mapping.mapMachine machine) := by
  cases control : machine.control with
  | halted outcome => simp [step, control]
  | force cell stack =>
      simp only [step, control, mapMachine_control, mapControl, mapMachine_world,
        mapWorld_heap, mapHeap_lookup]
      cases found : machine.world.heap.lookup cell with
      | none => simp
      | some record =>
          simp only [Option.map_some]
          cases cache : record.cache with
          | value value => simp [cache]
          | stableFault fault => simp [cache]
          | evaluating owner => simp [cache]
          | suspended =>
              simp only [mapRecord, cache, mapCache, mapWorld_nextEvaluator]
              rw [compatible.alternatives]
              cases alternatives : source.alternatives record.origin with
              | nil => simp
              | cons head tail =>
                  simp only [List.map_cons]
                  rw [map_branchAlternatives]
                  simp only [mapRecord, cache, mapCache, List.map_cons]
                  rfl
  | run state stack =>
      simp only [step, control, mapMachine_control, mapControl, mapMachine_world]
      rw [compatible.action]
      cases action : source.action state with
      | done outcome => simp
      | demand cell resume => simp
      | perform effect next => simp
      | allocate origin resume =>
          simp only [mapAction, mapWorld_freshCell, ← mapWorld_allocate]
          cases allocation : machine.world.allocate? origin with
          | none => simp
          | some pair =>
              rcases pair with ⟨world, cell⟩
              simp [compatible.afterAllocation]
      | resample cell resume =>
          simp only [mapAction, mapWorld_heap, mapHeap_lookup]
          cases found : machine.world.heap.lookup cell with
          | none => simp
          | some record =>
              simp only [Option.map_some, mapRecord, mapWorld_freshCell, ← mapWorld_allocate]
              cases allocation : machine.world.allocate? record.origin (cell.generation + 1) with
              | none => simp
              | some pair =>
                  rcases pair with ⟨world, fresh⟩
                  simp [compatible.afterAllocation]
  | returned outcome stack =>
      simp only [step, control, mapMachine_control, mapControl, mapMachine_world]
      cases stack with
      | nil => simp
      | cons frame rest =>
          cases frame with
          | resume token =>
              simp only [List.map_cons, mapFrame, List.map_nil, map_finished, mapControl,
                compatible.afterDemand]
          | commit cell owner =>
              simp only [List.map_cons, mapFrame, mapWorld_heap, mapHeap_lookup]
              cases found : machine.world.heap.lookup cell with
              | none => simp
              | some record =>
                  simp only [Option.map_some, mapRecord]
                  cases cache : record.cache with
                  | suspended => simp
                  | value value => simp
                  | stableFault fault => simp
                  | evaluating actual =>
                      simp only [mapCache]
                      by_cases owns : actual = owner
                      · simp only [owns, dite_true]
                        cases outcome <;> simp [cache, owns]
                      · simp [owns]

/-- Occurrence indices survive even if the data maps identify some payloads. -/
def mapOccurrence
    {machine next : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    (occurrence : StepOccurrence source machine next) :
    StepOccurrence target (mapping.mapMachine machine) (mapping.mapMachine next) where
  index := occurrence.index
  successorAt := by
    rw [← compatible.step_map, List.getElem?_map, occurrence.successorAt]
    rfl

@[simp] theorem mapOccurrence_index
    {machine next : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    (occurrence : StepOccurrence source machine next) :
    (compatible.mapOccurrence occurrence).index = occurrence.index := rfl

theorem steps_map
    {length : Nat}
    {machine final : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    (execution : Steps source length machine final) :
    Steps target length (mapping.mapMachine machine) (mapping.mapMachine final) := by
  induction execution with
  | refl => exact .refl _
  | cons occurrence _ ih => exact .cons (compatible.mapOccurrence occurrence) ih

theorem uniqueSteps_map
    {length : Nat}
    {machine final : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    (execution : UniqueSteps source length machine final) :
    UniqueSteps target length (mapping.mapMachine machine) (mapping.mapMachine final) := by
  induction execution with
  | refl => exact .refl _
  | cons next _ ih =>
      apply UniqueSteps.cons _ ih
      rw [← compatible.step_map, next]
      rfl

theorem advance_map
    (machine : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    (advance source machine).map mapping.mapMachine = advance target (mapping.mapMachine machine) := by
  unfold advance
  rw [← compatible.step_map]
  cases step source machine <;> rfl

omit compatible in
@[simp] theorem isHalted_map
    (machine : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    isHalted (mapping.mapMachine machine) = isHalted machine := by
  cases control : machine.control <;> simp [isHalted, control]

omit compatible in
@[simp] theorem haltedOutcome_map
    (machine : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    haltedOutcome (mapping.mapMachine machine) = (haltedOutcome machine).map mapping.mapOutcome := by
  cases control : machine.control <;> simp [haltedOutcome, control]

/-- This is equality of bounded frontier lists of full machines, retaining
positions and multiplicities, not just equality of sets of answers. -/
theorem runFrontier_map (fuel : Nat)
    (machines : List (Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)) :
    (runFrontier source fuel machines).map mapping.mapMachine =
      runFrontier target fuel (machines.map mapping.mapMachine) := by
  induction fuel generalizing machines with
  | zero => rfl
  | succ fuel ih =>
      simp only [runFrontier, List.all_map, Function.comp_def, isHalted_map]
      split
      · rfl
      · rw [ih, List.map_flatMap, List.flatMap_map]
        simp only [compatible.advance_map]

theorem answers_map (fuel : Nat)
    (machine : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    (answers source fuel machine).map mapping.mapOutcome =
      answers target fuel (mapping.mapMachine machine) := by
  unfold answers
  change _ = (runFrontier target fuel ([machine].map mapping.mapMachine)).filterMap haltedOutcome
  rw [← compatible.runFrontier_map]
  simp only [List.filterMap_map, List.map_filterMap, Function.comp_def, haltedOutcome_map]

/-- An occurrence cannot vanish merely because its language data is represented
by the same target data as another occurrence. -/
theorem step_length (machine : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    (step target (mapping.mapMachine machine)).length = (step source machine).length := by
  rw [← compatible.step_map, List.length_map]

theorem runFrontier_length (fuel : Nat)
    (machines : List (Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)) :
    (runFrontier target fuel (machines.map mapping.mapMachine)).length =
      (runFrontier source fuel machines).length := by
  rw [← compatible.runFrontier_map, List.length_map]

/-- Every target step from a represented machine has a source occurrence at
the same list position. Injectivity is not needed for existence of a preimage. -/
theorem occurrence_preimage
    {machine : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    {next : Machine Origin' Local' Resume' Rule' Value' StableFault' RetryableFault' Effect'}
    (occurrence : StepOccurrence target (mapping.mapMachine machine) next) :
    ∃ sourceNext, ∃ sourceOccurrence : StepOccurrence source machine sourceNext,
      sourceOccurrence.index = occurrence.index ∧ mapping.mapMachine sourceNext = next := by
  have atIndex : ((step source machine)[occurrence.index]?).map mapping.mapMachine = some next := by
    rw [← List.getElem?_map, compatible.step_map]
    exact occurrence.successorAt
  cases found : (step source machine)[occurrence.index]? with
  | none => simp [found] at atIndex
  | some sourceNext =>
      simp only [found, Option.map_some, Option.some.injEq] at atIndex
      exact ⟨sourceNext, ⟨occurrence.index, found⟩, rfl, atIndex⟩

/-- Finite target executions starting in the image have source executions with
exactly represented final worlds and the same number of transitions. -/
theorem steps_preimage
    {length : Nat}
    {initial final : Machine Origin' Local' Resume' Rule' Value' StableFault' RetryableFault' Effect'}
    (execution : Steps target length initial final)
    (machine : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (represented : mapping.mapMachine machine = initial) :
    ∃ sourceFinal, Steps source length machine sourceFinal ∧ mapping.mapMachine sourceFinal = final := by
  induction execution generalizing machine with
  | refl => exact ⟨machine, .refl _, represented⟩
  | cons occurrence _ ih =>
      subst represented
      obtain ⟨sourceNext, sourceOccurrence, _, nextEqual⟩ := compatible.occurrence_preimage occurrence
      obtain ⟨sourceFinal, rest, finalEqual⟩ := ih sourceNext nextEqual
      exact ⟨sourceFinal, .cons sourceOccurrence rest, finalEqual⟩

/-- Equality reflection is an additional embedding obligation, not a premise
silently inferred from transition commutation. -/
theorem steps_iff_of_injective
    (injective : Function.Injective mapping.mapMachine)
    {length : Nat}
    {machine final : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect} :
    Steps target length (mapping.mapMachine machine) (mapping.mapMachine final) ↔
      Steps source length machine final := by
  constructor
  · intro execution
    obtain ⟨sourceFinal, sourceExecution, equal⟩ := compatible.steps_preimage execution machine rfl
    exact (injective equal) ▸ sourceExecution
  · exact compatible.steps_map

end Compatible

namespace Mapping

variable (mapping : Mapping Origin Local Resume Rule Value StableFault RetryableFault Effect
  Origin' Local' Resume' Rule' Value' StableFault' RetryableFault' Effect')

/-- Even noninjective payload maps cannot identify distinct machine branch
paths. These coordinates belong to the machine, not the source representation. -/
theorem fork_ne
    (world : World Origin Rule Value StableFault RetryableFault Effect)
    {left right : Nat} (distinct : left ≠ right) :
    mapping.mapWorld (world.fork left) ≠ mapping.mapWorld (world.fork right) := by
  intro equal
  have paths : world.path ++ [left] = world.path ++ [right] := congrArg World.path equal
  exact distinct (by simpa using List.append_cancel_left paths)

theorem work_ne
    {left right : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    (distinct : left.work ≠ right.work) : mapping.mapMachine left ≠ mapping.mapMachine right := by
  intro equal
  have sameWork := congrArg (fun machine : Machine Origin' Local' Resume' Rule' Value'
    StableFault' RetryableFault' Effect' => machine.work) equal
  exact distinct sameWork

/-- Stable failure cannot become retryable failure through representation. -/
theorem stable_not_retry (fault : StableFault) (reason : RetryReason RetryableFault') :
    mapping.mapOutcome (.stableFault fault) ≠ .retryableFault reason := by
  simp [mapOutcome]

end Mapping

namespace Examples

/-- The target has an explicit absent representation as well as embedded data;
the source execution never needs to interpret the absent branch. -/
def tagged : Mapping Nat Bool Unit Nat Nat Unit Unit Nat
    (Option Nat) (Option Bool) (Option Unit) (Option Nat) (Option Nat)
    (Option Unit) (Option Unit) (Option Nat) :=
  ⟨some, some, some, some, some, some, some, some⟩

def source : Spec Nat Bool Unit Nat Nat Unit Unit Nat where
  alternatives origin := [(origin, false), (origin, false)]
  action
    | false => .perform 9 true
    | true => .done (.value 7)
  afterDemand _ _ := true
  afterAllocation _ _ := true

def target : Spec (Option Nat) (Option Bool) (Option Unit) (Option Nat) (Option Nat)
    (Option Unit) (Option Unit) (Option Nat) where
  alternatives
    | none => []
    | some origin => [(some origin, some false), (some origin, some false)]
  action
    | none => .done (.stableFault none)
    | some false => .perform (some 9) (some true)
    | some true => .done (.value (some 7))
  afterDemand _ _ := some true
  afterAllocation _ _ := some true

theorem tagged_compatible : Compatible tagged source target := by
  constructor
  · intro origin; rfl
  · intro state; cases state <;> rfl
  · intro resume outcome; rfl
  · intro resume cell; rfl

def cell : CellId := ⟨3, [], 0, 0⟩

def initial : Machine Nat Bool Unit Nat Nat Unit Unit Nat where
  world :=
    { lineage := 3
      path := []
      heap :=
        { current := fun key => if key = cell then some ⟨42, .suspended⟩ else none
          spine := [.allocate cell 42] }
      receipts := ReceiptGraph.empty
      nextCell := 1
      nextEvaluator := 0 }
  control := .force cell []

/-- Two equal rule occurrences remain two branches, each with its own complete
effect and observation receipts. Work is semantic operation count, not time. -/
theorem tagged_duplicate_execution :
    (runFrontier target 5 [tagged.mapMachine initial]).map
      (fun machine => (machine.world.path, haltedOutcome machine, machine.work,
        machine.world.receipts.nodes.map ReceiptNode.payload)) =
    [([0], some (.value (some 7)), ⟨5, 2, 2, 4, 0⟩,
       [.observe cell (.value (some 7)), .effect (some 9),
        .chooseRule cell (some 42), .evaluate cell 0]),
     ([1], some (.value (some 7)), ⟨5, 2, 2, 4, 0⟩,
       [.observe cell (.value (some 7)), .effect (some 9),
        .chooseRule cell (some 42), .evaluate cell 0])] := rfl

/-- Deduplicating an alternatives list violates the actual compatibility law. -/
def deduplicated : Spec (Option Nat) (Option Bool) (Option Unit) (Option Nat) (Option Nat)
    (Option Unit) (Option Unit) (Option Nat) := { target with alternatives := fun
  | none => []
  | some origin => [(some origin, some false)] }

theorem deduplicated_not_compatible : ¬ Compatible tagged source deduplicated := by
  intro compatible
  have count := congrArg List.length (compatible.alternatives 42)
  change 1 = 2 at count
  omega

theorem different_branch_worlds :
    tagged.mapWorld (initial.world.fork 0) ≠ tagged.mapWorld (initial.world.fork 1) :=
  tagged.fork_ne initial.world (by decide)

end Examples

#print axioms Compatible.step_map
#print axioms Compatible.mapOccurrence
#print axioms Compatible.steps_map
#print axioms Compatible.uniqueSteps_map
#print axioms Compatible.runFrontier_map
#print axioms Compatible.answers_map
#print axioms Compatible.steps_preimage
#print axioms Compatible.steps_iff_of_injective
#print axioms Mapping.fork_ne
#print axioms Mapping.work_ne
#print axioms Mapping.stable_not_retry
#print axioms Examples.tagged_compatible
#print axioms Examples.tagged_duplicate_execution
#print axioms Examples.deduplicated_not_compatible
#print axioms Examples.different_branch_worlds

end Mettapedia.Languages.MeTTa.PrimeNeedRepresentation
