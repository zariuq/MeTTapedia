import Mettapedia.GSLT.LanguageDef.CompiledPlanRigidCoordinateCompilation.Selection
import Mettapedia.GSLT.LanguageDef.ReusableSlotBufferCompilation

/-!
# Scored rigid-coordinate dispatch for compiled plans

This realization chooses a coordinate by separated rigid pairs, then by
rigid entries, with earliest ties and unsigned 64-bit saturation. It also
models the reusable scoring scratch buffer. These are choices of this
implementation. Ordered selection and exact answers for every available
coordinate are established separately in `Selection`.
-/

namespace Mettapedia.GSLT.LanguageDef.CompiledPlanRigidCoordinateCompilation

open CompiledPlanAdmission
open CompiledPlanLowering
open CompiledPlanTermSemantics

/-! ## Profitability policy of the scored realization -/

/-- Number of non-wildcard keys at one coordinate. -/
def rigidCount (keys : List (Option DispatchKey)) : Nat :=
  (keys.filter Option.isSome).length

/-- Number of rigid occurrences unequal to one key. -/
def unequalRigidCount (key : DispatchKey)
    (keys : List (Option DispatchKey)) : Nat :=
  (keys.filter (fun candidate =>
    match candidate with
    | some other => other != key
    | none => false)).length

/-- Number of unordered rigid pairs separated by unequal keys. -/
def separatedPairs : List (Option DispatchKey) -> Nat
  | [] => 0
  | none :: keys => separatedPairs keys
  | some key :: keys =>
      unequalRigidCount key keys + separatedPairs keys

/-! ## Streaming equivalence for the physical selector

The generic C realization scans keys from left to right.  On each rigid key it
adds the number of previously seen unequal keys.  The declarative definition
above scans the same unordered pairs from the opposite endpoint.  The
following kernel-checked invariant proves that both traversals compute the
same score; agreement is not inferred from test output.
-/

@[simp] theorem unequalRigidCount_append_none
    (key : DispatchKey) (keys : List (Option DispatchKey)) :
    unequalRigidCount key (keys ++ [none]) = unequalRigidCount key keys := by
  simp [unequalRigidCount]

@[simp] theorem unequalRigidCount_append_some
    (key other : DispatchKey) (keys : List (Option DispatchKey)) :
    unequalRigidCount key (keys ++ [some other]) =
      unequalRigidCount key keys + (if other != key then 1 else 0) := by
  by_cases same : other = key
  · simp [unequalRigidCount, same]
  · simp [unequalRigidCount, same, Nat.add_comm]

@[simp] theorem unequalRigidCount_none_cons
    (key : DispatchKey) (keys : List (Option DispatchKey)) :
    unequalRigidCount key (none :: keys) = unequalRigidCount key keys := by
  rfl

@[simp] theorem unequalRigidCount_some_cons
    (key other : DispatchKey) (keys : List (Option DispatchKey)) :
    unequalRigidCount key (some other :: keys) =
      (if other != key then 1 else 0) + unequalRigidCount key keys := by
  by_cases same : other = key
  · simp [unequalRigidCount, same]
  · simp [unequalRigidCount, same]
    omega

theorem separatedPairs_append_none
    (keys : List (Option DispatchKey)) :
    separatedPairs (keys ++ [none]) = separatedPairs keys := by
  induction keys with
  | nil => rfl
  | cons key keys inductionHypothesis =>
      cases key <;> simp [separatedPairs, inductionHypothesis]

theorem separatedPairs_append_some
    (keys : List (Option DispatchKey)) (key : DispatchKey) :
    separatedPairs (keys ++ [some key]) =
      separatedPairs keys + unequalRigidCount key keys := by
  induction keys with
  | nil => rfl
  | cons candidate keys inductionHypothesis =>
      cases candidate with
      | none => simpa [separatedPairs] using inductionHypothesis
      | some other =>
          simp only [List.cons_append, separatedPairs,
            unequalRigidCount_append_some, inductionHypothesis,
            unequalRigidCount_some_cons]
          by_cases same : other = key
          · subst other
            omega
          · have reverseNe : key ≠ other :=
              fun equality => same equality.symm
            have reverse : (key != other) = true := by
              simp [reverseNe]
            have forward : (other != key) = true := by
              simp [same]
            simp [reverse, forward]
            omega

@[simp] theorem rigidCount_append_none
    (keys : List (Option DispatchKey)) :
    rigidCount (keys ++ [none]) = rigidCount keys := by
  simp [rigidCount]

@[simp] theorem rigidCount_append_some
    (keys : List (Option DispatchKey)) (key : DispatchKey) :
    rigidCount (keys ++ [some key]) = rigidCount keys + 1 := by
  simp [rigidCount]

/-- Abstract state of the single-pass count-table calculation.  `seen` is a
proof model of the table contents; a concrete implementation may replace it
with any exact finite map. -/
structure StreamingPairState where
  seen : List (Option DispatchKey)
  rigid : Nat
  separated : Nat
  deriving DecidableEq, Repr

def streamingPairStep
    (state : StreamingPairState) (candidate : Option DispatchKey) :
    StreamingPairState :=
  { seen := state.seen ++ [candidate]
    rigid := state.rigid + if candidate.isSome then 1 else 0
    separated := state.separated +
      match candidate with
      | none => 0
      | some key => unequalRigidCount key state.seen }

def streamingPairScanFrom :
    StreamingPairState -> List (Option DispatchKey) -> StreamingPairState
  | state, [] => state
  | state, candidate :: candidates =>
      streamingPairScanFrom (streamingPairStep state candidate) candidates

def streamingPairScan (keys : List (Option DispatchKey)) :
    StreamingPairState :=
  streamingPairScanFrom
    { seen := [], rigid := 0, separated := 0 } keys

theorem streamingPairScanFrom_seen
    (state : StreamingPairState) (keys : List (Option DispatchKey)) :
    (streamingPairScanFrom state keys).seen = state.seen ++ keys := by
  induction keys generalizing state with
  | nil => simp [streamingPairScanFrom]
  | cons candidate keys inductionHypothesis =>
      simp [streamingPairScanFrom, inductionHypothesis, streamingPairStep,
        List.append_assoc]

theorem streamingPairScanFrom_rigid_invariant
    (state : StreamingPairState)
    (invariant : state.rigid = rigidCount state.seen)
    (keys : List (Option DispatchKey)) :
    (streamingPairScanFrom state keys).rigid =
      rigidCount (streamingPairScanFrom state keys).seen := by
  induction keys generalizing state with
  | nil => exact invariant
  | cons candidate keys inductionHypothesis =>
      apply inductionHypothesis (streamingPairStep state candidate)
      cases candidate with
      | none => simp [streamingPairStep, invariant]
      | some key => simp [streamingPairStep, invariant]

theorem streamingPairScanFrom_separated_invariant
    (state : StreamingPairState)
    (invariant : state.separated = separatedPairs state.seen)
    (keys : List (Option DispatchKey)) :
    (streamingPairScanFrom state keys).separated =
      separatedPairs (streamingPairScanFrom state keys).seen := by
  induction keys generalizing state with
  | nil => exact invariant
  | cons candidate keys inductionHypothesis =>
      apply inductionHypothesis (streamingPairStep state candidate)
      cases candidate with
      | none => simp [streamingPairStep, invariant,
          separatedPairs_append_none]
      | some key => simp [streamingPairStep, invariant,
          separatedPairs_append_some]

theorem streamingPairScan_rigid
    (keys : List (Option DispatchKey)) :
    (streamingPairScan keys).rigid = rigidCount keys := by
  have invariant := streamingPairScanFrom_rigid_invariant
    { seen := [], rigid := 0, separated := 0 } (by rfl) keys
  simpa [streamingPairScan, streamingPairScanFrom_seen] using invariant

theorem streamingPairScan_separated
    (keys : List (Option DispatchKey)) :
    (streamingPairScan keys).separated = separatedPairs keys := by
  have invariant := streamingPairScanFrom_separated_invariant
    { seen := [], rigid := 0, separated := 0 } (by rfl) keys
  simpa [streamingPairScan, streamingPairScanFrom_seen] using invariant

/-- Saturation used by the generic physical selector. -/
def saturateUInt64 (value : Nat) : Nat :=
  min value 18446744073709551615

/-- Prefer coordinates separating more rigid pairs, then coordinates exposing
more rigid entries. -/
def coordinateScore (rules : List TypedRule) (coordinate : Nat) : Nat :=
  let keys := rules.map (ruleCoordinateKey? coordinate)
  saturateUInt64
    (separatedPairs keys * (rules.length + 1) + rigidCount keys)

/-- Score computed by the same left-to-right accumulator used by the generic
physical selector. -/
def streamingCoordinateScore
    (rules : List TypedRule) (coordinate : Nat) : Nat :=
  let keys := rules.map (ruleCoordinateKey? coordinate)
  let scanned := streamingPairScan keys
  saturateUInt64
    (scanned.separated * (rules.length + 1) + scanned.rigid)

theorem streamingCoordinateScore_eq
    (rules : List TypedRule) (coordinate : Nat) :
    streamingCoordinateScore rules coordinate =
      coordinateScore rules coordinate := by
  simp [streamingCoordinateScore, coordinateScore,
    streamingPairScan_separated, streamingPairScan_rigid]

/-- Fold state for the earliest-maximum selector. -/
structure ScoredCoordinate where
  coordinate : Nat
  score : Nat
  deriving DecidableEq, Repr

/-- Select exactly the earliest positive maximum among in-range coordinates.
A zero score emits no dispatch plan. -/
def selectCoordinate (arity : Nat) (rules : List TypedRule) : Option Nat :=
  ((List.range arity).foldl
    (fun best coordinate =>
      let score := coordinateScore rules coordinate
      match best with
      | none =>
          if score > 0 then some { coordinate, score } else none
      | some current =>
          if score > current.score then some { coordinate, score }
          else best)
    none).map ScoredCoordinate.coordinate

/-- Independent selector using the streaming score. -/
def selectCoordinateStreaming
    (arity : Nat) (rules : List TypedRule) : Option Nat :=
  ((List.range arity).foldl
    (fun best coordinate =>
      let score := streamingCoordinateScore rules coordinate
      match best with
      | none =>
          if score > 0 then some { coordinate, score } else none
      | some current =>
          if score > current.score then some { coordinate, score }
          else best)
    none).map ScoredCoordinate.coordinate

theorem selectCoordinateStreaming_eq
    (arity : Nat) (rules : List TypedRule) :
    selectCoordinateStreaming arity rules = selectCoordinate arity rules := by
  simp only [selectCoordinateStreaming, selectCoordinate,
    streamingCoordinateScore_eq]

/-! ## One reusable scratch allocation across bucket analyses

The physical selector allocates one finite count table and clears it between
outer-head buckets.  The exact logical input to each bucket analysis is its
complete coordinate-by-occurrence key matrix.  Packaging that matrix as one
transaction lets the generic reset-and-reuse theorem certify the allocation
change independently of the table representation.
-/

abbrev DispatchScratchWork := List (List (Option DispatchKey))

/-- Complete rigid-key workload for one exact outer-head bucket. -/
def dispatchScratchWork (arity : Nat) (rules : List TypedRule) :
    DispatchScratchWork :=
  (List.range arity).map fun coordinate =>
    rules.map (ruleCoordinateKey? coordinate)

private def dispatchScratchSlot : Fin 1 := ⟨0, by omega⟩

/-- A source implementation allocates one logical scratch transaction for
every bucket. -/
def dispatchScratchTransactions
    (index : FiniteRuleIndexCompilation.BucketIndex
      CompiledPlanFixedHeadIndexCompilation.OuterKey TypedRule) :
    List (ReusableSlotBufferCompilation.Transaction 1
      DispatchScratchWork) :=
  index.map fun bucket =>
    [(dispatchScratchSlot,
      dispatchScratchWork bucket.1.arity bucket.2)]

/-- Complete expected work snapshots in exact bucket order. -/
def dispatchScratchSnapshots
    (index : FiniteRuleIndexCompilation.BucketIndex
      CompiledPlanFixedHeadIndexCompilation.OuterKey TypedRule) :
    List (List (Option DispatchScratchWork)) :=
  index.map fun bucket =>
    [some (dispatchScratchWork bucket.1.arity bucket.2)]

theorem executeFresh_dispatchScratchTransactions
    (index : FiniteRuleIndexCompilation.BucketIndex
      CompiledPlanFixedHeadIndexCompilation.OuterKey TypedRule) :
    ReusableSlotBufferCompilation.executeFresh
        (dispatchScratchTransactions index) =
      dispatchScratchSnapshots index := by
  simp [ReusableSlotBufferCompilation.executeFresh,
    dispatchScratchTransactions, dispatchScratchSnapshots,
    ReusableSlotBufferCompilation.runFresh,
    ReusableSlotBufferCompilation.runFrom,
    ReusableSlotBufferCompilation.write,
    ReusableSlotBufferCompilation.snapshot, dispatchScratchSlot,
    dispatchScratchWork]

/-- Resetting and reusing one physical scratch allocation preserves every
bucket's exact coordinate-key workload. -/
theorem executeReusable_dispatchScratchTransactions
    (index : FiniteRuleIndexCompilation.BucketIndex
      CompiledPlanFixedHeadIndexCompilation.OuterKey TypedRule) :
    ReusableSlotBufferCompilation.executeReusable
        (dispatchScratchTransactions index) =
      dispatchScratchSnapshots index := by
  rw [ReusableSlotBufferCompilation.executeReusable_eq_fresh,
    executeFresh_dispatchScratchTransactions]

theorem dispatchScratchTransactions_length
    (index : FiniteRuleIndexCompilation.BucketIndex
      CompiledPlanFixedHeadIndexCompilation.OuterKey TypedRule) :
    (dispatchScratchTransactions index).length = index.length := by
  simp [dispatchScratchTransactions]

/-- Sharing the scratch allocation never increases allocation count. -/
theorem dispatchScratchAllocationCount_le
    (index : FiniteRuleIndexCompilation.BucketIndex
      CompiledPlanFixedHeadIndexCompilation.OuterKey TypedRule) :
    ReusableSlotBufferCompilation.reusableAllocationCount
        (dispatchScratchTransactions index) ≤
      ReusableSlotBufferCompilation.freshAllocationCount
        (dispatchScratchTransactions index) :=
  ReusableSlotBufferCompilation.reusableAllocationCount_le_fresh _

/-- Two or more outer buckets make the allocation reduction strict. -/
theorem dispatchScratchAllocationCount_lt_of_two_buckets
    (index : FiniteRuleIndexCompilation.BucketIndex
      CompiledPlanFixedHeadIndexCompilation.OuterKey TypedRule)
    (multiple : 2 ≤ index.length) :
    ReusableSlotBufferCompilation.reusableAllocationCount
        (dispatchScratchTransactions index) <
      ReusableSlotBufferCompilation.freshAllocationCount
        (dispatchScratchTransactions index) := by
  apply ReusableSlotBufferCompilation.reusableAllocationCount_lt_fresh_of_two_le
  simpa [dispatchScratchTransactions]

/-- Coordinate plan retained by one outer-head/arity bucket. -/
structure Plan where
  coordinate : Nat
  entries : List Entry
  deriving DecidableEq, Repr

/-- Emit a coordinate plan only when the local profitability score is
positive. -/
def compile? (arity : Nat) (rules : List TypedRule) : Option Plan := do
  let coordinate <- selectCoordinate arity rules
  some { coordinate, entries := compileEntries coordinate rules }

/-- The profitability policy chooses only the coordinate. It does not
change the entry inventory for that coordinate. -/
theorem entries_of_compile?
    (arity : Nat) (rules : List TypedRule) (plan : Plan)
    (compiled : compile? arity rules = some plan) :
    plan.entries = compileEntries plan.coordinate rules := by
  unfold compile? at compiled
  cases selected : selectCoordinate arity rules with
  | none => simp [selected] at compiled
  | some coordinate =>
      simp [selected] at compiled
      subst plan
      rfl

/-- A successful bucket compilation retains every source rule occurrence. -/
theorem compile?_rules
    (arity : Nat) (rules : List TypedRule) (plan : Plan)
    (compiled : compile? arity rules = some plan) :
    plan.entries.map Entry.rule = rules := by
  rw [entries_of_compile? arity rules plan compiled, compileEntries_rules]

/-- Instantiate the ordered selection theorem for the scored compiler.
The proof does not inspect its score or tie policy. -/
theorem compiled_observations_exact {Answer : Type*}
    (arity : Nat) (rules : List TypedRule) (plan : Plan)
    (compiled : compile? arity rules = some plan)
    (queryHead queryCoordinate : GroundTerm) (observe : TypedRule → List Answer)
    (queryFound : groundHeadCoordinate? queryHead plan.coordinate = some queryCoordinate)
    (sound : ∀ rule ∈ rules, observe rule ≠ [] →
      ∃ substitution, instantiateTerm substitution rule.head = some queryHead) :
    (executeEntries queryCoordinate plan.entries).flatMap observe = rules.flatMap observe := by
  rw [entries_of_compile? arity rules plan compiled]
  exact executeEntries_flatMap_eq plan.coordinate queryHead queryCoordinate rules observe queryFound sound

#print axioms compiled_observations_exact

/-! ## Independent cross-guest canaries -/

private def unary (name constructor : UInt8) : TypedRule :=
  { name := [name]
    head := .application [1]
      (.cons (.application [constructor] (.cons (.variable 0) .nil)) .nil)
    body := []
    variableCount := 1 }

private def evaluatorRules : List TypedRule :=
  [unary 1 10, unary 2 20,
   { name := [3]
     head := .application [1] (.cons (.variable 0) .nil)
     body := []
     variableCount := 1 }]

private def literalRules : List TypedRule :=
  [unary 4 30, unary 5 40]

/-- A reflective evaluator chooses its constructor coordinate and keeps the
matching branch plus its wildcard fallback. -/
example : selectCoordinate 1 evaluatorRules = some 0 /\
    executeEntries
      (.application [10] (.cons (.symbol [99]) .nil))
      (compileEntries 0 evaluatorRules) =
        [evaluatorRules[0], evaluatorRules[2]] := by
  decide

/-- A distinct literal dispatcher uses the same selector and excludes the
opposite polarity branch. -/
example : selectCoordinate 1 literalRules = some 0 /\
    executeEntries
      (.application [40] (.cons (.symbol [99]) .nil))
      (compileEntries 0 literalRules) = [literalRules[1]] := by
  decide

/-- An all-variable coordinate emits no unprofitable dispatch structure. -/
example :
    selectCoordinate 1
      [{ name := [6]
         head := .application [1] (.cons (.variable 0) .nil)
         body := []
         variableCount := 1 }] = none := by
  decide

end Mettapedia.GSLT.LanguageDef.CompiledPlanRigidCoordinateCompilation
