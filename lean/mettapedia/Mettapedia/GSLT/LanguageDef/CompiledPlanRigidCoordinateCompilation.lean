import Mettapedia.GSLT.LanguageDef.CompiledPlanFixedHeadIndexCompilation
import Mettapedia.GSLT.LanguageDef.CompiledPlanTermSemantics
import Mettapedia.GSLT.LanguageDef.ReusableSlotBufferCompilation

/-!
# Rigid-coordinate dispatch for exact compiled-plan terms

After fixed outer-head and arity indexing, every rule in a bucket has the same
number of immediate arguments.  This stage chooses one argument coordinate
using only the finite rigid roots present in that bucket.  Variables remain
wildcards.  Symbols, strings, integers, and application-head/arity pairs form
the closed dispatch-key vocabulary.

The selector models the generic C realization: it maximizes separated rigid
pairs, then rigid entries, retains the earliest coordinate on ties, and
saturates the combined score at the unsigned 64-bit boundary.  Selection is a
profitability decision only.  The semantic theorem applies to every
coordinate: a rule whose head instantiates to the ground query is never
removed by rigid-root dispatch.
-/

namespace Mettapedia.GSLT.LanguageDef.CompiledPlanRigidCoordinateCompilation

open CompiledPlanAdmission
open CompiledPlanLowering
open CompiledPlanTermSemantics

/-- Closed vocabulary of immediate rigid roots available in the admitted
typed carrier. -/
inductive DispatchKey where
  | symbol (name : List UInt8)
  | string (value : List UInt8)
  | integer (value : Int64)
  | application (head : List UInt8) (arity : Nat)
  deriving DecidableEq, Repr

/-- Number of immediate arguments in a closed value. -/
def groundTermsLength : GroundTerms -> Nat
  | .nil => 0
  | .cons _ tail => groundTermsLength tail + 1

/-- A variable has no rigid key and is therefore compiled as a wildcard. -/
def rootKey? : Term -> Option DispatchKey
  | .symbol name => some (.symbol name)
  | .variable _ => none
  | .string value => some (.string value)
  | .integer value => some (.integer value)
  | .application head arguments =>
      some (.application head
        (CompiledPlanFixedHeadIndexCompilation.termsLength arguments))

/-- Every closed value exposes exactly one rigid root. -/
def groundRootKey : GroundTerm -> DispatchKey
  | .symbol name => .symbol name
  | .string value => .string value
  | .integer value => .integer value
  | .application head arguments =>
      .application head (groundTermsLength arguments)

/-- A source root can match a closed target root precisely when it is a
variable or exposes the same rigid key. -/
def rootCompatible (source : Term) (target : GroundTerm) : Bool :=
  match rootKey? source with
  | none => true
  | some key => key == groundRootKey target

/-- Instantiation preserves the immediate arity of a term list. -/
theorem groundTermsLength_eq_of_instantiateTerms :
    forall (source : Terms) (substitution : Substitution)
      (target : GroundTerms),
      instantiateTerms substitution source = some target ->
        groundTermsLength target =
          CompiledPlanFixedHeadIndexCompilation.termsLength source
  | .nil, _, target, instantiated => by
      simp [instantiateTerms] at instantiated
      subst target
      rfl
  | .cons head tail, substitution, target, instantiated => by
      cases headInstantiated : instantiateTerm substitution head with
      | none =>
          simp [instantiateTerms, headInstantiated] at instantiated
      | some groundedHead =>
          cases tailInstantiated : instantiateTerms substitution tail with
          | none =>
              simp [instantiateTerms, headInstantiated, tailInstantiated]
                at instantiated
          | some groundedTail =>
              simp [instantiateTerms, headInstantiated, tailInstantiated]
                at instantiated
              subst target
              simp [groundTermsLength,
                CompiledPlanFixedHeadIndexCompilation.termsLength,
                groundTermsLength_eq_of_instantiateTerms tail substitution
                  groundedTail tailInstantiated]

/-- A successfully instantiated term always agrees with its target on every
visible rigid-root component. -/
theorem rootCompatible_of_instance
    (source : Term) (substitution : Substitution) (target : GroundTerm)
    (instantiated : instantiateTerm substitution source = some target) :
    rootCompatible source target = true := by
  cases source with
  | symbol name =>
      simp [instantiateTerm] at instantiated
      subst target
      simp [rootCompatible, rootKey?, groundRootKey]
  | «variable» slot =>
      simp [rootCompatible, rootKey?]
  | «string» value =>
      simp [instantiateTerm] at instantiated
      subst target
      simp [rootCompatible, rootKey?, groundRootKey]
  | integer value =>
      simp [instantiateTerm] at instantiated
      subst target
      simp [rootCompatible, rootKey?, groundRootKey]
  | application head arguments =>
      cases argumentsInstantiated :
          instantiateTerms substitution arguments with
      | none =>
          simp [instantiateTerm, argumentsInstantiated] at instantiated
      | some groundedArguments =>
          simp [instantiateTerm, argumentsInstantiated] at instantiated
          subst target
          have sameLength := groundTermsLength_eq_of_instantiateTerms
            arguments substitution groundedArguments argumentsInstantiated
          simp [rootCompatible, rootKey?, groundRootKey, sameLength]

/-! ## Exact immediate-coordinate projection -/

/-- Read one immediate source argument. -/
def termAt? : Terms -> Nat -> Option Term
  | .nil, _ => none
  | .cons head _, 0 => some head
  | .cons _ tail, coordinate + 1 => termAt? tail coordinate

/-- Read one immediate closed argument. -/
def groundTermAt? : GroundTerms -> Nat -> Option GroundTerm
  | .nil, _ => none
  | .cons head _, 0 => some head
  | .cons _ tail, coordinate + 1 => groundTermAt? tail coordinate

/-- Project a source head to one argument coordinate. -/
def headCoordinate? (head : Term) (coordinate : Nat) : Option Term :=
  match head with
  | .application _ arguments => termAt? arguments coordinate
  | _ => none

/-- Project a closed query head to one argument coordinate. -/
def groundHeadCoordinate? (head : GroundTerm) (coordinate : Nat) :
    Option GroundTerm :=
  match head with
  | .application _ arguments => groundTermAt? arguments coordinate
  | _ => none

/-- Instantiating a term list preserves every coordinate and its exact
instantiated value. -/
theorem instantiateTerms_termAt? :
    forall (source : Terms) (substitution : Substitution)
      (target : GroundTerms) (coordinate : Nat) (sourceTerm : Term),
      instantiateTerms substitution source = some target ->
        termAt? source coordinate = some sourceTerm ->
          exists targetTerm,
            groundTermAt? target coordinate = some targetTerm /\
              instantiateTerm substitution sourceTerm = some targetTerm
  | .nil, _, _, _, _, _, sourceFound => by
      simp [termAt?] at sourceFound
  | .cons head tail, substitution, target, coordinate, sourceTerm,
      instantiated, sourceFound => by
      cases headInstantiated : instantiateTerm substitution head with
      | none =>
          simp [instantiateTerms, headInstantiated] at instantiated
      | some groundedHead =>
          cases tailInstantiated : instantiateTerms substitution tail with
          | none =>
              simp [instantiateTerms, headInstantiated, tailInstantiated]
                at instantiated
          | some groundedTail =>
              simp [instantiateTerms, headInstantiated, tailInstantiated]
                at instantiated
              subst target
              cases coordinate with
              | zero =>
                  simp [termAt?] at sourceFound
                  subst sourceTerm
                  exact ⟨groundedHead, rfl, headInstantiated⟩
              | succ coordinate =>
                  exact instantiateTerms_termAt? tail substitution
                    groundedTail coordinate sourceTerm tailInstantiated
                    sourceFound

/-- When a complete rule head instantiates to a closed query, the same
selected coordinate exists on both sides and remains rigid-compatible. -/
theorem coordinateCompatible_of_headInstance
    (source : Term) (substitution : Substitution) (target : GroundTerm)
    (coordinate : Nat) (sourceTerm : Term)
    (instantiated : instantiateTerm substitution source = some target)
    (sourceFound : headCoordinate? source coordinate = some sourceTerm) :
    exists targetTerm,
      groundHeadCoordinate? target coordinate = some targetTerm /\
        rootCompatible sourceTerm targetTerm = true := by
  cases source with
  | symbol name => simp [headCoordinate?] at sourceFound
  | «variable» slot => simp [headCoordinate?] at sourceFound
  | «string» value => simp [headCoordinate?] at sourceFound
  | integer value => simp [headCoordinate?] at sourceFound
  | application head arguments =>
      cases argumentsInstantiated :
          instantiateTerms substitution arguments with
      | none =>
          simp [instantiateTerm, argumentsInstantiated] at instantiated
      | some groundedArguments =>
          simp [instantiateTerm, argumentsInstantiated] at instantiated
          subst target
          obtain ⟨targetTerm, targetFound, coordinateInstantiated⟩ :=
            instantiateTerms_termAt? arguments substitution
              groundedArguments coordinate sourceTerm argumentsInstantiated
              sourceFound
          exact ⟨targetTerm, targetFound,
            rootCompatible_of_instance sourceTerm substitution targetTerm
              coordinateInstantiated⟩

/-! ## C-shaped profitability selector -/

/-- Generated key for one source rule at a candidate coordinate. -/
def ruleCoordinateKey? (coordinate : Nat) (rule : TypedRule) :
    Option DispatchKey :=
  (headCoordinate? rule.head coordinate).bind rootKey?

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

/-- One generated occurrence in a dispatch plan. -/
structure Entry where
  rule : TypedRule
  key : Option DispatchKey
  deriving DecidableEq, Repr

/-- Generated per-occurrence key inventory. -/
def compileEntries (coordinate : Nat) (rules : List TypedRule) : List Entry :=
  rules.map fun rule =>
    { rule, key := ruleCoordinateKey? coordinate rule }

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

/-- Execute generated rigid groups extensionally.  `none` is a wildcard;
rigid keys retain precisely their matching group. -/
def keyCompatible (query : GroundTerm) : Option DispatchKey -> Bool
  | none => true
  | some key => key == groundRootKey query

def executeEntries (query : GroundTerm) : List Entry -> List TypedRule
  | [] => []
  | entry :: entries =>
      if keyCompatible query entry.key then
        entry.rule :: executeEntries query entries
      else executeEntries query entries

/-- Source-order specification for rigid-coordinate candidates. -/
def sourceCandidates (coordinate : Nat) (query : GroundTerm)
    (rules : List TypedRule) : List TypedRule :=
  rules.filter fun rule =>
    keyCompatible query (ruleCoordinateKey? coordinate rule)

/-- Generated entries retain exactly the source scan, including order and
multiplicity. -/
theorem executeEntries_compileEntries
    (coordinate : Nat) (query : GroundTerm) (rules : List TypedRule) :
    executeEntries query (compileEntries coordinate rules) =
      sourceCandidates coordinate query rules := by
  induction rules with
  | nil => rfl
  | cons rule rules inductionHypothesis =>
      simp only [compileEntries, List.map_cons, executeEntries,
        sourceCandidates, List.filter_cons]
      change
        (if keyCompatible query (ruleCoordinateKey? coordinate rule) = true
          then rule :: executeEntries query (compileEntries coordinate rules)
          else executeEntries query (compileEntries coordinate rules)) =
        (if keyCompatible query (ruleCoordinateKey? coordinate rule) = true
          then rule :: sourceCandidates coordinate query rules
          else sourceCandidates coordinate query rules)
      rw [inductionHypothesis]

/-- Compiling entries never changes the underlying source occurrence list. -/
theorem compileEntries_rules (coordinate : Nat) (rules : List TypedRule) :
    (compileEntries coordinate rules).map Entry.rule = rules := by
  simp [compileEntries, Function.comp_def]

/-- A successful bucket compilation retains every source rule occurrence. -/
theorem compile?_rules
    (arity : Nat) (rules : List TypedRule) (plan : Plan)
    (compiled : compile? arity rules = some plan) :
    plan.entries.map Entry.rule = rules := by
  unfold compile? at compiled
  cases selected : selectCoordinate arity rules with
  | none => simp [selected] at compiled
  | some coordinate =>
      simp [selected] at compiled
      subst plan
      exact compileEntries_rules coordinate rules

/-- A possible rule application survives generated rigid-coordinate
selection. -/
theorem mem_sourceCandidates_of_headInstance
    (coordinate : Nat) (queryCoordinate : GroundTerm)
    (rules : List TypedRule) (rule : TypedRule)
    (member : rule ∈ rules) (substitution : Substitution)
    (queryHead : GroundTerm)
    (instantiated :
      instantiateTerm substitution rule.head = some queryHead)
    (queryFound :
      groundHeadCoordinate? queryHead coordinate = some queryCoordinate) :
    rule ∈ sourceCandidates coordinate queryCoordinate rules := by
  apply List.mem_filter.mpr
  refine ⟨member, ?_⟩
  cases sourceFound : headCoordinate? rule.head coordinate with
  | none => simp [ruleCoordinateKey?, sourceFound, keyCompatible]
  | some sourceTerm =>
      obtain ⟨targetTerm, targetFound, compatible⟩ :=
        coordinateCompatible_of_headInstance rule.head substitution queryHead
          coordinate sourceTerm instantiated sourceFound
      rw [queryFound] at targetFound
      cases targetFound
      simpa [ruleCoordinateKey?, sourceFound, keyCompatible,
        rootCompatible] using compatible

/-- Therefore the exact generated entry program never removes a rule that
can instantiate to the closed query. -/
theorem mem_executeEntries_of_headInstance
    (coordinate : Nat) (queryCoordinate : GroundTerm)
    (rules : List TypedRule) (rule : TypedRule)
    (member : rule ∈ rules) (substitution : Substitution)
    (queryHead : GroundTerm)
    (instantiated :
      instantiateTerm substitution rule.head = some queryHead)
    (queryFound :
      groundHeadCoordinate? queryHead coordinate = some queryCoordinate) :
    rule ∈ executeEntries queryCoordinate
      (compileEntries coordinate rules) := by
  rw [executeEntries_compileEntries]
  exact mem_sourceCandidates_of_headInstance coordinate queryCoordinate rules
    rule member substitution queryHead instantiated queryFound

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
