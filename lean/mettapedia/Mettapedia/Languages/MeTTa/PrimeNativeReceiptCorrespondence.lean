import Mettapedia.Languages.MeTTa.PrimeEquationCallSemantics
import Mathlib.Data.List.Nodup

/-!
# Prime native receipt correspondence boundary

This module formalizes the independently checkable side of the native receipt
bridge.  It does not claim a C refinement theorem.  A decoded receipt retains
native event occurrence IDs, Need-session-qualified cell identity, dynamic
application and argument identity, admitted rule occurrence, observations, and
effects.  An executable validity predicate checks occurrence uniqueness and
conflict-free causal closure before publication.

The producer obligation remains empirical: the native runtime must emit traces
accepted by this checker.  The runtime tournament and killed mutations test that
obligation separately.
-/

namespace Mettapedia.Languages.MeTTa.PrimeNativeReceiptCorrespondence

open PrimeCallSharingTournament
open PrimeEquationCallSemantics

/-- Native cell identity is scoped by its Need session. -/
structure NativeCell where
  needSession : Nat
  cell : Nat
deriving DecidableEq, Repr

abbrev NativeSource := SourceArgumentOccurrence Nat Nat Nat

/-- The occurrence-bearing subset of native receipt payloads used by the
equation-call checker.  State reads and writes are represented in `Effect` so
the chosen effect algebra, not this decoder, decides their compatibility. -/
inductive NativePayload (Observation Effect : Type*) where
  | evaluateCell (cell : NativeCell) (source : Option NativeSource)
  | observeCell (cell : NativeCell) (source : Option NativeSource)
      (observation : Observation)
  | inspectOrigin (cell : NativeCell) (origin : Observation)
  | useEquation (application : Nat) (rule : Nat)
  | effect (effect : Effect)
  | resample (origin : Observation)
deriving DecidableEq, Repr

structure NativeEvent (Observation Effect : Type*) where
  eventId : Nat
  payload : NativePayload Observation Effect
deriving DecidableEq, Repr

structure NativeReceipt (Observation Effect : Type*) where
  receiptId : Nat
  events : List (NativeEvent Observation Effect)
deriving DecidableEq, Repr

abbrev DecodedEvent Observation Effect :=
  EquationEventOccurrence (Option NativeSource) NativeCell Nat
    Observation Effect

def decodeEvent (event : NativeEvent Observation Effect) :
    DecodedEvent Observation Effect :=
  { occurrence := event.eventId
    payload :=
      match event.payload with
      | .evaluateCell cell source => .cellEvaluated source cell
      | .observeCell cell source observation =>
          .cellObserved source cell observation
      | .inspectOrigin cell origin => .originInspected cell origin
      | .useEquation _ rule => .ruleMatched rule
      | .effect effect => .effect effect
      | .resample origin => .resampled origin }

def decodedEvents (receipt : NativeReceipt Observation Effect) :
    List (DecodedEvent Observation Effect) :=
  receipt.events.map decodeEvent

def decodedRoots
    [DecidableEq Observation] [DecidableEq Effect]
    (receipt : NativeReceipt Observation Effect) :
    Finset (DecodedEvent Observation Effect) :=
  (decodedEvents receipt).toFinset

/-- Decoded equation-event conflict.  Producer and rule occurrences do not
conflict merely by co-occurring.  Cell observations and origin inspections are
functional; effects use the supplied algebra. -/
def EquationConflict
    (effectConflict : Effect → Effect → Prop) :
    DecodedEvent Observation Effect →
      DecodedEvent Observation Effect → Prop
  | ⟨_, .cellObserved _ leftCell leftObservation⟩,
      ⟨_, .cellObserved _ rightCell rightObservation⟩ =>
      leftCell = rightCell ∧ leftObservation ≠ rightObservation
  | ⟨_, .originInspected leftCell leftOrigin⟩,
      ⟨_, .originInspected rightCell rightOrigin⟩ =>
      leftCell = rightCell ∧ leftOrigin ≠ rightOrigin
  | ⟨_, .effect left⟩, ⟨_, .effect right⟩ =>
      effectConflict left right
  | _, _ => False

instance equationConflictDecidable
    [DecidableEq Observation] [DecidableEq Effect]
    (effectConflict : Effect → Effect → Prop)
    [DecidableRel effectConflict] :
    DecidableRel (EquationConflict (Observation := Observation)
      effectConflict) := by
  intro left right
  rcases left with ⟨leftOccurrence, leftPayload⟩
  rcases right with ⟨rightOccurrence, rightPayload⟩
  cases leftPayload <;> cases rightPayload <;>
    simp [EquationConflict] <;> infer_instance

def EventIdsUnique (receipt : NativeReceipt Observation Effect) : Prop :=
  (receipt.events.map NativeEvent.eventId).Nodup

def Valid
    [DecidableEq Observation] [DecidableEq Effect]
    (basis : PrimeNeedWorlds.FiniteCausalBasis
      (DecodedEvent Observation Effect))
    (effectConflict : Effect → Effect → Prop)
    (receipt : NativeReceipt Observation Effect) : Prop :=
  EventIdsUnique receipt ∧
  PrimeNeedWorlds.ConflictFree (EquationConflict effectConflict)
    (basis.close (decodedRoots receipt))

/-- A computational enumeration of the support carried by a finite causal
basis.  `FiniteCausalBasis` remains the mathematical authority; this structure
supplies an exact list representation for trace checking. -/
structure ExecutableCausalBasis
    [DecidableEq Event]
    (basis : PrimeNeedWorlds.FiniteCausalBasis Event) where
  supportList : Event → List Event
  support_exact : ∀ event, (supportList event).toFinset = basis.support event

def closedEventList
    [DecidableEq Event]
    {basis : PrimeNeedWorlds.FiniteCausalBasis Event}
    (executable : ExecutableCausalBasis basis)
    (roots : List Event) : List Event :=
  roots.flatMap executable.supportList

theorem closedEventList_toFinset
    [DecidableEq Event]
    {basis : PrimeNeedWorlds.FiniteCausalBasis Event}
    (executable : ExecutableCausalBasis basis)
    (roots : List Event) :
    (closedEventList executable roots).toFinset = basis.close roots.toFinset := by
  ext event
  simp [closedEventList, PrimeNeedWorlds.FiniteCausalBasis.close]
  constructor
  · rintro ⟨source, sourceMem, eventMem⟩
    refine ⟨source, sourceMem, ?_⟩
    have inListFinset : event ∈ (executable.supportList source).toFinset := by
      simpa using eventMem
    rwa [executable.support_exact source] at inListFinset
  · rintro ⟨source, sourceMem, eventMem⟩
    refine ⟨source, sourceMem, ?_⟩
    have inListFinset : event ∈ (executable.supportList source).toFinset := by
      rw [executable.support_exact source]
      exact eventMem
    simpa using inListFinset

/-- Executable conflict-freedom check over an explicitly enumerated list. -/
def conflictFreeListCheck
    (conflict : Event → Event → Prop) [DecidableRel conflict]
    (events : List Event) : Bool :=
  events.all fun left =>
    events.all fun right => decide (¬ conflict left right)

theorem conflictFreeListCheck_eq_true_iff
    [DecidableEq Event]
    (conflict : Event → Event → Prop) [DecidableRel conflict]
    (events : List Event) :
    conflictFreeListCheck conflict events = true ↔
      PrimeNeedWorlds.ConflictFree conflict events.toFinset := by
  constructor
  · intro checked left right leftMem rightMem
    have leftChecked := (List.all_eq_true.mp checked) left (by simpa using leftMem)
    have rightChecked := (List.all_eq_true.mp leftChecked) right (by simpa using rightMem)
    simpa using rightChecked
  · intro conflictFree
    apply List.all_eq_true.mpr
    intro left leftMem
    apply List.all_eq_true.mpr
    intro right rightMem
    exact decide_eq_true (conflictFree (by simpa using leftMem) (by simpa using rightMem))

def eventIdsUniqueCheck (receipt : NativeReceipt Observation Effect) : Bool :=
  decide ((receipt.events.map NativeEvent.eventId).Nodup)

/-- Executable checker for the trace-facing validity predicate. -/
def accepts
    [DecidableEq Observation] [DecidableEq Effect]
    (basis : PrimeNeedWorlds.FiniteCausalBasis
      (DecodedEvent Observation Effect))
    (executable : ExecutableCausalBasis basis)
    (effectConflict : Effect → Effect → Prop)
    [DecidableRel effectConflict]
    (receipt : NativeReceipt Observation Effect) : Bool :=
  eventIdsUniqueCheck receipt &&
    conflictFreeListCheck (EquationConflict effectConflict)
      (closedEventList executable (decodedEvents receipt))

theorem accepts_iff_valid
    [DecidableEq Observation] [DecidableEq Effect]
    (basis : PrimeNeedWorlds.FiniteCausalBasis
      (DecodedEvent Observation Effect))
    (executable : ExecutableCausalBasis basis)
    (effectConflict : Effect → Effect → Prop)
    [DecidableRel effectConflict]
    (receipt : NativeReceipt Observation Effect) :
    accepts basis executable effectConflict receipt = true ↔
      Valid basis effectConflict receipt := by
  rw [accepts, Bool.and_eq_true, eventIdsUniqueCheck]
  simp only [decide_eq_true_eq]
  rw [conflictFreeListCheck_eq_true_iff]
  rw [closedEventList_toFinset]
  rfl

@[simp] theorem decodeEvent_occurrence
    (event : NativeEvent Observation Effect) :
    (decodeEvent event).occurrence = event.eventId :=
  rfl

/-- Unique native IDs imply unique decoded occurrences even when payloads are
equal. -/
theorem decodedEvents_nodup
    (receipt : NativeReceipt Observation Effect)
    (unique : EventIdsUnique receipt) :
    (decodedEvents receipt).Nodup := by
  have sourceNodup : receipt.events.Nodup :=
    List.Nodup.of_map _ unique
  apply sourceNodup.map_on
  intro left leftMem right rightMem equalDecoded
  have sameId : left.eventId = right.eventId := by
    exact congrArg EventOccurrence.occurrence equalDecoded
  exact (List.inj_on_of_nodup_map unique) leftMem rightMem sameId

/-- Two equal native payloads with distinct occurrence IDs remain two decoded
events rather than collapsing before receipt construction. -/
theorem equal_payload_distinct_ids_decode_distinct
    {left right : NativeEvent Observation Effect}
    (_samePayload : left.payload = right.payload)
    (differentIds : left.eventId ≠ right.eventId) :
    decodeEvent left ≠ decodeEvent right := by
  intro equalDecoded
  exact differentIds (congrArg EventOccurrence.occurrence equalDecoded)

def ObservationsFunctional
    (events : Finset (DecodedEvent Observation Effect)) : Prop :=
  ∀ ⦃left right source otherSource cell observation other⦄,
    left ∈ events → right ∈ events →
    left.payload = .cellObserved source cell observation →
    right.payload = .cellObserved otherSource cell other →
    observation = other

/-- Conflict-free decoded closure entails a functional cell-observation
projection. -/
theorem valid_observations_functional
    [DecidableEq Observation] [DecidableEq Effect]
    {basis : PrimeNeedWorlds.FiniteCausalBasis
      (DecodedEvent Observation Effect)}
    {effectConflict : Effect → Effect → Prop}
    {receipt : NativeReceipt Observation Effect}
    (valid : Valid basis effectConflict receipt) :
    ObservationsFunctional (decodedRoots receipt) := by
  intro left right source otherSource cell observation other
    leftMem rightMem leftPayload rightPayload
  have rootFree : PrimeNeedWorlds.ConflictFree
      (EquationConflict effectConflict) (decodedRoots receipt) :=
    valid.2.mono (basis.subset_close _)
  by_contra different
  apply rootFree leftMem rightMem
  rcases left with ⟨leftOccurrence, leftEvent⟩
  rcases right with ⟨rightOccurrence, rightEvent⟩
  simp only at leftPayload rightPayload
  subst leftEvent
  subst rightEvent
  exact ⟨rfl, different⟩

/-- An accepted native receipt publishes to a valid causal configuration. -/
def publishAccepted
    [DecidableEq Observation] [DecidableEq Effect]
    (basis : PrimeNeedWorlds.FiniteCausalBasis
      (DecodedEvent Observation Effect))
    (effectConflict : Effect → Effect → Prop)
    (receipt : NativeReceipt Observation Effect)
    (valid : Valid basis effectConflict receipt) :
    PrimeNeedWorlds.Configuration basis (EquationConflict effectConflict) :=
  (PrimeNeedWorlds.DependencyReceipt.mk (decodedRoots receipt)).publish valid.2

/-- Publication is least among valid worlds containing the decoded roots. -/
theorem publishAccepted_least
    [DecidableEq Observation] [DecidableEq Effect]
    (basis : PrimeNeedWorlds.FiniteCausalBasis
      (DecodedEvent Observation Effect))
    (effectConflict : Effect → Effect → Prop)
    (receipt : NativeReceipt Observation Effect)
    (valid : Valid basis effectConflict receipt)
    (world : PrimeNeedWorlds.Configuration basis
      (EquationConflict effectConflict))
    (containsRoots : decodedRoots receipt ⊆ world.events) :
    publishAccepted basis effectConflict receipt valid ≤ world := by
  exact PrimeNeedWorlds.DependencyReceipt.publish_least
    { roots := decodedRoots receipt } valid.2 world containsRoots

/-! ## Decoded answer/state correspondence -/

/-- A replay certificate links a decoded receipt to a reached candidate state.
This is the honest seam: the trace checker verifies the receipt, while a
separate replay establishes the candidate transition history. -/
structure CandidateReplay
    [DecidableEq Argument] [DecidableEq Observation] [DecidableEq Effect]
    (Context Answer : Type*)
    (candidate : OperationalCandidate Argument Nat Context)
    (receipt : NativeReceipt Observation Effect) where
  finalState : State Argument (Option NativeSource) NativeCell Nat
    Observation Effect Answer
  trace : CandidateTrace candidate unadmittedState finalState
  ready : finalState.phase = .ready ∨ finalState.phase = .published
  exactRoots : finalState.roots = decodedRoots receipt

theorem replay_receipt_is_exact
    [DecidableEq Argument] [DecidableEq Observation] [DecidableEq Effect]
    {Context : Type*}
    {candidate : OperationalCandidate Argument Nat Context}
    {receipt : NativeReceipt Observation Effect}
    (replay : CandidateReplay Context Answer candidate receipt)
    (application : Nat) (answer : Answer) :
    (answerFromReady application candidate replay.finalState answer).receipt.roots =
      decodedRoots receipt := by
  exact replay.exactRoots

/-- A replayed ready answer contains its admitted rule occurrence in the
decoded receipt; validity checking alone does not manufacture this fact. -/
theorem replay_receipt_records_rule_match
    [DecidableEq Argument] [DecidableEq Observation] [DecidableEq Effect]
    {Context : Type*}
    {candidate : OperationalCandidate Argument Nat Context}
    {receipt : NativeReceipt Observation Effect}
    (replay : CandidateReplay Context Answer candidate receipt) :
    ∃ occurrence : Nat,
      ({ occurrence := occurrence, payload := .ruleMatched candidate.rule } :
        DecodedEvent Observation Effect) ∈ decodedRoots receipt := by
  rcases reachable_answer_records_rule_match replay.trace replay.ready with
    ⟨occurrence, recorded⟩
  refine ⟨occurrence, ?_⟩
  rw [replay.exactRoots] at recorded
  exact recorded

/-! ## Positive and negative executable checker examples -/

def discreteBasis (Event : Type*) [DecidableEq Event] :
    PrimeNeedWorlds.FiniteCausalBasis Event where
  support event := {event}
  self_mem event := by simp
  hereditary := by
    intro event predecessor predecessorMem
    simpa using predecessorMem

def discreteExecutableBasis (Event : Type*) [DecidableEq Event] :
    ExecutableCausalBasis (discreteBasis Event) where
  supportList event := [event]
  support_exact event := by simp [discreteBasis]

def noEffectConflict (_ _ : Nat) : Prop := False

instance : DecidableRel noEffectConflict := fun _ _ => isFalse id

def demoCell : NativeCell := { needSession := 1, cell := 1 }
def demoSource : NativeSource :=
  { episode := 1, application := 1, position := 1 }

def validDemoReceipt : NativeReceipt Nat Nat :=
  { receiptId := 1
    events :=
      [ { eventId := 1
          payload := .evaluateCell demoCell (some demoSource) }
      , { eventId := 2
          payload := .observeCell demoCell (some demoSource) 7 }
      , { eventId := 3
          payload := .useEquation 1 1 } ] }

example : accepts (discreteBasis _) (discreteExecutableBasis _)
    noEffectConflict validDemoReceipt = true := by
  decide

def duplicateIdReceipt : NativeReceipt Nat Nat :=
  { receiptId := 2
    events :=
      [ { eventId := 1
          payload := .evaluateCell demoCell (some demoSource) }
      , { eventId := 1
          payload := .useEquation 1 1 } ] }

/-- Negative: one native event ID cannot name two receipt occurrences. -/
example : accepts (discreteBasis _) (discreteExecutableBasis _)
    noEffectConflict duplicateIdReceipt = false := by
  decide

def conflictingCellReceipt : NativeReceipt Nat Nat :=
  { receiptId := 3
    events :=
      [ { eventId := 1
          payload := .observeCell demoCell (some demoSource) 7 }
      , { eventId := 2
          payload := .observeCell demoCell (some demoSource) 8 } ] }

/-- Negative: one Need cell cannot publish two distinct observations. -/
example :
    accepts (discreteBasis _) (discreteExecutableBasis _)
      noEffectConflict conflictingCellReceipt = false := by
  decide

end Mettapedia.Languages.MeTTa.PrimeNativeReceiptCorrespondence
