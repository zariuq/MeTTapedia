import Mettapedia.Languages.MeTTa.Prime.NativeFibredScheduleObservation

/-!
# Receipt-retaining observation of cost layer execution

The existing Cost schedule observation computes `WorkSpan` directly as its
witness container.  That view is useful for scheduling, but the full Prime
factorization keeps a richer boundary:

```
selected cost layer normalization path
  → proof-relevant operational schedule
  → exact chronological wave-event history   (S)
  → WorkSpan valuation                        (V)
  → optional scheduler score                  (Q)
```

This module constructs that factorization.  The witness container is the
complete list of existentially indexed wave events, so it retains endpoints,
funded-occurrence receipts, and execution evidence.  `WorkSpan` is only the
declared value read from that history.  Any actual operational realization of
a `Cost.Layer` pulls the architecture back to its selected semantic
normalization paths.

The concrete two-ordering control proves the separation is strict: two valid
Prime schedules retain different chronological receipt histories while
producing the same `WorkSpan`.  No value-level equality identifies the
proof-relevant executions or their witness containers.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Prime.NativeCostLayerReceiptObservation

open Mettapedia.Algebra
open Mettapedia.GSLT.Dynamics
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.Cost.Layer.Operational
open Mettapedia.GSLT.LanguageDef.CostScheduleObservation
open Mettapedia.Languages.MeTTa.Prime.NativeCostLayerOperationalAdequacy
open Mettapedia.Languages.MeTTa.Prime.NativeFibredScheduleObservation
open Mettapedia.Languages.MeTTa.Prime.NativeInteractionFamilyFibration
open Mettapedia.Languages.MeTTa.Prime.NativeInteractionFibration
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

universe uGround

/-! ## Exact wave history as the witness container -/

/-- Retain the complete chronological event history as the `S` dial. -/
def historyCollector (Ground : Type uGround) :
    WitnessCollector (WaveEvent Ground) where
  Container := List (WaveEvent Ground)
  collect := some

/-- Sequential WorkSpan valuation of one retained wave history. -/
def historyWorkSpan {Ground : Type uGround} :
    List (WaveEvent Ground) → WorkSpan
  | [] => 0
  | event :: rest =>
      WorkSpan.sequential event.workSpan (historyWorkSpan rest)

@[simp] theorem historyWorkSpan_nil {Ground : Type uGround} :
    historyWorkSpan ([] : List (WaveEvent Ground)) = 0 :=
  rfl

@[simp] theorem historyWorkSpan_cons {Ground : Type uGround}
    (event : WaveEvent Ground) (rest : List (WaveEvent Ground)) :
    historyWorkSpan (event :: rest) =
      WorkSpan.sequential event.workSpan (historyWorkSpan rest) :=
  rfl

/-- Chronological concatenation is valued sequentially. -/
theorem historyWorkSpan_append {Ground : Type uGround}
    (first second : List (WaveEvent Ground)) :
    historyWorkSpan (first ++ second) =
      WorkSpan.sequential (historyWorkSpan first) (historyWorkSpan second) := by
  induction first with
  | nil => simp
  | cons event rest inductionHypothesis =>
      simp only [List.cons_append, historyWorkSpan_cons]
      rw [inductionHypothesis]
      exact (WorkSpan.sequential_assoc _ _ _).symm

/-- The observation discipline keeps exact history in `S` and reads
`WorkSpan` only as `V`. -/
def historyDiscipline (Ground : Type uGround) :
    ObservationDiscipline (WaveEvent Ground) where
  collection := historyCollector Ground
  Value := WorkSpan
  readout := historyWorkSpan

/-- Exact histories compose by list concatenation. -/
def historyChronological (Ground : Type uGround) :
    ChronologicalCapability (historyDiscipline Ground).collection where
  algebra := IndexedEventValuation.chronologicalListPartialMonoid
    (WaveEvent Ground)
  collect_nil := rfl
  collect_append := by
    intro first second
    rfl

/-! ## Operational schedules inhabit the receipt-retaining architecture -/

/-- Observe a proof-relevant operational schedule without replacing its event
history by the WorkSpan valuation. -/
def operationalObservation (Ground : Type uGround) :
    IndexedExecutionObservation (historyDiscipline Ground) (CostConfig Ground)
      (OperationalSchedule Ground) where
  events := Schedule.events
  container := Schedule.events
  collects := fun _ => rfl

/-- The corresponding public capability-indexed architecture. -/
def operationalArchitecture (Ground : Type uGround) :
    CapabilityIndexedObservationArchitecture (CostConfig Ground)
      (OperationalSchedule Ground) where
  Event := WaveEvent Ground
  discipline := historyDiscipline Ground
  observation := operationalObservation Ground
  domain := ObservationDiscipline.OperationalDomain.reachable
    (historyDiscipline Ground)

/-- Operational concatenation is chronological composition for the richer
container too. -/
def operationalChronological (Ground : Type uGround) :
    (operationalObservation Ground).Chronological where
  append := OperationalSchedule.append
  events_append := Schedule.events_append

/-- Reading the exact wave history reproduces the established schedule
WorkSpan. -/
@[simp] theorem historyWorkSpan_events {Ground : Type uGround}
    {source target : CostConfig Ground}
    (schedule : OperationalSchedule Ground source target) :
    historyWorkSpan (Schedule.events schedule) = schedule.workSpan := by
  induction schedule with
  | refl => rfl
  | cons step tail inductionHypothesis =>
      rcases step with ⟨receipt, stepProof⟩
      simp only [Schedule.events, historyWorkSpan_cons, WaveEvent.workSpan,
        WaveEvent.receipt, OperationalSchedule.workSpan]
      rw [inductionHypothesis]

/-- `V` is exactly the declared WorkSpan valuation, while `S` remains the
complete event list. -/
@[simp] theorem operational_value {Ground : Type uGround}
    {source target : CostConfig Ground}
    (schedule : OperationalSchedule Ground source target) :
    (operationalObservation Ground).value schedule = schedule.workSpan := by
  exact historyWorkSpan_events schedule

/-- The richer witness container recovers the complete funded-occurrence
receipt. -/
@[simp] theorem operational_receipt {Ground : Type uGround}
    {source target : CostConfig Ground}
    (schedule : OperationalSchedule Ground source target) :
    Schedule.eventReceipt
        ((operationalObservation Ground).container schedule) =
      schedule.receipt := by
  exact Schedule.eventReceipt_events schedule

/-- Chronological composition is preserved both before and after valuation. -/
theorem operational_value_append {Ground : Type uGround}
    {source middle target : CostConfig Ground}
    (first : OperationalSchedule Ground source middle)
    (second : OperationalSchedule Ground middle target) :
    (operationalObservation Ground).value (first.append second) =
      WorkSpan.sequential
        ((operationalObservation Ground).value first)
        ((operationalObservation Ground).value second) := by
  rw [operational_value, operational_value, operational_value]
  exact OperationalSchedule.workSpan_append first second

/-! ## Pullback to selected cost layer semantic execution -/

/-- Any genuine operational realization induces an exact observation of the
selected proof-relevant cost layer normalization paths. -/
def semanticObservation {object : Cost.Layer}
    {Ground : Type uGround} (realization : Realization object Ground) :
    IndexedExecutionObservation (historyDiscipline Ground)
      (SemanticState object) (NormalizationPath object) where
  events := fun path => Schedule.events (realization.realizePath path)
  container := fun path => Schedule.events (realization.realizePath path)
  collects := fun _ => rfl

/-- The selected cost layer execution, exact operational receipt history, and
WorkSpan valuation as one capability-indexed architecture. -/
def semanticArchitecture {object : Cost.Layer}
    {Ground : Type uGround} (realization : Realization object Ground) :
    CapabilityIndexedObservationArchitecture (SemanticState object)
      (NormalizationPath object) where
  Event := WaveEvent Ground
  discipline := historyDiscipline Ground
  observation := semanticObservation realization
  domain := ObservationDiscipline.OperationalDomain.reachable
    (historyDiscipline Ground)

/-- Composition of semantic cost layer paths is witnessed by exact concatenation
of their realized event histories. -/
def semanticChronological {object : Cost.Layer}
    {Ground : Type uGround} (realization : Realization object Ground) :
    (semanticObservation realization).Chronological where
  append := fun first second => first.append second
  events_append := by
    intro source middle target first second
    change Schedule.events (realization.realizePath (first.append second)) = _
    rw [realization.realizePath_append, Schedule.events_append]
    rfl

/-- The semantic value is a declared observation of the realized schedule;
it is not the cost layer state or event itself. -/
@[simp] theorem semantic_value {object : Cost.Layer}
    {Ground : Type uGround} (realization : Realization object Ground)
    {source target : SemanticState object}
    (path : NormalizationPath object source target) :
    (semanticObservation realization).value path =
      (realization.realizePath path).workSpan := by
  exact historyWorkSpan_events (realization.realizePath path)

/-- The selected semantic path retains the complete operational receipt after
realization. -/
@[simp] theorem semantic_receipt {object : Cost.Layer}
    {Ground : Type uGround} (realization : Realization object Ground)
    {source target : SemanticState object}
    (path : NormalizationPath object source target) :
    Schedule.eventReceipt
        ((semanticObservation realization).container path) =
      (realization.realizePath path).receipt := by
  exact Schedule.eventReceipt_events (realization.realizePath path)

/-- WorkSpan composes because semantic paths and operational schedules compose;
it is derived rather than installed as cost layer's execution law. -/
theorem semantic_value_append {object : Cost.Layer}
    {Ground : Type uGround} (realization : Realization object Ground)
    {source middle target : SemanticState object}
    (first : NormalizationPath object source middle)
    (second : NormalizationPath object middle target) :
    (semanticObservation realization).value (first.append second) =
      WorkSpan.sequential
        ((semanticObservation realization).value first)
        ((semanticObservation realization).value second) := by
  rw [semantic_value, semantic_value, semantic_value]
  exact realization.workSpan_append first second

/-! ## Concrete strictness: equal WorkSpan, different valid histories -/

namespace Examples

open NativeInteractionFibration.Examples
open NativeInteractionFamilyFibration.Examples

/-- The same two funded occurrences executed in the opposite chronological
order. -/
def rightSingleton : FamilySeparation Ground [rightEvent] source where
  frame := leftEvent.consumed
  source_eq := by
    simp [source, costWaveSource]
    ac_rfl
  nonempty := by simp

def leftAfterRight :
    FamilySeparation Ground [leftEvent] rightSingleton.target where
  frame := rightEvent.produced
  source_eq := by
    simp [FamilySeparation.target, FamilySeparation.toMatching,
      CostMatching.target, costWaveTarget, costWaveSource, rightSingleton]
    ac_rfl
  nonempty := by simp

def reverseTwoColouring :
    ValidWaveColoring Ground source [[rightEvent], [leftEvent]]
      leftAfterRight.target :=
  .cons rightSingleton
    (.cons leftAfterRight (.nil leftAfterRight.target))

/-- The two certified colourings written directly as operational paths.  This
avoids forgetting their wave boundaries through a scalar schedule value. -/
def forwardSchedule : OperationalSchedule Ground source rightAfterLeft.target :=
  .cons ⟨leftSingleton.receipt, ⟨leftSingleton.parallelStep⟩⟩
    (.cons ⟨rightAfterLeft.receipt, ⟨rightAfterLeft.parallelStep⟩⟩
      (.refl rightAfterLeft.target))

def reverseSchedule : OperationalSchedule Ground source leftAfterRight.target :=
  .cons ⟨rightSingleton.receipt, ⟨rightSingleton.parallelStep⟩⟩
    (.cons ⟨leftAfterRight.receipt, ⟨leftAfterRight.parallelStep⟩⟩
      (.refl leftAfterRight.target))

abbrev forwardHistory :=
  (operationalObservation Ground).container forwardSchedule

abbrev reverseHistory :=
  (operationalObservation Ground).container reverseSchedule

/-- Both valid chronological policies have the same WorkSpan value. -/
theorem two_orders_same_workSpan :
    (historyDiscipline Ground).readout forwardHistory =
      (historyDiscipline Ground).readout reverseHistory := by
  change forwardSchedule.workSpan = reverseSchedule.workSpan
  apply WorkSpan.ext
  · simp [forwardSchedule, reverseSchedule,
      OperationalSchedule.workSpan, FamilySeparation.receipt_card]
  · simp [forwardSchedule, reverseSchedule, OperationalSchedule.workSpan]

theorem singleton_receipts_ne :
    leftSingleton.receipt ≠ rightSingleton.receipt := by
  intro receiptsEqual
  have spendsEqual := congrArg
    (Multiset.map (fun receipt => receipt.rawSpend)) receiptsEqual
  change {leftSeal} = {rightSeal} at spendsEqual
  have sealsEqual : leftSeal = rightSeal := by
    simpa using spendsEqual
  simp [leftSeal, rightSeal] at sealsEqual

/-- Their retained histories remain distinct.  The first wave spends the
left occurrence in one schedule and the right occurrence in the other. -/
theorem two_orders_distinct_histories : forwardHistory ≠ reverseHistory := by
  intro equalHistories
  have firstReceipts := congrArg
    (fun history => (history.head?.map WaveEvent.receipt)) equalHistories
  change some leftSingleton.receipt = some rightSingleton.receipt at firstReceipts
  exact singleton_receipts_ne (Option.some.inj firstReceipts)

/-- Therefore WorkSpan is a genuinely lossy valuation of the exact operational
witness container, even when restricted to valid Prime schedules. -/
theorem workSpan_does_not_determine_receipt_history :
    (historyDiscipline Ground).Lossy :=
  ObservationDiscipline.lossy_of_collision (historyDiscipline Ground)
    two_orders_distinct_histories two_orders_same_workSpan

/-- Both separating containers are reached by actual schedules, not invented
values outside the operational domain. -/
theorem both_histories_are_operational :
    (operationalArchitecture Ground).domain.contains forwardHistory ∧
      (operationalArchitecture Ground).domain.contains reverseHistory :=
  ⟨(operationalArchitecture Ground).observed_container_mem
      forwardSchedule,
    (operationalArchitecture Ground).observed_container_mem
      reverseSchedule⟩

end Examples

#print axioms historyWorkSpan_append
#print axioms historyWorkSpan_events
#print axioms operational_receipt
#print axioms operational_value_append
#print axioms semantic_value
#print axioms semantic_receipt
#print axioms semantic_value_append
#print axioms Examples.two_orders_same_workSpan
#print axioms Examples.two_orders_distinct_histories
#print axioms Examples.workSpan_does_not_determine_receipt_history
#print axioms Examples.both_histories_are_operational

end Mettapedia.Languages.MeTTa.Prime.NativeCostLayerReceiptObservation
