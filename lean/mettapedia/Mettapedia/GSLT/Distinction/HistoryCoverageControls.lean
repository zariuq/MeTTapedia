import Mettapedia.GSLT.Distinction.HistoryCoverage
import Mettapedia.GSLT.Distinction.HistoryContextualReadout
import Mettapedia.GSLT.Distinction.HistoryCappedStage

/-!
# Controls for the history instance, and one authored instance

* **An authored instance** (`Node`, `grammar`, `readings`, `pending`).  A
  pending task completes to a result; merging propagates a failure.  The result
  reading is one on a result, the fault reading flags a failure, and the
  program can read the pending work.  On it: the two fibres separating result
  and fault (`instance_result_fault`, `instance_fault_result`), a history fault
  that is not a faulty node (`instance_history_fault`), the readable pending
  cost reflected by the cost reading on a run (`instance_pending_reflected`),
  unit work kept in the account (`instance_levels`), the listed fibres without
  repetition (`instance_outSteps_nodup`), a certified stage of the
  capacity-one system with the stage lifts (`instance_certificate`), and the
  material readout separating a result from a failure only when events label
  the arrows (`instance_material_distinct`, `instance_unlabelled_same`).
* **Endpoint lifts are weaker than event identity.**  The endpoint relation of
  the labelled span satisfies all four occurrence laws and relates two
  different events (`endpoints_laws_not_events`); the GSLT span is covered by
  labelled steps occurrence by occurrence, and its edges forget the event
  (`shadow_lifts_forget_event`).  Where the bridge's stage lifts apply, on the
  bounded system with copy-carrying occurrences, they hold and no choice of
  occurrence from its label and endpoints returns both copies
  (`bounded_lifts_not_copies`).  On the kind-labelled bounded swap system the
  certified classes identify `{true}` and `{false}`, and the lifted event has the
  same kind and a different node (`certified_quotient`).
* **Equality of futures licenses neither the predecessor box nor the descent of
  a provenance-dependent term.**  A result and a failure have one material
  value when events do not label the arrows, but only the result has a pending
  task among its predecessors (`future_equal_box_differs`,
  `past_not_descend`); two receipts with one child have one readout and
  different events (`receipt_not_descend`).
* **Contexts** (`context_enables_merge`, `cost_not_congruent`).  A context can
  enable an event, so contexts preserve steps without covering them; the
  clamped cost reading is not congruent for contexts, while the potential is.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction.HistoryCoverageControls

open _root_.CategoryTheory
open Mettapedia.GSLT
open Mettapedia.GSLT.HennessyMilner
open Mettapedia.GSLT.ObservationSpans
open Mettapedia.GSLT.Distinction.HistoryGrammar
open Mettapedia.GSLT.Distinction.HistoryObserver
open Mettapedia.GSLT.Distinction.HistoryCoverage
open Mettapedia.GSLT.Distinction.HistoryContextualReadout
open Mettapedia.GSLT.Distinction.HistoryCappedStage
open Mettapedia.GSLT.Distinction.Constructive
open Mettapedia.GSLT.Distinction.SpanTransport
open Mettapedia.GSLT.GradedTwoSidedObservation
open Mettapedia.GSLT.Causality.OccurrenceHistory
open Mettapedia.Cybernetics.DistinctionCalculus.History
open Mettapedia.OSLF.Framework.DerivedModalities
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open Mettapedia.TypeTheory.MaterialSets.Hypersets.LabelledContextPaths
open Mettapedia.TypeTheory.MaterialSets.Hypersets.PowerClassFamilyDescent
open Mettapedia.OSLF.Bridges.TypeTheory.GradedValueNativeDescent
open HistoryIndependence (presentation costValuation)

/-! ## Endpoint lifts are weaker than event identity -/

section Endpoints

variable {V : Type} [DecidableEq V] (G : Grammar V)

/-- **The endpoint relation satisfies all four occurrence laws and relates two
different events**: erasing one of two copies and merging them, when the merge
is idempotent. -/
theorem endpoints_laws_not_events (x : V) (idempotent : G.merge x x = x) :
    (SpanRelation.endpoints (A := labelledSpan G) (B := labelledSpan G) Eq).SourceForthOcc ∧
      (SpanRelation.endpoints (A := labelledSpan G) (B := labelledSpan G) Eq).SourceBackOcc ∧
      (SpanRelation.endpoints (A := labelledSpan G) (B := labelledSpan G) Eq).TargetForthOcc ∧
      (SpanRelation.endpoints (A := labelledSpan G) (B := labelledSpan G) Eq).TargetBackOcc ∧
      ¬ (SpanRelation.endpoints (A := labelledSpan G) (B := labelledSpan G) Eq).Keeps
        (LabelledStep.event G) (LabelledStep.event G) := by
  refine ⟨(SpanRelation.endpoints_sourceForthOcc_iff Eq).mpr (sourceForth_eq _),
    (SpanRelation.endpoints_sourceBackOcc_iff Eq).mpr (sourceBack_eq _),
    (SpanRelation.endpoints_targetForthOcc_iff Eq).mpr (targetForth_eq _),
    (SpanRelation.endpoints_targetBackOcc_iff Eq).mpr (targetBack_eq _), fun keeps => ?_⟩
  let fibre := step_forgets_event G x idempotent
  have sources := congrArg Prod.fst fibre.sameShadow
  have targets := congrArg Prod.snd fibre.sameShadow
  exact fibre.differentValue (keeps ⟨sources, targets⟩)

/-- **The GSLT span is covered by labelled steps, and forgets their events**:
both occurrence lifts of the event shadow hold, and two labelled steps with
different events have one shadow. -/
theorem shadow_lifts_forget_event (x : V) (idempotent : G.merge x x = x) :
    (eventShadow G).SourceOccurrenceLifts ∧ (eventShadow G).TargetOccurrenceLifts ∧
      ¬ Function.Injective (eventShadow G).events := by
  refine ⟨eventShadow_sourceOccurrenceLifts G, eventShadow_targetOccurrenceLifts G, fun injective => ?_⟩
  let fibre := step_forgets_event G x idempotent
  have same : fibre.left = fibre.right := injective (by
    obtain ⟨sources, targets⟩ := Prod.mk.inj fibre.sameShadow
    change (⟨_, _, _⟩ : (historyGSLT G).LabeledStep) = ⟨_, _, _⟩
    congr 1)
  exact fibre.differentValue (congrArg (LabelledStep.event G) same)

variable (L : Listing V) (capacity : ℕ)

/-- Causal occurrences of the bounded system: a labelled bounded step and the
copy of its principal node that it uses. -/
def boundedCausal {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W] (K : Scale W)
    (R : NodeReadings K V) : AuthoredEvents (boundedPresented G L capacity K R) where
  span := {
    Edge := {occurrence : Event V × Bounded V capacity × Bounded V capacity × ℕ //
      Fires G occurrence.1 occurrence.2.1.1 occurrence.2.2.1.1 ∧
        occurrence.2.2.2 < occurrence.2.1.1.count (principal occurrence.1)}
    source := fun occurrence => occurrence.1.2.1
    target := fun occurrence => occurrence.1.2.2.1 }
  label occurrence := occurrence.1.1
  sound occurrence := occurrence.2.1
  cover label source target action :=
    ⟨⟨(label, source, target, 0), action, Multiset.count_pos.mpr (principal_mem G action)⟩, rfl, rfl, rfl⟩

/-- **Where the stage lifts apply they do not recover occurrences.**  On the
bounded system with copy-carrying occurrences, the bridge's stage lifts hold
at a certified stage, and no choice of an occurrence from its label and
endpoints returns the two copies erased from `{x, x}`. -/
theorem bounded_lifts_not_copies (x : V) (room : 2 ≤ capacity) (unit : ℤ) (positive : 0 < unit)
    (R : NodeReadings (Scale.integers unit positive) V) :
    (∃ stage,
      (stageMap _ (boundedPast G L capacity _ R) (boundedCausal G L capacity _ R) stage).SourceLifts ∧
        (stageMap _ (boundedPast G L capacity _ R) (boundedCausal G L capacity _ R) stage).TargetLifts) ∧
      ¬ ∃ pick : Event V → Bounded V capacity → Bounded V capacity →
          (boundedCausal G L capacity _ R).span.Edge,
        ∀ occurrence, pick ((boundedCausal G L capacity _ R).label occurrence)
          ((boundedCausal G L capacity _ R).span.source occurrence)
          ((boundedCausal G L capacity _ R).span.target occurrence) = occurrence := by
  refine ⟨?_, ?_⟩
  · obtain ⟨stage, sourceLifts, targetLifts, _, _⟩ :=
      bounded_stage_lifts G L capacity unit positive R (boundedCausal G L capacity _ R)
    exact ⟨stage, sourceLifts, targetLifts⟩
  · rintro ⟨pick, recovers⟩
    have doubled : ∀ y, (pair x x).count y ≤ capacity := by
      intro y
      have bound := Multiset.count_le_card y (pair x x)
      have size : Multiset.card (pair x x) = 2 := by simp [pair]
      omega
    have single : ∀ y, (x ::ₘ 0).count y ≤ capacity := by
      intro y
      have bound := Multiset.count_le_card y (x ::ₘ 0)
      have size : Multiset.card (x ::ₘ 0) = 1 := by simp
      omega
    have erased : Fires G (.erase x) (pair x x) (x ::ₘ 0) := by
      have fires := Fires.erase (G := G) (x := x) (live := pair x x) (by simp [pair])
      simpa [pair] using fires
    have copies : (pair x x).count (principal (Event.erase x)) = 2 := by
      simp [pair, principal]
    let first : (boundedCausal G L capacity _ R).span.Edge :=
      ⟨(.erase x, ⟨pair x x, doubled⟩, ⟨x ::ₘ 0, single⟩, 0), erased,
        show 0 < (pair x x).count (principal (Event.erase x)) by rw [copies]; omega⟩
    let second : (boundedCausal G L capacity _ R).span.Edge :=
      ⟨(.erase x, ⟨pair x x, doubled⟩, ⟨x ::ₘ 0, single⟩, 1), erased,
        show 1 < (pair x x).count (principal (Event.erase x)) by rw [copies]; omega⟩
    have firstBack := recovers first
    have secondBack := recovers second
    have same : first = second := firstBack.symm.trans secondBack
    have indices := congrArg (fun occurrence : (boundedCausal G L capacity _ R).span.Edge =>
      occurrence.1.2.2.2) same
    exact Nat.zero_ne_one indices

end Endpoints

/-! ### A certified stage that identifies configurations -/

section Certified

open HistoryObserverControls (swapGrammar)

/-- The two nodes of the swap grammar, listed once each. -/
def boolListing : Listing Bool := ⟨[false, true], fun node => by cases node <;> simp⟩

theorem unit_pos' : (0 : ℤ) < 1 := Int.one_pos

/-- Readings that do not depend on the node. -/
def flatReadings : NodeReadings (Scale.integers 1 unit_pos') Bool where
  result _ := 0
  result_nonneg _ := le_rfl
  result_le_one _ := by decide
  faulty _ := false
  potential _ := 0

/-- The two-sided kind-labelled swap system with capacity one. -/
abbrev swapKind :=
  twoSided (boundedKindPresented swapGrammar boolListing 1 _ flatReadings)
    (boundedKindPast swapGrammar boolListing 1 _ flatReadings)

theorem not_injective : Function.Injective not := fun first second same => by
  cases first <;> cases second <;> simp_all

theorem swap_bounded (live : Bounded Bool 1) : ∀ y, (live.1.map not).count y ≤ 1 := by
  intro y
  have counted := Multiset.count_map_eq_count' not live.1 not_injective (not y)
  rw [Bool.not_not] at counted
  rw [counted]
  exact live.2 _

/-- Swap the two nodes of a bounded configuration. -/
def swapped (live : Bounded Bool 1) : Bounded Bool 1 := ⟨live.1.map not, swap_bounded live⟩

theorem swapped_swapped (live : Bounded Bool 1) : swapped (swapped live) = live := by
  apply Subtype.ext
  change (live.1.map not).map not = live.1
  rw [Multiset.map_map]
  conv_rhs => rw [← Multiset.map_id' live.1]
  congr 1
  funext node
  cases node <;> rfl

theorem fires_swapped {event : Event Bool} {source target : Bounded Bool 1}
    (fires : Fires swapGrammar event source.1 target.1) :
    Fires swapGrammar (HistoryObserverControls.relabel not event) (swapped source).1 (swapped target).1 :=
  HistoryObserverControls.fires_map swapGrammar not not_injective (fun _ => rfl) (fun _ _ => rfl) fires

theorem flat_reading (observation : Reading) (live : Multiset Bool) :
    reading (Scale.integers 1 unit_pos') flatReadings observation (live.map not) =
      reading (Scale.integers 1 unit_pos') flatReadings observation live :=
  reading_congruent_rename (Scale.integers 1 unit_pos') flatReadings not (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl) observation rfl

theorem swap_forth {label : Direction × EventKind} {source target : Bounded Bool 1}
    (action : swapKind.dynamics.act label source target) :
    swapKind.dynamics.act label (swapped source) (swapped target) := by
  rcases label with ⟨direction, kind⟩
  cases direction with
  | forward =>
      obtain ⟨event, kindEq, fires⟩ := action
      exact ⟨HistoryObserverControls.relabel not event,
        (HistoryObserverControls.kindOf_relabel not event).trans kindEq, fires_swapped fires⟩
  | backward =>
      obtain ⟨event, kindEq, fires⟩ := action
      exact ⟨HistoryObserverControls.relabel not event,
        (HistoryObserverControls.kindOf_relabel not event).trans kindEq, fires_swapped fires⟩

/-- **Swapping the nodes is a graded bisimulation of the kind-labelled system.** -/
theorem swap_isGradedBisimulation :
    swapKind.IsGradedBisimulation fun left right => right = swapped left := by
  refine ⟨?_, ?_, ?_⟩
  · rintro left _ rfl label left' action
    exact ⟨swapped left', swap_forth action, rfl⟩
  · rintro left _ rfl label right' action
    refine ⟨swapped right', ?_, (swapped_swapped right').symm⟩
    have back := swap_forth action
    rwa [swapped_swapped] at back
  · rintro left _ rfl observation
    exact (flat_reading observation left.1).symm

/-- A single node, within capacity one. -/
def single (node : Bool) : Bounded Bool 1 :=
  ⟨node ::ₘ 0, fun y => by
    have bound := Multiset.count_le_card y (node ::ₘ 0)
    simp only [Multiset.card_cons, Multiset.card_zero] at bound
    omega⟩

theorem single_bisimilar : swapKind.GradedBisimilar (single true) (single false) :=
  ⟨_, swap_isGradedBisimulation, rfl⟩

/-- Erasing the node of `{true}`. -/
def eraseTrue :
    (boundedKindEvents swapGrammar boolListing 1 (Scale.integers 1 unit_pos') flatReadings).span.Edge :=
  ⟨(.erase true, single true, ⟨0, fun _ => Nat.zero_le _⟩), by
    have fires := Fires.erase (G := swapGrammar) (Multiset.mem_cons_self true 0)
    rwa [Multiset.erase_cons_head] at fires⟩

/-- **A certified stage with a real quotient, and lifts that change the event.**
The kind-labelled swap system with capacity one has a certified stage; there
the stage lifts hold, `{true}` and `{false}` are one class although they are
different configurations, and the event matched at `{false}` for erasing the
node of `{true}` has the same kind and is a different event. -/
theorem certified_quotient :
    ∃ stage,
      (stageMap _ (boundedKindPast swapGrammar boolListing 1 _ flatReadings)
        (boundedKindEvents swapGrammar boolListing 1 _ flatReadings) stage).SourceLifts ∧
      (stageMap _ (boundedKindPast swapGrammar boolListing 1 _ flatReadings)
        (boundedKindEvents swapGrammar boolListing 1 _ flatReadings) stage).TargetLifts ∧
      stateOf swapKind stage (single true) = stateOf swapKind stage (single false) ∧
      single true ≠ single false ∧
      ∃ matched : (boundedKindEvents swapGrammar boolListing 1 _ flatReadings).span.Edge,
        kindOf matched.1.1 = kindOf eraseTrue.1.1 ∧ matched.1.2.1 = single false ∧
          matched.1.1 ≠ eraseTrue.1.1 := by
  obtain ⟨stage, stable, sourceLifts, targetLifts⟩ :=
    boundedKind_stage_lifts swapGrammar boolListing 1 1 unit_pos' flatReadings
      (boundedKindEvents swapGrammar boolListing 1 _ flatReadings)
  have sameClass := stateOf_eq_of_gradedBisimilar swapKind stage single_bisimilar
  refine ⟨stage, sourceLifts, targetLifts, sameClass, ?_, ?_⟩
  · intro same
    have nodes := Multiset.singleton_inj.mp (congrArg Subtype.val same)
    exact Bool.noConfusion nodes
  · obtain ⟨matched, labelEq, sourceEq, _⟩ := match_future _
      (boundedKindPast swapGrammar boolListing 1 _ flatReadings)
      (boundedKindEvents swapGrammar boolListing 1 _ flatReadings)
      (boundedKindVocabulary swapGrammar boolListing 1 _ flatReadings) stage
      (Scale.integers_positive 1 unit_pos') stable (single false) eraseTrue sameClass
    refine ⟨matched, labelEq, sourceEq, fun same => ?_⟩
    obtain ⟨⟨event, source, target⟩, fires⟩ := matched
    change event = .erase true at same
    change source = single false at sourceEq
    subst same
    subst sourceEq
    have member := principal_mem swapGrammar fires
    simp [principal, single] at member

end Certified

/-! ## Contexts -/

section Contexts

variable {V : Type} [DecidableEq V] (G : Grammar V)

/-- **A context can enable an event**: merging two copies of a node fires once a
second copy is in context, and not before. -/
theorem context_enables_merge (x : V) :
    (¬ ∃ result, Fires G (.merge x x) (x ::ₘ 0) result) ∧
      Fires G (.merge x x) ((x ::ₘ 0) + (x ::ₘ 0)) (G.merge x x ::ₘ 0) := by
  constructor
  · rintro ⟨result, fires⟩
    cases fires with
    | merge enabled =>
        have := Multiset.count_le_of_le x enabled
        simp [pair] at this
  · have fires := Fires.merge (G := G) (x := x) (y := x) (live := (x ::ₘ 0) + (x ::ₘ 0))
      (by simp [pair])
    have rest : (x ::ₘ 0) + (x ::ₘ 0) - pair x x = 0 := by
      simp [pair]
    rwa [rest] at fires

end Contexts

/-! ## The authored instance -/

/-- The nodes of the authored instance: a pending task, a result, a failure. -/
inductive Node where
  | task
  | done
  | failed
  deriving DecidableEq, Repr

namespace Node

/-- An injective index of the nodes. -/
def index : Node → ℕ
  | .task => 0
  | .done => 1
  | .failed => 2

theorem index_injective : Function.Injective index := by
  intro first second same
  cases first <;> cases second <;> first | rfl | exact absurd same (by decide)

end Node

open Node

/-- **The authored grammar**: a pending task completes to a result; merging two
nodes fails if either failed, gives a result if both are results, and is
pending otherwise. -/
def grammar : Grammar Node where
  evolve
    | .task => .done
    | node => node
  merge
    | .failed, _ => .failed
    | _, .failed => .failed
    | .done, .done => .done
    | _, _ => .task

/-- The three nodes, listed once each. -/
def listing : Listing Node := ⟨[.task, .done, .failed], fun node => by cases node <;> simp⟩

theorem listing_nodup : listing.nodes.Nodup := by decide

theorem unit_pos : (0 : ℤ) < 1 := Int.one_pos

/-- The integer scale of unit one. -/
abbrev scale : Scale ℤ := Scale.integers 1 unit_pos

/-- **The authored readings**: a result reads one, a failure is faulty, and a
pending task carries one unit of potential. -/
def readings : NodeReadings scale Node where
  result
    | .done => 1
    | _ => 0
  result_nonneg node := by cases node <;> decide
  result_le_one node := by cases node <;> decide
  faulty
    | .failed => true
    | _ => false
  potential
    | .task => 1
    | _ => 0

/-- The pending work a program can read: one unit per pending task. -/
def pending : Node → ℤ
  | .task => 1
  | _ => 0

/-- The event cost of the pending work. -/
def pendingCost : Event Node → ℤ
  | .evolve x => pending (grammar.evolve x) - pending x
  | .fork x => pending x
  | .merge x y => pending (grammar.merge x y) - pending x - pending y
  | .erase x => -pending x

theorem pendingCost_laws : PotentialLaws grammar pendingCost pending :=
  fun _ _ => ⟨rfl, rfl, rfl, rfl⟩

/-- **Result and fault on the instance (1)**: one result reading, two fault
readings. -/
def instance_result_fault :
    Core.NonFactorization.NonTrivialFiber (reading scale readings .result) (reading scale readings .fault) :=
  result_fault_fibre scale readings (healthy := .done) (faulty := .failed) rfl rfl rfl

/-- **Result and fault on the instance (2)**: one fault reading, two result
readings. -/
def instance_fault_result :
    Core.NonFactorization.NonTrivialFiber (reading scale readings .fault) (reading scale readings .result) :=
  fault_result_fibre scale readings (healthy := .done) (faulty := .failed) rfl rfl rfl rfl

/-- **A history fault is not a faulty node, on the instance.** -/
theorem instance_history_fault :
    run grammar [.fork .failed] (.failed ::ₘ 0) = some (.failed ::ₘ .failed ::ₘ 0) ∧
      0 < (presented grammar scale readings).val (chain grammar scale readings [.fork .failed] .top)
        (.failed ::ₘ 0) ∧
      reading scale readings .fault (.failed ::ₘ .failed ::ₘ 0) = scale.one ∧
      run grammar [.erase .done, .erase .done] (.done ::ₘ 0) = none ∧
      (presented grammar scale readings).val (chain grammar scale readings [.erase .done, .erase .done] .top)
        (.done ::ₘ 0) = 0 ∧
      reading scale readings .fault (.done ::ₘ 0) = 0 :=
  history_fault_not_fault_reading grammar scale readings (Scale.integers_positive 1 unit_pos) rfl rfl

/-- The run that completes the pending task. -/
def completeRun : OccurrencePath (presentation grammar) (.task ::ₘ 0) (.done ::ₘ 0) :=
  .cons (occurrence grammar (evolve_head grammar .task 0)) (.refl _)

/-- **The pending work is readable, and the cost reading reflects it on a run**:
completing the task costs `-1`, the change of the cost reading. -/
theorem instance_pending_reflected :
    ProgramReadable grammar pendingCost ∧
      (costValuation grammar pendingCost).onPath completeRun = -1 ∧
      (costValuation grammar pendingCost).onPath completeRun =
        reading scale readings .cost (.done ::ₘ 0) - reading scale readings .cost (.task ::ₘ 0) := by
  refine ⟨readable_of_laws grammar pendingCost_laws, rfl, ?_⟩
  have laws : PotentialLaws grammar pendingCost readings.potential := fun x y => by
    cases x <;> cases y <;> exact ⟨rfl, rfl, rfl, rfl⟩
  exact readable_reflected grammar scale readings laws completeRun (by decide) (by decide)

/-- **Unit work stays in the account, on the instance**: replaying the
copy-and-erase loop of a task by the empty run is qualified for the pending
work, not for the work, and not for the three levels together. -/
theorem instance_levels :
    LevelAccounts.QualifiedReplay (levels grammar pendingCost).reference (forkEraseLoop grammar .task)
        (OccurrencePath.refl (P := presentation grammar) (.task ::ₘ 0)) ∧
      ¬ LevelAccounts.QualifiedReplay (levels grammar pendingCost).work (forkEraseLoop grammar .task)
        (OccurrencePath.refl (P := presentation grammar) (.task ::ₘ 0)) ∧
      ¬ LevelAccounts.QualifiedReplay (levels grammar pendingCost).total (forkEraseLoop grammar .task)
        (OccurrencePath.refl (P := presentation grammar) (.task ::ₘ 0)) :=
  levels_replay grammar pendingCost_laws .task

/-- **The listed fibres of the instance have no repetition.** -/
theorem instance_outSteps_nodup (live : Multiset Node) :
    (outSteps grammar listing live).Nodup ∧ (inSteps grammar listing live).Nodup :=
  ⟨outSteps_nodup grammar listing listing_nodup live, inSteps_nodup grammar listing listing_nodup live⟩

/-- **A certified stage for the instance with capacity one**, with both stage
lifts and the two modal pullbacks for its labelled bounded steps. -/
theorem instance_certificate :
    ∃ stage,
      (stageMap _ (boundedPast grammar listing 1 _ readings) (boundedEvents grammar listing 1 _ readings)
        stage).SourceLifts ∧
      (stageMap _ (boundedPast grammar listing 1 _ readings) (boundedEvents grammar listing 1 _ readings)
        stage).TargetLifts ∧
      (∀ predicate (source : Bounded Node 1),
        derivedDiamond (stageSpan _ (boundedPast grammar listing 1 _ readings)
            (boundedEvents grammar listing 1 _ readings) stage) predicate
            (stateOf (twoSided _ (boundedPast grammar listing 1 _ readings)) stage source) ↔
          derivedDiamond (boundedEvents grammar listing 1 _ readings).span
            (predicate ∘ stateOf (twoSided _ (boundedPast grammar listing 1 _ readings)) stage) source) ∧
      (∀ predicate (target : Bounded Node 1),
        derivedBox (stageSpan _ (boundedPast grammar listing 1 _ readings)
            (boundedEvents grammar listing 1 _ readings) stage) predicate
            (stateOf (twoSided _ (boundedPast grammar listing 1 _ readings)) stage target) ↔
          derivedBox (boundedEvents grammar listing 1 _ readings).span
            (predicate ∘ stateOf (twoSided _ (boundedPast grammar listing 1 _ readings)) stage) target) :=
  bounded_stage_lifts grammar listing 1 1 unit_pos readings (boundedEvents grammar listing 1 _ readings)

/-- **With events on the arrows, a result and a failure have different material
values.** -/
theorem instance_material_distinct (point : World) :
    material grammar (eventCode Node.index) ⟨point, fresh point (.done ::ₘ 0)⟩ ≠
      material grammar (eventCode Node.index) ⟨point, fresh point (.failed ::ₘ 0)⟩ := by
  intro same
  have configurations := (material_fresh_eq_iff grammar (eventCode Node.index)
    (eventCode_injective Node.index_injective) point _ _).mp same
  exact absurd configurations (by decide)

/-- **Without event labels, they have one material value.** -/
theorem instance_unlabelled_same (point : World) :
    material grammar unlabelled ⟨point, fresh point (.done ::ₘ 0)⟩ =
      material grammar unlabelled ⟨point, fresh point (.failed ::ₘ 0)⟩ :=
  (material_eq_iff grammar unlabelled point _ _).mpr
    ((unlabelled_fresh_bisimilar_iff grammar point _ _).mpr rfl)

/-! ## Equality of futures licenses neither the predecessor box nor descent -/

/-- What steps into a single node: an evolution of a single node, or a step
from the empty configuration or from two nodes. -/
theorem into_singleton {event : Event Node} {source target : Multiset Node} {y : Node}
    (fires : Fires grammar event source target) (single : target = y ::ₘ 0) :
    (∃ u, source = u ::ₘ 0 ∧ grammar.evolve u = y) ∨ source = 0 ∨ 2 ≤ Multiset.card source := by
  have sizes := congrArg Multiset.card single
  rw [Multiset.card_cons, Multiset.card_zero] at sizes
  cases fires with
  | @evolve u _ member =>
      left
      have erased := card_erase_add_one member
      rw [Multiset.card_cons] at sizes
      have empty : source.erase u = 0 := Multiset.card_eq_zero.mp (by omega)
      rw [empty] at single
      refine ⟨u, ?_, Multiset.singleton_inj.mp single⟩
      rw [← Multiset.cons_erase member, empty]
  | fork member =>
      rw [Multiset.card_cons] at sizes
      exact Or.inr (Or.inl (Multiset.card_eq_zero.mp (by omega)))
  | merge enabled =>
      have two := card_sub_pair_add_two enabled
      rw [Multiset.card_cons] at sizes
      exact Or.inr (Or.inr (by omega))
  | erase member =>
      have erased := card_erase_add_one member
      exact Or.inr (Or.inr (by omega))

/-- **Equal futures, different pasts.**  Without event labels a result and a
failure have one material value, at every world; but a pending task steps into
the result, and nothing that is a single pending task steps into the
failure. -/
theorem future_equal_box_differs (point : World) :
    material grammar unlabelled ⟨point, fresh point (.done ::ₘ 0)⟩ =
        material grammar unlabelled ⟨point, fresh point (.failed ::ₘ 0)⟩ ∧
      ¬ derivedBox (labelledSpan grammar) (fun live => live ≠ .task ::ₘ 0) (.done ::ₘ 0) ∧
      derivedBox (labelledSpan grammar) (fun live => live ≠ .task ::ₘ 0) (.failed ::ₘ 0) := by
  refine ⟨instance_unlabelled_same point, fun box => ?_, ?_⟩
  · exact box ⟨(.evolve .task, .task ::ₘ 0, .done ::ₘ 0), evolve_head grammar .task 0⟩ rfl rfl
  · rintro ⟨⟨event, source, target⟩, fires⟩ targetEq
    change target = .failed ::ₘ 0 at targetEq
    change source ≠ .task ::ₘ 0
    rcases into_singleton fires targetEq with ⟨u, rfl, evolved⟩ | rfl | large
    · intro same
      rw [Multiset.singleton_inj.mp same] at evolved
      exact absurd evolved (by decide)
    · intro same
      exact absurd (congrArg Multiset.card same) (by simp)
    · intro same
      rw [same] at large
      simp at large

/-- **A provenance-dependent term does not descend to the futures**: no reading
of material values decides whether a pending task is among the predecessors. -/
theorem past_not_descend (point : World) :
    ¬ ∃ decide : HSet.{0} → Prop, ∀ live : Multiset Node,
      decide (material grammar unlabelled ⟨point, fresh point live⟩) ↔
        derivedBox (labelledSpan grammar) (fun source => source ≠ .task ::ₘ 0) live := by
  rintro ⟨decide, decides⟩
  obtain ⟨same, notDone, failed⟩ := future_equal_box_differs point
  exact notDone ((decides _).mp (same ▸ (decides _).mpr failed))

/-- **Receipts do not descend to the readout**: without event labels, erasing
one of two results and merging them are two receipts whose children have one
readout value, so no reading of the readout returns the event. -/
theorem receipt_not_descend (point : World) :
    ¬ ∃ decode : (ContextualSmallCoalgebraGenerators.quotient (D := World)).obj (next point) → Event Node,
      ∀ receipt : (receipts grammar unlabelled point (fresh point (pair .done .done))).Carrier
          ⟨next point, oneStep point 0⟩,
        decode ((readout grammar unlabelled).app (next point)
          ((receipts grammar unlabelled point (fresh point (pair .done .done))).value _ receipt)) =
          receipt.1.1 := by
  rintro ⟨decode, decodes⟩
  obtain ⟨first, second, different, sameChild⟩ :=
    unlabelled_receipts_one_child grammar .done rfl point
  have firstEvent := decodes first
  have secondEvent := decodes second
  rw [sameChild] at firstEvent
  have events : first.1.1 = second.1.1 := firstEvent.symm.trans secondEvent
  obtain ⟨⟨firstEventValue, firstChild, firstRest⟩, firstPath, firstFires⟩ := first
  obtain ⟨⟨secondEventValue, secondChild, secondRest⟩, secondPath, secondFires⟩ := second
  change firstEventValue = secondEventValue at events
  subst events
  apply different
  have pathFirst : firstRest = [] := (List.cons.inj firstPath).2.symm
  have pathSecond : secondRest = [] := (List.cons.inj secondPath).2.symm
  subst pathFirst
  subst pathSecond
  have children : firstChild = secondChild :=
    fires_target_unique grammar firstFires secondFires
  subst children
  rfl

/-! ## The cost reading in context -/

/-- Signed readings on the instance: a failure carries negative potential. -/
def signedReadings : NodeReadings scale Node where
  result _ := 0
  result_nonneg _ := le_rfl
  result_le_one _ := by decide
  faulty _ := false
  potential
    | .task => 1
    | .failed => -1
    | .done => 0

/-- **The clamped cost reading is not congruent for contexts**: the empty
configuration and a failure both read `0`, and with a pending task in context
they read `1` and `0`. -/
theorem cost_not_congruent :
    ¬ ∃ onValue : ℤ → ℤ, Congruent (fun live value => reading scale signedReadings .cost live = value)
      (· + (.task ::ₘ 0)) onValue := by
  rintro ⟨onValue, congruent⟩
  have empty := congruent (x := (0 : Multiset Node)) (y := 0) (by decide)
  have failure := congruent (x := .failed ::ₘ 0) (y := 0) (by decide)
  change reading scale signedReadings .cost (0 + (.task ::ₘ 0)) = onValue 0 at empty
  change reading scale signedReadings .cost ((.failed ::ₘ 0) + (.task ::ₘ 0)) = onValue 0 at failure
  have values : reading scale signedReadings .cost (0 + (.task ::ₘ 0)) =
      reading scale signedReadings .cost ((.failed ::ₘ 0) + (.task ::ₘ 0)) := empty.trans failure.symm
  revert values
  decide

/-- **The potential is congruent for the same context.** -/
theorem potential_congruent_instance :
    Congruent (fun live value => potentialSum signedReadings.potential live = value)
      (· + (.task ::ₘ 0)) (· + potentialSum signedReadings.potential (.task ::ₘ 0)) :=
  potential_congruent_add signedReadings.potential _

end Mettapedia.GSLT.Distinction.HistoryCoverageControls
