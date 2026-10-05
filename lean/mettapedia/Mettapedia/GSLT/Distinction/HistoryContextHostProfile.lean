import Mettapedia.GSLT.Distinction.HistoryContextControls
import Mettapedia.GSLT.Distinction.HistoryCappedStage
import Mettapedia.GSLT.Distinction.HistoryCoverageControls

/-!
# The multiset history instance as a host profile of the contextual model

The contextual two-sided model (`HistoryContextCategory`,
`HistoryContextTwoSided`, `HistoryContextCost`, `HistoryCoverageProfiles`,
`HistoryContextControls`) fires events by splitting configurations, with
multiset addition and renaming only, and is free of `Classical.choice`.  The
earlier history modules fire events with Mathlib's multiset erasure and
subtraction, whose well-definedness proofs (`List.Perm.erase`,
`List.Perm.diff`, `List.perm_iff_count`) carry `Classical.choice`.  This module
is the optional host profile that connects the two, and every declaration in it
that uses the multiset firing relation lists `Classical.choice`.

* **The two firing relations agree** (`splits_iff_fires`, `stepEquiv`).
* **The earlier context and renaming span maps are faces of the one context
  category** (`contextSpan_ofFrame`, `contextSpan_ofRenaming`).  A frame and a
  renaming act on the labelled span of `HistoryCoverage` exactly as the
  corresponding contexts act on the span of the model, on events and on both
  endpoints.
* **The unbounded history grammar never stabilizes**
  (`observer_not_stabilizes_listed`).  Over any listed node set with a node, for
  every unit and every readings on the integer scale, by the pigeonhole theorem
  `HistoryCoverageProfiles.not_stabilizes_of_injective`.
* **Depth transfer** (`approx_bounded_iff`).  Configurations within capacity
  whose every count is at least `2 n` below the capacity are depth-`n`
  approximants in the bounded system exactly when they are in the unbounded
  one.
* **The three profiles of the authored instance, side by side**
  (`instance_profiles`): the unbounded instance without a certificate, the
  growing contextual model, and the capacity-one certificate, with the
  transfer between the last and the first.
* **Behaviour agrees, the exact kernel separates** (`behaviour_agrees_kernel_separates`).
  The earlier future-only readout without event labels gives a result and a
  failure one material value; the contextual model's exact kernel separates
  them under the signed readings.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction.HistoryContextHostProfile

open _root_.CategoryTheory
open Mettapedia.GSLT
open Mettapedia.GSLT.HennessyMilner
open Mettapedia.GSLT.ObservationSpans
open Mettapedia.GSLT.Distinction.HistoryGrammar
open Mettapedia.GSLT.Distinction.HistoryObserver
open Mettapedia.GSLT.Distinction.HistoryTwoSidedObserver
open Mettapedia.GSLT.Distinction.HistoryCappedStage
open Mettapedia.GSLT.Distinction.HistoryCoverageProfiles
open Mettapedia.GSLT.Distinction.Constructive
open Mettapedia.GSLT.GradedTwoSidedObservation
open Mettapedia.Cybernetics.DistinctionCalculus.History

/-! ## The two firing relations agree -/

section Bridge

open Mettapedia.GSLT.Distinction.HistoryContextCategory
open Mettapedia.GSLT.Distinction.HistoryIndependence (consumed read produced)
open Mettapedia.GSLT.Distinction.HistoryObserverControls (relabel)

variable {V : Type} [DecidableEq V] (G : Grammar V)

/-- **Firing by splitting is the firing relation of `HistoryGrammar`.** -/
theorem splits_iff_fires (event : Event V) (source target : Multiset V) :
    Splits G event source target ↔ Fires G event source target := by
  rw [HistoryIndependence.fires_iff]
  constructor
  · rintro ⟨rest, rfl, rfl⟩
    refine ⟨Multiset.le_add_right _ _, ?_⟩
    have removed : consumed event + read event + rest - consumed event = read event + rest := by
      rw [Multiset.add_assoc, add_tsub_cancel_left]
    rw [removed]
    abel
  · rintro ⟨enabled, rfl⟩
    obtain ⟨rest, rfl⟩ := Multiset.le_iff_exists_add.mp enabled
    refine ⟨rest, rfl, ?_⟩
    have removed : consumed event + read event + rest - consumed event = read event + rest := by
      rw [Multiset.add_assoc, add_tsub_cancel_left]
    rw [removed]
    abel

/-- **Labelled steps of the two presentations are one.** -/
def stepEquiv : EventStep G ≃ LabelledStep G where
  toFun step := ⟨(step.event, step.source, step.target), (splits_iff_fires G _ _ _).mp step.splits⟩
  invFun step := ⟨step.1.1, step.1.2.1, step.1.2.2, (splits_iff_fires G _ _ _).mpr step.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **A frame acts on the earlier labelled span as the context of the frame
acts on the model's span.** -/
theorem contextSpan_ofFrame (frame : List V) (step : EventStep G) :
    stepEquiv G ((contextSpan G (Context.ofFrame G frame)).events step) =
      (HistoryCoverage.contextMap G (frame : Multiset V)).events (stepEquiv G step) := by
  apply Subtype.ext
  change (relabel (fun x => x) step.event, (Context.ofFrame G frame).apply step.source,
      (Context.ofFrame G frame).apply step.target) = (step.event, step.source + _, step.target + _)
  rw [relabel_id, Context.apply_ofFrame, Context.apply_ofFrame]

/-- **A renaming acts on the earlier labelled span as the context of the
renaming acts on the model's span.** -/
theorem contextSpan_ofRenaming (rename : HistoryCoverage.Renaming G) (step : EventStep G) :
    stepEquiv G ((contextSpan G (Context.ofRenaming rename)).events step) =
      (HistoryCoverage.renameMap G rename).events (stepEquiv G step) := by
  apply Subtype.ext
  change (relabel rename.map step.event, (Context.ofRenaming rename).apply step.source,
      (Context.ofRenaming rename).apply step.target) = (relabel rename.map step.event, step.source.map rename.map,
        step.target.map rename.map)
  rw [Context.apply_ofRenaming, Context.apply_ofRenaming]

/-- **The earlier readout's one-event arrows agree with the model's forward
entries**: with an injective code, a fresh configuration emits a fresh result
along the arrow of an event's code exactly when it does so along the event's
forward entry in the exact profile. -/
theorem readout_arrows_agree (code : Event V → ℕ) (injective : Function.Injective code)
    (oldPoint : Mettapedia.TypeTheory.MaterialSets.Hypersets.LabelledContextPaths.World)
    (point : World G) (live result : Multiset V) (event : Event V) :
    HistoryContextualReadout.Emits G code (HistoryContextualReadout.fresh oldPoint live)
        (HistoryContextualReadout.oneStep oldPoint (code event))
        (HistoryContextualReadout.fresh (HistoryContextualReadout.next oldPoint) result) ↔
      HistoryContextTwoSided.Emits (HistoryContextTwoSided.exact G) (HistoryContextTwoSided.fresh point live)
        (HistoryContextTwoSided.entryArrow point (.forward, event))
        (HistoryContextTwoSided.fresh (HistoryContextTwoSided.next point) result) := by
  rw [HistoryContextualReadout.emits_fresh_iff G code injective,
    HistoryContextTwoSided.emits_entry_fresh_iff]
  constructor
  · intro fires
    exact ⟨(.forward, event), rfl, (splits_iff_fires G event live result).mpr fires⟩
  · rintro ⟨actual, admitted, moves⟩
    change actual = (.forward, event) at admitted
    subst admitted
    exact (splits_iff_fires G event live result).mp moves

end Bridge

/-! ## The unbounded history grammar never stabilizes -/

section Unbounded

variable {V : Type} [DecidableEq V] (G : Grammar V)

omit [DecidableEq V] in
theorem replicate_injective (x : V) : Function.Injective (fun count : ℕ => Multiset.replicate count x) := by
  intro first second same
  have sizes := congrArg Multiset.card same
  simp only [Multiset.card_replicate] at sizes
  exact sizes

/-- **The unbounded history grammar has no certificate at any depth**: over any
listed node set with a node, for every unit and every readings on the integer
scale. -/
theorem observer_not_stabilizes_listed (L : Listing V) (x : V) (unit : ℤ) (positive : 0 < unit)
    (R : NodeReadings (Scale.integers unit positive) V) (stage : ℕ) :
    ¬ (observer G _ R).Stabilizes (observerVocabulary G _ R L) stage :=
  not_stabilizes_of_injective (observer G _ R) (observerVocabulary G _ R L) (fun _ _ same => same)
    (fun left right => (observer_gradedBisimilar_iff_eq G _ R left right).mp)
    (fun count => Multiset.replicate count x) (replicate_injective x) stage

end Unbounded

/-! ## Depth transfer between the bounded and the unbounded grammar -/

section Transfer

variable {V : Type} [DecidableEq V] (G : Grammar V) (L : Listing V) (capacity : ℕ)
variable {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W] (K : Scale W) (R : NodeReadings K V)

/-- The two-sided bounded system. -/
abbrev boundedObserver : PresentedSystem (boundedGSLT G capacity) K :=
  twoSided (boundedPresented G L capacity K R) (boundedPast G L capacity K R)

/-- A two-sided step adds at most two copies of each node. -/
theorem count_le_of_twoSided {label : Direction × Event V} {source target : Multiset V}
    (action : (observer G K R).dynamics.act label source target) (y : V) :
    target.count y ≤ source.count y + 2 := by
  obtain ⟨direction, event⟩ := label
  cases direction with
  | forward => exact (count_le_of_fires G action y).trans (Nat.le_succ _)
  | backward => exact count_le_of_unfires G action y

/-- **Depth transfer.**  Within capacity, configurations whose every count is at
least `2 n` below the capacity are depth-`n` approximants in the bounded system
exactly when they are in the unbounded one. -/
theorem approx_bounded_iff : ∀ (depth : ℕ) (left right : Bounded V capacity),
    (∀ y, left.1.count y + 2 * depth ≤ capacity) → (∀ y, right.1.count y + 2 * depth ≤ capacity) →
      ((boundedObserver G L capacity K R).Approx depth left right ↔
        (observer G K R).Approx depth left.1 right.1)
  | 0, _, _, _, _ => Iff.rfl
  | depth + 1, left, right, leftMargin, rightMargin => by
      have within : ∀ {source target : Multiset V} {label : Direction × Event V},
          (∀ y, source.count y + 2 * (depth + 1) ≤ capacity) →
            (observer G K R).dynamics.act label source target →
              (∀ y, target.count y ≤ capacity) ∧ ∀ y, target.count y + 2 * depth ≤ capacity := by
        intro source target label margin action
        constructor
        · intro y
          have := count_le_of_twoSided G K R action y
          have := margin y
          omega
        · intro y
          have := count_le_of_twoSided G K R action y
          have := margin y
          omega
      have weaker : ∀ (state : Bounded V capacity), (∀ y, state.1.count y + 2 * (depth + 1) ≤ capacity) →
          ∀ y, state.1.count y + 2 * depth ≤ capacity := by
        intro state margin y
        have := margin y
        omega
      constructor
      · rintro ⟨values, forth, back⟩
        refine ⟨values, ?_, ?_⟩
        · intro label left' action
          obtain ⟨bounded, margin'⟩ := within leftMargin action
          obtain ⟨right', action', approx⟩ := forth label ⟨left', bounded⟩ action
          refine ⟨right'.1, action', ?_⟩
          exact (approx_bounded_iff depth ⟨left', bounded⟩ right' margin'
            (within rightMargin action').2).mp approx
        · intro label right' action
          obtain ⟨bounded, margin'⟩ := within rightMargin action
          obtain ⟨left', action', approx⟩ := back label ⟨right', bounded⟩ action
          refine ⟨left'.1, action', ?_⟩
          exact (approx_bounded_iff depth left' ⟨right', bounded⟩ (within leftMargin action').2
            margin').mp approx
      · rintro ⟨values, forth, back⟩
        refine ⟨values, ?_, ?_⟩
        · intro label left' action
          obtain ⟨right', action', approx⟩ := forth label left'.1 action
          obtain ⟨bounded, margin'⟩ := within rightMargin action'
          refine ⟨⟨right', bounded⟩, action', ?_⟩
          exact (approx_bounded_iff depth left' ⟨right', bounded⟩ (within leftMargin action).2
            margin').mpr approx
        · intro label right' action
          obtain ⟨left', action', approx⟩ := back label right'.1 action
          obtain ⟨bounded, margin'⟩ := within leftMargin action'
          refine ⟨⟨left', bounded⟩, action', ?_⟩
          exact (approx_bounded_iff depth ⟨left', bounded⟩ right' margin'
            (within rightMargin action).2).mpr approx

end Transfer


/-! ## The three profiles on the authored instance -/

section Instance

open Mettapedia.GSLT.Distinction.HistoryContextCategory
open Mettapedia.GSLT.Distinction.HistoryContextTwoSided
open Mettapedia.GSLT.Distinction.HistoryContextControls (nodeCoding integerCoding)
open Mettapedia.GSLT.Distinction.HistoryCoverageControls (Node grammar listing scale readings unit_pos)
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open Mettapedia.OSLF.Framework.DerivedModalities

/-- **The three profiles of the authored instance, side by side.**
1. The unbounded instance has no stabilization certificate at any depth.
2. Its contextual model grows: a configuration placed fresh at a later world
   has a material value that no transport of an earlier state has, and at every
   world the fresh values of growing numbers of pending tasks are all different.
3. The capacity-one instance has a certified stage with both endpoint lifts.
4. Within capacity, and `2 n` below it, the bounded and the unbounded
   approximants of depth `n` agree. -/
theorem instance_profiles :
    (∀ stage, ¬ (observer grammar scale readings).Stabilizes
      (observerVocabulary grammar scale readings listing) stage) ∧
    (∀ (point : World grammar) (entry : Entry Node) (earlier : Placed point) (live : Multiset Node),
      value (exact grammar) scale readings nodeCoding listing integerCoding
          ⟨next point, transport (entryArrow point entry) earlier⟩ ≠
        value (exact grammar) scale readings nodeCoding listing integerCoding ⟨next point, fresh (next point) live⟩) ∧
    (∀ point : World grammar, Function.Injective fun count : ℕ =>
      freshValue (exact grammar) scale readings nodeCoding listing integerCoding point
        (Multiset.replicate count Node.task)) ∧
    (∃ stage,
      (stageMap _ (boundedPast grammar listing 1 _ readings) (boundedEvents grammar listing 1 _ readings)
        stage).SourceLifts ∧
      (stageMap _ (boundedPast grammar listing 1 _ readings) (boundedEvents grammar listing 1 _ readings)
        stage).TargetLifts) ∧
    (∀ (capacity depth : ℕ) (left right : Bounded Node capacity),
      (∀ y, left.1.count y + 2 * depth ≤ capacity) → (∀ y, right.1.count y + 2 * depth ≤ capacity) →
        ((boundedObserver grammar listing capacity scale readings).Approx depth left right ↔
          (observer grammar scale readings).Approx depth left.1 right.1)) := by
  refine ⟨fun stage => observer_not_stabilizes_listed grammar listing .task 1 unit_pos readings stage,
    fun point entry earlier live => fresh_not_transport scale readings nodeCoding listing integerCoding
      point entry earlier live,
    fun point => fresh_values_infinite scale readings nodeCoding listing integerCoding point .task, ?_,
    fun capacity depth left right => approx_bounded_iff grammar listing capacity scale readings depth left right⟩
  obtain ⟨stage, sourceLifts, targetLifts, _, _⟩ := HistoryCoverageControls.instance_certificate
  exact ⟨stage, sourceLifts, targetLifts⟩

end Instance

/-! ## Behaviour agrees, the exact kernel separates -/

section Behaviour

open Mettapedia.GSLT.Distinction.HistoryContextCategory
open Mettapedia.GSLT.Distinction.HistoryContextTwoSided
open Mettapedia.GSLT.Distinction.HistoryContextCost
open Mettapedia.GSLT.Distinction.HistoryContextControls
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open HistoryCoverageControls (Node grammar scale)

/-- **Behaviour agrees, the exact kernel separates.**  The earlier future-only
readout without event labels gives a result and a failure one material value at
every world; the two agree on every present signed reading; the contextual
model's exact kernel separates them in every profile. -/
theorem behaviour_agrees_kernel_separates (point : World grammar) :
    (∀ oldPoint, HistoryContextualReadout.material grammar HistoryContextualReadout.unlabelled
        ⟨oldPoint, HistoryContextualReadout.fresh oldPoint (.done ::ₘ 0)⟩ =
      HistoryContextualReadout.material grammar HistoryContextualReadout.unlabelled
        ⟨oldPoint, HistoryContextualReadout.fresh oldPoint (.failed ::ₘ 0)⟩) ∧
      (∀ observation, reading scale signedReadings observation (.done ::ₘ 0) =
        reading scale signedReadings observation (.failed ::ₘ 0)) ∧
      ∀ profile : Profile grammar,
        ¬ ObservedBisimilar profile scale signedReadings point (fresh point (.done ::ₘ 0))
          (fresh point (.failed ::ₘ 0)) :=
  ⟨HistoryCoverageControls.instance_unlabelled_same, (kernel_stronger_than_behaviour point).2.1,
    (kernel_stronger_than_behaviour point).2.2⟩

end Behaviour

end Mettapedia.GSLT.Distinction.HistoryContextHostProfile
