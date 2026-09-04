import Mathlib.CategoryTheory.Products.Basic
import Mettapedia.GSLT.Core.ObservationIndexedPruning
import Mettapedia.GSLT.Dynamics.EventValuationFunctor
import Mettapedia.GSLT.Dynamics.PartialObservationProduct

/-!
# Independent and synchronized products of partial event valuations

Two partial valuation axes have two different products.

* The categorical product retains both optional history grades independently:
  `Option Left × Option Right`.
* `Valuation.prod` synchronizes acceptance and retains
  `Option (Left × Right)`.

These agree only under an explicit failure-alignment condition.  This file
defines both constructions, characterizes exactly when splitting the
synchronized grade preserves composition, and proves the corresponding
history-observation criterion.  A counterexample shows why an unqualified
identification would erase a successful independent coordinate.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.IndependentEventValuationProduct

open CategoryTheory
open Mettapedia.Cybernetics
open Mettapedia.GSLT
open Mettapedia.GSLT.Core.ObservationIndexedPruning
open Mettapedia.GSLT.Dynamics.IndexedEventValuation
open Mettapedia.GSLT.Dynamics.EventValuationFunctor
open Mettapedia.GSLT.Dynamics.PartialObservationProduct

universe uEvent uLeft uRight

/-! ## Independent and synchronized grade carriers -/

/-- The genuinely independent history functor.  Its two target morphisms are
optional grades in separate categorical coordinates. -/
def independentHistoryFunctor {Event : Type uEvent}
    (left : Valuation.{uEvent, uLeft} Event)
    (right : Valuation.{uEvent, uRight} Event) :
    EventHistory Event ⥤
      (PartialMonoidDelooping left.algebra ×
        PartialMonoidDelooping right.algebra) :=
  (toHistoryFunctor left).prod' (toHistoryFunctor right)

/-- Independent pointwise observation of one event history. -/
def independentGrade {Event : Type uEvent}
    (left : Valuation.{uEvent, uLeft} Event)
    (right : Valuation.{uEvent, uRight} Event)
    (history : List Event) : Option left.Grade × Option right.Grade :=
  (functorGrade left history, functorGrade right history)

@[simp] theorem independentHistoryFunctor_map {Event : Type uEvent}
    (left : Valuation.{uEvent, uLeft} Event)
    (right : Valuation.{uEvent, uRight} Event)
    (history : List Event) :
    (independentHistoryFunctor left right).map
        (X := EventHistory.object Event) (Y := EventHistory.object Event)
        history = independentGrade left right history :=
  rfl

/-! ## Exact categorical comparison criterion -/

/-- Componentwise composition in the categorical product of the two
partial-monoid deloopings. -/
def independentCompose {Left : Type uLeft} {Right : Type uRight}
    (left : PartialMonoid Left) (right : PartialMonoid Right)
    (first second : Option Left × Option Right) :
    Option Left × Option Right :=
  (PartialMonoidDelooping.compose left first.1 second.1,
    PartialMonoidDelooping.compose right first.2 second.2)

/-- The two partial operations fail together on every paired input. -/
def OperationsFailTogether {Left : Type uLeft} {Right : Type uRight}
    (left : PartialMonoid Left) (right : PartialMonoid Right) : Prop :=
  ∀ leftFirst leftSecond rightFirst rightSecond,
    (left.op leftFirst leftSecond).isSome =
      (right.op rightFirst rightSecond).isSome

/-- Every pair of grades has a defined composite. -/
def OperationTotal {Grade : Type uLeft}
    (algebra : PartialMonoid Grade) : Prop :=
  ∀ first second, ∃ result, algebra.op first second = some result

/-- Global cross-coordinate failure alignment is possible exactly when both
partial operations are actually total.  The units force the reverse
direction: compare any operation in one coordinate with unit composition in
the other. -/
theorem operationsFailTogether_iff_operationTotal
    {Left : Type uLeft} {Right : Type uRight}
    (left : PartialMonoid Left) (right : PartialMonoid Right) :
    OperationsFailTogether left right ↔
      OperationTotal left ∧ OperationTotal right := by
  constructor
  · intro aligned
    constructor
    · intro first second
      have same := aligned first second right.unit right.unit
      rw [right.unit_op] at same
      cases equation : left.op first second with
      | none => simp [equation] at same
      | some result => exact ⟨result, rfl⟩
    · intro first second
      have same := aligned left.unit left.unit first second
      rw [left.unit_op] at same
      cases equation : right.op first second with
      | none => simp [equation] at same
      | some result => exact ⟨result, rfl⟩
  · rintro ⟨leftTotal, rightTotal⟩
    intro leftFirst leftSecond rightFirst rightSecond
    obtain ⟨leftResult, leftEquation⟩ := leftTotal leftFirst leftSecond
    obtain ⟨rightResult, rightEquation⟩ := rightTotal rightFirst rightSecond
    simp [leftEquation, rightEquation]

/-- Splitting synchronized composition preserves categorical composition
exactly when the two partial operations fail together. -/
theorem operationsFailTogether_iff_split_preserves_comp
    {Left : Type uLeft} {Right : Type uRight}
    (left : PartialMonoid Left) (right : PartialMonoid Right) :
    OperationsFailTogether left right ↔
      ∀ first second : Option (Left × Right),
        split
            (PartialMonoidDelooping.compose (left.prod right) first second) =
          independentCompose left right
            (split first) (split second) := by
  constructor
  · intro aligned first second
    cases first with
    | none => rfl
    | some first =>
        rcases first with ⟨leftFirst, rightFirst⟩
        cases second with
        | none => simp [split, independentCompose,
            PartialMonoidDelooping.compose]
        | some second =>
            rcases second with ⟨leftSecond, rightSecond⟩
            have sameFailure := aligned leftFirst leftSecond rightFirst rightSecond
            cases leftEquation : left.op leftFirst leftSecond <;>
              cases rightEquation : right.op rightFirst rightSecond <;>
              simp [split, independentCompose,
                PartialMonoidDelooping.compose, PartialMonoid.prod,
                leftEquation, rightEquation] at sameFailure ⊢
  · intro preserves leftFirst leftSecond rightFirst rightSecond
    have comparison := preserves
      (some (leftFirst, rightFirst)) (some (leftSecond, rightSecond))
    cases leftEquation : left.op leftFirst leftSecond <;>
      cases rightEquation : right.op rightFirst rightSecond <;>
      simp [split, independentCompose,
        PartialMonoidDelooping.compose, PartialMonoid.prod,
        leftEquation, rightEquation] at comparison ⊢

/-- Under operation-level failure alignment, splitting synchronized grades is
a genuine functor into the categorical product. -/
def splitComparisonFunctor {Left : Type uLeft} {Right : Type uRight}
    (left : PartialMonoid Left) (right : PartialMonoid Right)
    (aligned : OperationsFailTogether left right) :
    PartialMonoidDelooping (left.prod right) ⥤
      (PartialMonoidDelooping left × PartialMonoidDelooping right) where
  obj _ :=
    (PartialMonoidDelooping.object left,
      PartialMonoidDelooping.object right)
  map grade := split grade
  map_id _ := rfl
  map_comp first second := by
    change
      split
          (PartialMonoidDelooping.compose (left.prod right) first second) =
        independentCompose left right
          (split first) (split second)
    exact
      (operationsFailTogether_iff_split_preserves_comp left right).1 aligned
        first second

/-! ## Exact history-observation comparison -/

/-- The two valuation axes accept exactly the same finite histories. -/
def HistoryFailureAligned {Event : Type uEvent}
    (left : Valuation.{uEvent, uLeft} Event)
    (right : Valuation.{uEvent, uRight} Event) : Prop :=
  ∀ history, DefinedTogether
    (functorGrade left history) (functorGrade right history)

/-- Splitting the synchronized history grade recovers the independent
observation on every history. -/
def PreservesIndependentObservation {Event : Type uEvent}
    (left : Valuation.{uEvent, uLeft} Event)
    (right : Valuation.{uEvent, uRight} Event) : Prop :=
  ∀ history,
    split (functorGrade (left.prod right) history) =
      independentGrade left right history

theorem preservesIndependentObservation_iff_historyFailureAligned
    {Event : Type uEvent}
    (left : Valuation.{uEvent, uLeft} Event)
    (right : Valuation.{uEvent, uRight} Event) :
    PreservesIndependentObservation left right ↔
      HistoryFailureAligned left right := by
  constructor
  · intro preserves history
    have comparison := preserves history
    rw [functorGrade_prod] at comparison
    exact (split_synchronize_eq_iff_definedTogether
      (functorGrade left history) (functorGrade right history)).1
        (by simpa [independentGrade, synchronize] using comparison)
  · intro aligned history
    rw [functorGrade_prod]
    exact (split_synchronize_eq_iff_definedTogether
      (functorGrade left history) (functorGrade right history)).2
        (aligned history)

/-- Total independent valuations are necessarily failure-aligned on every
history. -/
theorem historyFailureAligned_of_total {Event : Type uEvent}
    {left : Valuation.{uEvent, uLeft} Event}
    {right : Valuation.{uEvent, uRight} Event}
    (leftTotal : left.IsTotal) (rightTotal : right.IsTotal) :
    HistoryFailureAligned left right := by
  intro history
  obtain ⟨leftGrade, leftEquation⟩ := leftTotal.historyGrade_some history
  obtain ⟨rightGrade, rightEquation⟩ := rightTotal.historyGrade_some history
  simp [DefinedTogether, functorGrade_eq_historyGrade,
    leftEquation, rightEquation]

/-- The exact conditions needed for a categorical synchronized-to-independent
comparison over the complete history functors. -/
structure ComparisonLawful {Event : Type uEvent}
    (left : Valuation.{uEvent, uLeft} Event)
    (right : Valuation.{uEvent, uRight} Event) : Prop where
  operations : OperationsFailTogether left.algebra right.algebra
  histories : HistoryFailureAligned left right

/-- Total valuations support both the global categorical comparison and the
history-image comparison. -/
theorem comparisonLawful_of_total {Event : Type uEvent}
    {left : Valuation.{uEvent, uLeft} Event}
    {right : Valuation.{uEvent, uRight} Event}
    (leftTotal : left.IsTotal) (rightTotal : right.IsTotal) :
    ComparisonLawful left right where
  operations :=
    (operationsFailTogether_iff_operationTotal
      left.algebra right.algebra).2
        ⟨leftTotal.op_some, rightTotal.op_some⟩
  histories := historyFailureAligned_of_total leftTotal rightTotal

/-- With both failure conditions, the categorical comparison has exactly the
independent map on every history arrow. -/
theorem synchronizedComparison_map
    {Event : Type uEvent}
    (left : Valuation.{uEvent, uLeft} Event)
    (right : Valuation.{uEvent, uRight} Event)
    (lawful : ComparisonLawful left right)
    (history : List Event) :
    (toHistoryFunctor (left.prod right) ⋙
        splitComparisonFunctor left.algebra right.algebra lawful.operations).map
          (X := EventHistory.object Event) (Y := EventHistory.object Event)
          history =
      (independentHistoryFunctor left right).map
        (X := EventHistory.object Event) (Y := EventHistory.object Event)
        history := by
  change split (functorGrade (left.prod right) history) =
    independentGrade left right history
  exact (preservesIndependentObservation_iff_historyFailureAligned
    left right).2 lawful.histories history

/-! ## Observer-fibre boundary -/

/-- The observer that retains each partial valuation coordinate independently. -/
def independentObserver {Event : Type uEvent}
    (left : Valuation.{uEvent, uLeft} Event)
    (right : Valuation.{uEvent, uRight} Event) :
    Observer (List Event) (Option left.Grade × Option right.Grade) where
  observe := independentGrade left right

/-- The coarser implementation observation obtained by synchronizing first and
then attempting to split the joint result. -/
def synchronizedSplitObserver {Event : Type uEvent}
    (left : Valuation.{uEvent, uLeft} Event)
    (right : Valuation.{uEvent, uRight} Event) :
    Observer (List Event) (Option left.Grade × Option right.Grade) where
  observe := fun history =>
    split (functorGrade (left.prod right) history)

/-- The synchronized observer and the independent observer have exactly the
same fibres precisely when the two valuation axes accept the same histories. -/
theorem synchronizedSplitObserver_eq_iff_historyFailureAligned
    {Event : Type uEvent}
    (left : Valuation.{uEvent, uLeft} Event)
    (right : Valuation.{uEvent, uRight} Event) :
    synchronizedSplitObserver left right = independentObserver left right ↔
      HistoryFailureAligned left right := by
  rw [← preservesIndependentObservation_iff_historyFailureAligned]
  constructor
  · intro equal history
    exact congrArg (fun observer => observer.observe history) equal
  · intro preserves
    cases left
    cases right
    simp only [synchronizedSplitObserver, independentObserver]
    congr
    funext history
    exact preserves history

/-- Under history-failure alignment, a control change preserves synchronized
observation exactly when it preserves the genuinely independent observation. -/
theorem lawfulAt_synchronized_iff_independent_of_aligned
    {Event : Type uEvent} {Receipt : Type*}
    (left : Valuation.{uEvent, uLeft} Event)
    (right : Valuation.{uEvent, uRight} Event)
    (aligned : HistoryFailureAligned left right)
    (change : Change Event Receipt) :
    LawfulAt (synchronizedSplitObserver left right) change ↔
      LawfulAt (independentObserver left right) change := by
  rw [(synchronizedSplitObserver_eq_iff_historyFailureAligned
    left right).2 aligned]

/-! ## Positive and adversarial controls -/

namespace Canary

open Mettapedia.GSLT.Dynamics.EventValuationFunctor.Canary

/-- The same partial valuation on both coordinates is aligned on every
history in the image, even though its complete delooping is not globally
comparable to the categorical product. -/
theorem alignedExclusiveHistories :
    HistoryFailureAligned exclusiveValuation exclusiveValuation := by
  intro history
  rfl

theorem aligned_partial_comparison_agrees :
    split
        (functorGrade (exclusiveValuation.prod exclusiveValuation)
          [false, true]) =
      independentGrade exclusiveValuation exclusiveValuation [false, true] :=
  (preservesIndependentObservation_iff_historyFailureAligned
    exclusiveValuation exclusiveValuation).2 alignedExclusiveHistories _

/-- Nevertheless, the partial operation cannot define the global categorical
comparison: independent target arrows may fail in only one coordinate. -/
theorem aligned_partial_has_no_global_comparison :
    ¬ OperationsFailTogether exclusive exclusive := by
  rw [operationsFailTogether_iff_operationTotal]
  rintro ⟨leftTotal, _⟩
  obtain ⟨result, impossible⟩ := leftTotal true true
  simp [exclusive] at impossible

/-- A genuinely total pair supplies the complete categorical comparison. -/
def totalComparison : ComparisonLawful
    (chronological (fun value : Bool => value)) rightHistoryValuation :=
  comparisonLawful_of_total
    (chronological_isTotal (fun value : Bool => value))
    (chronological_isTotal (fun _ : Bool => ()))

theorem total_categorical_comparison_agrees :
    (toHistoryFunctor
        ((chronological (fun value : Bool => value)).prod
          rightHistoryValuation) ⋙
      splitComparisonFunctor
        (chronological (fun value : Bool => value)).algebra
        rightHistoryValuation.algebra totalComparison.operations).map
        (X := EventHistory.object Bool) (Y := EventHistory.object Bool)
        [false, true] =
      (independentHistoryFunctor
        (chronological (fun value : Bool => value))
        rightHistoryValuation).map
        (X := EventHistory.object Bool) (Y := EventHistory.object Bool)
        [false, true] :=
  synchronizedComparison_map _ _ totalComparison _

/-- The independent right coordinate continues to observe a two-event history
after the exclusive left coordinate has rejected it. -/
theorem mismatched_history_failure :
    ¬ HistoryFailureAligned exclusiveValuation rightHistoryValuation := by
  intro aligned
  have impossible := aligned [false, true]
  simp [DefinedTogether, functorGrade_eq_historyGrade,
    exclusiveValuation, exclusive, rightHistoryValuation,
    chronological, chronologicalListPartialMonoid] at impossible

theorem synchronized_product_not_independent :
    ¬ PreservesIndependentObservation
      exclusiveValuation rightHistoryValuation := by
  rw [preservesIndependentObservation_iff_historyFailureAligned]
  exact mismatched_history_failure

/-- Extending a history after the left axis has already failed is invisible to
the synchronized observation, while the independent right axis still records
the added event. -/
def mismatchedVisibilityChange : Change Bool Unit where
  source := [false, true]
  target := [false, true, false]
  receipt := ()

theorem mismatched_change_lawful_synchronized :
    LawfulAt
      (synchronizedSplitObserver exclusiveValuation rightHistoryValuation)
      mismatchedVisibilityChange := by
  rfl

theorem mismatched_change_not_lawful_independent :
    ¬ LawfulAt
      (independentObserver exclusiveValuation rightHistoryValuation)
      mismatchedVisibilityChange := by
  intro equal
  have impossible := congrArg (fun grades => grades.2.map List.length) equal
  simp [mismatchedVisibilityChange, independentObserver,
    independentGrade, functorGrade_eq_historyGrade,
    rightHistoryValuation, chronological, chronologicalListPartialMonoid] at impossible

/-- Splitting joint failure is not composition-preserving when one operation
rejects and the other succeeds. -/
theorem split_not_composition_preserving :
    ¬ OperationsFailTogether exclusive
      (chronologicalListPartialMonoid Unit) := by
  intro aligned
  have impossible := aligned true true [()] [()]
  simp [exclusive, chronologicalListPartialMonoid] at impossible

end Canary

/-! ## Axiom audit -/

#print axioms operationsFailTogether_iff_split_preserves_comp
#print axioms operationsFailTogether_iff_operationTotal
#print axioms splitComparisonFunctor
#print axioms preservesIndependentObservation_iff_historyFailureAligned
#print axioms synchronizedComparison_map
#print axioms synchronizedSplitObserver_eq_iff_historyFailureAligned
#print axioms lawfulAt_synchronized_iff_independent_of_aligned
#print axioms Canary.aligned_partial_comparison_agrees
#print axioms Canary.aligned_partial_has_no_global_comparison
#print axioms Canary.total_categorical_comparison_agrees
#print axioms Canary.synchronized_product_not_independent
#print axioms Canary.mismatched_change_lawful_synchronized
#print axioms Canary.mismatched_change_not_lawful_independent
#print axioms Canary.split_not_composition_preserving

end Mettapedia.GSLT.Dynamics.IndependentEventValuationProduct
