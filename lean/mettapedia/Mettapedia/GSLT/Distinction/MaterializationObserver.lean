import Mettapedia.GSLT.Logic.ObservedMaterialization
import Mettapedia.GSLT.Distinction.BehaviouralMetric
import Mettapedia.GSLT.Distinction.SpanTransportControls

/-!
# The material readout as an observer of the shared contract

`ObservedMaterialization` reads an observed labelled system into material
hypersets; with faithful readings its equality kernel is the system's
bisimilarity (`LabelReadings.value_eq_iff_bisimilar`).  The behavioural metric
reads the same system with indicator atoms and a discount; under finitely many
successor classes and a positive discount its zero kernel is that bisimilarity
(`GradedSystem.logicalDistance_ofSystem_eq_zero_iff`).  This module states the
comparison with every hypothesis explicit, extends it to the two-sided
observation, and gives the readout's event span as a span relation.

* **One kernel** (`value_eq_iff_logicalDistance_eq_zero`): faithful readings,
  the indicator vocabulary of the system's own atoms (`GradedSystem.ofSystem`),
  a discount in `(0, 1]` and finitely many successor classes.  Equal material
  values are at distance zero for every discount and without finiteness
  (`logicalDistance_eq_zero_of_value_eq`).
* **The discount hypothesis is needed** (`discount_zero_control`): with discount
  `0` a terminating state and a cycling state reporting the same outcome are at
  distance zero, while their material values differ.  With a positive discount
  the two phases of a cycle are at distance zero and termination is not
  (`positive_discount_kernel`).
* **The two-sided readout** (`twoSidedReadings`): actions read forward and
  backward under two material tags.  Its kernel is two-sided bisimilarity
  (`twoSided_value_eq_iff_bisimilar`), and its graded zero kernel needs both
  successor and predecessor finiteness
  (`twoSided_value_eq_iff_logicalDistance_eq_zero`).  The future-equal,
  past-different terminals have equal forward values and different two-sided
  values (`forward_values_eq`, `twoSided_values_ne`).
* **The readout's event span** (`occurrences_sourceBack`, `occurrences_keeps`):
  the authored action occurrences map to the material span with the source back
  law, keeping labels; the target back law is a separate premise.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction.MaterializationObserver

open Mettapedia.GSLT
open Mettapedia.GSLT.HennessyMilner
open Mettapedia.GSLT.ObservedMaterialization
open Mettapedia.GSLT.Distinction.SpanTransport
open Mettapedia.TypeTheory.MaterialSets.Hypersets

universe u

variable {S : GSLT.{u}} {M : System.{u, u} S}

/-- **The material kernel is the graded zero kernel**, for the indicator
vocabulary of the system's atoms, a discount in `(0, 1]` and finitely many
successor classes. -/
theorem value_eq_iff_logicalDistance_eq_zero (readings : LabelReadings M)
    (faithful : readings.Faithful) (finite : M.ImageFiniteModulo) {discount : ℝ}
    (nonneg : 0 ≤ discount) (le_one : discount ≤ 1) (positive : 0 < discount) (left right : S.Term) :
    readings.value left = readings.value right ↔
      (GradedSystem.ofSystem M discount nonneg le_one).logicalDistance left right = 0 := by
  rw [readings.value_eq_iff_bisimilar faithful,
    GradedSystem.logicalDistance_ofSystem_eq_zero_iff M nonneg le_one finite positive]

/-- Equal material values are at graded distance zero, for every discount and
without finiteness. -/
theorem logicalDistance_eq_zero_of_value_eq (readings : LabelReadings M)
    (faithful : readings.Faithful) {discount : ℝ} (nonneg : 0 ≤ discount) (le_one : discount ≤ 1)
    {left right : S.Term} (equal : readings.value left = readings.value right) :
    (GradedSystem.ofSystem M discount nonneg le_one).logicalDistance left right = 0 :=
  GradedSystem.logicalDistance_eq_zero_of_gradedBisimilar _
    ((GradedSystem.gradedBisimilar_ofSystem_iff M nonneg le_one left right).mpr
      ((readings.value_eq_iff_bisimilar faithful left right).mp equal))

/-- With discount `0`, terms whose graded atoms agree have equal formula values. -/
theorem eval_eq_of_discount_zero {T : GSLT.{u}} (Q : GradedSystem.{u, u, u, u} T)
    (zero : Q.discount = 0) {left right : T.Term}
    (atoms : ∀ atom, Q.observations.value atom left = Q.observations.value atom right) :
    ∀ formula, Q.eval formula left = Q.eval formula right
  | .top => rfl
  | .atom atom => atoms atom
  | .neg inner => by
      simp only [GradedSystem.eval_neg, eval_eq_of_discount_zero Q zero atoms inner]
  | .conj first second => by
      simp only [GradedSystem.eval_conj, eval_eq_of_discount_zero Q zero atoms first,
        eval_eq_of_discount_zero Q zero atoms second]
  | .shift threshold inner => by
      simp only [GradedSystem.eval_shift, eval_eq_of_discount_zero Q zero atoms inner]
  | .dia label inner => by
      simp only [GradedSystem.eval_dia, zero, zero_mul]

/-! ## The discount hypothesis is needed -/

namespace DiscountControl

open Mettapedia.GSLT.ObservedMaterialization.Controls

/-- **With discount `0`, termination and cycling are at distance zero**, while the
material values separate them. -/
theorem discount_zero_control (result : OutcomeLabels.Outcome.{0}) (phase : Bool) :
    (GradedSystem.ofSystem system.{0} 0 le_rfl zero_le_one).logicalDistance
        (State.terminal result) (State.cycle result phase) = 0 ∧
      readings.{0}.value (State.terminal result) ≠ readings.value (State.cycle result phase) := by
  refine ⟨le_antisymm ?_ (GradedSystem.logicalDistance_nonneg _ _ _), terminal_ne_cycle result phase⟩
  refine (GradedSystem.logicalDistance_le_iff _).mpr fun formula => ?_
  have same := eval_eq_of_discount_zero (GradedSystem.ofSystem system.{0} 0 le_rfl zero_le_one) rfl
    (left := State.terminal result) (right := State.cycle result phase) (fun _ => rfl) formula
  exact abs_nonpos_iff.mpr (sub_eq_zero.mpr same)

/-- **Positive**: the two phases of one cycle are at distance zero for every
positive discount; termination and cycling are not. -/
theorem positive_discount_kernel (result : OutcomeLabels.Outcome.{0}) (phase : Bool) {discount : ℝ}
    (nonneg : 0 ≤ discount) (le_one : discount ≤ 1) (positive : 0 < discount) :
    (GradedSystem.ofSystem system.{0} discount nonneg le_one).logicalDistance
        (State.cycle result phase) (State.cycle result (!phase)) = 0 ∧
      (GradedSystem.ofSystem system.{0} discount nonneg le_one).logicalDistance
        (State.terminal result) (State.cycle result phase) ≠ 0 :=
  ⟨(value_eq_iff_logicalDistance_eq_zero readings faithful imageFiniteModulo nonneg le_one positive
      _ _).mp (cycle_values_eq result phase (!phase)),
    fun zero => terminal_ne_cycle result phase
      ((value_eq_iff_logicalDistance_eq_zero readings faithful imageFiniteModulo nonneg le_one
        positive _ _).mpr zero)⟩

end DiscountControl

/-! ## The two-sided readout -/

/-- The tag of a backward action. -/
def backwardTag : HSet.{u} := HSet.kpair ∅ ∅

theorem backwardTag_ne_empty : backwardTag.{u} ≠ ∅ := by
  intro equal
  have member : ({∅} : HSet.{u}) ∈ backwardTag := HSet.mem_kpair.mpr (Or.inl rfl)
  rw [equal] at member
  exact HSet.notMem_empty _ member

/-- **The two-sided readout**: forward actions under the tag `∅`, backward ones
under the tag `⟨∅, ∅⟩`, each with the action's own reading. -/
def twoSidedReadings (readings : LabelReadings M) : LabelReadings (twoSided M) where
  atom := readings.atom
  action
    | .inl label => HSet.kpair ∅ (readings.action label)
    | .inr label => HSet.kpair backwardTag (readings.action label)
  atomPresentation := readings.atomPresentation
  actionPresentation :=
    ⟨fun
      | .inl label => kuratowskiGraph AccessiblePointedGraph.empty
          (readings.actionPresentation.graph label)
      | .inr label => kuratowskiGraph
          (kuratowskiGraph AccessiblePointedGraph.empty AccessiblePointedGraph.empty)
          (readings.actionPresentation.graph label),
      fun label => by
        cases label with
        | inl label =>
            change HSet.mk (kuratowskiGraph _ _) = _
            rw [mk_kuratowskiGraph, HSet.mk_empty, readings.actionPresentation.mk_graph]
        | inr label =>
            change HSet.mk (kuratowskiGraph _ _) = _
            rw [mk_kuratowskiGraph, mk_kuratowskiGraph, HSet.mk_empty,
              readings.actionPresentation.mk_graph]
            rfl⟩

theorem twoSidedReadings_faithful (readings : LabelReadings M) (faithful : readings.Faithful) :
    (twoSidedReadings readings).Faithful := by
  refine ⟨faithful.1, ?_⟩
  intro first second equal
  cases first with
  | inl first =>
      cases second with
      | inl second =>
          exact congrArg Sum.inl (faithful.2 (HSet.kpair_inj.mp equal).2)
      | inr second =>
          exact (backwardTag_ne_empty (HSet.kpair_inj.mp equal).1.symm).elim
  | inr first =>
      cases second with
      | inl second =>
          exact (backwardTag_ne_empty (HSet.kpair_inj.mp equal).1).elim
      | inr second =>
          exact congrArg Sum.inr (faithful.2 (HSet.kpair_inj.mp equal).2)

/-- **The two-sided material kernel is two-sided bisimilarity.** -/
theorem twoSided_value_eq_iff_bisimilar (readings : LabelReadings M) (faithful : readings.Faithful)
    (left right : S.Term) :
    (twoSidedReadings readings).value left = (twoSidedReadings readings).value right ↔
      (twoSided M).Bisimilar left right :=
  (twoSidedReadings readings).value_eq_iff_bisimilar (twoSidedReadings_faithful readings faithful)
    left right

/-- **The two-sided graded zero kernel needs both branching requirements.** -/
theorem twoSided_value_eq_iff_logicalDistance_eq_zero (readings : LabelReadings M)
    (faithful : readings.Faithful) (successors : M.ImageFiniteModulo)
    (predecessors : PredecessorFiniteModulo M) {discount : ℝ} (nonneg : 0 ≤ discount)
    (le_one : discount ≤ 1) (positive : 0 < discount) (left right : S.Term) :
    (twoSidedReadings readings).value left = (twoSidedReadings readings).value right ↔
      (GradedSystem.ofSystem (twoSided M) discount nonneg le_one).logicalDistance left right = 0 :=
  value_eq_iff_logicalDistance_eq_zero (twoSidedReadings readings)
    (twoSidedReadings_faithful readings faithful)
    ((twoSided_imageFiniteModulo_iff M).mpr ⟨successors, predecessors⟩) nonneg le_one positive
    left right

/-! ## The future-equal, past-different terminals -/

namespace PastControl

open Mettapedia.GSLT.ObservationSpans.Controls.DifferentPasts
open Mettapedia.GSLT.Distinction.SpanTransport.Controls.Passed

/-- Readings of the forward system: no atoms, and one action read as `∅`. -/
def forwardReadings : LabelReadings forward where
  atom atom := atom.elim
  action _ := ∅
  atomPresentation := ⟨fun atom => atom.elim, fun atom => atom.elim⟩
  actionPresentation := ⟨fun _ => AccessiblePointedGraph.empty, fun _ => HSet.mk_empty⟩

theorem forwardReadings_faithful : forwardReadings.Faithful :=
  ⟨fun atom => atom.elim, fun _ _ _ => rfl⟩

/-- **The forward readout identifies the two terminals** ... -/
theorem forward_values_eq :
    forwardReadings.value State.entered = forwardReadings.value State.isolated :=
  forwardReadings.value_eq_of_bisimilar forward_bisimilar

/-- **... and the two-sided readout separates them.** -/
theorem twoSided_values_ne :
    (twoSidedReadings forwardReadings).value State.entered ≠
      (twoSidedReadings forwardReadings).value State.isolated :=
  fun equal => not_twoSided_bisimilar
    ((twoSided_value_eq_iff_bisimilar forwardReadings forwardReadings_faithful _ _).mp equal)

end PastControl

/-! ## The readout's event span -/

section Occurrences

open Mettapedia.GSLT.ObservationSpans

/-- **The authored occurrences map to the material span with the source back
law.** -/
theorem occurrences_sourceBack (occurrences : ActionOccurrences M) (readings : LabelReadings M)
    (faithful : readings.Faithful) :
    SourceBack occurrences.sourceSpan (occurrences.materialSpan readings)
      (graph (occurrences.observation readings)) :=
  (spanMap_sourceBack_iff _).mpr (occurrences.sourceLifts readings faithful)

/-- The occurrence relation of the readout keeps the action label of every
event. -/
theorem occurrences_keeps (occurrences : ActionOccurrences M) (readings : LabelReadings M) :
    (SpanRelation.ofSpanMap (occurrences.observation readings)).Keeps
      ActionOccurrences.Event.label ActionOccurrences.Event.label := by
  rintro event _ rfl
  rfl

/-- The target back law, supplied, gives the material past box. -/
theorem occurrences_box (occurrences : ActionOccurrences M) (readings : LabelReadings M)
    (incoming : TargetBack occurrences.sourceSpan (occurrences.materialSpan readings)
      (graph (occurrences.observation readings)))
    (predicate : HSet.{u} → Prop) (state : S.Term) :
    Mettapedia.OSLF.Framework.DerivedModalities.derivedBox (occurrences.materialSpan readings)
        predicate (readings.value state) ↔
      Mettapedia.OSLF.Framework.DerivedModalities.derivedBox occurrences.sourceSpan
        (predicate ∘ readings.value) state :=
  spanMap_box (occurrences.observation readings) ((spanMap_targetBack_iff _).mp incoming)
    predicate state

end Occurrences

end Mettapedia.GSLT.Distinction.MaterializationObserver
