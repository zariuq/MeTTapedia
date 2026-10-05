import Mettapedia.GSLT.Distinction.HistoryCoverageControls
import Mettapedia.GSLT.Logic.ContextualObservedCoalgebra
import Mettapedia.GSLT.Logic.DiscreteReadingCodings

/-!
# History execution with declared result, fault and cost material rows

The authored task/done/failed grammar has an actual contextual material
readout containing all three exact integer readings, in addition to its
context actions and event-labelled execution children. Even the unlabelled
event profile retains different results and faults through these rows.

The exact kernel is a stable future bisimulation preserving all declared
readings. It is finer than the earlier future-only readout. Present reading
agreement alone does not replace stability. The clamped cost is precisely
the declared program reading; extensive pending-work accounts remain a
different observation and are not silently substituted for it.

This concrete instance inherits the history library's external host Choice
dependency through multiset firing and readings. Its authored integer label
dictionaries and the generic observed-material construction use no Choice.
No predecessor-modal or occurrence inverse follows from the forward value.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction.HistoryObservedMaterialReadings

open _root_.CategoryTheory
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open ContextualCoalgebraLabelledGraph
open HistoryObserver HistoryContextualReadout HistoryCoverageControls
open Mettapedia.GSLT.ContextualObservedCoalgebra

def readingIndex : Reading → Nat
  | .result => 0
  | .fault => 1
  | .cost => 2

theorem readingIndex_injective : Function.Injective readingIndex := by
  intro first second same
  cases first <;> cases second <;> simp only [readingIndex] at same <;> first | rfl | omega

def readingCoding : ArgumentCoding Reading where
  graph field := OutcomeLabels.chainGraph (readingIndex field)
  injective := by
    intro first second same
    change HSet.mk (OutcomeLabels.chainGraph (readingIndex first)) =
      HSet.mk (OutcomeLabels.chainGraph (readingIndex second)) at same
    rw [OutcomeLabels.mk_chainGraph, OutcomeLabels.mk_chainGraph] at same
    exact readingIndex_injective (OutcomeLabels.chainValue_injective same)

abbrev Atom := Reading × Int
abbrev atomCoding := Mettapedia.GSLT.DiscreteReadingCodings.namedIntegers readingCoding

def observes (atom : Atom) (state : State (states Node)) : Prop :=
  atom.2 = reading scale readings atom.1 state.2.live

abbrev observedValue (code : Mettapedia.Cybernetics.DistinctionCalculus.History.Event Node → Nat) :=
  Mettapedia.GSLT.ContextualObservedCoalgebra.value (coalgebra grammar code) observes
    LabelledContextPaths.worlds LabelledContextPaths.arrows atomCoding

theorem exact_reading_row (code : Mettapedia.Cybernetics.DistinctionCalculus.History.Event Node → Nat)
    (state : State (states Node)) (field : Reading) (number : Int) :
    HSet.kpair ((Mettapedia.GSLT.ContextualObservedCoalgebra.readings (coalgebra grammar code) observes
        LabelledContextPaths.worlds LabelledContextPaths.arrows atomCoding).taggedReading (.inl (field, number))) ∅ ∈
      observedValue code state ↔ number = reading scale readings field state.2.live :=
  observation_row_iff (coalgebra grammar code) observes LabelledContextPaths.worlds LabelledContextPaths.arrows
    atomCoding state (field, number)

theorem observed_kernel (code : Mettapedia.Cybernetics.DistinctionCalculus.History.Event Node → Nat) (point : LabelledContextPaths.World)
    (left right : Placed Node point) :
    observedValue code ⟨point, left⟩ = observedValue code ⟨point, right⟩ ↔
      ObservedBisimilar (coalgebra grammar code) observes point left right :=
  value_eq_iff (coalgebra grammar code) observes LabelledContextPaths.worlds LabelledContextPaths.arrows atomCoding
    point left right

theorem observed_equality_preserves_reading (code : Mettapedia.Cybernetics.DistinctionCalculus.History.Event Node → Nat)
    (point : LabelledContextPaths.World) (left right : Placed Node point)
    (same : observedValue code ⟨point, left⟩ = observedValue code ⟨point, right⟩) (field : Reading) :
    reading scale readings field left.live = reading scale readings field right.live :=
  (observed_bisimilar_atoms (coalgebra grammar code) observes ((observed_kernel code point left right).mp same)
    (field, reading scale readings field left.live)).mp rfl

theorem observed_equality_forgets_to_future_readout (code : Mettapedia.Cybernetics.DistinctionCalculus.History.Event Node → Nat)
    (point : LabelledContextPaths.World) (left right : Placed Node point)
    (same : observedValue code ⟨point, left⟩ = observedValue code ⟨point, right⟩) :
    (readout grammar code).app point left = (readout grammar code).app point right :=
  (readout_eq_iff grammar code point left right).mpr
    (observed_bisimilar_forgets_atoms (coalgebra grammar code) observes ((observed_kernel code point left right).mp same))

theorem declared_formula_materializes (code : Mettapedia.Cybernetics.DistinctionCalculus.History.Event Node → Nat)
    (formula : HennessyMilner.Formula Atom (Label LabelledContextPaths.World)) (state : State (states Node)) :
    (Mettapedia.GSLT.ContextualObservedCoalgebra.readings (coalgebra grammar code) observes
        LabelledContextPaths.worlds LabelledContextPaths.arrows atomCoding).materialSat formula (observedValue code state) ↔
      (system (coalgebra grammar code) observes).sat formula state :=
  material_formula_iff (coalgebra grammar code) observes LabelledContextPaths.worlds LabelledContextPaths.arrows
    atomCoding formula state

theorem result_done : reading scale readings .result (.done ::ₘ 0) = 1 := by
  rw [reading, best_cons, best_zero]
  decide

theorem result_failed : reading scale readings .result (.failed ::ₘ 0) = 0 := by
  rw [reading, best_cons, best_zero]
  decide

theorem fault_done : reading scale readings .fault (.done ::ₘ 0) = 0 := by
  rw [reading, best_cons, best_zero]
  decide

theorem fault_failed : reading scale readings .fault (.failed ::ₘ 0) = 1 := by
  rw [reading, best_cons, best_zero]
  decide

theorem cost_task : reading scale readings .cost (.task ::ₘ 0) = 1 := by
  simp only [reading, potentialSum, Multiset.map_cons, Multiset.map_zero,
    Multiset.sum_cons, Multiset.sum_zero, HistoryCoverageControls.readings, add_zero]
  exact scale.clamp_of_mem (by decide) (by decide)

theorem cost_done : reading scale readings .cost (.done ::ₘ 0) = 0 := by
  simp only [reading, potentialSum, Multiset.map_cons, Multiset.map_zero,
    Multiset.sum_cons, Multiset.sum_zero, HistoryCoverageControls.readings, add_zero]
  exact scale.clamp_of_mem (by decide) (by decide)

theorem done_and_failed_observed_distinct (code : Mettapedia.Cybernetics.DistinctionCalculus.History.Event Node → Nat) (point : LabelledContextPaths.World) :
    observedValue code ⟨point, fresh point (.done ::ₘ 0)⟩ ≠
      observedValue code ⟨point, fresh point (.failed ::ₘ 0)⟩ := by
  intro same
  have readingsEqual := observed_equality_preserves_reading code point _ _ same .result
  change reading scale readings .result (.done ::ₘ 0) = reading scale readings .result (.failed ::ₘ 0) at readingsEqual
  rw [result_done, result_failed] at readingsEqual
  exact Int.one_ne_zero readingsEqual

theorem task_and_done_cost_distinct (code : Mettapedia.Cybernetics.DistinctionCalculus.History.Event Node → Nat) (point : LabelledContextPaths.World) :
    observedValue code ⟨point, fresh point (.task ::ₘ 0)⟩ ≠
      observedValue code ⟨point, fresh point (.done ::ₘ 0)⟩ := by
  intro same
  have readingsEqual := observed_equality_preserves_reading code point _ _ same .cost
  change reading scale readings .cost (.task ::ₘ 0) = reading scale readings .cost (.done ::ₘ 0) at readingsEqual
  rw [cost_task, cost_done] at readingsEqual
  exact Int.one_ne_zero readingsEqual

theorem unlabelled_future_equality_loses_declared_readings (point : LabelledContextPaths.World) :
    HistoryContextualReadout.material grammar unlabelled ⟨point, fresh point (.done ::ₘ 0)⟩ =
        HistoryContextualReadout.material grammar unlabelled ⟨point, fresh point (.failed ::ₘ 0)⟩ ∧
      observedValue unlabelled ⟨point, fresh point (.done ::ₘ 0)⟩ ≠
        observedValue unlabelled ⟨point, fresh point (.failed ::ₘ 0)⟩ :=
  ⟨instance_unlabelled_same point, done_and_failed_observed_distinct unlabelled point⟩

theorem reading_row_is_not_execution_child (code : Mettapedia.Cybernetics.DistinctionCalculus.History.Event Node → Nat) (point : LabelledContextPaths.World) :
    HSet.kpair ((Mettapedia.GSLT.ContextualObservedCoalgebra.readings (coalgebra grammar code) observes
        LabelledContextPaths.worlds LabelledContextPaths.arrows atomCoding).taggedReading (.inl (.result, 1))) ∅ ∈
      observedValue code ⟨point, fresh point (.done ::ₘ 0)⟩ :=
  (exact_reading_row code ⟨point, fresh point (.done ::ₘ 0)⟩ .result 1).mpr result_done.symm

theorem complete_pending_run_cost_reflected :
    (HistoryIndependence.costValuation grammar pendingCost).onPath completeRun =
      reading scale readings .cost (.done ::ₘ 0) - reading scale readings .cost (.task ::ₘ 0) :=
  instance_pending_reflected.2.2

end Mettapedia.GSLT.Distinction.HistoryObservedMaterialReadings
