import Mettapedia.GSLT.Logic.ContextualObservedCoalgebra
import Mettapedia.TypeTheory.MaterialSets.Hypersets.IndexedCoalgebraQuotientControls

/-!
# Declared readings on infinite growing contextual executions

Results, faults and unbounded natural-number costs are actual atomic rows
of the readout. The source has genuinely growing occurrences at every
stage. Different readings are retained even when execution child sets are
empty; different unobserved receipt tags still have one observed value.

A second observer agrees on all present readings of two source states
but distinguishes them after context transport. Its full observed values
are different already at the initial context. Thus present reading
agreement intersected with ordinary bisimilarity is not sufficient.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ContextualObservedCoalgebraControls

open _root_.CategoryTheory
open Mettapedia.TypeTheory.ContextualWitnessCover
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open CoveredFuturePowerFunctor
open PowerClassPresheafDescent.Controls

def worlds : ArgumentCoding Stagesᵒᵖ where
  graph point := OutcomeLabels.chainGraph (stageIndex point)
  injective := by
    intro first second same
    change HSet.mk (OutcomeLabels.chainGraph (stageIndex first)) =
      HSet.mk (OutcomeLabels.chainGraph (stageIndex second)) at same
    rw [OutcomeLabels.mk_chainGraph, OutcomeLabels.mk_chainGraph] at same
    exact congrArg world (OutcomeLabels.chainValue_injective same)

def arrows (first second : Stagesᵒᵖ) : ArgumentCoding (first ⟶ second) where
  graph _ := AccessiblePointedGraph.empty
  injective _ _ _ := Subsingleton.elim _ _

def naturalAtoms : ArgumentCoding Nat where
  graph := OutcomeLabels.chainGraph
  injective := by
    intro first second same
    change HSet.mk (OutcomeLabels.chainGraph first) = HSet.mk (OutcomeLabels.chainGraph second) at same
    rw [OutcomeLabels.mk_chainGraph, OutcomeLabels.mk_chainGraph] at same
    exact OutcomeLabels.chainValue_injective same

abbrev Readings := Nat × Bool × Nat

def parameters : Stagesᵒᵖ ⥤ Type where
  obj _ := Readings
  map _ := TypeCat.ofHom id
  map_id _ := rfl
  map_comp _ _ := rfl

abbrev source := CoveredFuturePowerClassifier.product parameters growingSource

def emptyCoalgebra (A : Stagesᵒᵖ ⥤ Type) : NaturalHom A (CoveredFuturePowerFamilies.family A) where
  app _ _ := CoveredFuturePowerFamilies.ofFull {
    holds := fun _ => False
    closed := fun _ impossible => impossible.elim }
  naturality _ _ := rfl

abbrev Atom := Fin 3 × Nat

def atomCoding : ArgumentCoding Atom where
  graph atom := AccessiblePointedGraph.kpairGraph (OutcomeLabels.chainGraph atom.1.val)
    (OutcomeLabels.chainGraph atom.2)
  injective := by
    intro first second same
    change HSet.mk (AccessiblePointedGraph.kpairGraph (OutcomeLabels.chainGraph first.1.val)
      (OutcomeLabels.chainGraph first.2)) =
      HSet.mk (AccessiblePointedGraph.kpairGraph (OutcomeLabels.chainGraph second.1.val)
        (OutcomeLabels.chainGraph second.2)) at same
    simp only [AccessiblePointedGraph.mk_kpairGraph, OutcomeLabels.mk_chainGraph] at same
    have fields := HSet.kpair_inj.mp same
    exact Prod.ext (Fin.ext (OutcomeLabels.chainValue_injective fields.1))
      (OutcomeLabels.chainValue_injective fields.2)

def read (field : Fin 3) (values : Readings) : Nat :=
  if field.val = 0 then values.1 else if field.val = 1 then if values.2.1 then 1 else 0 else values.2.2

def observes (atom : Atom) (state : ContextualCoalgebraLabelledGraph.State source) : Prop :=
  atom.2 = read atom.1 state.2.1

abbrev value := ContextualObservedCoalgebra.value (emptyCoalgebra source) observes worlds arrows atomCoding

def state (stage result cost : Nat) (fault receipt : Bool) : source.obj (world stage) :=
  ((result, fault, cost), stageValue stage 0 (Nat.zero_lt_succ stage) receipt)

theorem same_values_observed (point : Stagesᵒᵖ) (left right : source.obj point) (same : left.1 = right.1) :
    ContextualObservedCoalgebra.ObservedBisimilar (emptyCoalgebra source) observes point left right := by
  refine ⟨fun _ first second => first.1 = second.1, {
    underlying := {
      stable := fun {_ _} _ {_ _} same => same
      forth := fun {_ _ _} _ _ {_} impossible => impossible.elim
      back := fun {_ _ _} _ _ {_} impossible => impossible.elim }
    atoms := ?_ }, same⟩
  intro point first second same atom
  change atom.2 = read atom.1 first.1 ↔ atom.2 = read atom.1 second.1
  rw [same]

theorem no_execution_children (point : Stagesᵒᵖ) (argument : source.obj point)
    (future : PowerClassPresheafBaseChange.Future.Objects point) (child : source.obj future.1) :
    ¬ ((emptyCoalgebra source).app point argument).val.holds ⟨future, child⟩ := fun impossible => impossible.elim

theorem reading_row (point : Stagesᵒᵖ) (argument : source.obj point) (field : Fin 3) (reading : Nat) :
    HSet.kpair ((ContextualObservedCoalgebra.readings (emptyCoalgebra source) observes worlds arrows atomCoding).taggedReading
      (.inl (field, reading))) ∅ ∈ value ⟨point, argument⟩ ↔ reading = read field argument.1 :=
  ContextualObservedCoalgebra.observation_row_iff (emptyCoalgebra source) observes worlds arrows atomCoding _ _

theorem equality_preserves_reading (point : Stagesᵒᵖ) (left right : source.obj point)
    (same : value ⟨point, left⟩ = value ⟨point, right⟩) (field : Fin 3) : read field left.1 = read field right.1 :=
  (ContextualObservedCoalgebra.observed_bisimilar_atoms (emptyCoalgebra source) observes
    ((ContextualObservedCoalgebra.value_eq_iff (emptyCoalgebra source) observes worlds arrows atomCoding point left right).mp same)
      (field, read field left.1)).mp rfl

theorem infinitely_many_result_readings (cost : Nat) (fault receipt : Bool) :
    Function.Injective (fun result => value ⟨world 0, state 0 result cost fault receipt⟩) := by
  intro first second same
  exact equality_preserves_reading (world 0) _ _ same ⟨0, by decide⟩

theorem infinitely_many_cost_readings (result : Nat) (fault receipt : Bool) :
    Function.Injective (fun cost => value ⟨world 0, state 0 result cost fault receipt⟩) := by
  intro first second same
  exact equality_preserves_reading (world 0) _ _ same ⟨2, by decide⟩

theorem fault_readings_differ (result cost : Nat) (receipt : Bool) :
    value ⟨world 0, state 0 result cost true receipt⟩ ≠ value ⟨world 0, state 0 result cost false receipt⟩ := by
  intro same
  exact Nat.one_ne_zero (equality_preserves_reading (world 0) _ _ same ⟨1, by decide⟩)

theorem omitted_children_lose_every_result (left right : source.obj (world 0)) :
    ContextualCoalgebraBisimulation.Bisimilar (emptyCoalgebra source) (world 0) left right := by
  apply ContextualCoalgebraBisimulation.greatest (emptyCoalgebra source) (relation := fun _ _ _ => True)
  · exact {
      stable := fun {_ _} _ {_ _} _ => trivial
      forth := fun {_ _ _} _ _ {_} impossible => impossible.elim
      back := fun {_ _ _} _ _ {_} impossible => impossible.elim }
  · trivial

theorem unobserved_receipt_aliases (stage result cost : Nat) (fault : Bool) :
    state stage result cost fault true ≠ state stage result cost fault false ∧
      value ⟨world stage, state stage result cost fault true⟩ =
        value ⟨world stage, state stage result cost fault false⟩ := by
  constructor
  · intro same
    exact Bool.noConfusion (congrArg (fun argument : source.obj (world stage) => argument.2.2) same)
  · exact (ContextualObservedCoalgebra.value_eq_iff (emptyCoalgebra source) observes worlds arrows atomCoding
      (world stage) _ _).mpr (same_values_observed _ _ _ rfl)

def newlyAvailable (stage result cost : Nat) (fault : Bool) : source.obj (world (stage + 1)) :=
  ((result, fault, cost), stageValue (stage + 1) (stage + 1) (Nat.lt_succ_self (stage + 1)) false)

theorem new_occurrence_every_stage (stage result cost : Nat) (fault : Bool) :
    ¬ ∃ earlier : source.obj (world stage),
      source.map (IndexedCoalgebraQuotientControls.advance stage) earlier = newlyAvailable stage result cost fault := by
  rintro ⟨earlier, same⟩
  have positions := congrArg (fun value : source.obj (world (stage + 1)) => value.2.1.val) same
  change earlier.2.1.val = stage + 1 at positions
  have bound := earlier.2.1.isLt
  change earlier.2.1.val < stage + 1 at bound
  rw [positions] at bound
  exact Nat.lt_irrefl _ bound

namespace Late

def result (state : ContextualCoalgebraLabelledGraph.State growingSource) : Nat :=
  if stageIndex state.1 = 0 then 0 else if state.2.2 then 1 else 0

def observes (atom : Nat) (state : ContextualCoalgebraLabelledGraph.State growingSource) : Prop := atom = result state

abbrev value := ContextualObservedCoalgebra.value (emptyCoalgebra growingSource) observes worlds arrows naturalAtoms

def initial (tag : Bool) : growingSource.obj (world 0) := stageValue 0 0 (Nat.zero_lt_one) tag

theorem same_present_atoms (atom : Nat) : observes atom ⟨world 0, initial true⟩ ↔ observes atom ⟨world 0, initial false⟩ :=
  Iff.rfl

theorem ordinary_bisimilar :
    ContextualCoalgebraBisimulation.Bisimilar (emptyCoalgebra growingSource) (world 0) (initial true) (initial false) := by
  apply ContextualCoalgebraBisimulation.greatest (emptyCoalgebra growingSource) (relation := fun _ _ _ => True)
  · exact {
      stable := fun {_ _} _ {_ _} _ => trivial
      forth := fun {_ _ _} _ _ {_} impossible => impossible.elim
      back := fun {_ _ _} _ _ {_} impossible => impossible.elim }
  · trivial

theorem complete_observed_values_differ : value ⟨world 0, initial true⟩ ≠ value ⟨world 0, initial false⟩ := by
  intro same
  obtain ⟨relation, bisimulation, related⟩ :=
    (ContextualObservedCoalgebra.value_eq_iff (emptyCoalgebra growingSource) observes worlds arrows naturalAtoms
      (world 0) (initial true) (initial false)).mp same
  have future := bisimulation.underlying.stable (IndexedCoalgebraQuotientControls.advance 0) related
  have atoms := bisimulation.atoms future 1
  have admitted : observes 1 ⟨world 1, growingSource.map (IndexedCoalgebraQuotientControls.advance 0) (initial true)⟩ := rfl
  have impossible := atoms.mp admitted
  exact Nat.one_ne_zero impossible

end Late

end Mettapedia.GSLT.ContextualObservedCoalgebraControls
