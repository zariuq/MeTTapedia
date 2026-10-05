import Mettapedia.GSLT.Logic.ObservedGradedFamilyDescent
import Mettapedia.GSLT.Logic.ObservedMaterialization

/-!
# Actual reduction occurrences with decreasing observation depth

An event goes from depth n+1 to depth n. Its state readout uses the exact
finite-depth observation classes, while its edge readout retains the entire
authored occurrence. Positive discount derives outgoing endpoint lifting
from the constructed finite approximants. The matching occurrence retains
the label but need not be the same event witness.

The resulting span has exact successor-modal preservation for arbitrary
predicates on the observed depth states. Predecessor box still requires
its separate target-lifting law; occurrence-sensitive consumers require the
stronger occurrence laws. None is inferred from finite future agreement.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ObservedDepthBudgetSpan

open Mettapedia.GSLT.Distinction.Constructive
open Mettapedia.TypeTheory.MaterialSets.Hypersets.PowerClassFamilyDescent
open ObservedMaterialization ObservationSpans
open Mettapedia.OSLF.Framework.DerivedModalities

universe u v
variable {V : Type v} [AddCommGroup V] [LinearOrder V] [IsOrderedAddMonoid V]
variable {S : GSLT.{u}} {K : Scale V}
variable (system : PresentedSystem.{u, u, u, u} S K)
variable (vocabulary : system.Vocabulary)
variable (occurrences : ActionOccurrences system.dynamics)

abbrev RawState := Nat × S.Term
abbrev ObservedState := Σ depth : Nat, ObservationClass (ObservedGradedFamilyDescent.readout system depth)

structure Event where
  depth : Nat
  occurrence : ActionOccurrences.Event occurrences

def rawSpan : ReductionSpan (RawState (S := S)) where
  Edge := Event system occurrences
  source event := ⟨event.depth + 1, event.occurrence.source⟩
  target event := ⟨event.depth, event.occurrence.target⟩

def observedSpan : ReductionSpan (ObservedState system) where
  Edge := Event system occurrences
  source event := ⟨event.depth + 1,
    classOf (ObservedGradedFamilyDescent.readout system (event.depth + 1)) event.occurrence.source⟩
  target event := ⟨event.depth,
    classOf (ObservedGradedFamilyDescent.readout system event.depth) event.occurrence.target⟩

def stateReading (state : RawState (S := S)) : ObservedState system :=
  ⟨state.1, classOf (ObservedGradedFamilyDescent.readout system state.1) state.2⟩

def observation : SpanMap (rawSpan system occurrences) (observedSpan system occurrences) where
  states := stateReading system
  events := id
  source_comm _ := rfl
  target_comm _ := rfl

include vocabulary in
theorem source_lifting_retains_label (positive : K.Positive)
    (state : RawState (S := S)) (event : Event system occurrences)
    (same : (observedSpan system occurrences).source event = stateReading system state) :
    ∃ lifted : Event system occurrences,
      (rawSpan system occurrences).source lifted = state ∧
      stateReading system ((rawSpan system occurrences).target lifted) =
        (observedSpan system occurrences).target event ∧
      lifted.occurrence.label = event.occurrence.label := by
  rcases state with ⟨depth, source⟩
  have depths : event.depth + 1 = depth := congrArg Sigma.fst same
  subst depth
  have classes :
      classOf (ObservedGradedFamilyDescent.readout system (event.depth + 1)) event.occurrence.source =
        classOf (ObservedGradedFamilyDescent.readout system (event.depth + 1)) source :=
    eq_of_heq (Sigma.mk.inj_iff.mp same).2
  have readouts := (classOf_eq_iff _ _ _).mp classes
  have zero := (ObservedGradedFamilyDescent.readout_eq_iff system vocabulary _ _ _).mp readouts
  have related := (system.depthBound_eq_zero_iff_approx vocabulary positive _ _ _).mp zero
  have action := (occurrences.erases _ _ _).mp ⟨event.occurrence.occurrence⟩
  obtain ⟨target, step, matched⟩ := related.2.1 event.occurrence.label event.occurrence.target action
  obtain ⟨occurrence⟩ := (occurrences.erases event.occurrence.label source target).mpr step
  refine ⟨⟨event.depth, ⟨event.occurrence.label, source, target, occurrence⟩⟩, rfl, ?_, rfl⟩
  apply congrArg (fun value => (⟨event.depth, value⟩ : ObservedState system))
  apply (classOf_eq_iff _ _ _).mpr
  exact ((ObservedGradedFamilyDescent.readout_eq_iff system vocabulary _ _ _).mpr
    (system.depthBound_eq_zero_of_approx vocabulary matched)).symm

include vocabulary in
theorem sourceLifts (positive : K.Positive) : (observation system occurrences).SourceLifts := by
  intro state event same
  obtain ⟨lifted, source, target, _⟩ := source_lifting_retains_label system vocabulary occurrences positive state event same
  exact ⟨lifted, source, target⟩

include vocabulary in
theorem diamond_pullback (positive : K.Positive) (predicate : ObservedState system → Prop)
    (state : RawState (S := S)) :
    derivedDiamond (observedSpan system occurrences) predicate (stateReading system state) ↔
      derivedDiamond (rawSpan system occurrences) (predicate ∘ stateReading system) state :=
  (observation system occurrences).diamond_pullback (sourceLifts system vocabulary occurrences positive) predicate state

theorem predecessor_box_iff_targetLifts :
    (observation system occurrences).TargetLifts ↔
      ∀ (predicate : ObservedState system → Prop) (state : RawState (S := S)),
        derivedBox (observedSpan system occurrences) predicate (stateReading system state) ↔
          derivedBox (rawSpan system occurrences) (predicate ∘ stateReading system) state :=
  (observation system occurrences).targetLifts_iff_box

/-- The edge observation keeps the occurrence itself. Its data does not
assert that every raw state representative can lift that very occurrence. -/
theorem event_readout (event : Event system occurrences) :
    (observation system occurrences).events event = event := rfl

end Mettapedia.GSLT.ObservedDepthBudgetSpan
