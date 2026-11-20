import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TypedPublicationTargetResult
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TypedPublicationCoherenceModal

/-!
# Actual predecessor lifting for the full certified-publication step

An incoming application is recertified at the compared endpoint, retaining
its entire source state. Thus isomorphic endpoints have exactly the same
predecessor states in this step. The source and target projections of the
comparison graph both have backward lifting, independently of the previously
proved forward lifting. Restricted offer tables and permissions require
their own closure under this construction.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.CoherenceModal

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta DependentFull
open LogicOverTheStep LogicOverTheStep.StepSpan LogicOverTheStep.ModalComparison
open FragmentsOfTheStep.TransitionMaps
open Mettapedia.OSLF.Framework.DerivedModalities

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head}
  {levels : LevelModel rules L} {O : Type} [DecidableEq O]

theorem predecessor_lift {before endpoint desired : State rules O}
    (transition : Succ (realizationStep levels O) before endpoint) (comparison : PlainIso levels endpoint desired) :
    Succ (realizationStep levels O) before desired := by
  obtain ⟨original, accepted, rfl⟩ := transition
  let sourceAccepted := (realization_admits_iff original).mp accepted
  have sourceComparison : PlainIso levels (original.sourceResult sourceAccepted) desired := by
    rw [← realization_result original sourceAccepted]
    exact comparison
  exact ⟨TargetChange.application original sourceAccepted sourceComparison,
    TargetChange.native_admitted original sourceAccepted sourceComparison,
    TargetChange.native_result original sourceAccepted sourceComparison⟩

theorem predecessors_equal {endpoint desired : State rules O} (comparison : PlainIso levels endpoint desired)
    (before : State rules O) :
    Succ (realizationStep levels O) before endpoint ↔ Succ (realizationStep levels O) before desired :=
  ⟨fun transition => predecessor_lift transition comparison,
    fun transition => predecessor_lift transition comparison.symm⟩

/-- The predecessor itself is retained, so this past modality needs no
invariance assumption on its source predicate. -/
theorem predecessor_necessity {endpoint desired : State rules O} (comparison : PlainIso levels endpoint desired)
    (observation : State rules O → Prop) :
    derivedBox (firingSpan (realizationStep levels O)) observation endpoint ↔
      derivedBox (firingSpan (realizationStep levels O)) observation desired := by
  rw [firing_predecessorBox_eq, box_iff, box_iff]
  exact ⟨fun all before transition => all before ((predecessors_equal comparison before).mpr transition),
    fun all before transition => all before ((predecessors_equal comparison before).mp transition)⟩

theorem projections_backward :
    BackZag
      (graphStep (Succ (realizationStep levels O)) (Succ (realizationStep levels O)) (Related levels O))
      (Succ (realizationStep levels O)) (fun pair => pair.val.1) ∧
    BackZag
      (graphStep (Succ (realizationStep levels O)) (Succ (realizationStep levels O)) (Related levels O))
      (Succ (realizationStep levels O)) (fun pair => pair.val.2) := by
  constructor
  · intro pair before transition
    obtain ⟨comparison⟩ := pair.property
    exact ⟨⟨(before, before), ⟨PlainIso.refl before⟩⟩,
      ⟨transition, predecessor_lift transition comparison⟩, rfl⟩
  · intro pair before transition
    obtain ⟨comparison⟩ := pair.property
    exact ⟨⟨(before, before), ⟨PlainIso.refl before⟩⟩,
      ⟨predecessor_lift transition comparison.symm, transition⟩, rfl⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.CoherenceModal

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.CoherenceModal.predecessor_lift
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.CoherenceModal.projections_backward
