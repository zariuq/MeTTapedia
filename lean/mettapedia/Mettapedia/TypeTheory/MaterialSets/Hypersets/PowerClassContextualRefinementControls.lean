import Mettapedia.TypeTheory.MaterialSets.Hypersets.PowerClassContextualRefinement

/-!
# Contextual refinement controls on an infinite growing base

The authored stages introduce new source values, retain their source tags,
and have genuine nonconstant decoded families. Keeping more observations
preserves natural sections. Forgetting a tag or a selected position can
prevent descent even when the family and contextual action still descend.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.PowerClassContextualRefinementControls

open CategoryTheory AccessiblePointedGraph
open PowerClassFamilyDescent PowerClassPresheafDescent PowerClassContextualRefinement
open PowerClassPresheafDescent.Controls

def retainedObservation : NatTrans growingSource growingSource where
  app _ := TypeCat.ofHom id
  naturality _ _ _ := rfl

theorem retained_refines : KernelRefinement growingSource growingSource growingTarget
    retainedObservation growingObservation := by
  intro _ _ _ same
  exact congrArg Prod.fst same

def retainedAlternativeTransport :=
  refineTransport growingSource growingSource growingTarget retainedObservation growingObservation
    retained_refines alternativeGraphs alternativeTransport

theorem tagTerm_retained_compatible : ContextualCompatible growingSource growingSource
    retainedObservation alternativeGraphs retainedAlternativeTransport tagTerm := by
  constructor
  · intro _ left right same
    change left = right at same
    cases same
    rfl
  · exact tagTerm_natural

def tagSection := descendContextualSection growingSource growingSource retainedObservation
  alternativeGraphs retainedAlternativeTransport tagTerm tagTerm_retained_compatible

theorem tagSection_source_values : pullContextualSection growingSource growingSource
    retainedObservation alternativeGraphs retainedAlternativeTransport tagSection = tagTerm :=
  pull_descendContextualSection _ _ _ _ _ _ _

theorem tagSection_cannot_coarsen :
    ¬ CoarseCompatibleSection growingSource growingSource growingTarget retainedObservation
      growingObservation retained_refines alternativeGraphs alternativeTransport tagSection := by
  intro compatible
  have raw : ContextualCompatible growingSource growingTarget growingObservation alternativeGraphs
      alternativeTransport tagTerm := by
    change ContextualCompatible growingSource growingTarget growingObservation alternativeGraphs
      alternativeTransport (pullContextualSection growingSource growingSource retainedObservation
        alternativeGraphs retainedAlternativeTransport tagSection) at compatible
    rw [tagSection_source_values] at compatible
    exact compatible
  exact tagTerm_not_contextually_compatible raw

theorem tagSection_outside_coarse_image :
    ¬ ∃ term, refineSection growingSource growingSource growingTarget retainedObservation
      growingObservation retained_refines alternativeGraphs alternativeTransport term = tagSection := by
  intro inRange
  exact tagSection_cannot_coarsen
    ((coarseCompatible_iff_in_range _ _ _ _ _ _ _ _ _).mpr inRange)

def emptySection := descendContextualSection growingSource growingTarget growingObservation
  alternativeGraphs alternativeTransport emptyTerm emptyTerm_compatible

theorem refined_empty_source_values :
    pullContextualSection growingSource growingSource retainedObservation alternativeGraphs
        retainedAlternativeTransport
        (refineSection growingSource growingSource growingTarget retainedObservation growingObservation
          retained_refines alternativeGraphs alternativeTransport emptySection) = emptyTerm :=
  (pull_refineSection _ _ _ _ _ _ _ _ _).trans (pull_descendContextualSection _ _ _ _ _ _ _)

theorem nonconstant_decoders_coarsen (X : Stagesᵒᵖ)
    (observed : ObservationClass (retainedObservation.app X)) :
    decodedFamily (fun value => growingGraphs ⟨X, value⟩) observed =
      decodedFamily (fun value => growingGraphs ⟨X, value⟩)
        ((classCoarsening growingSource growingSource growingTarget retainedObservation
          growingObservation retained_refines).app X observed) :=
  family_coarsening _ _ _ _ _ _ _ growingTransport X observed

theorem original_nonconstant_family :
    decodedFamily (fun value => growingGraphs ⟨world 0, value⟩)
        (classOf (growingObservation.app (world 0)) (stageValue 0 0 (by omega) true)) ≠
      decodedFamily (fun value => growingGraphs ⟨world 1, value⟩)
        (classOf (growingObservation.app (world 1)) (stageValue 1 1 (by omega) false)) :=
  growing_family_nonconstant

def terminalTarget : Stagesᵒᵖ ⥤ Type where
  obj _ := PUnit
  map _ := TypeCat.ofHom id
  map_id _ := rfl
  map_comp _ _ := rfl

def terminalObservation : NatTrans growingSource terminalTarget where
  app _ := TypeCat.ofHom (fun _ => PUnit.unit)
  naturality _ _ _ := rfl

def terminalTransport : MaterialTransport growingSource terminalTarget terminalObservation
    alternativeGraphs where
  invariant _ := by intro _ _ _; rfl
  map _ _ member := member
  map_id_value _ _ _ := rfl
  map_comp_value _ _ _ _ := rfl
  compatible _ := by intro _ _ _ _ _ same; exact same

theorem position_refines_terminal : KernelRefinement growingSource growingTarget terminalTarget
    growingObservation terminalObservation := fun _ _ _ _ => rfl

def middleTransport := refineTransport growingSource growingTarget terminalTarget growingObservation
  terminalObservation position_refines_terminal alternativeGraphs terminalTransport

/-- Selected material values depend on a real position retained by the
middle observation, and preserved by every stage extension. -/
def positionTerm (point : growingSource.Elements) : El (· ∈ ·) (HSet.mk (alternativeGraphs point)) :=
  ⟨HSet.mk (PowerClassFamilyDescent.Controls.selectedGraph (decide (point.2.1.val = 0))),
    HSet.mem_range.mpr ⟨⟨decide (point.2.1.val = 0)⟩, rfl⟩⟩

theorem positionTerm_middle_compatible : ContextualCompatible growingSource growingTarget
    growingObservation alternativeGraphs middleTransport positionTerm := by
  constructor
  · intro _ _ _ same
    exact congrArg (fun index => HSet.mk
      (PowerClassFamilyDescent.Controls.selectedGraph (decide (index.val = 0)))) same
  · intro _ _ _ _
    rfl

def positionSection := descendContextualSection growingSource growingTarget growingObservation
  alternativeGraphs middleTransport positionTerm positionTerm_middle_compatible

theorem positionTerm_terminal_incompatible :
    ¬ ContextualCompatible growingSource terminalTarget terminalObservation alternativeGraphs
      terminalTransport positionTerm := by
  intro compatible
  have same := compatible.1 (world 1)
    (left := stageValue 1 0 (by omega) false) (right := stageValue 1 1 (by omega) false) rfl
  have firstValue : (positionTerm ⟨world 1, stageValue 1 0 (by omega) false⟩).1 =
      ({∅} : HSet) :=
    (picture_eq_mk _).symm.trans picture_oneChild_empty
  have secondValue : (positionTerm ⟨world 1, stageValue 1 1 (by omega) false⟩).1 =
      (∅ : HSet) := HSet.mk_empty
  exact HSet.empty_ne_singleton_empty (secondValue.symm.trans (same.symm.trans firstValue))

theorem middle_section_fails_second_stage :
    ¬ CoarseCompatibleSection growingSource growingTarget terminalTarget growingObservation
      terminalObservation position_refines_terminal alternativeGraphs terminalTransport positionSection := by
  intro compatible
  change ContextualCompatible growingSource terminalTarget terminalObservation alternativeGraphs
    terminalTransport (pullContextualSection growingSource growingTarget growingObservation
      alternativeGraphs middleTransport positionSection) at compatible
  unfold positionSection at compatible
  rw [pull_descendContextualSection] at compatible
  exact positionTerm_terminal_incompatible compatible

def terminalEmptySection := descendContextualSection growingSource terminalTarget terminalObservation
  alternativeGraphs terminalTransport emptyTerm ⟨by intro _ _ _ _; rfl, by intro _ _ _ _; rfl⟩

theorem three_observers_full_section_composition :
    refineSection growingSource growingSource growingTarget retainedObservation growingObservation
        retained_refines alternativeGraphs middleTransport
        (refineSection growingSource growingTarget terminalTarget growingObservation terminalObservation
          position_refines_terminal alternativeGraphs terminalTransport terminalEmptySection) =
      refineSection growingSource growingSource terminalTarget retainedObservation terminalObservation
        (kernelRefinement_comp growingSource growingSource terminalTarget retainedObservation terminalObservation
          growingTarget growingObservation retained_refines position_refines_terminal)
        alternativeGraphs terminalTransport terminalEmptySection :=
  refineSection_comp _ _ _ _ _ _ _ _ _ _ _ _

end Mettapedia.TypeTheory.MaterialSets.Hypersets.PowerClassContextualRefinementControls
