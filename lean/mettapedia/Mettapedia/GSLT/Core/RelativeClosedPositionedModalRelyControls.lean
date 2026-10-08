import Mettapedia.GSLT.Core.RelativeClosedPositionedModalRelyInputs
import Mettapedia.GSLT.Core.RelativeClosedPositionedModalControls

/-!
# Environment-only rely functions retain complete generated modal values

The supplied rely function has only the first number as its data argument.
Its independently authored pullback and raw modal expression retain the
whole postcondition and predicate parameter. The actual generated image
agrees with the previously checked successor-rule interpretation. Changing
only the rely function changes a complete result, and actual future
substitution changes the parameter reading.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Core.RelativeClosedPositionedModalRelyControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
open Mettapedia.CategoryTheory RelativeClosedSyntax GeneratedCategory
open PositionedRewritePredicatePower ElementaryTypePredicateReadout

abbrev source := RelativeClosedPositionedModalControlData.theory
abbrev selected := RelativeClosedPositionedModalControlData.selected
abbrev base := RelativeClosedPositionedModalControlData.base
abbrev origin : RelativeClosedPositionedModalControlData.Origin := ULift.up false
abbrev Assay := RelativeClosedPositionedModalControls.Assay
abbrev Outgoing := RelativeClosedPositionedModalControls.Outgoing

def environmentRelies : Subobject (Nat ⊗ Nat) := fromSet {supplied | fst Nat Nat supplied > 0}
def environmentName : Nat ⟶ power doctrine Nat := name doctrine environmentRelies
def environmentInputs : Nat ⟶ profiles doctrine Nat Outgoing :=
  lift environmentName RelativeClosedPositionedModalControls.postName

theorem environment_pullback :
    doctrine.reindex (base.map (RelativeClosedPositionedModalRelyInputs.assayProjection source selected origin) ▷ Nat)
      environmentRelies = RelativeClosedPositionedModalControls.relies := by
  apply le_antisymm
  · apply (le_iff_contains _ _).mpr
    intro value held
    have pulled := (contains_reindex _ _ _).mp held
    have read := (contains_fromSet _ _).mp pulled
    exact (RelativeClosedPositionedModalControls.relies_read value.1 value.2).mpr read
  · apply (le_iff_contains _ _).mpr
    intro value held
    apply (contains_reindex _ _ _).mpr
    apply (contains_fromSet _ _).mpr
    exact (RelativeClosedPositionedModalControls.relies_read value.1 value.2).mp held

theorem environment_name_pullback :
    environmentName ≫ InternalPredicateQuantifier.precomposition
        (HigherOrderInternalPredicateObject.operations doctrine)
        (base.map (RelativeClosedPositionedModalRelyInputs.assayProjection source selected origin)) =
      RelativeClosedPositionedModalControls.relyName := by
  apply HigherOrderInternalPredicateObject.family_injective doctrine
  exact (HigherOrderInternalPredicateQuantifier.precomposition_supplied doctrine _ environmentName).trans
    ((congrArg (doctrine.reindex
      (base.map (RelativeClosedPositionedModalRelyInputs.assayProjection source selected origin) ▷ Nat))
      (family_name doctrine environmentRelies)).trans
        (environment_pullback.trans (family_name doctrine RelativeClosedPositionedModalControls.relies).symm))

theorem complete_input_comparison :
    environmentInputs ≫ RelativeClosedPositionedModalRelyInputs.inputMap source selected base
        (RelativeClosedPositionedModalRelyInputs.nativeMeaning source base doctrine) origin =
      RelativeClosedPositionedModalControls.inputs := by
  apply hom_ext
  · calc
      (environmentInputs ≫ RelativeClosedPositionedModalRelyInputs.inputMap source selected base
          (RelativeClosedPositionedModalRelyInputs.nativeMeaning source base doctrine) origin) ≫ fst _ _ =
        environmentInputs ≫ (fst _ _ ≫ InternalPredicateQuantifier.precomposition
          (HigherOrderInternalPredicateObject.operations doctrine)
          (base.map (RelativeClosedPositionedModalRelyInputs.assayProjection source selected origin))) :=
            (Category.assoc _ _ _).trans
              (congrArg (fun arrow => environmentInputs ≫ arrow)
                (RelativeClosedPositionedModalRelyInputs.inputMap_first source selected base doctrine origin))
      _ = environmentName ≫ InternalPredicateQuantifier.precomposition
          (HigherOrderInternalPredicateObject.operations doctrine)
          (base.map (RelativeClosedPositionedModalRelyInputs.assayProjection source selected origin)) := by
            rw [← Category.assoc]
            exact congrArg (fun arrow => arrow ≫ _) (lift_fst environmentName
              RelativeClosedPositionedModalControls.postName)
      _ = RelativeClosedPositionedModalControls.inputs ≫ fst _ _ :=
        environment_name_pullback.trans
          (lift_fst RelativeClosedPositionedModalControls.relyName
            RelativeClosedPositionedModalControls.postName).symm
  · exact ((Category.assoc _ _ _).trans
      ((congrArg (fun arrow => environmentInputs ≫ arrow)
        (RelativeClosedPositionedModalRelyInputs.inputMap_second source selected base doctrine origin)).trans
          (lift_snd environmentName RelativeClosedPositionedModalControls.postName))).trans
      (lift_snd RelativeClosedPositionedModalControls.relyName
        RelativeClosedPositionedModalControls.postName).symm

def generatedImage : profiles doctrine Nat Outgoing ⟶ power doctrine Nat :=
  RelativeClosedPositionedModalRelyInputs.image source selected base doctrine origin

theorem actual_raw_source_image :
    HEq (RelativeClosedPositionedModalControlData.diagram.map
      (classOf (RelativeClosedPositionedModalRelyInputs.sourceArrow source selected origin))) generatedImage :=
  RelativeClosedPositionedModalRelyInputs.complete_source_image source selected base doctrine origin

def output : Subobject (Nat ⊗ Nat) := family doctrine (environmentInputs ≫ generatedImage)

theorem output_complete : output = RelativeClosedPositionedModalControls.output :=
  congrArg (family doctrine)
    ((Category.assoc _ _ _).symm.trans
      (congrArg (fun inputs => inputs ≫ RelativeClosedPositionedModalControls.modalImage)
        complete_input_comparison))

theorem output_read (focus parameter : Nat) : Contains output (focus, parameter) ↔ parameter < focus :=
  output_complete ▸ RelativeClosedPositionedModalControls.output_read focus parameter

theorem complete_parameter_is_retained : Contains output (2, 0) ∧ ¬ Contains output (2, 2) :=
  ⟨(output_read 2 0).mpr (by omega), fun held => Nat.lt_irrefl 2 ((output_read 2 2).mp held)⟩

theorem actual_future_read (focus parameter : Nat) :
    Contains (family doctrine
      ((RelativeClosedPositionedModalControls.future ≫ environmentInputs) ≫ generatedImage))
        (focus, parameter) ↔ parameter + 1 < focus := by
  have complete := (family_substitution doctrine RelativeClosedPositionedModalControls.future
    (environmentInputs ≫ generatedImage)).trans
      (congrArg (family doctrine) (Category.assoc _ _ _).symm)
  rw [← complete, contains_reindex]
  exact output_read focus (parameter + 1)

theorem actual_future_changes_a_complete_answer : Contains output (1, 0) ∧
    ¬ Contains (family doctrine
      ((RelativeClosedPositionedModalControls.future ≫ environmentInputs) ≫ generatedImage)) (1, 0) :=
  ⟨(output_read 1 0).mpr (by omega),
    fun held => Nat.lt_irrefl 1 ((actual_future_read 1 0).mp held)⟩

def emptyRely : Subobject (Nat ⊗ Nat) := fromSet ∅
def emptyName : Nat ⟶ power doctrine Nat := name doctrine emptyRely
def emptyInputs : Nat ⟶ profiles doctrine Nat Outgoing :=
  lift emptyName RelativeClosedPositionedModalControls.postName

theorem empty_rely_has_no_member (value parameter : Nat) : ¬ Contains emptyRely (value, parameter) :=
  fun held => (contains_fromSet ∅ (value, parameter)).mp held

theorem empty_rely_admits_the_same_rejected_parameter :
    Contains (family doctrine (emptyInputs ≫ generatedImage)) (2, 2) := by
  have reading : family doctrine (emptyInputs ≫ generatedImage) =
      modalAt doctrine (base.map (selected origin).frame.forget) (base.map (selected origin).frame.focus)
        (base.map (selected origin).position.relies) (base.map (selected origin).frame.outgoing) emptyInputs :=
    RelativeClosedPositionedModalRelyInputs.supplied_read source selected base doctrine origin emptyInputs
  apply (congrArg (fun predicate : Subobject (Nat ⊗ Nat) => Contains predicate (2, 2)) reading).mpr
  change Contains (doctrine.existsAlong (base.map RelativeClosedPositionedModalControlData.frame.focus ▷ Nat)
    (doctrine.forallAlong (base.map RelativeClosedPositionedModalControlData.frame.forget ▷ Nat) _)) _
  apply (contains_exists _ _ _).mpr
  refine ⟨((2 : Nat), (2 : Nat)), ?_, rfl⟩
  apply (contains_forall _ _ _).mpr
  intro supplied _reaches
  change Contains (doctrine.algebra _ |>.himp
    (doctrine.reindex (base.map (selected origin).position.relies ▷ Nat)
      (family doctrine (emptyInputs ≫ fst _ _))) _) _
  rw [contains_implication]
  intro impossible
  have emptyReading : family doctrine (emptyInputs ≫ fst _ _) = emptyRely :=
    (congrArg (family doctrine) (lift_fst emptyName RelativeClosedPositionedModalControls.postName)).trans
      (family_name doctrine emptyRely)
  rw [emptyReading, contains_reindex] at impossible
  exact (empty_rely_has_no_member _ _ impossible).elim

theorem changing_only_the_rely_input_changes_the_complete_result :
    family doctrine (environmentInputs ≫ generatedImage) ≠
      family doctrine (emptyInputs ≫ generatedImage) := by
  intro same
  have complete := (congrArg (fun predicate : Subobject (Nat ⊗ Nat) => Contains predicate (2, 2)) same).mpr
    empty_rely_admits_the_same_rejected_parameter
  exact complete_parameter_is_retained.2 complete

end Mettapedia.GSLT.Core.RelativeClosedPositionedModalRelyControls
