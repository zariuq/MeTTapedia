import Mettapedia.GSLT.Core.RelativeClosedStructuralImageNativeMeaning
import Mettapedia.GSLT.Core.RelativeClosedPositionedModalControlData
import Mettapedia.CategoryTheory.RelativeClosedProgramReductionExtension
import Mettapedia.GSLT.Core.RelativeClosedStructuralImageLocalModels
import Mettapedia.GSLT.Core.RelativeClosedPositionedModalModelControls

/-!
# Complete generated constructor predicates with two independent inputs

An actual source constructor sends a number pair to twice its first number
plus four times its second, then one. Its independently generated structural
name is read through the real quotient interpretation. Complete supplied
child predicates retain both numbers and a changing parameter. Empty input
and constant-truth alternatives discriminate the defining admission.
Distinct authored names may have equal images when their bodies agree.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Core.RelativeClosedStructuralImageControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
open Mettapedia.CategoryTheory RelativeClosedSyntax GeneratedCategory
open HigherOrderInternalPredicateObject HigherOrderInternalPredicateQuantifier
open ElementaryTypePredicateReadout
open PositionedRewritePredicatePower (name family_name)

abbrev source := RelativeClosedPositionedModalControlData.theory
abbrev selected := RelativeClosedPositionedModalControlData.selected
abbrev base := RelativeClosedPositionedModalControlData.base
abbrev Origin := RelativeClosedPositionedModalControlData.Origin

def constructor : Nat × Nat ⟶ Nat := TypeCat.ofHom fun pair => 2 * pair.1 + 4 * pair.2 + 1

def constructors (_origin : Origin) : RelativeClosedStructuralImagePresentation.Constructor source where
  arguments := RelativeClosedPositionedModalControlData.upward.obj (Nat × Nat)
  term := RelativeClosedPositionedModalControlData.upward.map constructor

abbrev diagram := RelativeClosedStructuralImageNativeMeaning.diagram doctrine source selected constructors base
abbrev values := RelativeClosedStructuralImageNativeMeaning.added doctrine source constructors base
abbrev meanings := RelativeClosedStructuralImageNativeMeaning.meanings doctrine source selected constructors base

def image : power doctrine (Nat × Nat) ⟶ power doctrine Nat :=
  RelativeClosedStructuralImageNativeMeaning.imageAt doctrine source selected constructors base (ULift.up false)

theorem actual_named_quotient_image : HEq
    (diagram.map (classOf (RelativeClosedStructuralImagePresentation.namedRaw source selected constructors (ULift.up false))))
    (RelativeClosedStructuralImageNativeMeaning.constructorOperation doctrine constructor) :=
  RelativeClosedStructuralImageNativeMeaning.complete_named_image doctrine source selected constructors base (ULift.up false)

theorem image_complete : image = existsOperation doctrine constructor :=
  (RelativeClosedStructuralImageNativeMeaning.imageAt_complete doctrine source selected constructors base (ULift.up false)).trans
    (RelativeClosedStructuralImageNativeMeaning.constructorOperation_complete doctrine constructor)

def child (chosen : Nat → Nat) : Subobject (Nat ⊗ Nat) := fromSet {supplied | supplied.1 = chosen supplied.2}
def childName (chosen : Nat → Nat) : Nat ⟶ power doctrine Nat := name doctrine (child chosen)
def inputs (first second : Nat → Nat) : Nat ⟶ power doctrine (Nat × Nat) :=
  lift (childName first) (childName second) ≫ InternalPredicateConstructorImage.binaryArguments doctrine Nat Nat

theorem complete_input_read (first second : Nat → Nat) (left right parameter : Nat) :
    Contains (family doctrine (inputs first second)) ((left, right), parameter) ↔
      left = first parameter ∧ right = second parameter := by
  rw [inputs, InternalPredicateConstructorImage.binaryArguments_supplied, contains_inf,
    contains_reindex, contains_reindex]
  have firstRead : family doctrine (childName first) = child first := family_name doctrine (child first)
  have secondRead : family doctrine (childName second) = child second := family_name doctrine (child second)
  rw [firstRead, secondRead]
  change Contains (child first) (left, parameter) ∧ Contains (child second) (right, parameter) ↔ _
  unfold child
  rw [contains_fromSet, contains_fromSet]
  rfl

def output (first second : Nat → Nat) : Subobject (Nat ⊗ Nat) :=
  family doctrine (inputs first second ≫ image)

theorem output_complete (first second : Nat → Nat) : output first second =
    doctrine.existsAlong (constructor ▷ Nat) (family doctrine (inputs first second)) := by
  rw [output, image_complete]
  exact exists_supplied doctrine constructor (inputs first second)

theorem output_read (first second : Nat → Nat) (result parameter : Nat) :
    Contains (output first second) (result, parameter) ↔
      result = 2 * first parameter + 4 * second parameter + 1 := by
  rw [output_complete, contains_exists]
  constructor
  · rintro ⟨⟨⟨left, right⟩, retainedParameter⟩, held, reaches⟩
    change (constructor (left, right), retainedParameter) = (result, parameter) at reaches
    obtain ⟨answer, sameParameter⟩ := Prod.mk.inj reaches
    subst retainedParameter
    obtain ⟨leftRead, rightRead⟩ := (complete_input_read first second left right parameter).mp held
    exact answer.symm.trans (by change 2 * left + 4 * right + 1 = _; rw [leftRead, rightRead])
  · intro answer
    refine ⟨((first parameter, second parameter), parameter),
      (complete_input_read first second (first parameter) (second parameter) parameter).mpr ⟨rfl, rfl⟩, ?_⟩
    change (2 * first parameter + 4 * second parameter + 1, parameter) = (result, parameter)
    exact congrArg (fun number => (number, parameter)) answer.symm

theorem neither_complete_child_input_can_be_dropped :
    Contains (output (fun _ => 2) (fun _ => 3)) (17, 0) ∧
      ¬ Contains (output (fun _ => 3) (fun _ => 3)) (17, 0) ∧
        ¬ Contains (output (fun _ => 2) (fun _ => 4)) (17, 0) := by
  refine ⟨(output_read _ _ 17 0).mpr rfl, ?_, ?_⟩
  · intro held
    have impossible := (output_read _ _ 17 0).mp held
    omega
  · intro held
    have impossible := (output_read _ _ 17 0).mp held
    omega

def future : Nat ⟶ Nat := TypeCat.ofHom Nat.succ

theorem future_read (result parameter : Nat) :
    Contains (family doctrine ((future ≫ inputs id Nat.succ) ≫ image)) (result, parameter) ↔
      result = 6 * parameter + 11 := by
  have reading := (congrArg (family doctrine) (Category.assoc future (inputs id Nat.succ) image)).trans
    (family_substitution doctrine future (inputs id Nat.succ ≫ image))
  rw [reading, contains_reindex]
  change Contains (output id Nat.succ) (result, parameter + 1) ↔ _
  rw [output_read]
  constructor <;> intro equation <;> simp only [id_eq, Nat.succ_eq_add_one] at equation ⊢ <;> omega

theorem actual_future_changes_the_complete_result : Contains (output id Nat.succ) (5, 0) ∧
    ¬ Contains (family doctrine ((future ≫ inputs id Nat.succ) ≫ image)) (5, 0) := by
  refine ⟨(output_read id Nat.succ 5 0).mpr rfl, ?_⟩
  intro held
  have impossible := (future_read 5 0).mp held
  omega

def emptyArgument : Subobject ((Nat × Nat) ⊗ Nat) := fromSet ∅
def emptyName : Nat ⟶ power doctrine (Nat × Nat) := name doctrine emptyArgument

theorem actual_constructor_image_has_no_empty_argument_member :
    ¬ Contains (family doctrine (emptyName ≫ image)) (0, 0) := by
  intro held
  have reading := (congrArg (fun arrow => family doctrine (emptyName ≫ arrow)) image_complete).trans
    ((exists_supplied doctrine constructor emptyName).trans
      (congrArg (doctrine.existsAlong (constructor ▷ Nat)) (family_name doctrine emptyArgument)))
  have admitted := (congrArg (fun predicate : Subobject (Nat ⊗ Nat) => Contains predicate (0, 0)) reading).mp held
  obtain ⟨witness, impossible, _⟩ := (contains_exists _ _ _).mp admitted
  exact (contains_fromSet ∅ witness).mp impossible

def constantTruth : power doctrine (Nat × Nat) ⟶ power doctrine Nat :=
  name doctrine (⊤ : Subobject (Nat ⊗ power doctrine (Nat × Nat)))

theorem constant_truth_accepts_the_empty_argument :
    Contains (family doctrine (emptyName ≫ constantTruth)) (0, 0) := by
  have reading : family doctrine (emptyName ≫ constantTruth) = ⊤ := by
    have whole : family doctrine constantTruth = ⊤ := family_name doctrine
      (⊤ : Subobject (Nat ⊗ power doctrine (Nat × Nat)))
    exact (family_substitution doctrine emptyName constantTruth).trans
      ((congrArg (doctrine.reindex (Nat ◁ emptyName)) whole).trans (doctrine.reindex_top _))
  exact (congrArg (fun predicate : Subobject (Nat ⊗ Nat) => Contains predicate (0, 0)) reading).mpr (contains_top _)

theorem constant_truth_is_not_the_actual_constructor_image : constantTruth ≠ image := by
  intro same
  exact actual_constructor_image_has_no_empty_argument_member
    ((congrArg (fun arrow : power doctrine (Nat × Nat) ⟶ power doctrine Nat =>
      Contains (family doctrine (emptyName ≫ arrow)) (0, 0)) same).mp constant_truth_accepts_the_empty_argument)

def wrongValues (_origin : Origin) : RelativeClosedSyntax.Interpretation.ArrowValue Type :=
  ⟨power doctrine (Nat × Nat), power doctrine Nat, constantTruth⟩

theorem wrong_local_declaration_is_rejected :
    ¬ RelativeClosedStructuralImageRealization.LocalAdmission source constructors base
      (RelativeClosedPredicateLogic.NativeMeaning.meaning base doctrine) wrongValues := by
  intro admitted
  have reading := RelativeClosedSyntax.Interpretation.ArrowValue.arrows_heq
    ((admitted (ULift.up false)).trans
      (RelativeClosedStructuralImageNativeMeaning.admitted doctrine source constructors base (ULift.up false)).symm)
  exact constant_truth_is_not_the_actual_constructor_image
    ((eq_of_heq reading).trans
      (RelativeClosedStructuralImageNativeMeaning.imageAt_complete doctrine source selected constructors base
        (ULift.up false)).symm)

theorem wrong_complete_meanings_have_no_generated_realization :
    ¬ RelativeClosedSyntax.Interpretation.Realization
      (RelativeClosedStructuralImagePresentation.signature source selected constructors)
      (RelativeClosedStructuralImageRealization.assignment source base
        (RelativeClosedPredicateLogic.NativeMeaning.meaning base doctrine)
        (RelativeClosedPositionedModalNativeMeaning.added doctrine source selected base) wrongValues) :=
  fun actual => wrong_local_declaration_is_rejected
    ((RelativeClosedStructuralImageRealization.realization_iff_local source selected constructors base
      (RelativeClosedPredicateLogic.NativeMeaning.meaning base doctrine)
      (RelativeClosedPositionedModalNativeMeaning.added doctrine source selected base) wrongValues).mp actual).2.2

theorem authored_name_codes_remain_distinct :
    (RelativeClosedStructuralImagePresentation.namedRaw source selected constructors (ULift.up false)).code ≠
      (RelativeClosedStructuralImagePresentation.namedRaw source selected constructors (ULift.up true)).code := by
  intro same
  have names := ArrowCode.name.inj same
  exact Bool.false_ne_true (congrArg ULift.down (Sum.inr.inj names))

theorem equal_constructor_bodies_have_equal_quotient_names :
    classOf (RelativeClosedStructuralImagePresentation.namedRaw source selected constructors (ULift.up false)) =
      classOf (RelativeClosedStructuralImagePresentation.namedRaw source selected constructors (ULift.up true)) :=
  (RelativeClosedStructuralImagePresentation.named_operation_is_constructor_image source selected constructors (ULift.up false)).trans
    (RelativeClosedStructuralImagePresentation.named_operation_is_constructor_image source selected constructors (ULift.up true)).symm

namespace WeakNative

abbrev original := RelativeClosedPositionedModalModelControls.source
abbrev selection := RelativeClosedPositionedModalModelControls.selected
abbrev previous := RelativeClosedPositionedModalModelControls.model

def constructors (_origin : Bool) : RelativeClosedStructuralImagePresentation.Constructor original where
  arguments := true
  term := 𝟙 true

def model : RelativeClosedStructuralImageLocalModels.LocalModel original selection constructors Type where
  previous := previous
  constructorValues := RelativeClosedStructuralImageNativeMeaning.added doctrine original constructors previous.base
  constructorDiagrams := RelativeClosedStructuralImageNativeMeaning.admitted doctrine original constructors previous.base

def interpretation : LambdaTheoryMap (RelativeClosedStructuralImagePresentation.nativeTheory original selection constructors)
    (LambdaTheory.ofCategory Type) := model.closedInterpretation

theorem actual_weak_closed_base_is_retained :
    (RelativeClosedStructuralImagePresentation.baseMap original selection constructors).functor ⋙
      interpretation.functor = previous.base := model.base_readback

theorem actual_original_modal_diagram_is_retained :
    (RelativeClosedStructuralImagePresentation.inclusion original selection constructors).functor ⋙
      model.diagram = previous.diagram := model.previous_diagram_readback

theorem actual_native_named_image : HEq (interpretation.functor.map (classOf
    ((RelativeClosedStructuralImagePresentation.nativeInclusion original selection constructors).rawArrow
      (RelativeClosedStructuralImagePresentation.namedRaw original selection constructors false))))
    (model.constructorValues false).arrow := model.native_named_image false

theorem false_scope_remains_empty : IsEmpty (interpretation.functor.obj
    (baseObject (RelativeClosedStructuralImagePresentation.nativeSignature original selection constructors) false)) := by
  have same := RelativeClosedSyntax.Interpretation.functor_base_object model.nativeModel.meanings
    model.nativeModel.realization false
  exact same.symm ▸ RelativeClosedWeakBaseControls.false_fibre_empty

end WeakNative

end Mettapedia.GSLT.Core.RelativeClosedStructuralImageControls
