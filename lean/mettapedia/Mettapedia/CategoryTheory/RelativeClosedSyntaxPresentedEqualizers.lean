import Mettapedia.CategoryTheory.RelativeClosedSyntaxLimits

/-!
# Equalizers with independently supplied raw presentations

The two arrows defining an equalizer may be authored representatives rather
than the representatives selected by the quotient category's limit choices.
Their generated condition, lifts and complete uniqueness earn an actual
limit. The resulting comparison isomorphism preserves the entire inclusion
arrow; it does not equate the two raw object codes.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.GeneratedCategory.PresentedEqualizer

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v a

variable {C : Type u} [Category.{v} C] {symbols : Symbols.{a}}
variable {signature : Signature (C := C) (symbols := symbols)}
variable {source target : Object signature}

def object (before after : RawHom source target) : Object signature :=
  ⟨.equalizer source.code target.code before.code after.code,
    ⟨.equalizerObject source.formed.some target.formed.some
      before.admitted.some after.admitted.some⟩⟩

def inclusion (before after : RawHom source target) : object before after ⟶ source :=
  classOf ⟨.equalizerArrow source.code target.code before.code after.code,
    ⟨.equalizerArrow source.formed.some target.formed.some
      before.admitted.some after.admitted.some⟩⟩

theorem condition (before after : RawHom source target) :
    inclusion before after ≫ classOf before = inclusion before after ≫ classOf after :=
  Quotient.sound ⟨.equalizerCondition source.formed.some target.formed.some
    before.admitted.some after.admitted.some⟩

theorem represented_condition {context : Object signature}
    (before after : RawHom source target) (candidate : context ⟶ source)
    (commutes : candidate ≫ classOf before = candidate ≫ classOf after) :
    Nonempty (Derivation signature (.equation context.code target.code
      (.compose (representative candidate).code before.code)
      (.compose (representative candidate).code after.code))) := by
  have represented : classOf (RawHom.compose (representative candidate) before) =
      classOf (RawHom.compose (representative candidate) after) := by
    simpa only [classOf_compose, classOf_representative] using commutes
  exact Quotient.exact represented

def lift {context : Object signature} (before after : RawHom source target)
    (candidate : context ⟶ source)
    (commutes : candidate ≫ classOf before = candidate ≫ classOf after) :
    context ⟶ object before after :=
  classOf ⟨.equalizerLift source.code target.code before.code after.code
    context.code (representative candidate).code,
    ⟨.equalizerLift source.formed.some target.formed.some context.formed.some
      before.admitted.some after.admitted.some (representative candidate).admitted.some
      (represented_condition before after candidate commutes).some⟩⟩

@[simp] theorem lift_inclusion {context : Object signature}
    (before after : RawHom source target) (candidate : context ⟶ source)
    (commutes : candidate ≫ classOf before = candidate ≫ classOf after) :
    lift before after candidate commutes ≫ inclusion before after = candidate := by
  have represented : lift before after candidate commutes ≫ inclusion before after =
      classOf (representative candidate) :=
    Quotient.sound ⟨.equalizerBeta source.formed.some target.formed.some context.formed.some
      before.admitted.some after.admitted.some (representative candidate).admitted.some
      (represented_condition before after candidate commutes).some⟩
  exact represented.trans (classOf_representative candidate)

theorem joint_cancel {context : Object signature} (before after : RawHom source target)
    {first second : context ⟶ object before after}
    (same : first ≫ inclusion before after = second ≫ inclusion before after) :
    first = second := by
  revert same
  refine Quotient.inductionOn₂ first second ?_
  intro first second same
  have represented : Nonempty (Derivation signature (.equation context.code source.code
    (.compose first.code (.equalizerArrow source.code target.code before.code after.code))
    (.compose second.code (.equalizerArrow source.code target.code before.code after.code)))) :=
    Quotient.exact same
  exact Quotient.sound ⟨.equalizerUniqueness first.admitted.some second.admitted.some represented.some⟩

instance inclusion_mono (before after : RawHom source target) : Mono (inclusion before after) where
  right_cancellation _ _ same := joint_cancel before after same

def isLimit (before after : RawHom source target) :
    IsLimit (Fork.ofι (inclusion before after) (condition before after)) :=
  Fork.IsLimit.mk _ (fun cone => lift before after cone.ι cone.condition)
    (fun cone => lift_inclusion before after cone.ι cone.condition)
    (fun cone _candidate factors => joint_cancel before after
      (factors.trans (lift_inclusion before after cone.ι cone.condition).symm))

def chosenComparison (before after : RawHom source target) :
    object before after ≅ equalizerObject (classOf before) (classOf after) where
  hom := equalizerLift (classOf before) (classOf after) (inclusion before after)
    (condition before after)
  inv := lift before after (equalizerInclusion (classOf before) (classOf after))
    (equalizer_condition (classOf before) (classOf after))
  hom_inv_id := by
    apply joint_cancel before after
    simp only [Category.assoc, lift_inclusion, equalizerLift_inclusion, Category.id_comp]
  inv_hom_id := by
    apply equalizer_joint_cancel (classOf before) (classOf after)
    simp only [Category.assoc, equalizerLift_inclusion, lift_inclusion, Category.id_comp]

@[simp] theorem chosenComparison_hom_inclusion (before after : RawHom source target) :
    (chosenComparison before after).hom ≫ equalizerInclusion (classOf before) (classOf after) =
      inclusion before after :=
  equalizerLift_inclusion (classOf before) (classOf after) (inclusion before after)
    (condition before after)

@[simp] theorem chosenComparison_inv_inclusion (before after : RawHom source target) :
    (chosenComparison before after).inv ≫ inclusion before after =
      equalizerInclusion (classOf before) (classOf after) :=
  lift_inclusion before after (equalizerInclusion (classOf before) (classOf after))
    (equalizer_condition (classOf before) (classOf after))

end Mettapedia.CategoryTheory.RelativeClosedSyntax.GeneratedCategory.PresentedEqualizer
