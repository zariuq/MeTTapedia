import Mettapedia.CategoryTheory.RelativeClosedSyntaxCategory
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers

/-!
# Equalizers and finite limits of generated relative syntax

An equalizer is formed from independently admitted representatives of the
two supplied arrow classes. Equality of the candidate composites yields an
actual generated commutativity tree, which admits its equalizer lift.
The generated beta and uniqueness rules give the full limit universal
property. Finite limits then follow from the earned finite products.

Choosing representatives selects an equalizer presentation; it does not
identify distinct raw objects or assert preservation of the base limits.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.GeneratedCategory

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v a

variable {C : Type u} [Category.{v} C] {symbols : Symbols.{a}}
variable {signature : Signature (C := C) (symbols := symbols)}

def equalizerObject {source target : Object signature} (before after : source ⟶ target) :
    Object signature :=
  ⟨.equalizer source.code target.code (representative before).code (representative after).code,
    ⟨.equalizerObject source.formed.some target.formed.some
      (representative before).admitted.some (representative after).admitted.some⟩⟩

def equalizerInclusion {source target : Object signature} (before after : source ⟶ target) :
    equalizerObject before after ⟶ source :=
  classOf
    ⟨.equalizerArrow source.code target.code (representative before).code (representative after).code,
      ⟨.equalizerArrow source.formed.some target.formed.some
        (representative before).admitted.some (representative after).admitted.some⟩⟩

theorem equalizer_condition {source target : Object signature} (before after : source ⟶ target) :
    equalizerInclusion before after ≫ before = equalizerInclusion before after ≫ after := by
  have represented : equalizerInclusion before after ≫ classOf (representative before) =
      equalizerInclusion before after ≫ classOf (representative after) :=
    Quotient.sound ⟨.equalizerCondition source.formed.some target.formed.some
      (representative before).admitted.some (representative after).admitted.some⟩
  simpa only [classOf_representative] using represented

theorem represented_commutativity {source target context : Object signature}
    (before after : source ⟶ target) (candidate : context ⟶ source)
    (commutes : candidate ≫ before = candidate ≫ after) :
    Nonempty (Derivation signature (.equation context.code target.code
      (.compose (representative candidate).code (representative before).code)
      (.compose (representative candidate).code (representative after).code))) := by
  have represented : classOf (RawHom.compose (representative candidate) (representative before)) =
      classOf (RawHom.compose (representative candidate) (representative after)) := by
    simpa only [classOf_compose, classOf_representative] using commutes
  exact Quotient.exact represented

def equalizerLift {source target context : Object signature}
    (before after : source ⟶ target) (candidate : context ⟶ source)
    (commutes : candidate ≫ before = candidate ≫ after) :
    context ⟶ equalizerObject before after :=
  classOf
    ⟨.equalizerLift source.code target.code (representative before).code
      (representative after).code context.code (representative candidate).code,
      ⟨.equalizerLift source.formed.some target.formed.some context.formed.some
        (representative before).admitted.some (representative after).admitted.some
        (representative candidate).admitted.some
        (represented_commutativity before after candidate commutes).some⟩⟩

@[simp] theorem equalizerLift_inclusion {source target context : Object signature}
    (before after : source ⟶ target) (candidate : context ⟶ source)
    (commutes : candidate ≫ before = candidate ≫ after) :
    equalizerLift before after candidate commutes ≫ equalizerInclusion before after = candidate := by
  have represented : equalizerLift before after candidate commutes ≫ equalizerInclusion before after =
      classOf (representative candidate) :=
    Quotient.sound ⟨.equalizerBeta source.formed.some target.formed.some context.formed.some
      (representative before).admitted.some (representative after).admitted.some
      (representative candidate).admitted.some
      (represented_commutativity before after candidate commutes).some⟩
  exact represented.trans (classOf_representative candidate)

theorem equalizer_joint_cancel {source target context : Object signature}
    (before after : source ⟶ target) {first second : context ⟶ equalizerObject before after}
    (same : first ≫ equalizerInclusion before after = second ≫ equalizerInclusion before after) :
    first = second := by
  revert same
  refine Quotient.inductionOn₂ first second ?_
  intro first second same
  have represented : Nonempty (Derivation signature (.equation context.code source.code
      (.compose first.code (.equalizerArrow source.code target.code
        (representative before).code (representative after).code))
      (.compose second.code (.equalizerArrow source.code target.code
        (representative before).code (representative after).code)))) :=
    Quotient.exact same
  exact Quotient.sound ⟨.equalizerUniqueness first.admitted.some second.admitted.some represented.some⟩

instance equalizerInclusion_mono {source target : Object signature} (before after : source ⟶ target) :
    Mono (equalizerInclusion before after) where
  right_cancellation _ _ same := equalizer_joint_cancel before after same

def equalizerIsLimit {source target : Object signature} (before after : source ⟶ target) :
    IsLimit (Fork.ofι (equalizerInclusion before after) (equalizer_condition before after)) :=
  Fork.IsLimit.mk _ (fun cone => equalizerLift before after cone.ι cone.condition)
    (fun cone => equalizerLift_inclusion before after cone.ι cone.condition)
    (fun cone _candidate factors =>
      equalizer_joint_cancel before after
        (factors.trans (equalizerLift_inclusion before after cone.ι cone.condition).symm))

instance equalizerHasLimit {source target : Object signature} (before after : source ⟶ target) :
    HasLimit (parallelPair before after) :=
  ⟨⟨Fork.ofι (equalizerInclusion before after) (equalizer_condition before after),
    equalizerIsLimit before after⟩⟩

instance hasEqualizers (signature : Signature (C := C) (symbols := symbols)) :
    HasEqualizers (Object signature) := hasEqualizers_of_hasLimit_parallelPair (Object signature)

instance hasFiniteLimits (signature : Signature (C := C) (symbols := symbols)) :
    HasFiniteLimits (Object signature) := hasFiniteLimits_of_hasEqualizers_and_finite_products

end Mettapedia.CategoryTheory.RelativeClosedSyntax.GeneratedCategory
