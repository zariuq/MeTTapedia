import Mettapedia.CategoryTheory.RelativeClosedSyntaxPresentedEqualizers
import Mettapedia.CategoryTheory.RelativeClosedSyntaxRawOperations

/-!
# Pullbacks of independently authored raw arrows

The matching object is the equalizer of the two endpoint maps on a product.
Its complete raw projections, lifts and uniqueness earn the actual pullback
universal property. The comparison with the chosen pullback retains both
projections and does not identify the two raw object presentations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.GeneratedCategory.PresentedPullback

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v a

variable {C : Type u} [Category.{v} C] {symbols : Symbols.{a}}
variable {signature : Signature (C := C) (symbols := symbols)}
variable {left right target : Object signature}

def before (first : RawHom left target) (_second : RawHom right target) :
    RawHom (product left right) target := (RawHom.first left right).compose first

def after (_first : RawHom left target) (second : RawHom right target) :
    RawHom (product left right) target := (RawHom.second left right).compose second

def object (first : RawHom left target) (second : RawHom right target) : Object signature :=
  PresentedEqualizer.object (before first second) (after first second)

def inclusion (first : RawHom left target) (second : RawHom right target) :
    RawHom (object first second) (product left right) :=
  ⟨.equalizerArrow (product left right).code target.code
      (before first second).code (after first second).code,
    ⟨.equalizerArrow (product left right).formed.some target.formed.some
      (before first second).admitted.some (after first second).admitted.some⟩⟩

def first (before : RawHom left target) (after : RawHom right target) :
    RawHom (object before after) left := (inclusion before after).compose (RawHom.first left right)

def second (before : RawHom left target) (after : RawHom right target) :
    RawHom (object before after) right := (inclusion before after).compose (RawHom.second left right)

@[simp] theorem inclusion_class (before : RawHom left target) (after : RawHom right target) :
    classOf (inclusion before after) =
      PresentedEqualizer.inclusion (PresentedPullback.before before after) (PresentedPullback.after before after) := rfl

@[simp] theorem raw_first_class (left right : Object signature) :
    classOf (RawHom.first left right) = GeneratedCategory.first left right := rfl

@[simp] theorem raw_second_class (left right : Object signature) :
    classOf (RawHom.second left right) = GeneratedCategory.second left right := rfl

theorem condition (before : RawHom left target) (after : RawHom right target) :
    classOf ((first before after).compose before) = classOf ((second before after).compose after) := by
  simpa only [first, second, PresentedPullback.before, PresentedPullback.after,
    classOf_compose, inclusion_class, raw_first_class, raw_second_class, Category.assoc] using
    PresentedEqualizer.condition (PresentedPullback.before before after) (PresentedPullback.after before after)

private theorem matchingDerivation {context : Object signature}
    (before : RawHom left target) (after : RawHom right target)
    (left : RawHom context left) (right : RawHom context right)
    (matching : classOf (left.compose before) = classOf (right.compose after)) :
    Nonempty (Derivation signature (.equation context.code target.code
      (.compose (RawHom.pair left right).code (PresentedPullback.before before after).code)
        (.compose (RawHom.pair left right).code (PresentedPullback.after before after).code))) := by
  have same : classOf ((RawHom.pair left right).compose (PresentedPullback.before before after)) =
      classOf ((RawHom.pair left right).compose (PresentedPullback.after before after)) := by
    simpa only [classOf_compose, PresentedPullback.before, PresentedPullback.after,
      RawHom.classOf_pair, classOf_compose, raw_first_class, raw_second_class, ← Category.assoc,
      pairing_first, pairing_second] using matching
  exact classOf_eq_iff.mp same

def lift {context : Object signature} (before : RawHom left target) (after : RawHom right target)
    (left : RawHom context left) (right : RawHom context right)
    (matching : classOf (left.compose before) = classOf (right.compose after)) :
    RawHom context (object before after) :=
  ⟨.equalizerLift (product _ _).code target.code
      (PresentedPullback.before before after).code (PresentedPullback.after before after).code
      context.code (RawHom.pair left right).code,
    ⟨.equalizerLift (product _ _).formed.some target.formed.some context.formed.some
      (PresentedPullback.before before after).admitted.some
      (PresentedPullback.after before after).admitted.some (RawHom.pair left right).admitted.some
      (matchingDerivation before after left right matching).some⟩⟩

@[simp] theorem lift_inclusion {context : Object signature}
    (before : RawHom left target) (after : RawHom right target)
    (left : RawHom context left) (right : RawHom context right)
    (matching : classOf (left.compose before) = classOf (right.compose after)) :
    classOf ((lift before after left right matching).compose (inclusion before after)) =
      classOf (RawHom.pair left right) := by
  apply Quotient.sound
  exact ⟨.equalizerBeta (product _ _).formed.some target.formed.some context.formed.some
    (PresentedPullback.before before after).admitted.some
    (PresentedPullback.after before after).admitted.some (RawHom.pair left right).admitted.some
    (matchingDerivation before after left right matching).some⟩

@[simp] theorem lift_first {context : Object signature}
    (before : RawHom left target) (after : RawHom right target)
    (left : RawHom context left) (right : RawHom context right)
    (matching : classOf (left.compose before) = classOf (right.compose after)) :
    classOf ((lift before after left right matching).compose (first before after)) = classOf left := by
  rw [classOf_compose, first, classOf_compose, ← Category.assoc, ← classOf_compose,
    lift_inclusion, RawHom.classOf_pair, raw_first_class, pairing_first]

@[simp] theorem lift_second {context : Object signature}
    (before : RawHom left target) (after : RawHom right target)
    (left : RawHom context left) (right : RawHom context right)
    (matching : classOf (left.compose before) = classOf (right.compose after)) :
    classOf ((lift before after left right matching).compose (second before after)) = classOf right := by
  rw [classOf_compose, second, classOf_compose, ← Category.assoc, ← classOf_compose,
    lift_inclusion, RawHom.classOf_pair, raw_second_class, pairing_second]

theorem joint_cancel {context : Object signature}
    (before : RawHom left target) (after : RawHom right target)
    {first second : context ⟶ object before after}
    (left : first ≫ classOf (PresentedPullback.first before after) =
      second ≫ classOf (PresentedPullback.first before after))
    (right : first ≫ classOf (PresentedPullback.second before after) =
      second ≫ classOf (PresentedPullback.second before after)) : first = second := by
  apply PresentedEqualizer.joint_cancel (PresentedPullback.before before after) (PresentedPullback.after before after)
  apply product_joint_cancel
  · simpa only [PresentedPullback.first, classOf_compose, inclusion_class, raw_first_class,
      Category.assoc] using left
  · simpa only [PresentedPullback.second, classOf_compose, inclusion_class, raw_second_class,
      Category.assoc] using right

def isLimit (before : RawHom left target) (after : RawHom right target) :
    IsLimit (PullbackCone.mk (classOf (first before after)) (classOf (second before after))
      (by simpa only [classOf_compose] using condition before after)) :=
  PullbackCone.IsLimit.mk _
    (fun cone => classOf (lift before after (representative cone.fst) (representative cone.snd)
      (by simpa only [classOf_compose, classOf_representative] using cone.condition)))
    (fun cone => by
      simpa only [← classOf_compose, classOf_representative] using
        lift_first before after (representative cone.fst) (representative cone.snd)
          (by simpa only [classOf_compose, classOf_representative] using cone.condition))
    (fun cone => by
      simpa only [← classOf_compose, classOf_representative] using
        lift_second before after (representative cone.fst) (representative cone.snd)
          (by simpa only [classOf_compose, classOf_representative] using cone.condition))
    (fun cone _candidate left right => by
      apply joint_cancel before after
      · exact left.trans (by
          simpa only [← classOf_compose, classOf_representative] using
            (lift_first before after (representative cone.fst) (representative cone.snd)
              (by simpa only [classOf_compose, classOf_representative] using cone.condition)).symm)
      · exact right.trans (by
          simpa only [← classOf_compose, classOf_representative] using
            (lift_second before after (representative cone.fst) (representative cone.snd)
              (by simpa only [classOf_compose, classOf_representative] using cone.condition)).symm))

def chosenComparison (before : RawHom left target) (after : RawHom right target) :
    object before after ≅ pullback (classOf before) (classOf after) :=
  (isLimit before after).conePointUniqueUpToIso
    (limit.isLimit (@cospan (Object signature) (category signature) left right target (classOf before) (classOf after)))

@[simp] theorem chosenComparison_first (before : RawHom left target) (after : RawHom right target) :
    (chosenComparison before after).hom ≫ pullback.fst _ _ = classOf (first before after) :=
  (isLimit before after).conePointUniqueUpToIso_hom_comp
    (limit.isLimit (@cospan (Object signature) (category signature) left right target (classOf before) (classOf after))) WalkingCospan.left

@[simp] theorem chosenComparison_second (before : RawHom left target) (after : RawHom right target) :
    (chosenComparison before after).hom ≫ pullback.snd _ _ = classOf (second before after) :=
  (isLimit before after).conePointUniqueUpToIso_hom_comp
    (limit.isLimit (@cospan (Object signature) (category signature) left right target (classOf before) (classOf after))) WalkingCospan.right

end Mettapedia.CategoryTheory.RelativeClosedSyntax.GeneratedCategory.PresentedPullback
