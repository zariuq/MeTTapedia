import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RunRearrangementRawSuffix
import Mathlib.CategoryTheory.EqToHom

/-!
# Composition of the displayed continuation action

Continuations are transported along actual raw comparison paths. Successive
paths transport the same complete continuation as their concatenation, and
the extended comparison cells compose after that endpoint equality. These
are laws of the displayed path action; no descent through cancellation of
the source comparison certificate is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Transport.RunRearrangement

open _root_.CategoryTheory

universe uO uT uH uOcc uS uF uI

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF}
  {P : Step X O State Firing} {T : Transport.{uO,uT,uH,uOcc,uS,uF,uI} P} {start : State}

theorem tailThrough_identity (run : Object T start) (continuation : P.Run run.last) :
    tailThrough (rawIdentity run) continuation = continuation := rfl

theorem tailThrough_comp {first middle last : Object T start}
    (early : RawCell T first middle) (later : RawCell T middle last) (continuation : P.Run first.last) :
    tailThrough (early.comp later) continuation = tailThrough later (tailThrough early continuation) := by
  induction later with
  | nil => rfl
  | cons path edge ih => exact congrArg (T.moveRun (Oriented.boundary edge)) ih

theorem rightEdge_continuation {first second : Object T start} (edge : Oriented T first second)
    {one two : P.Run first.last} (same : one = two) : HEq (rightEdge edge one) (rightEdge edge two) := by
  cases same
  rfl

theorem rightCell_identity (run : Object T start) (continuation : P.Run run.last) :
    rightCell (rawIdentity run) continuation = 𝟙 (object T (run.append continuation)) := rfl

theorem rightCell_comp {first middle last : Object T start}
    (early : RawCell T first middle) (later : RawCell T middle last) (continuation : P.Run first.last) :
    HEq (rightCell (early.comp later) continuation)
      (rightCell early continuation ≫ rightCell later (tailThrough early continuation)) := by
  induction later with
  | nil => exact heq_of_eq (Category.comp_id (rightCell early continuation)).symm
  | @cons before after path edge ih =>
      have sameTail := tailThrough_comp early path continuation
      have sameMiddle := congrArg (fun tail => object T (before.append tail)) sameTail
      have sameLast := congrArg (fun tail => object T (after.append (T.moveRun (Oriented.boundary edge) tail))) sameTail
      have composition := heq_comp (C := Groupoid T start) rfl sameMiddle sameLast ih
        (rightEdge_continuation edge sameTail)
      exact composition.trans (heq_of_eq (Category.assoc _ _ _))

theorem position_comp {first middle last : Object T start}
    (early : RawCell T first middle) (later : RawCell T middle last) (index : Nat) :
    rawPosition (early.comp later) index = rawPosition later (rawPosition early index) := by
  induction later with
  | nil => rfl
  | cons path edge ih => exact congrArg (Oriented.position edge) ih

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Transport.RunRearrangement

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Transport.RunRearrangement.rightCell_comp
