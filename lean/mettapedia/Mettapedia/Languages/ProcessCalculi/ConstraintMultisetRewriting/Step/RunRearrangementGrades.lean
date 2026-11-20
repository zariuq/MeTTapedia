import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RunRearrangementRawSuffix

/-!
# Grades of finite comparison certificates

The predicate checks every run visited by a raw certificate. It composes
along certificates and is invariant under reversal. It is not automatically
invariant under inserting an inverse-cancelling detour through another run.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Transport.RunRearrangement

universe uO uT uH uOcc uS uF uI

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF}
  {P : Step X O State Firing} {T : Transport.{uO,uT,uH,uOcc,uS,uF,uI} P}
  {start : State}

def Within (grade : Object T start → Prop) {first second : Object T start}
    (path : RawCell T first second) : Prop := by
  induction path with
  | nil => exact grade first
  | @cons middle target earlier edge ih => exact ih ∧ grade target

theorem Within.atStart {grade : Object T start → Prop} {first second : Object T start}
    {path : RawCell T first second} (inside : Within grade path) : grade first := by
  induction path with
  | nil => exact inside
  | cons earlier edge ih => exact ih inside.1

theorem Within.last {grade : Object T start → Prop} {first second : Object T start}
    {path : RawCell T first second} (inside : Within grade path) : grade second := by
  cases path with
  | nil => exact inside
  | cons => exact inside.2

theorem within_comp (grade : Object T start → Prop) {first middle last : Object T start}
    (early : RawCell T first middle) (later : RawCell T middle last) :
    Within grade (early.comp later) ↔ Within grade early ∧ Within grade later := by
  induction later with
  | nil => exact ⟨fun inside => ⟨inside, inside.last⟩, fun inside => inside.1⟩
  | @cons source target path edge ih =>
      change (Within grade (early.comp path) ∧ grade target) ↔
        Within grade early ∧ (Within grade path ∧ grade target)
      exact (and_congr ih Iff.rfl).trans and_assoc

theorem within_reverse (grade : Object T start → Prop) {first last : Object T start}
    (path : RawCell T first last) : Within grade (rawReverse path) ↔ Within grade path := by
  induction path with
  | nil => rfl
  | @cons middle target earlier edge ih =>
      let backwardEdge : RawCell T target middle := Oriented.toPath (T := T) edge.swap
      change Within grade (backwardEdge.comp (rawReverse earlier)) ↔ Within grade earlier ∧ grade target
      refine (within_comp grade backwardEdge (rawReverse earlier)).trans ?_
      change ((grade target ∧ grade middle) ∧ Within grade (rawReverse earlier)) ↔
        Within grade earlier ∧ grade target
      exact ⟨fun inside => ⟨ih.mp inside.2, inside.1.1⟩,
        fun inside => ⟨⟨inside.2, inside.1.last⟩, ih.mpr inside.1⟩⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Transport.RunRearrangement

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Transport.RunRearrangement.within_comp
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Transport.RunRearrangement.within_reverse
