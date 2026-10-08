import Mettapedia.CategoryTheory.GroundPathRelativePushout

/-!
# Distinct one-frame contexts can have the same ground value and be minimal

The universal property depends on typed paths, rather than injectivity of
their ground action. Distinct final edges cannot have a removable nonempty
common outer path. The proof checks every competing commuting candidate.
-/

set_option autoImplicit false

namespace Mettapedia.CategoryTheory.GroundPath

open _root_.CategoryTheory
open Mettapedia.GSLT.RelativePushout

universe u v w

variable {V : Type u} [Quiver.{v} V] (action : Action.{u,v,w} V)

theorem distinct_single_frames_ipo {source target : V}
    (first second : source ⟶ target) (different : first ≠ second)
    (left right : action.Value source)
    (square : valueArrow action left ≫ contextArrow action first.toPath =
      valueArrow action right ≫ contextArrow action second.toPath) :
    IsIdemPushout (valueArrow action left) (valueArrow action right)
      (contextArrow action first.toPath) (contextArrow action second.toPath) square := by
  have commutes : action.path first.toPath left = action.path second.toPath right := Arrow.value.inj square
  let selected : PathCandidate action left right first.toPath second.toPath := PathCandidate.self commutes
  apply selected.categorical_isRelativePushout
  intro other
  change other.down.length ≤ 0
  rcases other with ⟨apex, inl, inr, down, _, facLeft, facRight⟩
  change down.length ≤ 0
  have countedLeft := congrArg Quiver.Path.length facLeft
  have countedRight := congrArg Quiver.Path.length facRight
  simp only [Quiver.Path.length_comp, Quiver.Path.length_toPath] at countedLeft countedRight
  by_contra nonzero
  have leftZero : inl.length = 0 := by omega
  have rightZero : inr.length = 0 := by omega
  have same := Quiver.Path.eq_of_length_zero inl leftZero
  subst apex
  have leftNil := Quiver.Path.eq_nil_of_length_zero inl leftZero
  have rightNil := Quiver.Path.eq_nil_of_length_zero inr rightZero
  rw [leftNil, Quiver.Path.nil_comp] at facLeft
  rw [rightNil, Quiver.Path.nil_comp] at facRight
  have paths : first.toPath = second.toPath := facLeft.symm.trans facRight
  exact different (eq_of_heq (Quiver.Path.hom_heq_of_cons_eq_cons paths))

end Mettapedia.CategoryTheory.GroundPath
