import Mettapedia.OSLF.Syntax.BindingScopePullback
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrameControls

/-!
# Shared parameter interfaces beneath object binders

The left interface selects `x,y`; the right selects `y,z`. Their pullback
contains exactly `y`. Concrete terms use that shared position under a fresh
object binder, whose own local position must remain local.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ScopePullback.Controls

open Mettapedia.OSLF.Binding

abbrev base := ContextualFrame.Controls.signature

def leftMap : Ren base [(), ()] [(), (), ()]
  | _, .zero => .zero
  | _, .succ .zero => .succ .zero
  | _, .succ (.succ impossible) => nomatch impossible

def rightMap : Ren base [(), ()] [(), (), ()]
  | _, .zero => .succ .zero
  | _, .succ .zero => .succ (.succ .zero)
  | _, .succ (.succ impossible) => nomatch impossible

def toLeft : Ren base [()] [(), ()]
  | _, .zero => .succ .zero
  | _, .succ impossible => nomatch impossible

def toRight : Ren base [()] [(), ()]
  | _, .zero => .zero
  | _, .succ impossible => nomatch impossible

def recover : ∀ sort (first second : Var [(), ()] sort),
    leftMap sort first = rightMap sort second → Var [()] sort
  | _, .zero, .zero, same => nomatch same
  | _, .zero, .succ .zero, same => nomatch same
  | _, .succ .zero, .zero, _ => .zero
  | _, .succ .zero, .succ .zero, same => nomatch same
  | _, .succ (.succ impossible), _, _ => nomatch impossible
  | _, _, .succ (.succ impossible), _ => nomatch impossible

theorem recover_left : ∀ sort (first second : Var [(), ()] sort)
    (same : leftMap sort first = rightMap sort second), toLeft sort (recover sort first second same) = first
  | _, .zero, .zero, same => nomatch same
  | _, .zero, .succ .zero, same => nomatch same
  | _, .succ .zero, .zero, _ => rfl
  | _, .succ .zero, .succ .zero, same => nomatch same
  | _, .succ (.succ impossible), _, _ => nomatch impossible
  | _, _, .succ (.succ impossible), _ => nomatch impossible

theorem recover_right : ∀ sort (first second : Var [(), ()] sort)
    (same : leftMap sort first = rightMap sort second), toRight sort (recover sort first second same) = second
  | _, .zero, .zero, same => nomatch same
  | _, .zero, .succ .zero, same => nomatch same
  | _, .succ .zero, .zero, _ => rfl
  | _, .succ .zero, .succ .zero, same => nomatch same
  | _, .succ (.succ impossible), _, _ => nomatch impossible
  | _, _, .succ (.succ impossible), _ => nomatch impossible

def pullback : Mettapedia.OSLF.Binding.ScopePullback leftMap rightMap where
  context := [()]
  toLeft := toLeft
  toRight := toRight
  commutes := by
    intro sort position
    cases position with
    | zero => rfl
    | succ impossible => cases impossible
  recover := recover
  recover_left := recover_left
  recover_right := recover_right
  recover_pair := by
    intro sort position
    cases position with
    | zero => rfl
    | succ impossible => cases impossible

def pair {Γ : Ctx base} (first second : Term base Γ ()) : Term base Γ () :=
  .op .pair (.cons first (.cons second .nil))

def leftBody : Term base [(), ()] () :=
  .op .lam (.cons (pair (.var (.succ (.succ .zero))) (.var .zero)) .nil)

def rightBody : Term base [(), ()] () :=
  .op .lam (.cons (pair (.var (.succ .zero)) (.var .zero)) .nil)

def commonBody : Term base [()] () :=
  .op .lam (.cons (pair (.var (.succ .zero)) (.var .zero)) .nil)

theorem under_binder_terms_have_the_same_ambient_image :
    rename (S := base) leftMap leftBody = rename (S := base) rightMap rightBody := rfl

theorem common_body_has_the_required_projections :
    rename (S := base) pullback.toLeft commonBody = leftBody ∧
      rename (S := base) pullback.toRight commonBody = rightBody := ⟨rfl, rfl⟩

theorem the_common_body_is_unique :
    ∃! common : Term base pullback.context (),
      rename (S := base) pullback.toLeft common = leftBody ∧
        rename (S := base) pullback.toRight common = rightBody :=
  pullback.factor_terms_unique leftBody rightBody under_binder_terms_have_the_same_ambient_image

theorem unshared_positions_have_different_ambient_images :
    rename (S := base) leftMap (Term.var .zero) ≠
      rename (S := base) rightMap (Term.var (.succ .zero)) := by
  intro same
  cases same

theorem a_new_object_binder_remains_shared_locally :
    (pullback.liftS [()]).recover () Var.zero Var.zero rfl = Var.zero := rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ScopePullback.Controls
