import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSelfPairControls

/-!
# Sequential contextual solving retains the residual equation

First solve the swapped same-hole equation by a fresh nullary helper. Then
constrain the original hole to a constant. The second solver sees the helper
equation produced by the first answer; the composed answer is principal for
both original equations. The first answer alone does not solve the extra one.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualUnifierComposition.Controls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ScopePullback.Controls (base)
open ContextualSelfPair.Controls
  (others swapped old target problem frameAnswer generated_frame_answer_is_principal)

def root : Unit ⊕ Nat := .inl ()

def constant {Γ : Ctx base} : Term (signature base target) Γ () := .op (.inl .constant) .nil

def extra : EquationStore (Term (signature base old) [(), ()] ()) :=
  [(generator old root, .op (.inl .constant) .nil)]

def emptyMap : Ren base (target root).1 [(), ()] := by
  with_unfolding_all exact fun _ position => nomatch position

def inverseEmpty : Strengthener (S := signature base target) emptyMap where
  un := fun _ _ => none
  un_rho := by with_unfolding_all exact fun _ position => nomatch position
  rho_un := by intro sort position original impossible; cases impossible

def second : Assignment target target := ContextualBinding.answer root constant

theorem residual_equation_is_the_helper_equation :
    ContextualFrameUnifier.mapProblem frameAnswer extra =
      [(rename (S := signature base target) emptyMap (generator target root),
        rename (S := signature base target) emptyMap constant)] := by
  with_unfolding_all rfl

theorem the_second_answer_is_principal_for_the_residual :
    ContextualFrameUnifier.Principal (ContextualFrameUnifier.mapProblem frameAnswer extra) second := by
  rw [residual_equation_is_the_helper_equation]
  exact ContextualUnifierProfiles.binding_on_spine (S := base) root emptyMap inverseEmpty constant
    (by simp [constant, support, supportArgs])

def combined : Assignment old target := Assignment.compose second frameAnswer

theorem the_composed_answer_is_principal_for_both_original_equations :
    ContextualFrameUnifier.Principal (problem ++ extra) combined :=
  ContextualFrameUnifier.Principal.compose generated_frame_answer_is_principal the_second_answer_is_principal_for_the_residual

theorem the_original_hole_becomes_the_required_constant :
    combined root = constant (Γ := [(), ()]) := by with_unfolding_all rfl

theorem omitting_the_residual_equation_is_unsound :
    ¬ ContextualFrameUnifier.Models frameAnswer (problem ++ extra) := by
  intro solved
  have unfinished := solved (generator old root, Term.op (.inl .constant) .nil)
    (by simp [extra])
  with_unfolding_all
    change Term.op (S := signature base target) (.inr (.mk root)) .nil =
      Term.op (S := signature base target) (.inl .constant) .nil at unfinished
  with_unfolding_all cases unfinished

def originalConstant {Γ : Ctx base} : Term (signature base old) Γ () := .op (.inl .constant) .nil

def reverseFirst : Assignment old old := ContextualBinding.answer root originalConstant

theorem reverse_first_is_principal : ContextualFrameUnifier.Principal extra reverseFirst :=
  ContextualUnifierProfiles.binding root originalConstant
    (by simp [originalConstant, support, supportArgs])

theorem reverse_residual_is_reflexive :
    ContextualFrameUnifier.mapProblem reverseFirst problem =
      [(originalConstant (Γ := [(), ()]), originalConstant)] := by
  with_unfolding_all rfl

theorem reverse_second_is_principal :
    ContextualFrameUnifier.Principal (ContextualFrameUnifier.mapProblem reverseFirst problem)
      (generator old) := by
  rw [reverse_residual_is_reflexive]
  constructor
  · intro equation member
    have only := List.mem_singleton.mp member
    subst equation
    rfl
  · intro Future future candidate _
    exact ⟨candidate, fun identity => (instantiate_generator candidate identity).symm⟩

/-- One order prunes the hole's two parameters before binding it. The other
binds first and discharges the now-reflexive swap. The private declaration
arities differ, but all original terms have corresponding future instances. -/
theorem both_orders_preserve_every_original_term :
    ∃ toReverse : Assignment target old, ∃ toForward : Assignment old target,
      (∀ {Γ : Ctx base} (term : Term (signature base old) Γ ()),
        instantiate toReverse (instantiate combined term) =
          instantiate (Assignment.compose (generator old) reverseFirst) term) ∧
      (∀ {Γ : Ctx base} (term : Term (signature base old) Γ ()),
        instantiate toForward (instantiate (Assignment.compose (generator old) reverseFirst) term) =
          instantiate combined term) := by
  obtain ⟨toReverse, toForward, forward, backward⟩ :=
    ContextualFrameUnifier.Principal.solve_orders generated_frame_answer_is_principal
      the_second_answer_is_principal_for_the_residual reverse_first_is_principal reverse_second_is_principal
  exact ⟨toReverse, toForward, fun term => forward term, fun term => backward term⟩

theorem the_private_root_arities_differ : (target root).1.length = 0 ∧ (old root).1.length = 2 := by
  constructor <;> with_unfolding_all rfl

def underBinder : Term (signature base old) [] () :=
  .op (.inl .lam) (.cons (.op (.inr (.mk root))
    (.cons (.var .zero) (.cons (.var .zero) .nil))) .nil)

theorem both_orders_act_under_a_real_binder :
    instantiate combined underBinder =
      (.op (.inl .lam) (.cons (constant (Γ := [()])) .nil) : Term (signature base target) [] ()) ∧
    instantiate (Assignment.compose (generator old) reverseFirst) underBinder =
      (.op (.inl .lam) (.cons (originalConstant (Γ := [()])) .nil) : Term (signature base old) [] ()) := by
  constructor <;> with_unfolding_all rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualUnifierComposition.Controls
