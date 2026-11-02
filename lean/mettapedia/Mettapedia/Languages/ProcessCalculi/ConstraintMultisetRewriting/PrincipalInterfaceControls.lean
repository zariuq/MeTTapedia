import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PrincipalInterface
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Controls

/-!
# Fresh helper variables and retained-frame controls

Factoring `x = y` through a fresh helper `h` preserves the problem interface
and an unrelated retained value. It need not preserve a separately specified
old value of `h`. These are concrete substitutions in the existing first-order
term profile, not an assumed property of fresh allocation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PrincipalInterface.Controls

open Mettapedia.Logic.LP
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Controls (signature A)

def problem : EquationStore (Term signature) := [(.var 0, .var 1)]

def helperAnswer : Subst signature := fun name =>
  if name = 0 ∨ name = 1 then .var 2 else .var name

def retained : List (Term signature) := [.var 0, .var 1, .var 3]

theorem helper_answer_is_principal_on_the_retained_interface :
    A.PrincipalOn problem helperAnswer retained := by
  constructor
  · intro equation member
    have same := List.mem_singleton.mp member
    subst equation
    rfl
  · intro candidate solved
    have binding := solved (.var 0, .var 1) (by simp [problem])
    change candidate 0 = candidate 1 at binding
    let residual : Subst signature := fun name => if name = 2 then candidate 0 else candidate name
    refine ⟨residual, ?_⟩
    intro term member
    simp only [retained, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · rfl
    · exact binding.symm
    · rfl

def separated : Subst signature := fun name => if name = 2 then .const 1 else .const 0

theorem separate_old_helper_value_is_a_solution : A.Models separated problem := by
  intro equation member
  have same := List.mem_singleton.mp member
  subst equation
  rfl

/-- A helper already in the observed frame cannot be treated as fresh. -/
theorem existing_helper_value_cannot_be_forgotten :
    ¬ A.PrincipalOn problem helperAnswer [.var 0, .var 1, .var 2] := by
  intro principal
  obtain ⟨residual, through⟩ := principal.factors separated separate_old_helper_value_is_a_solution
  have first := through (.var 0) (by simp)
  have helper := through (.var 2) (by simp)
  change (Term.const (σ := signature) 0) = residual 2 at first
  change (Term.const (σ := signature) 1) = residual 2 at helper
  have impossible := first.trans helper.symm
  cases impossible

theorem introducing_a_helper_does_not_satisfy_all_terms_principality :
    ¬ A.Principal problem helperAnswer := by
  intro principal
  exact existing_helper_value_cannot_be_forgotten (principal.on _ _)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PrincipalInterface.Controls
