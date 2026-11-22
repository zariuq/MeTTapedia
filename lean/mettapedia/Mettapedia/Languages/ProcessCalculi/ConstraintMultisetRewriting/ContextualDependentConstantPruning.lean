import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentConstantConstraint
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentScopedDispatch

/-!
# Replacing an argument-independent function metavariable

The source context contains F:A->C; the target retains the outer context
and replaces F by H:C. The answer substitution is F := lambda x.H.
The source constraint is the actual scoped equation F x = F y under two
fresh arguments, rather than an assumed absence of an argument dependency.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentConstantShape

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentScope
open ContextualDependentConstantShape ContextualDependentConstantConstraint

variable {Head : Type} {rules : Rules Head} {Γ : Context rules}

namespace Shape

variable (shape : ContextualDependentConstantShape.Shape Γ)

abbrev source := extend Γ shape.whole
abbrev target := extend Γ shape.codomain

def answer : shape.target ⟶ shape.source :=
  pair (projectionHom Γ shape.codomain)
    (shape.constant (projectionHom Γ shape.codomain) (newest Γ shape.codomain))

theorem answer_projection : shape.answer ≫ projectionHom Γ shape.whole = projectionHom Γ shape.codomain :=
  pair_projection _ _

theorem answer_zero : shape.answer.substitution 0 = .lam (.var (0 : Fin (Γ.arity + 1)).succ) := rfl

theorem answer_succ (index : Fin Γ.arity) : shape.answer.substitution index.succ = .var index.succ := rfl

def problem : Scoped shape.source :=
  constraint (shape.reindex (projectionHom Γ shape.whole)) (newest Γ shape.whole)

set_option backward.isDefEq.respectTransparency false in
theorem problem_holds_iff {Δ : Context rules} (solution : Δ ⟶ shape.source) :
    shape.problem.Holds solution ↔
      Independent (shape.reindex (solution ≫ projectionHom Γ shape.whole)) (pulledNewest solution) := by
  rw [problem, holds_iff]
  unfold Independent
  simp only [ContextualDependentConstantShape.Shape.reindex]
  rw [← TypeOver.reindex_comp]
  simp only [Term.reindex, TypeOver.reindex, newest, subst, pulledNewest_code, subst_subComp]
  rfl

theorem factors_of_constant {Δ : Context rules} (solution : Δ ⟶ shape.source)
    (value : Term Δ (shape.codomain.reindex (solution ≫ projectionHom Γ shape.whole)))
    (same : Equal rules Δ.raw (pulledNewest solution).code
      (shape.constant (solution ≫ projectionHom Γ shape.whole) value).code
      (shape.whole.reindex (solution ≫ projectionHom Γ shape.whole)).code) :
    homTypedEquality rules solution (pair (solution ≫ projectionHom Γ shape.whole) value ≫ shape.answer) := by
  refine ⟨solution.typed, fun index => ?_⟩
  refine Fin.cases ?_ (fun index => ?_) index
  · rw [pulledNewest_code] at same
    change Equal rules Δ.raw (solution.substitution 0) (.lam (Presentation.rename wk value.code))
      (subst (subComp solution.substitution projection) shape.whole.code) at same
    change Equal rules Δ.raw (solution.substitution 0)
      (subst (consSub value.code (subComp solution.substitution projection)) (shape.answer.substitution 0))
      (subst solution.substitution (Presentation.rename wk shape.whole.code))
    rw [shape.answer_zero]
    simp only [subst, liftSub, Fin.cases_succ, consSub_zero]
    rw [← subst_projection shape.whole.code, subst_subComp]
    exact same
  · change Equal rules Δ.raw (solution.substitution index.succ)
      (subst (consSub value.code (subComp solution.substitution projection)) (shape.answer.substitution index.succ))
      (subst solution.substitution (Ctx.lookup shape.source.raw index.succ))
    rw [shape.answer_succ]
    exact .refl (solution.typed index.succ)

set_option backward.isDefEq.respectTransparency false in
theorem problem_pair {Δ : Context rules} (base : Δ ⟶ Γ) (function : Term Δ (shape.whole.reindex base)) :
    shape.problem.Holds (pair base function) ↔ Independent (shape.reindex base) function := by
  rw [shape.problem_holds_iff]
  simp only [Independent, ContextualDependentConstantShape.Shape.reindex, pair_projection, pulledNewest_code]
  rfl

theorem problem_constant {Δ : Context rules} (base : Δ ⟶ Γ) (value : Term Δ (shape.codomain.reindex base)) :
    shape.problem.Holds (pair base (shape.constant base value)) := by
  apply (shape.problem_pair base (shape.constant base value)).mpr
  have independent := constant_independent (shape.reindex base) value
  have same : (shape.reindex base).constantHere value = shape.constant base value :=
    Term.ext ((shape.reindex base).constantHere_code value)
  rw [same] at independent
  exact independent

theorem answer_sound : shape.problem.Holds shape.answer :=
  shape.problem_constant (projectionHom Γ shape.codomain) (newest Γ shape.codomain)

end Shape
end ContextualDependentConstantShape
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
