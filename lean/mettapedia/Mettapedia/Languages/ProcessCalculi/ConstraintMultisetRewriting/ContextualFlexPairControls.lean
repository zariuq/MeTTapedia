import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFlexPair
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ScopePullbackControls

/-!
# Flexible-pair solving with a genuine shared parameter

`F[x,y] = G[y,z]` is solved by a fresh `H[y]`. A concrete solution contains
an object binder and factors through that helper without capturing its local
variable. Unrelated contextual declarations remain available.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFlexPair.Controls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ScopePullback.Controls
  (base leftMap rightMap pullback)

abbrev others (_ : Nat) : MetaArity base := ([(), ()], ())
abbrev source := sourceDeclarations [(), ()] [(), ()] () others
abbrev target := targetDeclarations [()] () others

theorem left_hole_uses_its_second_parameter :
    answer pullback () others (.inl false) =
      Term.op (S := signature base target) (.inr (.mk (.inl ())))
        (.cons (.var (.succ .zero)) .nil) := rfl

theorem right_hole_uses_its_first_parameter :
    answer pullback () others (.inl true) =
      Term.op (S := signature base target) (.inr (.mk (.inl ())))
        (.cons (.var .zero) .nil) := rfl

theorem other_declarations_are_retained (identity : Nat) :
    answer pullback () others (.inr identity) = generator target (.inr identity) := rfl

theorem the_flexible_pair_is_solved :
    instantiate (answer pullback () others)
        (rename (S := signature base source) leftMap (generator source (.inl false))) =
      instantiate (answer pullback () others)
        (rename (S := signature base source) rightMap (generator source (.inl true))) :=
  sound pullback () others

def pair {Γ : Ctx base} (first second : Term (signature base others) Γ ()) :
    Term (signature base others) Γ () := .op (.inl .pair) (.cons first (.cons second .nil))

def candidate : Assignment source others
  | .inl false => .op (.inl .lam)
      (.cons (pair (.var (.succ (.succ .zero))) (.var .zero)) .nil)
  | .inl true => .op (.inl .lam)
      (.cons (pair (.var (.succ .zero)) (.var .zero)) .nil)
  | .inr identity => generator others identity

def residual : Assignment target others
  | .inl _ => .op (.inl .lam) (.cons (pair (.var (.succ .zero)) (.var .zero)) .nil)
  | .inr identity => generator others identity

theorem binder_containing_candidate_is_a_solution :
    instantiate candidate
        (rename (S := signature base source) leftMap (generator source (.inl false))) =
      instantiate candidate
        (rename (S := signature base source) rightMap (generator source (.inl true))) := rfl

theorem the_candidate_factors_through_the_shared_binder_body :
    ∀ identity, candidate identity = instantiate residual (answer pullback () others identity)
  | .inl false => rfl
  | .inl true => rfl
  | .inr _ => rfl

theorem every_solution_factors_at_every_old_term
    (assignment : Assignment source others)
    (solved : instantiate assignment
        (rename (S := signature base source) leftMap (generator source (.inl false))) =
      instantiate assignment
        (rename (S := signature base source) rightMap (generator source (.inl true)))) :
    ∃ through : Assignment target others,
      ∀ {Γ : Ctx base} {sort : base.Srt} (term : Term (signature base source) Γ sort),
        instantiate assignment term = instantiate through (instantiate (answer pullback () others) term) :=
  factors_all_terms pullback () others others assignment solved

def incompatible : Assignment source others
  | .inl false => .var .zero
  | .inl true => .var .zero
  | .inr identity => generator others identity

/-- The left private `x` and right shared `y` are different ambient
positions; they cannot be identified by the scope-intersection construction. -/
theorem unshared_dependencies_are_not_a_solution :
    instantiate incompatible
        (rename (S := signature base source) leftMap (generator source (.inl false))) ≠
      instantiate incompatible
        (rename (S := signature base source) rightMap (generator source (.inl true))) := by
  intro same
  cases same

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFlexPair.Controls
