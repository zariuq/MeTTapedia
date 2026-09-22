import Mettapedia.Logic.HOL.Syntax.Term

/-!
# Computable equality for intrinsic HOL syntax

Equality compares hidden application, equality, and binder types as well as
their subterms. It is syntactic equality, not beta-eta convertibility.
-/

namespace Mettapedia.Logic.HOL.Term

universe u v

variable {Base : Type u} {Const : Ty Base → Type v}
variable [DecidableEq Base] [∀ τ, DecidableEq (Const τ)]

private def decideEq {Γ : Ctx Base} {τ : Ty Base}
    (a b : Term Const Γ τ) : Decidable (a = b) :=
  match a, b with
  | .var x, .var y => decidable_of_iff (x = y) (by simp)
  | .const c, .const d => decidable_of_iff (c = d) (by simp)
  | @Term.app _ _ _ σ _ f x, @Term.app _ _ _ σ' _ g y =>
      if h : σ = σ' then by
        subst σ'
        letI := decideEq f g
        letI := decideEq x y
        exact decidable_of_iff (f = g ∧ x = y) (by simp)
      else .isFalse (by intro e; injection e; apply h; assumption)
  | .lam x, .lam y =>
      letI := decideEq x y
      decidable_of_iff (x = y) (by simp)
  | .top, .top => .isTrue rfl
  | .bot, .bot => .isTrue rfl
  | .and p q, .and r s =>
      letI := decideEq p r
      letI := decideEq q s
      decidable_of_iff (p = r ∧ q = s) (by simp)
  | .or p q, .or r s =>
      letI := decideEq p r
      letI := decideEq q s
      decidable_of_iff (p = r ∧ q = s) (by simp)
  | .imp p q, .imp r s =>
      letI := decideEq p r
      letI := decideEq q s
      decidable_of_iff (p = r ∧ q = s) (by simp)
  | .not p, .not q =>
      letI := decideEq p q
      decidable_of_iff (p = q) (by simp)
  | @Term.eq _ _ _ σ x y, @Term.eq _ _ _ σ' x' y' =>
      if h : σ = σ' then by
        subst σ'
        letI := decideEq x x'
        letI := decideEq y y'
        exact decidable_of_iff (x = x' ∧ y = y') (by simp)
      else .isFalse (by intro e; injection e; apply h; assumption)
  | @Term.all _ _ σ _ p, @Term.all _ _ σ' _ q =>
      if h : σ = σ' then by
        subst σ'
        letI := decideEq p q
        exact decidable_of_iff (p = q) (by simp)
      else .isFalse (by intro e; injection e; apply h; assumption)
  | @Term.ex _ _ σ _ p, @Term.ex _ _ σ' _ q =>
      if h : σ = σ' then by
        subst σ'
        letI := decideEq p q
        exact decidable_of_iff (p = q) (by simp)
      else .isFalse (by intro e; injection e; apply h; assumption)
  | .var _, .const _ | .var _, .app _ _ | .var _, .lam _ | .var _, .top | .var _, .bot
  | .var _, .and _ _ | .var _, .or _ _ | .var _, .imp _ _ | .var _, .not _ | .var _, .eq _ _
  | .var _, .all _ | .var _, .ex _
      => .isFalse (by intro h; cases h)
  | .const _, .var _ | .const _, .app _ _ | .const _, .lam _ | .const _, .top | .const _, .bot
  | .const _, .and _ _ | .const _, .or _ _ | .const _, .imp _ _ | .const _, .not _
  | .const _, .eq _ _ | .const _, .all _ | .const _, .ex _
      => .isFalse (by intro h; cases h)
  | .app _ _, .var _ | .app _ _, .const _ | .app _ _, .lam _ | .app _ _, .top | .app _ _, .bot
  | .app _ _, .and _ _ | .app _ _, .or _ _ | .app _ _, .imp _ _ | .app _ _, .not _
  | .app _ _, .eq _ _ | .app _ _, .all _ | .app _ _, .ex _
      => .isFalse (by intro h; cases h)
  | .lam _, .var _ | .lam _, .const _ | .lam _, .app _ _ => .isFalse (by intro h; cases h)
  | .top, .var _ | .top, .const _ | .top, .app _ _ | .top, .bot | .top, .and _ _
  | .top, .or _ _ | .top, .imp _ _ | .top, .not _ | .top, .eq _ _ | .top, .all _ | .top, .ex _
      => .isFalse (by intro h; cases h)
  | .bot, .var _ | .bot, .const _ | .bot, .app _ _ | .bot, .top | .bot, .and _ _
  | .bot, .or _ _ | .bot, .imp _ _ | .bot, .not _ | .bot, .eq _ _ | .bot, .all _ | .bot, .ex _
      => .isFalse (by intro h; cases h)
  | .and _ _, .var _ | .and _ _, .const _ | .and _ _, .app _ _ | .and _ _, .top
  | .and _ _, .bot | .and _ _, .or _ _ | .and _ _, .imp _ _ | .and _ _, .not _
  | .and _ _, .eq _ _ | .and _ _, .all _ | .and _ _, .ex _
      => .isFalse (by intro h; cases h)
  | .or _ _, .var _ | .or _ _, .const _ | .or _ _, .app _ _ | .or _ _, .top | .or _ _, .bot
  | .or _ _, .and _ _ | .or _ _, .imp _ _ | .or _ _, .not _ | .or _ _, .eq _ _
  | .or _ _, .all _ | .or _ _, .ex _
      => .isFalse (by intro h; cases h)
  | .imp _ _, .var _ | .imp _ _, .const _ | .imp _ _, .app _ _ | .imp _ _, .top
  | .imp _ _, .bot | .imp _ _, .and _ _ | .imp _ _, .or _ _ | .imp _ _, .not _
  | .imp _ _, .eq _ _ | .imp _ _, .all _ | .imp _ _, .ex _
      => .isFalse (by intro h; cases h)
  | .not _, .var _ | .not _, .const _ | .not _, .app _ _ | .not _, .top | .not _, .bot
  | .not _, .and _ _ | .not _, .or _ _ | .not _, .imp _ _ | .not _, .eq _ _ | .not _, .all _
  | .not _, .ex _
      => .isFalse (by intro h; cases h)
  | .eq _ _, .var _ | .eq _ _, .const _ | .eq _ _, .app _ _ | .eq _ _, .top | .eq _ _, .bot
  | .eq _ _, .and _ _ | .eq _ _, .or _ _ | .eq _ _, .imp _ _ | .eq _ _, .not _
  | .eq _ _, .all _ | .eq _ _, .ex _
      => .isFalse (by intro h; cases h)
  | .all _, .var _ | .all _, .const _ | .all _, .app _ _ | .all _, .top | .all _, .bot
  | .all _, .and _ _ | .all _, .or _ _ | .all _, .imp _ _ | .all _, .not _ | .all _, .eq _ _
  | .all _, .ex _
      => .isFalse (by intro h; cases h)
  | .ex _, .var _ | .ex _, .const _ | .ex _, .app _ _ | .ex _, .top | .ex _, .bot
  | .ex _, .and _ _ | .ex _, .or _ _ | .ex _, .imp _ _ | .ex _, .not _ | .ex _, .eq _ _
  | .ex _, .all _
      => .isFalse (by intro h; cases h)
termination_by structural a

instance {Γ : Ctx Base} {τ : Ty Base} : DecidableEq (Term Const Γ τ) := decideEq

end Mettapedia.Logic.HOL.Term
