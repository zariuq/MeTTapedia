import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentConstantShape

/-!
# An actual scoped constraint for argument independence

The two applications are formed under two independent rigid arguments.
The existing scoped interpretation transports this constraint through every
outer substitution. Constant abstraction satisfies it by beta reduction.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentConstantConstraint

open CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentScope ContextualDependentConstantShape

variable {Head : Type} {rules : Rules Head} {Γ : Context rules}

theorem base_code (domain : TypeOver Γ) (term : Tm Head Γ.arity) :
    subst (ContextualDependentParameterExchange.base domain domain).substitution term =
      Presentation.rename wk (Presentation.rename wk term) := by
  change subst (subComp projection projection) term = _
  rw [← subst_subComp, subst_projection, subst_projection]

theorem earlier_code (domain : TypeOver Γ) :
    (ContextualDependentParameterExchange.earlier domain domain).code = .var (0 : Fin (Γ.arity + 1)).succ := by
  rw [ContextualDependentParameterExchange.earlier, pulledNewest_code]
  rfl

theorem later_code (domain : TypeOver Γ) :
    (ContextualDependentParameterExchange.later domain domain).code = .var 0 := by
  exact Term.cast_code _ _

def active (shape : Shape Γ) (function : Term Γ shape.whole) :
    Active (ContextualDependentParameterExchange.context shape.domain shape.domain) :=
  let base := ContextualDependentParameterExchange.base shape.domain shape.domain
  ⟨shape.codomain.reindex base,
    shape.apply base (function.reindex base) (ContextualDependentParameterExchange.earlier shape.domain shape.domain),
    shape.apply base (function.reindex base) (ContextualDependentParameterExchange.later shape.domain shape.domain)⟩

theorem active_left_code (shape : Shape Γ) (function : Term Γ shape.whole) :
    (active shape function).left.code =
      .app (Presentation.rename wk (Presentation.rename wk function.code)) (.var (0 : Fin (Γ.arity + 1)).succ) := by
  change Tm.app (subst (ContextualDependentParameterExchange.base shape.domain shape.domain).substitution function.code)
    (ContextualDependentParameterExchange.earlier shape.domain shape.domain).code = _
  rw [base_code, earlier_code]

theorem active_right_code (shape : Shape Γ) (function : Term Γ shape.whole) :
    (active shape function).right.code =
      .app (Presentation.rename wk (Presentation.rename wk function.code)) (.var 0) := by
  change Tm.app (subst (ContextualDependentParameterExchange.base shape.domain shape.domain).substitution function.code)
    (ContextualDependentParameterExchange.later shape.domain shape.domain).code = _
  rw [base_code, later_code]

theorem active_type_code (shape : Shape Γ) (function : Term Γ shape.whole) :
    (active shape function).type.code = Presentation.rename wk (Presentation.rename wk shape.codomain.code) :=
  base_code shape.domain shape.codomain.code

def Independent (shape : Shape Γ) (function : Term Γ shape.whole) : Prop :=
  Equal rules (ContextualDependentParameterExchange.context shape.domain shape.domain).raw
    (.app (Presentation.rename wk (Presentation.rename wk function.code)) (.var (0 : Fin (Γ.arity + 1)).succ))
    (.app (Presentation.rename wk (Presentation.rename wk function.code)) (.var 0))
    (Presentation.rename wk (Presentation.rename wk shape.codomain.code))

theorem independent_iff_active (shape : Shape Γ) (function : Term Γ shape.whole) :
    Independent shape function ↔ Equal rules (ContextualDependentParameterExchange.context shape.domain shape.domain).raw
      (active shape function).left.code (active shape function).right.code (active shape function).type.code := by
  rw [active_left_code, active_right_code, active_type_code]
  rfl

def constraint (shape : Shape Γ) (function : Term Γ shape.whole) : Scoped Γ :=
  ContextualDependentParameterExchange.problem shape.domain shape.domain (active shape function)

theorem holds_iff {Δ : Context rules} (shape : Shape Γ) (function : Term Γ shape.whole) (solution : Δ ⟶ Γ) :
    (constraint shape function).Holds solution ↔ Independent (shape.reindex solution) (function.reindex solution) := by
  rw [constraint, ContextualDependentParameterExchange.problem_holds_iff]
  unfold Active.Holds
  rw [active_left_code, active_right_code, active_type_code, ContextualDependentParameterExchange.liftBoth_substitution]
  simp only [subst, subst_liftSub_wk, liftSub, Fin.cases_zero, Fin.cases_succ]
  rfl

theorem constant_reindex (shape : Shape Γ) (value : Term Γ shape.codomain) {Δ : Context rules} (base : Δ ⟶ Γ) :
    (shape.constantHere value).reindex base = shape.constant base (value.reindex base) := by
  apply Term.ext
  change subst base.substitution (shape.constantHere value).code = .lam (Presentation.rename wk (subst base.substitution value.code))
  rw [shape.constantHere_code]
  simp only [subst, subst_liftSub_wk]

theorem constant_independent (shape : Shape Γ) (value : Term Γ shape.codomain) :
    Independent shape (shape.constantHere value) := by
  apply (independent_iff_active shape (shape.constantHere value)).mpr
  let base := ContextualDependentParameterExchange.base shape.domain shape.domain
  change Equal rules _ (shape.apply base ((shape.constantHere value).reindex base) _).code
    (shape.apply base ((shape.constantHere value).reindex base) _).code _
  rw [constant_reindex]
  exact (shape.apply_constant base (value.reindex base) _).trans
    (shape.apply_constant base (value.reindex base) _).symm

set_option backward.isDefEq.respectTransparency false in
theorem independent_iff_fresh {L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
    {Γ : Context S.R} (shape : Shape Γ) (function : Term Γ shape.whole) :
    Independent shape function ↔ Equal S.R (ContextualDependentUnaryScope.twice Γ shape.domain).raw
      (Presentation.rename wk (shape.fresh function).code)
      (Presentation.rename (liftRen wk) (shape.fresh function).code)
      (Presentation.rename wk (shape.codomain.reindex (projectionHom Γ shape.domain)).code) := by
  rw [shape.fresh_code]
  change Independent shape function ↔ Equal S.R _ _ _ (Presentation.rename wk (subst projection shape.codomain.code))
  rw [subst_projection]
  unfold Independent
  simp only [Presentation.rename, liftRen, Fin.cases_zero, rename_comp]
  rfl

end ContextualDependentConstantConstraint
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
