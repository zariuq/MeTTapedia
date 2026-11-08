import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentUnaryRecovery
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentNormalCheckingTower
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentScope
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerDecidability

/-!
# Typed constancy follows from equality at two fresh arguments

For the pure cumulative tower, extraction succeeds at a sufficient budget
for every independently typed body and every formed outer context. Applied
to a function's fresh application, this yields a value in the outer context
and a typed eta equality between the function and its constant abstraction.
No inhabitant of the argument type is chosen.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentUnaryConstancy

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open TypedContextual.DependentTypes TypedContextual.QuotientComprehensionSyntax
open ContextualDependentUnaryScope

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head}

noncomputable def constant (levels : LevelModel rules L) {Γ : Context rules}
    (domain codomain : TypeOver Γ) (value : Term Γ codomain) :
    Term Γ (rawPi levels domain (codomain.reindex (projectionHom Γ domain))) :=
  Products.rawLam levels (value.reindex (projectionHom Γ domain))

theorem constant_of_recovery (levels : LevelModel rules L) {Γ : Context rules}
    (domain codomain : TypeOver Γ)
    (function : Term Γ (rawPi levels domain (codomain.reindex (projectionHom Γ domain))))
    (recovered : ContextualDependentProjectionInversion.Recovery levels (projectionHom Γ domain) codomain
      (⟨_, Products.rawFreshApp levels function⟩ : TotalTerm (extend Γ domain))) :
    Equal rules Γ.raw function.code (constant levels domain codomain recovered.body).code
      (rawPi levels domain (codomain.reindex (projectionHom Γ domain))).code := by
  have bodies := recovered.solves.2.symm
  have lambdas := Products.rawLam_congruent levels (Products.rawFreshApp levels function)
    (recovered.body.reindex (projectionHom Γ domain)) bodies
  have functions := (Products.rawEta levels function).symm.trans lambdas
  exact ((QTerm.mk_eq_iff levels _ _).mp functions).2

section Tower

variable {L : Type} [UniverseLevel.LevelOrder L] (valuation : Nat → L)

theorem rigid_constants (name : DeclName) : (TowerModel.setting valuation).roles name = .rigid := rfl

theorem declarations_formed : DeclaredTypesFormed (LevelTower.rules L) := by
  intro name type known
  cases known

def recover (fuel : Nat) (Γ : Context (LevelTower.rules L)) (domain codomain : TypeOver Γ)
    (value : Term (extend Γ domain) (codomain.reindex (projectionHom Γ domain)))
    (same : Equal (LevelTower.rules L) (twice (S := TowerModel.setting valuation) Γ domain).raw
      (Presentation.rename wk value.code) (Presentation.rename (liftRen wk) value.code)
      (Presentation.rename wk (codomain.reindex (projectionHom Γ domain)).code)) :=
  ContextualDependentUnaryRecovery.recover (S := TowerModel.setting valuation) (rigid_constants valuation)
    TowerModel.complete TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentNormalCheckingTower.head_typing_unique declarations_formed fuel Γ domain codomain value same

theorem eventually_recovers (Γ : Context (LevelTower.rules L)) (domain codomain : TypeOver Γ)
    (value : Term (extend Γ domain) (codomain.reindex (projectionHom Γ domain)))
    (same : Equal (LevelTower.rules L) (twice (S := TowerModel.setting valuation) Γ domain).raw
      (Presentation.rename wk value.code) (Presentation.rename (liftRen wk) value.code)
      (Presentation.rename wk (codomain.reindex (projectionHom Γ domain)).code)) :
    ∃ fuel, ∀ larger, fuel ≤ larger → (recover valuation larger Γ domain codomain value same).isSome = true := by
  obtain ⟨fuel, result, _, stable⟩ := ContextualDependentTowerBudget.term_eventually_stable value
  refine ⟨fuel, fun larger enough => ?_⟩
  apply (ContextualDependentUnaryRecovery.success_iff (S := TowerModel.setting valuation) (rigid_constants valuation)
    TowerModel.complete TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentNormalCheckingTower.head_typing_unique declarations_formed larger Γ domain codomain value same).mpr
  exact congrArg Option.isSome (stable larger enough)

theorem function_constancy (Γ : Context (LevelTower.rules L)) (domain codomain : TypeOver Γ)
    (function : Term Γ (rawPi (TowerModel.setting valuation).levels domain (codomain.reindex (projectionHom Γ domain))))
    (same : Equal (LevelTower.rules L) (twice (S := TowerModel.setting valuation) Γ domain).raw
      (Presentation.rename wk (Products.rawFreshApp (TowerModel.setting valuation).levels function).code)
      (Presentation.rename (liftRen wk) (Products.rawFreshApp (TowerModel.setting valuation).levels function).code)
      (Presentation.rename wk (codomain.reindex (projectionHom Γ domain)).code)) :
    ∃ value : Term Γ codomain, Equal (LevelTower.rules L) Γ.raw function.code
      (constant (TowerModel.setting valuation).levels domain codomain value).code
      (rawPi (TowerModel.setting valuation).levels domain (codomain.reindex (projectionHom Γ domain))).code := by
  obtain ⟨fuel, succeeds⟩ := eventually_recovers valuation Γ domain codomain
    (Products.rawFreshApp (TowerModel.setting valuation).levels function) same
  obtain ⟨recovered, _⟩ := Option.isSome_iff_exists.mp (succeeds fuel le_rfl)
  exact ⟨recovered.body, constant_of_recovery (TowerModel.setting valuation).levels domain codomain function recovered⟩

end Tower
end ContextualDependentUnaryConstancy
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
