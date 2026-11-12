import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.GlbControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.TrueMeetControls

/-!
# The domain condition of the greatest-lower-bound rule is needed

The glb rule (`glbMeet_exact`) lowers both codomains of `λ x. X x ≐ λ x. Y x` to a greatest lower bound `g`, under
the condition `LowersTo`: each unknown's codomain is `g`, or its domain is the annotation's, or its domain lies below
`g`.

**The cross store fails only that condition, and dropping it loses a solution.** Over `X : U0 → U0`,
`Y : U1 → U1`, at `Π (x : U0). U1`:
* `U0` is the greatest lower bound of the codomains `U0` and `U1`, the domains are ordered, and `X` lowers to `U0`
  (`cross_glb`, `cross_lowers_left`);
* `Y` does not: its domain `U1` is neither the annotation's domain `U0` nor below `U0`
  (`cross_not_lowers_right`);
* lowering `Y` to `U1 → U0` anyway loses the solution `X := λ x. x, Y := λ z. z` (`glb_lowering_loses`): its value
  of `Y` returns the local `z : U1`, and no type of `U0` is equal to a variable of `U1` (the tree's
  `var_not_small`).

The cross store has no principal answer at all (the tree's `cross_no_principal`), so no exact rule commits on it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

namespace TreeFibre

namespace Controls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPatternFiring.Controls ContextualDependentSweep.Witnesses

/-- **`U0` is the greatest lower bound of the cross store's codomains `U0` and `U1`.** -/
theorem cross_glb : IsGlb setting.R U0 U0 U1 :=
  ⟨by decide, by decide, by decide, fun _ _ below _ => below⟩

/-- `X : U0 → U0` lowers to `U0`: its codomain is `U0`. -/
theorem cross_lowers_left : LowersTo setting.R U0 U0 U0 U0 := Or.inl rfl

/-- **`Y : U1 → U1` does not lower to `U0`**: its domain is neither `U0` nor below `U0`. -/
theorem cross_not_lowers_right : ¬ LowersTo setting.R U0 U0 U1 U1 := by
  unfold LowersTo
  decide

/-- `Y` declared at `U1 → U0`: lowered to the greatest lower bound (`crossY_declared` is U3's). -/
abbrev crossLowered : Context setting.R where
  arity := ctxCross.arity
  raw := setFamAt ctxCross.raw 0 [U1] U0
  formed := setFamAt_formed ctxCross.raw 0 ctxCross.formed crossY_declared (by decide) (by decide) (by decide)
    (by decide)

/-- The identity on codes, from the lowered telescope. -/
def crossLowerHom : crossLowered ⟶ ctxCross where
  substitution := ids
  typed := setFamAt_substMor ctxCross.raw 0 crossY_declared (by decide) (by decide) (by decide) (by decide)
    crossLowered.formed

/-- **Lowering `Y` to the greatest lower bound loses a solution**: `X := λ x. x, Y := λ z. z` does not factor
through the telescope with `Y : U1 → U0`. -/
theorem glb_lowering_loses :
    ¬ ∃ τ : empty setting.R ⟶ crossLowered, homTypedEquality setting.R crossIdentity (τ ≫ crossLowerHom) := by
  rintro ⟨τ, same⟩
  have equal := same.2 (0 : Fin ctxCross.arity)
  have valueCode : crossIdentity.substitution 0 = .lam (.var 0) := by decide +kernel
  have declaredCode : Presentation.subst crossIdentity.substitution (Ctx.lookup ctxCross.raw 0) =
      .pi (.head U1) (.head U1) := by decide +kernel
  change Equal setting.R (empty setting.R).raw (crossIdentity.substitution 0)
    (τ.substitution (0 : Fin ctxCross.arity))
    (Presentation.subst crossIdentity.substitution (Ctx.lookup ctxCross.raw 0)) at equal
  rw [valueCode, declaredCode] at equal
  have typed := τ.typed (0 : Fin ctxCross.arity)
  change Typed setting.R (empty setting.R).raw (τ.substitution (0 : Fin ctxCross.arity))
    (Presentation.subst τ.substitution (Ctx.lookup (setFamAt ctxCross.raw 0 [U1] U0) 0)) at typed
  rw [lookup_setFamAt_self, famCode_subst] at typed
  have formed : CtxFormed setting.R (.snoc (empty setting.R).raw (.head U1)) :=
    (empty setting.R).formed.snoc (IsType.head_of_universe (by decide))
  have opened := ContextualDependentUniverseInjective.equal_of_lam_left TowerModel.facts (empty setting.R).formed
    equal
  have body : Typed setting.R (.snoc (empty setting.R).raw (.head U1))
      (.app (Presentation.rename wk (τ.substitution (0 : Fin ctxCross.arity))) (.var 0)) (.head U0) :=
    open_typed typed (var_head_typed _ U1)
  exact ContextualDependentUniverseInjective.var_not_small (S := setting) TowerModel.facts TowerModel.roots
    TowerModel.heads TowerModel.algebra ContextualDependentPiSpine.Controls.rigid TowerModel.complete formed
    (i := 0) rfl (by decide) (by decide) (by decide) body ⟨U1, by decide, opened.symm⟩

/-- **Only the domain condition fails**, and the store has no principal answer. -/
theorem lowersTo_needed :
    IsGlb setting.R U0 U0 U1 ∧ setting.R.cumulative U0 U1 ∧ LowersTo setting.R U0 U0 U0 U0 ∧
      ¬ LowersTo setting.R U0 U0 U1 U1 ∧ (frames setting.levels).Solvable crossStore ∧
      (∀ (Δ : Context setting.R) (answer : Δ ⟶ ctxCross), ¬ (frames setting.levels).Principal crossStore answer) :=
  ⟨cross_glb, by decide, cross_lowers_left, cross_not_lowers_right, cross_identity,
    fun _ answer => cross_no_principal answer⟩

end Controls

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
