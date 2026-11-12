import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.GlbMeet
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.FamilyControls

/-!
# Controls for the greatest lower bound, in the tree's tower

* **Two level variables have the least level as greatest lower bound** (`eval_le_zeroed`, `glb_Ua_Ub`). The tower's
  cumulativity is semantic. A level below `a` and below `b` at every valuation is zero at the valuations that send
  `a`, or `b`, to zero; and at every valuation a level expression is below the larger of these two values.
* **Greatest lower bounds, positive and negative** (`glb_U1_U2`, `not_glb_U0_U1_U2`): `U1` is one of `U1` and `U2`;
  `U0` is a lower bound of them that is not the greatest.
* **The store the families solver postpones has a principal answer** (`level_glbMeets`, `level_glb_principal`): over
  `X : U0 → U_a, Y : U0 → U_b`, the equation `λ x. X x ≐ λ x. Y x` at `Π (x : U0). U_{max a b}`, on which the
  families solver is stuck (`level_stuck`), is solved by lowering both unknowns to `U0 → U0`, then `X := λ x. Y x`.
* **A family that does not lower by the rule's condition** (`lowers_outside`): `U1 → U_a`, at the annotation's domain
  `U0`, towards `U0`: its codomain is not `U0`, and its domain is neither `U0` nor below it.
* **Least universes** (`least_U0`, `not_least_U0_U2`): `U1` is the least universe of `U0`; `U2` is a universe of `U0`
  that is not the least.
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
open UniverseLevel (LevelExpr)

/-! ## The greatest lower bound of two level variables -/

/-- At every valuation, a level expression is below the larger of its values with the first, or the second, level
variable sent to zero. -/
theorem eval_le_zeroed (v : Nat → Nat) : ∀ ℓ : LevelExpr Nat,
    LevelExpr.eval v ℓ ≤
      max (LevelExpr.eval (Function.update v 0 0) ℓ) (LevelExpr.eval (Function.update v 1 0) ℓ)
  | .const c => by
      change c ≤ max c c
      omega
  | .param i => by
      change v i ≤ max (Function.update v 0 0 i) (Function.update v 1 0 i)
      by_cases h0 : i = 0
      · subst h0
        have first : Function.update v 1 0 0 = v 0 := Function.update_of_ne (by decide) _ _
        omega
      · have second : Function.update v 0 0 i = v i := Function.update_of_ne h0 _ _
        omega
  | .succ ℓ => by
      have ih := eval_le_zeroed v ℓ
      change LevelExpr.eval v ℓ + 1 ≤
        max (LevelExpr.eval (Function.update v 0 0) ℓ + 1) (LevelExpr.eval (Function.update v 1 0) ℓ + 1)
      omega
  | .max ℓ₁ ℓ₂ => by
      have ih₁ := eval_le_zeroed v ℓ₁
      have ih₂ := eval_le_zeroed v ℓ₂
      change max (LevelExpr.eval v ℓ₁) (LevelExpr.eval v ℓ₂) ≤
        max (max (LevelExpr.eval (Function.update v 0 0) ℓ₁) (LevelExpr.eval (Function.update v 0 0) ℓ₂))
          (max (LevelExpr.eval (Function.update v 1 0) ℓ₁) (LevelExpr.eval (Function.update v 1 0) ℓ₂))
      omega

/-- **`U0` is a greatest lower bound of `U_a` and `U_b`.** -/
theorem glb_Ua_Ub : IsGlb setting.R U0 Ua Ub := by
  refine ⟨by decide, by decide, by decide, fun u hu belowA belowB => ?_⟩
  cases hu with
  | sort ℓ =>
      intro w
      have ha : LevelExpr.eval (Function.update w 0 0) ℓ ≤ Function.update w 0 0 0 := belowA (Function.update w 0 0)
      have hb : LevelExpr.eval (Function.update w 1 0) ℓ ≤ Function.update w 1 0 1 := belowB (Function.update w 1 0)
      have za : Function.update w 0 0 0 = 0 := Function.update_self _ _ _
      have zb : Function.update w 1 0 1 = 0 := Function.update_self _ _ _
      have key := eval_le_zeroed w ℓ
      change LevelExpr.eval w ℓ ≤ 0
      omega

/-- **Comparable universes**: the smaller one is a greatest lower bound. -/
theorem glb_U1_U2 : IsGlb setting.R U1 U1 U2 := ⟨by decide, by decide, by decide, fun _ _ below _ => below⟩

/-- **A lower bound that is not the greatest**: `U0` lies below `U1` and `U2`, and so does `U1`, which is not below
`U0`. -/
theorem not_glb_U0_U1_U2 : ¬ IsGlb setting.R U0 U1 U2 := fun glb =>
  absurd (glb.2.2.2 U1 (by decide) (by decide) (by decide)) (by decide)

/-! ## The postponed store has a principal answer -/

/-- The view of `levelEquation`: `X : U0 → U_a` on the left, `Y : U0 → U_b` on the right, at
`Π (x : U0). U_{max a b}`. -/
def levelView : FitFlex levelEquation where
  p := U0
  q := Uab
  left := 1
  right := 0
  pl := U0
  cl := Ua
  pr := U0
  cr := Ub
  annotation_left := by decide +kernel
  annotation_right := by decide +kernel
  side_left := by decide +kernel
  side_right := by decide +kernel
  declared_left := by decide +kernel
  declared_right := by decide +kernel
  universe_p := by decide
  universe_q := by decide
  universe_pl := by decide
  universe_cl := by decide
  universe_pr := by decide
  universe_cr := by decide
  domain_left := by decide
  domain_right := by decide
  codomain_left := by decide
  codomain_right := by decide

/-- **The two unknowns meet at `U0`**: the greatest lower bound of `U_a` and `U_b`; both domains are the annotation's. -/
theorem level_glbMeets : GlbMeets levelView U0 :=
  ⟨glb_Ua_Ub, by decide, Or.inr (Or.inl rfl), Or.inr (Or.inl rfl)⟩

theorem level_distinct : levelView.right ≠ levelView.left := by decide

theorem ctxAB_families : AllFamilies ctxAB := allFamilies_of_B (by decide +kernel)

/-- The greatest-lower-bound rule on the store. -/
noncomputable def levelGlbUpdate : Update setting.levels levelStore :=
  glbMeetUpdate (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete ContextualDependentNormalCheckingTower.head_typing_unique
    levelView level_glbMeets level_distinct ctxAB_families []

/-- **The store the families solver postpones has a principal answer**: both unknowns lowered to `U0 → U0`, then
`X := λ x. Y x`. -/
theorem level_glb_principal : (frames setting.levels).Principal levelStore levelGlbUpdate.answer :=
  levelGlbUpdate.completed rfl

/-! ## A family that does not lower by the rule's condition -/

/-- `U1 → U_a` at the annotation's domain `U0`, towards `U0`. -/
theorem lowers_outside : ¬ LowersTo setting.R U0 U0 U1 Ua := by
  unfold LowersTo
  decide

/-- `U0 → U_a` at the annotation's domain `U0`, towards `U0`. -/
theorem lowers_inside : LowersTo setting.R U0 U0 U0 Ua := Or.inr (Or.inl rfl)

/-! ## Least universes, positive and negative -/

/-- **`U1` is the least universe of `U0`.** -/
theorem least_U0 : LeastUniverse (S := setting) (empty setting.R).raw (.head U0) U1 := by
  refine ⟨by decide, Derivable.headType (LevelTower.HeadTyping.sort Tower.zero), fun u hu typed => ?_⟩
  obtain ⟨k, typing, below⟩ := ContextualDependentUniverseInjective.head_typed_cumulative TowerModel.facts
    TowerModel.algebra (empty setting.R).formed hu typed
  rw [ContextualDependentNormalCheckingTower.head_typing_unique typing (LevelTower.HeadTyping.sort Tower.zero)]
    at below
  exact below

/-- **`U2` is a universe of `U0`, not its least.** -/
theorem not_least_U0_U2 : ¬ LeastUniverse (S := setting) (empty setting.R).raw (.head U0) U2 := fun least =>
  absurd (least.2.2 U1 (by decide) (Derivable.headType (LevelTower.HeadTyping.sort Tower.zero))) (by decide)

end Controls

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
