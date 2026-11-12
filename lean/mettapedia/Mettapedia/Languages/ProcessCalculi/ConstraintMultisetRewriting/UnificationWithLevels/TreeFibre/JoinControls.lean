import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.JoinRule
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.SeveralControls

/-!
# Controls: twisted domains have a principal answer, the join

In the tree's tower.

* **Twisted domains** (`twist_principal`): over `X : U0 → U1 → U1` and `Y : U1 → U0 → U1`, the store
  `λ x y. X x y ≐ λ x y. Y x y` at `Π (x y : U0). U1` has a principal answer: `Y` declared again at the join
  `U1 → U1 → U1` and `X, Y := λ x y. Y x y` (`twistAnswer`, `twist_joined`, `twist_value`). The domains `U0, U1` and
  `U1, U0` are not comparable, so the store lies outside the fragment of meet groups, whose solver is stuck on it
  (`twist_outside_meet`).
* **What the join widening needs** (`redex_not_normal`, `join_needs_common_type`): a redex is not normal; and a typing
  over one telescope only does not survive the join: `x` is a type of `U0` over `x : U0` but not over the join
  `x : U1`.
* **A codomain condition is needed** (`join_codomain_needed`): the cross store, `X : U0 → U0` and `Y : U1 → U1` at
  `U0 → U1`, has different codomains, so the join rule does not apply to it, and it has no principal answer: its
  solution `X, Y := λ x. x` lives at no declaration of the join of the domains with the smaller codomain.
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

/-! ## Twisted domains -/

theorem twistAnnotation_right_code : twistEquation.2.1.code = famCode [U0, U0] U1 := by decide +kernel

/-- **The view of the twisted equation**: `X` on the left, `Y` on the right, both of codomain `U1`. -/
def twistViewK : FlexK (S := setting) twistEquation where
  ps := [U0, U0]
  q := U1
  left := 1
  right := 0
  psl := [U0, U1]
  cl := U1
  psr := [U1, U0]
  cr := U1
  annotation_left := twistAnnotation_code
  annotation_right := twistAnnotation_right_code
  side_left := twistLeft_code
  side_right := twistRight_code
  declared_left := twistX_declared
  declared_right := twistY_declared
  universes := by decide
  universes_left := by decide
  universes_right := by decide
  universe_q := by decide
  universe_cl := by decide
  universe_cr := by decide
  domain_left := .cons (by decide) (.cons (by decide) .nil)
  domain_right := .cons (by decide) (.cons (by decide) .nil)
  codomain_left := by decide
  codomain_right := by decide

theorem twistFamilies : Miller.Families (S := setting) ctxTwist := by decide +kernel

/-- Pointwise least upper bounds of the two domains: `U0 ⊔ U1 = U1` and `U1 ⊔ U0 = U1`. -/
theorem twistJoins : JoinsK setting.R [U0, U1] [U1, U0] [U1, U1] :=
  .cons (by decide) (isLub_right (S := setting) (by decide) (by decide))
    (.cons (by decide) (isLub_left (S := setting) (by decide) (by decide)) .nil)

/-- **The answer**: `Y` declared again at the join `U1 → U1 → U1`, and `X, Y := λ x y. Y x y`. -/
abbrev twistAnswer := joinKHom ctxTwist twistFamilies twistViewK rfl (psJ := [U1, U1]) twistJoins

/-- The unknown is declared at the join of the two domains. -/
theorem twist_joined :
    Ctx.lookup (joinedK ctxTwist twistFamilies twistViewK (psJ := [U1, U1]) twistJoins).raw 0 =
      famCode [U1, U1] U1 :=
  joinedK_self ctxTwist twistFamilies twistViewK twistJoins

/-- Both unknowns are sent to `λ x y. Y x y`. -/
theorem twist_value :
    twistAnswer.substitution 1 = etaExp 2 (.var 0) ∧ twistAnswer.substitution 0 = etaExp 2 (.var 0) :=
  ⟨rfl, rfl⟩

/-- **The join is exact on the store**, with nothing left. -/
theorem twist_exact : Exact (frames setting.levels) twistStore twistAnswer [] :=
  joinK_exact TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentNormalCheckingTower.head_typing_unique twistFamilies twistViewK rfl twistJoins []

/-- **Twisted domains have a principal answer.** -/
theorem twist_principal : (frames setting.levels).Principal twistStore twistAnswer :=
  exact_nil_iff_principal.mp twist_exact

/-- The store lies outside the fragment of meet groups, and that solver is stuck on it. -/
theorem twist_outside_meet : ¬ InMeetFragmentK twistStore ∧ isStuck (run meetTowerSolverK twistStore 1) = true :=
  ⟨twist_not_inside, twist_stuck⟩

/-! ## What the join widening needs -/

/-- **A redex is not normal**, so it is not an η-long form (`long_normal_at`). -/
theorem redex_not_normal {n : Nat} (b : Tm Tower.Head (n + 1)) (a : Tm Tower.Head n) :
    ¬ ContextualDependentNormalChecking.Normal (S := setting) (.app (.lam b) a) :=
  fun normal => normal _ (.betaPi b a)

/-- `x : U0`, `x : U1`, and their join `x : U1`. -/
abbrev ctxX0 : Tower.Ctx 1 := .snoc .nil (.head U0)
abbrev ctxX1 : Tower.Ctx 1 := .snoc .nil (.head U1)

theorem joinX : JoinOf setting.R ctxX0 ctxX1 ctxX1 :=
  .join .nil (by decide) (by decide) (by decide) (isLub_right (S := setting) (by decide) (by decide))

/-- **A typing over one telescope only does not survive the join**: `x` is a type of `U0` over `x : U0`, but not over
the join `x : U1`. The join widening asks for a type common to both telescopes (`typed_join`). -/
theorem join_needs_common_type :
    Typed setting.R ctxX0 (.var 0) (.head U0) ∧ ¬ Typed setting.R ctxX1 (.var 0) (.head U0) := by
  refine ⟨Derivable.var (R := setting.R) (Γ := ctxX0) 0, fun typed => ?_⟩
  have formed : CtxFormed setting.R ctxX1 := CtxFormed.nil.snoc (IsType.head_of_universe (by decide))
  have generation : GenerationAt setting.R ctxX1 (.var 0) (.head U0) := Typed.generation typed
  have le : TypeLe setting.R ctxX1 (.head U1) (.head U0) := generation
  have below : setting.R.cumulative U1 U0 :=
    ContextualDependentUniverseInjective.typeLe_head_cumulative TowerModel.facts TowerModel.algebra formed
      (by decide) (by decide) le
  exact absurd below (by decide)

/-! ## A codomain condition is needed -/

/-- **The cross store**: codomains `U0` and `U1`, so the join rule does not apply; and no answer is principal. -/
theorem join_codomain_needed :
    (Ctx.lookup ctxCross.raw 1 = famCode [U0] U0 ∧ Ctx.lookup ctxCross.raw 0 = famCode [U1] U1) ∧
      (frames setting.levels).Solvable crossStore ∧
      ∀ {Δ : Context setting.R} (answer : Δ ⟶ ctxCross), ¬ (frames setting.levels).Principal crossStore answer :=
  ⟨⟨crossX_declared, crossY_declared⟩, crossing_needed.2.1, fun answer => crossing_needed.2.2 answer⟩

end Controls

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
