import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.MillerGlb
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.MillerControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.TowerGlb

/-!
# Control: a Miller permutation with incomparable codomains

Over `F : U0 → U0 → U_a`, `G : U0 → U0 → U_b`, the equation `λ x y. F x y ≐ λ x y. G y x` at
`Π (x y : U0). U_{max a b}` lies outside the fragment of Miller patterns (the codomains `U_a`, `U_b` are not a chain),
and the Miller solver is stuck on it (`levelPerm_outside`, `levelPerm_stuck`). Lowering both unknowns to
`U_a ⊓ U_b = U0` is exact (`millerGlb_exact`); the Miller solver then commits on the lowered store
(`levelPerm_lowered_committed`), so the store has a principal answer (`levelPerm_principal`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

namespace TreeFibre

namespace Miller

namespace Controls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPatternFiring.Controls ContextualDependentSweep.Witnesses
open TreeFibre.Controls (Ua Ub Uab)

/-- **The lowering, read off the first equation**: two Miller flex sides of different unknowns, lowered to the
tower's greatest lower bound of their codomains. -/
def millerGlbStep {Θ : Context setting.R} (families : Families (S := setting) Θ) (e : Equation (TotalTerm Θ))
    (rest : EquationStore (TotalTerm Θ)) : Option (Update setting.levels (e :: rest)) :=
  match readEq (S := setting) e with
  | some v =>
      match hl : v.left, hr : v.right with
      | .flex D₁ b₁, .flex D₂ b₂ =>
          if ne : D₂.unknown = D₁.unknown then none else
          match hg : LevelGlb.towerGlb D₁.c D₂.c with
          | some _ => some (millerGlbUpdate towerInh TowerModel.facts TowerModel.roots TowerModel.heads
              TowerModel.algebra ContextualDependentPiSpine.Controls.rigid TowerModel.complete
              ContextualDependentNormalCheckingTower.head_typing_unique families v D₁ b₁ D₂ b₂ hl hr
              (LevelGlb.towerGlb_isGlb hg) ne rest)
          | none => none
      | _, _ => none
  | none => none

/-- `U0 → U0 → U_a`, and `U0 → U0 → U_b` over `F`. -/
def famA2 : TypeOver (empty setting.R) := formIn (empty setting.R) (famCode [u0, u0] Ua) (by decide +kernel)
abbrev ctxA2 := extend (empty setting.R) famA2
def famB2 : TypeOver ctxA2 := formIn ctxA2 (famCode [u0, u0] Ub) (by decide +kernel)

/-- `F : U0 → U0 → U_a, G : U0 → U0 → U_b`. -/
abbrev ctxAB2 := extend ctxA2 famB2

def annAB2 : TypeOver ctxAB2 := formIn ctxAB2 (famCode [u0, u0] Uab) (by decide +kernel)

/-- `λ x y. F x y ≐ λ x y. G y x` at `Π (x y : U0). U_{max a b}`. -/
def levelPermEquation : Equation (TotalTerm ctxAB2) :=
  (termIn ctxAB2 annAB2 (.lam (.lam (.app (.app (.var 3) (.var 1)) (.var 0)))) (by decide +kernel),
    termIn ctxAB2 annAB2 (.lam (.lam (.app (.app (.var 2) (.var 0)) (.var 1)))) (by decide +kernel))

def levelPermStore : EquationStore (TotalTerm ctxAB2) := [levelPermEquation]

/-- **Outside the fragment**: the codomains are not a chain. -/
theorem levelPerm_outside : inMillerB (S := setting) levelPermStore = false := by decide +kernel

/-- **The Miller solver is stuck on it.** -/
theorem levelPerm_stuck : isStuck (run millerTower levelPermStore 1) = true := by decide +kernel

theorem ctxAB2_families : Families (S := setting) ctxAB2 := of_decide_eq_true (by decide +kernel)

theorem levelPerm_step_some : (millerGlbStep ctxAB2_families levelPermEquation []).isSome = true := by
  decide +kernel

/-- **The lowering of both unknowns to `U0`.** -/
def levelPermLowering : Update setting.levels levelPermStore :=
  (millerGlbStep ctxAB2_families levelPermEquation []).get levelPerm_step_some

/-- **After the lowering the Miller solver commits.** -/
theorem levelPerm_lowered_committed : (run millerTower levelPermLowering.remaining 3).readout = .commit := by
  decide +kernel

/-- **The store has a principal answer**: the exact lowering, then the solver's principal answer. -/
theorem levelPerm_principal :
    ∃ (Δ : Context setting.R) (answer : Δ ⟶ ctxAB2), (frames setting.levels).Principal levelPermStore answer := by
  obtain ⟨Δ, answer, principal⟩ := TreeFibre.Controls.principal_of_commit levelPerm_lowered_committed
  have lowering : Exact (frames setting.levels) levelPermStore levelPermLowering.answer levelPermLowering.remaining :=
    (DependentFibre.exact_iff_update (levels := setting.levels) _ _).mpr ⟨levelPermLowering, rfl, rfl, rfl⟩
  exact ⟨Δ, _, exact_nil_iff_principal.mp (lowering.trans (exact_nil_iff_principal.mpr principal))⟩

end Controls

end Miller

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
