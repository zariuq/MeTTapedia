import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.MillerGlbDecided
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.MillerGlbControls

/-!
# Controls for the Miller solver without the chain, in the tree's tower

The solver at the tower's facts, with the tower's greatest lower bound on canonical level forms (`towerGlb`).
Membership and every run are evaluated by the kernel.

* **The permutation with incomparable codomains** (`levelPermGlb_*`): `λ x y. F x y ≐ λ x y. G y x` over
  `F : U0 → U0 → U_a`, `G : U0 → U0 → U_b`. Outside the fragment of the Miller solver, which is stuck on it; inside
  the new fragment; the new solver commits in one run, with no lowering done by hand.
* **Pruning, then the lowering** (`pruneGlb_*`): `λ x y. F x y ≐ λ x y. G x` over `F : U0 → U0 → U_a`,
  `G : U0 → U_b`. `F` is pruned to its first argument, then both are lowered to `U0` and `G := λ z. F z`. The Miller
  solver prunes and then is stuck; the new solver commits.
* **The Miller fragment is decided by the new solver too** (`perm_insideGlb`, `perm_committedGlb`), and refutations
  are kept (`scope_refutedGlb`).
* **Just outside**: `λ y. F y y ≐ λ y. y` is not read (`twice_unreadGlb`), and the new solver stops postponed
  (`twice_postponedGlb`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

namespace TreeFibre

namespace Miller

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist

variable {Head L : Type} [UniverseLevel.LevelOrder L]

/-! ## Membership, decided -/

section Membership

variable {S : Setting Head L} [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)]
  [DecidableRel S.R.cumulative]

/-- Membership in the fragment without the chain, decided. -/
def inMillerGlbB {Γ : Context S.R} (store : EquationStore (TotalTerm Γ)) : Bool :=
  decide (Families Γ) && store.all fun e => (readEq (S := S) e).isSome

theorem inMillerGlb_of_B {Γ : Context S.R} (store : EquationStore (TotalTerm Γ)) (h : inMillerGlbB store = true) :
    InMillerGlb (S := S) store := by
  unfold inMillerGlbB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨families, views⟩ := h
  refine ⟨families, fun e member => ?_⟩
  obtain ⟨v, _⟩ := Option.isSome_iff_exists.mp (views e member)
  exact ⟨v⟩

end Membership

namespace Controls

open ContextualDependentPatternFiring.Controls ContextualDependentSweep.Witnesses
open TreeFibre.Controls (Ua Ub Uab)

/-- **The Miller solver without the chain, at the tower's facts and greatest lower bound.** -/
def millerGlbTower : ContextualDependentWorklist.Solver setting.levels :=
  millerGlbSolver (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes towerInh
    ContextualDependentNormalCheckingTower.head_typing_unique LevelGlb.towerGlb LevelGlb.towerGlb_isGlb

/-- **Decided in the tower**: every store of the fragment, from some budget on. -/
theorem millerGlbTower_decided {Θ : Context setting.R} {original : EquationStore (TotalTerm Θ)}
    (inside : InMillerGlb (S := setting) original) :
    ∃ fuel, ∀ larger, fuel ≤ larger →
      run millerGlbTower original larger = run millerGlbTower original fuel ∧
        ((∃ state finished, run millerGlbTower original larger = .solved state finished ∧
            (frames setting.levels).Principal original state.answer) ∨
          (∃ absent, run millerGlbTower original larger = .refuted absent)) :=
  millerGlb_decided TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes towerInh
    ContextualDependentNormalCheckingTower.head_typing_unique LevelGlb.towerGlb LevelGlb.towerGlb_isGlb
    LevelGlb.towerGlb_total inside

/-! ## The permutation with incomparable codomains -/

theorem levelPerm_insideGlb : InMillerGlb (S := setting) levelPermStore := inMillerGlb_of_B _ (by decide +kernel)

/-- **The new solver commits**: both unknowns lowered to `U0`, then `G := λ a b. F b a`. -/
theorem levelPerm_committedGlb : (run millerGlbTower levelPermStore 3).readout = .commit := by decide +kernel

/-- **The Miller solver is stuck on it at every budget tried** (here 5). -/
theorem levelPerm_stuckOld : isStuck (run millerTower levelPermStore 5) = true := by decide +kernel

theorem levelPerm_principalGlb :
    ∃ (Δ : Context setting.R) (answer : Δ ⟶ ctxAB2), (frames setting.levels).Principal levelPermStore answer :=
  TreeFibre.Controls.principal_of_commit levelPerm_committedGlb

/-! ## Pruning, then the lowering -/

/-- `U0 → U_b`, over `F`. -/
def famBu : TypeOver ctxA2 := formIn ctxA2 (famCode [u0] Ub) (by decide +kernel)

/-- `F : U0 → U0 → U_a, G : U0 → U_b`. -/
abbrev ctxAB1 := extend ctxA2 famBu

def annAB1 : TypeOver ctxAB1 := formIn ctxAB1 (famCode [u0, u0] Uab) (by decide +kernel)

/-- `λ x y. F x y ≐ λ x y. G x` at `Π (x y : U0). U_{max a b}`: `y` escapes `G`'s scope. -/
def pruneGlbStore : EquationStore (TotalTerm ctxAB1) :=
  [(termIn ctxAB1 annAB1 (.lam (.lam (.app (.app (.var 3) (.var 1)) (.var 0)))) (by decide +kernel),
    termIn ctxAB1 annAB1 (.lam (.lam (.app (.var 2) (.var 1)))) (by decide +kernel))]

/-- **Outside the Miller fragment**: the codomains `U_a`, `U_b` are not a chain. -/
theorem pruneGlb_outside : inMillerB (S := setting) pruneGlbStore = false := by decide +kernel

theorem pruneGlb_insideGlb : InMillerGlb (S := setting) pruneGlbStore := inMillerGlb_of_B _ (by decide +kernel)

/-- **The Miller solver prunes `F`, then is stuck.** -/
theorem pruneGlb_stuck : isStuck (run millerTower pruneGlbStore 4) = true := by decide +kernel

/-- **The new solver commits**: `F` pruned to its first argument, both lowered to `U0`, then `G := λ z. F z`. -/
theorem pruneGlb_committed : (run millerGlbTower pruneGlbStore 4).readout = .commit := by decide +kernel

theorem pruneGlb_principal :
    ∃ (Δ : Context setting.R) (answer : Δ ⟶ ctxAB1), (frames setting.levels).Principal pruneGlbStore answer :=
  TreeFibre.Controls.principal_of_commit pruneGlb_committed

/-! ## The Miller fragment, and a refutation, through the new solver -/

theorem perm_insideGlb : InMillerGlb (S := setting) permStore := inMillerGlb_of_inMiller perm_inside

theorem perm_committedGlb : (run millerGlbTower permStore 3).readout = .commit := by decide +kernel

theorem scope_refutedGlb : (run millerGlbTower scopeStore 1).readout = .refuted := by decide +kernel

/-! ## Just outside: the same local twice -/

theorem twice_unreadGlb : inMillerGlbB (S := setting) twiceStore = false := by decide +kernel

theorem twice_postponedGlb : (run millerGlbTower twiceStore 2).readout = .suspended := by decide +kernel

end Controls

end Miller

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
