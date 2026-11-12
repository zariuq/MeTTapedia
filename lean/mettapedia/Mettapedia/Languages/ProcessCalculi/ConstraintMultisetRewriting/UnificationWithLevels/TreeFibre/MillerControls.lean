import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.MillerDecided
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.PatternRules

/-!
# Controls for the Miller solver, in the tree's tower

The Miller solver at the tower's facts, with `legacyGround : U0` as the inhabitant of every universe
(`towerInh`). Membership in the fragment and every run are evaluated by the kernel.

* **A permutation** (`perm_*`): `λ x y. F x y ≐ λ x y. G y x` over `F G : U0 → U0 → U0`; inside, commits with
  `G := λ a b. F b a`, principal.
* **Pruning, a local escaping its scope** (`prune_*`): `λ y z. F y ≐ λ y z. G y z`; `G` is pruned to its first
  argument, then solved; commits.
* **Pruning both sides** (`both_*`): `λ x y z. F x y ≐ λ x y z. G y z`; both are pruned to the common local `y`;
  commits.
* **Intersection, the same unknown** (`inter_*`): `λ x y. F x y ≐ λ x y. F y x`; `F` is declared again with no
  argument; commits, principal.
* **Projection** (`project_*`): `λ y z. F z y ≐ λ y z. y`; `F := λ a b. b`; commits.
* **Re-reading through a second equation** (`chain_*`): `G` solved by a permutation of `F`, then the equation on
  `G` is read on `F`; commits.
* **A local escaping its scope, refuted** (`scope_*`): `λ y z. F y ≐ λ y z. z`; refuted, with no solution.
* **Two different rigid locals** (`locals_*`): `λ y z. y ≐ λ y z. z`; refuted.
* **A misfit local** (`misfit_*`): `λ (y : U1). F y ≐ λ y. y` over `F : U1 → U0`; inside, refuted: `F` would
  return a type of `U1` in `U0`.
* **The same local twice, not a pattern** (`twice_*`): `λ y. F y y ≐ λ y. y`; not read as a Miller equation,
  outside the fragment, and the solver stops postponed.
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

/-- The chain of codomains, decided. -/
def chainB (Θ : Context S.R) : Bool :=
  decide (∀ i j : Fin Θ.arity,
    (match readFam (Ctx.lookup Θ.raw i), readFam (Ctx.lookup Θ.raw j) with
      | some r, some r' => decide (S.R.cumulative r.2 r'.2) || decide (S.R.cumulative r'.2 r.2)
      | _, _ => true) = true)

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] in
theorem chain_of_B {Θ : Context S.R} (h : chainB Θ = true) : Chain Θ := by
  intro i j ps ps' c c' hi hj
  have all := of_decide_eq_true h i j
  rw [hi, hj, readFam_famCode, readFam_famCode] at all
  simpa using all

/-- Membership in the Miller fragment, decided. -/
def inMillerB {Γ : Context S.R} (store : EquationStore (TotalTerm Γ)) : Bool :=
  decide (Families Γ) && chainB Γ && store.all fun e => (readEq (S := S) e).isSome

theorem inMiller_of_B {Γ : Context S.R} (store : EquationStore (TotalTerm Γ)) (h : inMillerB store = true) :
    InMiller (S := S) store := by
  unfold inMillerB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨families, chain⟩, views⟩ := h
  refine ⟨families, chain_of_B chain, fun e member => ?_⟩
  obtain ⟨v, _⟩ := Option.isSome_iff_exists.mp (views e member)
  exact ⟨v⟩

end Membership

namespace Controls

open ContextualDependentPatternFiring.Controls

/-- `legacyGround : U0`, below every universe. -/
def towerInh : Inhabitants setting.R where
  pick _ := .legacyGround
  typed := by
    intro q hq n Γ
    cases hq with
    | sort l =>
        exact Derivable.cumul (Derivable.headType LevelTower.HeadTyping.legacyGround)
          (fun v => by
            rw [LevelTower.eval_zero]
            exact UniverseLevel.LevelOrder.bot_le _)

/-- **The Miller solver at the tower's facts.** -/
def millerTower : ContextualDependentWorklist.Solver setting.levels :=
  millerSolver (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes towerInh

/-- The universe `U0`. -/
abbrev u0 : Tower.Head := .sort Tower.zero

/-! ## Telescopes -/

/-- `U0 → U0 → U0`. -/
def bin0 : TypeOver (empty setting.R) := formIn (empty setting.R) (famCode [u0, u0] u0) (by decide +kernel)

/-- `U0 → U0`. -/
def un0 : TypeOver (empty setting.R) := formIn (empty setting.R) (famCode [u0] u0) (by decide +kernel)

/-- `F : U0 → U0 → U0`. -/
abbrev ctxB := extend (empty setting.R) bin0

/-- `F : U0 → U0`. -/
abbrev ctxU := extend (empty setting.R) un0

def binB : TypeOver ctxB := formIn ctxB (famCode [u0, u0] u0) (by decide +kernel)

/-- `F G : U0 → U0 → U0`. -/
abbrev ctxBB := extend ctxB binB

def binU : TypeOver ctxU := formIn ctxU (famCode [u0, u0] u0) (by decide +kernel)

/-- `F : U0 → U0, G : U0 → U0 → U0`. -/
abbrev ctxUB := extend ctxU binU

def binBB : TypeOver ctxBB := formIn ctxBB (famCode [u0, u0] u0) (by decide +kernel)

/-- `F G H : U0 → U0 → U0`. -/
abbrev ctxBBB := extend ctxBB binBB

/-! ## A permutation -/

def annBB : TypeOver ctxBB := formIn ctxBB (famCode [u0, u0] u0) (by decide +kernel)

/-- `λ x y. F x y ≐ λ x y. G y x`. -/
def permStore : EquationStore (TotalTerm ctxBB) :=
  [(termIn ctxBB annBB (.lam (.lam (.app (.app (.var 3) (.var 1)) (.var 0)))) (by decide +kernel),
    termIn ctxBB annBB (.lam (.lam (.app (.app (.var 2) (.var 0)) (.var 1)))) (by decide +kernel))]

theorem perm_inside : InMiller (S := setting) permStore := inMiller_of_B _ (by decide +kernel)

/-- **The permutation is inverted**: `G := λ a b. F b a`, then the equation is deleted. -/
theorem perm_committed : (run millerTower permStore 3).readout = .commit := by decide +kernel

theorem perm_principal :
    ∃ (Δ : Context setting.R) (answer : Δ ⟶ ctxBB), (frames setting.levels).Principal permStore answer :=
  TreeFibre.Controls.principal_of_commit perm_committed

/-! ## Pruning one side -/

def annUB : TypeOver ctxUB := formIn ctxUB (famCode [u0, u0] u0) (by decide +kernel)

/-- `λ y z. F y ≐ λ y z. G y z`: `z` escapes `F`'s scope. -/
def pruneStore : EquationStore (TotalTerm ctxUB) :=
  [(termIn ctxUB annUB (.lam (.lam (.app (.var 3) (.var 1)))) (by decide +kernel),
    termIn ctxUB annUB (.lam (.lam (.app (.app (.var 2) (.var 1)) (.var 0)))) (by decide +kernel))]

theorem prune_inside : InMiller (S := setting) pruneStore := inMiller_of_B _ (by decide +kernel)

/-- **`G` is pruned to its first argument, then solved by `F`.** -/
theorem prune_committed : (run millerTower pruneStore 4).readout = .commit := by decide +kernel

theorem prune_principal :
    ∃ (Δ : Context setting.R) (answer : Δ ⟶ ctxUB), (frames setting.levels).Principal pruneStore answer :=
  TreeFibre.Controls.principal_of_commit prune_committed

/-! ## Pruning both sides -/

def ann3 : TypeOver ctxBB := formIn ctxBB (famCode [u0, u0, u0] u0) (by decide +kernel)

/-- `λ x y z. F x y ≐ λ x y z. G y z`. -/
def bothStore : EquationStore (TotalTerm ctxBB) :=
  [(termIn ctxBB ann3 (.lam (.lam (.lam (.app (.app (.var 4) (.var 2)) (.var 1))))) (by decide +kernel),
    termIn ctxBB ann3 (.lam (.lam (.lam (.app (.app (.var 3) (.var 1)) (.var 0))))) (by decide +kernel))]

theorem both_inside : InMiller (S := setting) bothStore := inMiller_of_B _ (by decide +kernel)

/-- **Both are pruned to the common local `y`, then one solves the other.** -/
theorem both_committed : (run millerTower bothStore 5).readout = .commit := by decide +kernel

theorem both_principal :
    ∃ (Δ : Context setting.R) (answer : Δ ⟶ ctxBB), (frames setting.levels).Principal bothStore answer :=
  TreeFibre.Controls.principal_of_commit both_committed

/-! ## Intersection -/

def annB : TypeOver ctxB := formIn ctxB (famCode [u0, u0] u0) (by decide +kernel)

/-- `λ x y. F x y ≐ λ x y. F y x`. -/
def interStore : EquationStore (TotalTerm ctxB) :=
  [(termIn ctxB annB (.lam (.lam (.app (.app (.var 2) (.var 1)) (.var 0)))) (by decide +kernel),
    termIn ctxB annB (.lam (.lam (.app (.app (.var 2) (.var 0)) (.var 1)))) (by decide +kernel))]

theorem inter_inside : InMiller (S := setting) interStore := inMiller_of_B _ (by decide +kernel)

/-- **`F` is declared again with no argument; the equation is then deleted.** -/
theorem inter_committed : (run millerTower interStore 3).readout = .commit := by decide +kernel

theorem inter_principal :
    ∃ (Δ : Context setting.R) (answer : Δ ⟶ ctxB), (frames setting.levels).Principal interStore answer :=
  TreeFibre.Controls.principal_of_commit inter_committed

/-! ## Projection -/

/-- `λ y z. F z y ≐ λ y z. y`. -/
def projectStore : EquationStore (TotalTerm ctxB) :=
  [(termIn ctxB annB (.lam (.lam (.app (.app (.var 2) (.var 0)) (.var 1)))) (by decide +kernel),
    termIn ctxB annB (.lam (.lam (.var 1))) (by decide +kernel))]

theorem project_inside : InMiller (S := setting) projectStore := inMiller_of_B _ (by decide +kernel)

/-- **`F := λ a b. b`.** -/
theorem project_committed : (run millerTower projectStore 3).readout = .commit := by decide +kernel

theorem project_principal :
    ∃ (Δ : Context setting.R) (answer : Δ ⟶ ctxB), (frames setting.levels).Principal projectStore answer :=
  TreeFibre.Controls.principal_of_commit project_committed

/-! ## Re-reading through a second equation -/

def annBBB : TypeOver ctxBBB := formIn ctxBBB (famCode [u0, u0] u0) (by decide +kernel)

/-- `λ x y. F x y ≐ λ x y. G y x` and `λ x y. G x y ≐ λ x y. H x y`. -/
def chainStore : EquationStore (TotalTerm ctxBBB) :=
  [(termIn ctxBBB annBBB (.lam (.lam (.app (.app (.var 4) (.var 1)) (.var 0)))) (by decide +kernel),
      termIn ctxBBB annBBB (.lam (.lam (.app (.app (.var 3) (.var 0)) (.var 1)))) (by decide +kernel)),
    (termIn ctxBBB annBBB (.lam (.lam (.app (.app (.var 3) (.var 1)) (.var 0)))) (by decide +kernel),
      termIn ctxBBB annBBB (.lam (.lam (.app (.app (.var 2) (.var 1)) (.var 0)))) (by decide +kernel))]

theorem chain_inside : InMiller (S := setting) chainStore := inMiller_of_B _ (by decide +kernel)

/-- **The second equation is read on `F` after `G` is solved, then solved in its turn.** -/
theorem chain_committed : (run millerTower chainStore 5).readout = .commit := by decide +kernel

/-! ## Refutations -/

def annU : TypeOver ctxU := formIn ctxU (famCode [u0, u0] u0) (by decide +kernel)

/-- `λ y z. F y ≐ λ y z. z`: the rigid local `z` escapes `F`'s scope. -/
def scopeStore : EquationStore (TotalTerm ctxU) :=
  [(termIn ctxU annU (.lam (.lam (.app (.var 2) (.var 1)))) (by decide +kernel),
    termIn ctxU annU (.lam (.lam (.var 0))) (by decide +kernel))]

theorem scope_inside : InMiller (S := setting) scopeStore := inMiller_of_B _ (by decide +kernel)

/-- **Refuted.** -/
theorem scope_refuted : (run millerTower scopeStore 1).readout = .refuted := by decide +kernel

theorem scope_unsolvable : ¬ (frames setting.levels).Solvable scopeStore :=
  Outcome.readout_eq_refuted scope_refuted

/-- `λ y z. y ≐ λ y z. z`. -/
def localsStore : EquationStore (TotalTerm ctxU) :=
  [(termIn ctxU annU (.lam (.lam (.var 1))) (by decide +kernel),
    termIn ctxU annU (.lam (.lam (.var 0))) (by decide +kernel))]

theorem locals_inside : InMiller (S := setting) localsStore := inMiller_of_B _ (by decide +kernel)

theorem locals_refuted : (run millerTower localsStore 1).readout = .refuted := by decide +kernel

theorem locals_unsolvable' : ¬ (frames setting.levels).Solvable localsStore :=
  Outcome.readout_eq_refuted locals_refuted

/-! ## A misfit local, refuted -/

/-- The universe `U1`. -/
abbrev u1 : Tower.Head := .sort (.succ Tower.zero)

/-- `U1 → U0`. -/
def down0 : TypeOver (empty setting.R) := formIn (empty setting.R) (famCode [u1] u0) (by decide +kernel)

/-- `F : U1 → U0`: its domain does not lie below its codomain. -/
abbrev ctxDown := extend (empty setting.R) down0

def annDown : TypeOver ctxDown := formIn ctxDown (famCode [u1] u1) (by decide +kernel)

/-- `λ (y : U1). F y ≐ λ y. y`: `F` would return its argument, a type of `U1`, in `U0`. -/
def misfitStore : EquationStore (TotalTerm ctxDown) :=
  [(termIn ctxDown annDown (.lam (.app (.var 1) (.var 0))) (by decide +kernel),
    termIn ctxDown annDown (.lam (.var 0)) (by decide +kernel))]

/-- **Inside the fragment** (no domain of a family has to lie below its codomain). -/
theorem misfit_inside : InMiller (S := setting) misfitStore := inMiller_of_B _ (by decide +kernel)

/-- **Refuted**, by the tree's `var_not_small`. -/
theorem misfit_refuted : (run millerTower misfitStore 1).readout = .refuted := by decide +kernel

theorem misfit_unsolvable' : ¬ (frames setting.levels).Solvable misfitStore :=
  Outcome.readout_eq_refuted misfit_refuted

/-! ## Just outside: the same local twice -/

def annOne : TypeOver ctxB := formIn ctxB (famCode [u0] u0) (by decide +kernel)

/-- `λ y. F y y ≐ λ y. y`: not a Miller pattern. -/
def twiceStore : EquationStore (TotalTerm ctxB) :=
  [(termIn ctxB annOne (.lam (.app (.app (.var 1) (.var 0)) (.var 0))) (by decide +kernel),
    termIn ctxB annOne (.lam (.var 0)) (by decide +kernel))]

/-- **It is not read as a Miller equation**, so it is outside the fragment. -/
theorem twice_unread : inMillerB (S := setting) twiceStore = false := by decide +kernel

/-- **The solver stops postponed.** -/
theorem twice_postponed : (run millerTower twiceStore 2).readout = .suspended := by decide +kernel

end Controls

end Miller

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
