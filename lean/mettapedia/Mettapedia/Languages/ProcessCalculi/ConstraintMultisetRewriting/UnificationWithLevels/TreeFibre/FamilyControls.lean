import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.FamilySolver

/-!
# Controls for the families solver, in the tree's tower

All stores are in the tree's cumulative tower (`ContextualDependentPatternFiring.Controls.setting`), with the solver
of `FamilySolver` at the tower's own facts (`towerSolver`). Membership, readings and runs are evaluated by the
kernel.

* **Inside, decided** (`fit_inside`, `fit_committed`, `fit_principal`): over `X : U0 → U0` and `Y : U0 → U1`, the
  store `λ x. Y x ≐ λ x. X x`, `λ x. X x ≐ λ x. Y x`, `λ x. X x ≐ λ x. X x` is in the fragment; the solver inverts
  the first equation in its swapped orientation (`Y := X`), then deletes twice, and commits; the answer is principal.
* **The cross store lies outside** (`cross_outside`): `X : U0 → U0` and `Y : U1 → U1` are declared over different
  domains, so the reader does not read its equation. Every run of the solver on it stops postponed, at an exact
  residual without a principal answer (`cross_postponed_by_families`).
* **An undecided level comparison is postponed** (`level_undecided`, `level_read`, `level_stuck`,
  `level_postponed`, `level_solvable`): over `X : U0 → U_a` and `Y : U0 → U_b` with level variables `a`, `b`, the
  equation `λ x. X x ≐ λ x. Y x` is read, but neither codomain lies below the other at every valuation. The solver
  does not choose a direction: it is stuck, the run ends at an exact residual, and the store is solvable, so no
  refutation would be sound.
* **The annotations must agree** (`mixed_unread`, `mixed_unsolvable`): `λ x. X x ≐ λ x. X x` with its two sides
  annotated at `Π (x : U0). U1` and `Π (x : U0). U2` is not read, and it has no solution: deleting it, as for one
  unknown at one annotation, would add solutions.
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

/-- The families solver at the tower's facts. -/
def towerSolver : ContextualDependentWorklist.Solver setting.levels :=
  familySolver (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete

/-- `U0`, `U1`, `U2`. -/
abbrev U0 : Tower.Head := .sort Tower.zero
abbrev U1 : Tower.Head := .sort (.succ Tower.zero)
abbrev U2 : Tower.Head := .sort (.succ (.succ Tower.zero))

/-! ## Inside the fragment, decided -/

/-- `U0 → U1`, over `X : U0 → U0`. -/
def raisedFamily : TypeOver ctxSmall :=
  formIn ctxSmall (.pi (.head U0) (.head U1)) (by decide +kernel)

/-- `X : U0 → U0, Y : U0 → U1`. -/
abbrev ctxFit := extend ctxSmall raisedFamily

/-- `Π (x : U0). U1`, over `X Y`. -/
def fitType : TypeOver ctxFit := formIn ctxFit (.pi (.head U0) (.head U1)) (by decide +kernel)

/-- `λ x. X x`. -/
def etaX : TotalTerm ctxFit := termIn ctxFit fitType (.lam (.app (.var 2) (.var 0))) (by decide +kernel)

/-- `λ x. Y x`. -/
def etaY : TotalTerm ctxFit := termIn ctxFit fitType (.lam (.app (.var 1) (.var 0))) (by decide +kernel)

/-- `λ x. Y x ≐ λ x. X x`, `λ x. X x ≐ λ x. Y x`, `λ x. X x ≐ λ x. X x`. -/
def fitStore : EquationStore (TotalTerm ctxFit) := [(etaY, etaX), (etaX, etaY), (etaX, etaX)]

/-- **The store is in the fragment.** -/
theorem fit_inside : InFragment fitStore := inFragment_of_B (by decide +kernel)

/-- **The solver commits on it**: inversion in the swapped orientation, then two deletions. -/
theorem fit_committed : (run towerSolver fitStore 4).readout = .commit := by decide +kernel

/-- **Its answer is principal.** -/
theorem fit_principal :
    ∃ (Δ : Context setting.R) (answer : Δ ⟶ ctxFit), (frames setting.levels).Principal fitStore answer :=
  principal_of_inFragment TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete fit_inside

/-! ## The cross store lies outside -/

/-- **The cross store's equation is not read**: its unknowns are declared over different domains. -/
theorem cross_unread : (readFlexData (S := setting) crossEquation).isNone = true := by decide +kernel

/-- **The cross store lies outside the fragment.** -/
theorem cross_outside : ¬ InFragment crossStore := by
  intro inside
  obtain ⟨v⟩ := inside.shapes crossEquation List.mem_cons_self
  have read := readFlexData_complete v
  have none := cross_unread
  rw [read] at none
  cases none

/-- **On the cross store the solver stops postponed**, at every large budget, at an exact residual without a
principal answer. -/
theorem cross_postponed_by_families :
    ∃ fuel, ∀ larger, fuel ≤ larger →
      run towerSolver crossStore larger = run towerSolver crossStore fuel ∧
      ∃ state, run towerSolver crossStore larger = .stuck state ∧ state.remaining ≠ [] ∧
        Exact (frames setting.levels) crossStore state.answer state.remaining ∧
        DependentFibre.NoPrincipal setting.levels state.remaining :=
  DependentFibre.cross_run_postponed towerSolver

/-! ## An undecided level comparison is postponed -/

/-- Universes at the level variables `a`, `b` and at their maximum. -/
abbrev Ua : Tower.Head := .sort (.param 0)
abbrev Ub : Tower.Head := .sort (.param 1)
abbrev Uab : Tower.Head := .sort (.max (.param 0) (.param 1))

/-- `U0 → U_a`. -/
def familyA : TypeOver (empty setting.R) :=
  formIn (empty setting.R) (.pi (.head U0) (.head Ua)) (by decide +kernel)

/-- `X : U0 → U_a`. -/
abbrev ctxA := extend (empty setting.R) familyA

/-- `U0 → U_b`, over `X`. -/
def familyB : TypeOver ctxA := formIn ctxA (.pi (.head U0) (.head Ub)) (by decide +kernel)

/-- `X : U0 → U_a, Y : U0 → U_b`. -/
abbrev ctxAB := extend ctxA familyB

/-- `Π (x : U0). U_{max a b}`, over `X Y`. -/
def abType : TypeOver ctxAB := formIn ctxAB (.pi (.head U0) (.head Uab)) (by decide +kernel)

/-- `λ x. X x ≐ λ x. Y x` at `Π (x : U0). U_{max a b}`. -/
def levelEquation : Equation (TotalTerm ctxAB) :=
  (termIn ctxAB abType (.lam (.app (.var 2) (.var 0))) (by decide +kernel),
    termIn ctxAB abType (.lam (.app (.var 1) (.var 0))) (by decide +kernel))

def levelStore : EquationStore (TotalTerm ctxAB) := [levelEquation]

/-- **Neither codomain lies below the other at every valuation.** -/
theorem level_undecided : ¬ setting.R.cumulative Ua Ub ∧ ¬ setting.R.cumulative Ub Ua := by decide

/-- **The equation is read**: it is a flex-flex equation of families. -/
theorem level_read : (readFlexData (S := setting) levelEquation).isSome = true := by decide +kernel

/-- **The solver is stuck on it**: it does not choose a direction. -/
theorem level_stuck : isStuck (run towerSolver levelStore 1) = true := by decide +kernel

/-- **The run ends postponed, at an exact residual.** -/
theorem level_postponed : ∃ state, run towerSolver levelStore 1 = .stuck state ∧
    Exact (frames setting.levels) levelStore state.answer state.remaining := by
  have stuck := level_stuck
  cases h : run towerSolver levelStore 1 with
  | stuck state => exact ⟨state, rfl, DependentFibre.update_exact state⟩
  | solved _ _ => rw [h] at stuck; cases stuck
  | refuted _ => rw [h] at stuck; cases stuck
  | cutoff _ => rw [h] at stuck; cases stuck

/-- `X := λ x. x, Y := λ x. x`. -/
def levelIdentity : empty setting.R ⟶ ctxAB :=
  Elimination.instantiate (empty setting.R) (termIn (empty setting.R) familyA (.lam (.var 0)) (by decide +kernel)).2 ≫
    Elimination.instantiate ctxA (termIn ctxA familyB (.lam (.var 0)) (by decide +kernel)).2

/-- **The store is solvable**, so no refutation of it would be sound. -/
theorem level_solvable : (frames setting.levels).Solvable levelStore :=
  solvable_by levelIdentity levelEquation.1.2 levelEquation.2.2 (by decide +kernel)

/-! ## The annotations must agree -/

/-- `Π (x : U0). U1` and `Π (x : U0). U2`, over `X : U0 → U0`. -/
def annotOne : TypeOver ctxSmall := formIn ctxSmall (.pi (.head U0) (.head U1)) (by decide +kernel)
def annotTwo : TypeOver ctxSmall := formIn ctxSmall (.pi (.head U0) (.head U2)) (by decide +kernel)

/-- `λ x. X x ≐ λ x. X x`, the sides annotated at `Π (x : U0). U1` and at `Π (x : U0). U2`. -/
def mixedEquation : Equation (TotalTerm ctxSmall) :=
  (termIn ctxSmall annotOne (.lam (.app (.var 1) (.var 0))) (by decide +kernel),
    termIn ctxSmall annotTwo (.lam (.app (.var 1) (.var 0))) (by decide +kernel))

def mixedStore : EquationStore (TotalTerm ctxSmall) := [mixedEquation]

/-- **The equation is not read.** -/
theorem mixed_unread : (readFlexData (S := setting) mixedEquation).isNone = true := by decide +kernel

/-- **The store has no solution**: its two annotations are not equal types. -/
theorem mixed_unsolvable : ¬ (frames setting.levels).Solvable mixedStore := by
  rintro ⟨Δ, f, solved⟩
  have held := solved mixedEquation List.mem_cons_self
  have typeEq := ((equivalent_iff setting.levels _ _).mp held).1
  change TypeEq setting.R Δ.raw (Presentation.subst f.substitution annotOne.code)
    (Presentation.subst f.substitution annotTwo.code) at typeEq
  rw [show annotOne.code = .pi (.head U0) (.head U1) from formIn_code _ _ _,
    show annotTwo.code = .pi (.head U0) (.head U2) from formIn_code _ _ _] at typeEq
  simp only [Presentation.subst] at typeEq
  obtain ⟨_, codomains⟩ := TypeEq.pi_injective TowerModel.facts typeEq Δ.formed
  have same := TypeEq.head_injective TowerModel.facts codomains
    (Δ.formed.snoc (IsType.head_of_universe (S := setting) (by decide)))
  rcases same with h | h
  · exact absurd h (by decide)
  · exact absurd h (by decide)

end Controls

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
