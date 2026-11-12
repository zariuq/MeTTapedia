import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.InPlaceAudit
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.ThroughPhasesControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.MixedObstructionControls

/-!
# Controls: the tree's in-place solver with level variables, cumulativity and no budget of rounds

Every run here is driven by the solver's rank (`runRank`), so a store left suspended is stuck, and stuck at every
budget (`undecided_every_budget`).

* **Level variables are rigid.** `U_a ≐ U0` is refuted, though the controls' valuation gives both universes the level
  `0` (`clash_refuted`, `clash_levels_agree`); the store has no solution at any valuation
  (`clash_unsolvable_every_valuation`). `U_{max a 0} ≐ U_a` commits (`max_committed`).
* **Cumulativity is used.** Over `A : U0, X : U_a`, `X ≐ Π (_ : A). A` commits (`cumul_committed`). Over
  `A : U_a, X : U0`, `X ≐ A` has only the solutions that send `A` to `X`'s value; the in-place solver commits with a
  principal answer (`orient_committed`, `orient_principal`), where the tree's step, which solves the newest unknown, is
  stuck (`orient_step_stuck`).
* **Where it is incomplete**: over `X : U0`, `X ≐ U_a` has no solution; the in-place solver is stuck, the solver of
  mixed stores refutes it (`misfit_inPlace_stuck`, `misfit_mixed_refuted`). Unknowns with codomains at incomparable
  level variables need a greatest lower bound; the in-place solver is stuck, the solver of mixed stores commits
  (`level_inPlace_stuck`, `level_mixed_committed`).
* **Miller patterns with glb-join families**: the obstruction store of `MixedObstructionControls` is decided by the
  in-place solver (`mj_rank_committed`), its join being a raising of `X`'s domain to `Y`'s. With the domains crossed
  (`X : U1 → U0 → U0`, `Y : U0 → U1 → U0`, the Miller equation `λ x y. F x y ≐ λ x y. X y x` over
  `F : U0 → U1 → U0`), the store is solvable (`cx_solvable`), each equation alone is decided (`cx_parts_decided`),
  and every solver of the tree is stuck on it at every budget, the in-place solver included (`cx_stuck_everywhere`).
* **The earlier uses, with no budget**: the in-place decisions of the obstruction store and of `y ≐ y'` at a budget of 8
  rounds are the decisions with no budget (`mj_inPlace_agrees`, `metFlex_inPlace_agrees`).
* **Beyond telescopes of universe families**: the in-place solver decides the met store in one run, its rank counting
  declarations and equations (`met_rank_committed`); the dd store too (`dd_rank_committed`). The phases decide the
  cooperation store from a base with no budget of rounds (`coop_phases_rank`).
* **The common rank with no budget**: the blend store, cut off at a budget of 3 rounds, commits
  (`blend_budget_three`, `blend_rank_committed`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

namespace TreeFibre

namespace AuditControls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPatternFiring.Controls ContextualDependentSweep.Witnesses
open TreeFibre.Controls (U0 U1 towerMixedSolver towerMixedJoinSolver)

/-- The tree's in-place solver of the tower. -/
abbrev inPlace : ContextualDependentWorklist.Solver setting.levels := ContextualDependentInPlace.Controls.inPlaceOnly

/-- The tree's step, which solves the newest unknown. -/
abbrev step : ContextualDependentWorklist.Solver setting.levels := ContextualDependentWorklist.Controls.step

/-- **A run driven by the rank that is suspended is undecided at every budget.** -/
theorem undecided_every_budget {Γ : Context setting.R} {original : EquationStore (TotalTerm Γ)}
    {solver : ContextualDependentWorklist.Solver setting.levels}
    (suspended : (runRank solver original).readout = .suspended) : ∀ fuel, ¬ (run solver original fuel).Decided := by
  intro fuel decided
  have rank := (runRank_decided_iff solver original).mpr ⟨fuel, decided⟩
  cases h : runRank solver original with
  | solved state finished =>
      rw [h] at suspended
      cases suspended
  | refuted absent =>
      rw [h] at suspended
      cases suspended
  | stuck state =>
      rw [h] at rank
      exact rank
  | cutoff state =>
      rw [h] at rank
      exact rank

/-- A run driven by the rank that commits carries a principal answer. -/
theorem principal_of_rankCommit {Γ : Context setting.R} {original : EquationStore (TotalTerm Γ)}
    {solver : ContextualDependentWorklist.Solver setting.levels}
    (committed : (runRank solver original).readout = .commit) :
    ∃ (Δ : Context setting.R) (answer : Δ ⟶ Γ), (frames setting.levels).Principal original answer := by
  cases h : runRank solver original with
  | solved state finished => exact ⟨state.target, state.answer, state.completed finished⟩
  | refuted absent =>
      rw [h] at committed
      cases committed
  | stuck state =>
      rw [h] at committed
      cases committed
  | cutoff state =>
      rw [h] at committed
      cases committed

/-! ## Level variables are rigid -/

/-- Universes at the level variable `a`, at its successor, and at `max a 0`. -/
abbrev Ua : Tower.Head := .sort (.param 0)
abbrev Ua1 : Tower.Head := .sort (.succ (.param 0))
abbrev Uma : Tower.Head := .sort (.max (.param 0) Tower.zero)

def univA1 : TypeOver (empty setting.R) := formIn (empty setting.R) (.head Ua1) (by decide +kernel)

/-- `U_a ≐ U0` at `U_{a+1}`. -/
def clashStore : EquationStore (TotalTerm (empty setting.R)) :=
  [(termIn (empty setting.R) univA1 (.head Ua) (by decide +kernel),
    termIn (empty setting.R) univA1 (.head U0) (by decide +kernel))]

/-- **The controls' valuation gives `U_a` and `U0` the same level.** -/
theorem clash_levels_agree : setting.levels.level Ua = setting.levels.level U0 := rfl

/-- **The in-place solver refutes `U_a ≐ U0`**: it compares universes for every valuation. -/
theorem clash_refuted : (runRank inPlace clashStore).readout = .refuted := by decide +kernel

theorem clash_unsolvable : ¬ (frames setting.levels).Solvable clashStore := runRank_refuted _ clash_refuted

/-- **No valuation solves it.** -/
theorem clash_unsolvable_every_valuation (ν : Nat → Nat) :
    ¬ (frames (TowerModel.setting ν).levels).Solvable clashStore :=
  fun solvable => clash_unsolvable ((solvable_valuation_free ν (fun _ => 0) clashStore).mp solvable)

/-- `U_{max a 0} ≐ U_a` at `U_{a+1}`. -/
def maxStore : EquationStore (TotalTerm (empty setting.R)) :=
  [(termIn (empty setting.R) univA1 (.head Uma) (by decide +kernel),
    termIn (empty setting.R) univA1 (.head Ua) (by decide +kernel))]

/-- **`U_{max a 0} ≐ U_a` commits**: the two universes are equal at every valuation. -/
theorem max_committed : (runRank inPlace maxStore).readout = .commit := by decide +kernel

/-! ## Cumulativity is used -/

def tA0 : TypeOver (empty setting.R) := formIn (empty setting.R) (.head U0) (by decide +kernel)
abbrev cA0 := extend (empty setting.R) tA0
def tXa : TypeOver cA0 := formIn cA0 (.head Ua) (by decide +kernel)
/-- `A : U0, X : U_a`. -/
abbrev cA0Xa := extend cA0 tXa
def atUa : TypeOver cA0Xa := formIn cA0Xa (.head Ua) (by decide +kernel)

/-- `X ≐ Π (_ : A). A` at `U_a`. -/
def cumulStore : EquationStore (TotalTerm cA0Xa) :=
  [(termIn cA0Xa atUa (.var 0) (by decide +kernel), termIn cA0Xa atUa (.pi (.var 1) (.var 2)) (by decide +kernel))]

/-- **A type of `U0` answers an unknown of `U_a`.** -/
theorem cumul_committed : (runRank inPlace cumulStore).readout = .commit := by decide +kernel

def tAa : TypeOver (empty setting.R) := formIn (empty setting.R) (.head Ua) (by decide +kernel)
abbrev cAa := extend (empty setting.R) tAa
def tX0 : TypeOver cAa := formIn cAa (.head U0) (by decide +kernel)
/-- `A : U_a, X : U0`. -/
abbrev cAaX0 := extend cAa tX0
def atUa' : TypeOver cAaX0 := formIn cAaX0 (.head Ua) (by decide +kernel)

/-- `X ≐ A` at `U_a`: `X := A` is not typed, `A := X` is. -/
def orientStore : EquationStore (TotalTerm cAaX0) :=
  [(termIn cAaX0 atUa' (.var 0) (by decide +kernel), termIn cAaX0 atUa' (.var 1) (by decide +kernel))]

/-- **The in-place solver commits**, sending the unknown at the larger universe to the one at the smaller. -/
theorem orient_committed : (runRank inPlace orientStore).readout = .commit := by decide +kernel

theorem orient_principal :
    ∃ (Δ : Context setting.R) (answer : Δ ⟶ cAaX0), (frames setting.levels).Principal orientStore answer :=
  principal_of_rankCommit orient_committed

/-- **The tree's step is stuck on it**, at every budget. -/
theorem orient_step_stuck : (runRank step orientStore).readout = .suspended := by decide +kernel

/-! ## Where the in-place solver is incomplete -/

def tX0' : TypeOver (empty setting.R) := formIn (empty setting.R) (.head U0) (by decide +kernel)
abbrev cX0 := extend (empty setting.R) tX0'
def atUa1 : TypeOver cX0 := formIn cX0 (.head Ua1) (by decide +kernel)

/-- `X ≐ U_a` at `U_{a+1}` over `X : U0`: no solution. -/
def misfitStore : EquationStore (TotalTerm cX0) :=
  [(termIn cX0 atUa1 (.var 0) (by decide +kernel), termIn cX0 atUa1 (.head Ua) (by decide +kernel))]

/-- **The in-place solver is stuck on a universe misfit.** -/
theorem misfit_inPlace_stuck : (runRank inPlace misfitStore).readout = .suspended := by decide +kernel

/-- **The solver of mixed stores refutes it**, with a certificate. -/
theorem misfit_mixed_refuted : (runRank towerMixedSolver misfitStore).readout = .refuted := by decide +kernel

theorem misfit_unsolvable : ¬ (frames setting.levels).Solvable misfitStore := runRank_refuted _ misfit_mixed_refuted

/-- **Codomains at incomparable level variables**: the in-place solver is stuck. -/
theorem level_inPlace_stuck : (runRank inPlace TreeFibre.Controls.levelStore).readout = .suspended := by
  decide +kernel

/-- **The solver of mixed stores commits**, through a greatest lower bound. -/
theorem level_mixed_committed : (runRank towerMixedSolver TreeFibre.Controls.levelStore).readout = .commit := by
  decide +kernel

/-! ## Miller patterns with glb-join families -/

/-- **The obstruction store is decided by the in-place solver**, with no budget: its join raises `X`'s domain. -/
theorem mj_rank_committed : (runRank inPlace TreeFibre.Controls.mjStore).readout = .commit := by decide +kernel

/-- **Its principal answer is one at every valuation.** -/
theorem mj_principal_every_valuation (ν : Nat → Nat) :
    ∃ (Δ : Context setting.R) (answer : Δ ⟶ TreeFibre.Controls.ctxMJ),
      (frames (TowerModel.setting ν).levels).Principal TreeFibre.Controls.mjStore answer := by
  obtain ⟨Δ, answer, principal⟩ := principal_of_rankCommit mj_rank_committed
  exact ⟨Δ, answer, (principal_valuation_free (fun _ => 0) ν _ answer).mp principal⟩

/-- `X : U1 → U0 → U0`. -/
def cxX : TypeOver (empty setting.R) :=
  formIn (empty setting.R) (.pi (.head U1) (.pi (.head U0) (.head U0))) (by decide +kernel)
abbrev cc1 := extend (empty setting.R) cxX
/-- `F : U0 → U1 → U0`. -/
def cxF : TypeOver cc1 := formIn cc1 (.pi (.head U0) (.pi (.head U1) (.head U0))) (by decide +kernel)
abbrev cc2 := extend cc1 cxF
/-- `Y : U0 → U1 → U0`. -/
def cxY : TypeOver cc2 := formIn cc2 (.pi (.head U0) (.pi (.head U1) (.head U0))) (by decide +kernel)
/-- `X : U1 → U0 → U0, F : U0 → U1 → U0, Y : U0 → U1 → U0`. -/
abbrev ctxCx := extend cc2 cxY
/-- `U0 → U1 → U0`: the Miller equation's binders. -/
def cxMillerType : TypeOver ctxCx := formIn ctxCx (.pi (.head U0) (.pi (.head U1) (.head U0))) (by decide +kernel)
/-- `U0 → U0 → U0`: the join equation's binders. -/
def cxJoinType : TypeOver ctxCx := formIn ctxCx (.pi (.head U0) (.pi (.head U0) (.head U0))) (by decide +kernel)

/-- `λ x y. F x y ≐ λ x y. X y x`: a permutation with exact domains. -/
def cxMiller : Equation (TotalTerm ctxCx) :=
  (termIn ctxCx cxMillerType (.lam (.lam (.app (.app (.var 3) (.var 1)) (.var 0)))) (by decide +kernel),
    termIn ctxCx cxMillerType (.lam (.lam (.app (.app (.var 4) (.var 0)) (.var 1)))) (by decide +kernel))

/-- `λ u v. X u v ≐ λ u v. Y u v`: domains crossed, `U1, U0` against `U0, U1`. -/
def cxJoin : Equation (TotalTerm ctxCx) :=
  (termIn ctxCx cxJoinType (.lam (.lam (.app (.app (.var 4) (.var 1)) (.var 0)))) (by decide +kernel),
    termIn ctxCx cxJoinType (.lam (.lam (.app (.app (.var 2) (.var 1)) (.var 0)))) (by decide +kernel))

/-- **Miller with a glb join of crossed domains.** -/
def cxStore : EquationStore (TotalTerm ctxCx) := [cxMiller, cxJoin]

/-- **Each equation is read by its piece**: the first as a Miller equation, the second as a family equation. -/
theorem cx_readers : (Miller.readEq (S := setting) cxMiller).isSome = true ∧
    (readFlexK (S := setting) cxJoin).isSome = true := by decide +kernel

/-- **Each alone is decided**: the Miller equation by the in-place solver, the join by the mixed join solver. -/
theorem cx_parts_decided : (runRank inPlace [cxMiller]).readout = .commit ∧
    (runRank towerMixedJoinSolver [cxJoin]).readout = .commit := by decide +kernel

/-- `X F Y := λ a b. Ground`. -/
def cxSolution : empty setting.R ⟶ ctxCx :=
  Elimination.instantiate (empty setting.R)
      (termIn (empty setting.R) cxX (.lam (.lam (.head .legacyGround))) (by decide +kernel)).2 ≫
    Elimination.instantiate cc1 (termIn cc1 cxF (.lam (.lam (.head .legacyGround))) (by decide +kernel)).2 ≫
      Elimination.instantiate cc2 (termIn cc2 cxY (.lam (.lam (.head .legacyGround))) (by decide +kernel)).2

/-- **Together, solvable.** -/
theorem cx_solvable : (frames setting.levels).Solvable cxStore := by
  refine ⟨_, cxSolution, fun e member => ?_⟩
  rcases List.mem_cons.mp member with rfl | member
  · exact models_by cxSolution cxMiller.1.2 cxMiller.2.2 (by decide +kernel) _ List.mem_cons_self
  · rw [List.mem_singleton.mp member]
    exact models_by cxSolution cxJoin.1.2 cxJoin.2.2 (by decide +kernel) _ List.mem_cons_self

/-- **Every solver of the tree is stuck on it**, the in-place solver included. -/
theorem cx_stuck_everywhere : (runRank inPlace cxStore).readout = .suspended ∧
    (runRank towerMixedSolver cxStore).readout = .suspended ∧
    (runRank towerMixedJoinSolver cxStore).readout = .suspended ∧ (runRank step cxStore).readout = .suspended := by
  decide +kernel

/-- **So no budget decides it, for the in-place solver.** -/
theorem cx_inPlace_undecided : ∀ fuel, ¬ (run inPlace cxStore fuel).Decided :=
  undecided_every_budget cx_stuck_everywhere.1

/-- A decision that went to a finished update is a decision. -/
theorem isSome_of_kind {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)}
    {found : Option (Decided problem)} (kind : TreeFibre.Controls.decidedKind found = 1) : found.isSome = true := by
  cases found with
  | none => simp [TreeFibre.Controls.decidedKind] at kind
  | some _ => rfl

/-- **The in-place decision of the obstruction store at a budget of 8 rounds is the one with no budget.** -/
theorem mj_inPlace_agrees :
    Decided.ofRank inPlace TreeFibre.Controls.mjStore = Decided.ofRun inPlace 8 TreeFibre.Controls.mjStore :=
  Decided.ofRank_eq_ofRun (isSome_of_kind TreeFibre.Controls.mj_inPlace)

/-- **So is its decision of `y ≐ y'` with `y y' : X`, `X` unsolved.** -/
theorem metFlex_inPlace_agrees :
    Decided.ofRank inPlace [TreeFibre.Controls.metFlex] = Decided.ofRun inPlace 8 [TreeFibre.Controls.metFlex] :=
  Decided.ofRank_eq_ofRun (isSome_of_kind TreeFibre.Controls.metFlex_inPlace)

/-! ## Beyond telescopes of universe families -/

/-- **The met store**, which meets `y : X` with `X` solved by another equation, is decided by the in-place solver in
one run: its rank counts declarations and equations. -/
theorem met_rank_committed : (runRank inPlace TreeFibre.Controls.metStore).readout = .commit := by decide +kernel

theorem dd_rank_committed : (runRank inPlace TreeFibre.Controls.ddStore).readout = .commit := by decide +kernel

/-- The mixed solver, the mixed join solver and the in-place solver, each driven by its rank. -/
def towerBaseRank {Θ : Context setting.R} (problem : EquationStore (TotalTerm Θ)) : Option (Decided problem) :=
  (Decided.ofRank towerMixedSolver problem).orElse fun _ =>
    (Decided.ofRank towerMixedJoinSolver problem).orElse fun _ => Decided.ofRank inPlace problem

/-- **Deciding in phases from bases with no budget of rounds.** The executable budget and the depth remain. -/
abbrev towerAllRank (fuel depth : Nat) {Θ : Context setting.R} (problem : EquationStore (TotalTerm Θ)) :=
  phases (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer towerBaseRank fuel depth problem

/-- **The cooperation store is decided in two phases**, none of its bases alone deciding it. -/
theorem coop_phases_rank : TreeFibre.Controls.decidedKind (towerAllRank 6 2 TreeFibre.Controls.coopStore) = 1 := by
  decide +kernel

theorem coop_base_rank_alone : TreeFibre.Controls.decidedKind (towerBaseRank TreeFibre.Controls.coopStore) = 0 := by
  decide +kernel

/-! ## The common rank with no budget -/

/-- The blend store is cut off at a budget of 3 rounds. -/
theorem blend_budget_three : (run towerMixedSolver TreeFibre.Controls.blendStore 3).readout = .suspended :=
  TreeFibre.Controls.blend_mixed_suspended_before

/-- **Driven by the common rank, the solver of mixed stores commits.** -/
theorem blend_rank_committed : (runRank towerMixedSolver TreeFibre.Controls.blendStore).readout = .commit := by
  decide +kernel

end AuditControls

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
