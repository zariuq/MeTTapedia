import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.RankSettler
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.OlderUnknownControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.CodomainControls

/-!
# Controls: the settler with no budget of rounds, evaluated by the kernel

* **A fixed budget postpones a store its solver decides.** Over `F G H : U0 → U0 → U0`, the store
  `λ x y z. F x y ≐ λ x y z. G y z`, `λ x y z. G x y ≐ λ x y z. H x y` needs 8 rounds of the Miller solver
  (`twoPruned_budget`). Every family of the budgeted settler declines it: the tree's step and the older-unknown family
  do not read it, and the Miller family's 6 rounds are cut off (`twoPruned_all_declined`). The Miller family driven by
  its rank settles it along its trimmed, initial answer (`twoPruned_rank_settled`), and so does the settler with no
  budget (`twoPruned_rank_first`). At a firing that reads the store, the converting step with the budgeted settler is
  undecided (`twoPrunedFiring_all_undecided`) and the one with no budget admits it (`twoPrunedFiring_rank_decided`,
  `twoPrunedFiring_rank_admitted`).
* **The tree's step**: four flex–flex equations chaining five unary unknowns need 5 rounds of the step
  (`chain_budget`); the step family with its budget of 4 declines (`chain_step_declined`), the one driven by its rank
  settles (`chain_rank_settled`).
* **The family of the common rank** refutes the occurs check at a codomain and a misfit head, which the budgeted
  settler leaves undecided (`occ_rank_refuted`, `mis_rank_refuted`).
* **D2's coerce firing** is still decided with no budget, and admitted by the converting step with the settler with no
  budget (`coerce_rank_decided`, `coerce_rank_admitted`).
* **Negative control**: no family, with or without a budget, decides the cross store, which is solvable and has no
  initial solution (`cross_rank_undecided`); the settler with no budget postpones it (`cross_rank_postponed`). Removing
  the budget decides nothing new outside the solvers' fragments.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep.RankSettler.Controls

open _root_.CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate
open Interface.DependentFull Interface.DependentFull.Controls
open ContextualDependentPatternFiring.Controls (formIn termIn)
open UnificationWithLevels.TreeFibre (famCode runRank)
open UnificationWithLevels.TreeFibre.Miller.Controls (u0 ctxB binB ctxBB binBB ctxBBB)
open ComputableControls OlderUnknown MillerFamily

/-! ## Two pruned equations: every budgeted family declines -/

/-- `U0 → U0 → U0 → U0`, over `F G H`. -/
def ternary : TypeOver ctxBBB := formIn ctxBBB (famCode [u0, u0, u0] u0) (by decide +kernel)

/-- `λ x y z. F x y ≐ λ x y z. G y z`: both sides pruned. -/
def prunedFG : Equation (TotalTerm ctxBBB) :=
  (termIn ctxBBB ternary (.lam (.lam (.lam (.app (.app (.var 5) (.var 2)) (.var 1))))) (by decide +kernel),
    termIn ctxBBB ternary (.lam (.lam (.lam (.app (.app (.var 4) (.var 1)) (.var 0))))) (by decide +kernel))

/-- `λ x y z. G x y ≐ λ x y z. H x y`. -/
def prunedGH : Equation (TotalTerm ctxBBB) :=
  (termIn ctxBBB ternary (.lam (.lam (.lam (.app (.app (.var 4) (.var 2)) (.var 1))))) (by decide +kernel),
    termIn ctxBBB ternary (.lam (.lam (.lam (.app (.app (.var 3) (.var 2)) (.var 1))))) (by decide +kernel))

/-- **The store**, over `F G H : U0 → U0 → U0`. -/
def twoPrunedStore : EquationStore (TotalTerm ctxBBB) := [prunedFG, prunedGH]

theorem twoPruned_inside :
    UnificationWithLevels.TreeFibre.Miller.inMillerGlbB (S := setting) twoPrunedStore = true := by decide +kernel

/-- **The Miller solver needs 8 rounds**: cut off at 7, committed at 8. -/
theorem twoPruned_budget :
    (ContextualDependentWorklist.run millerTower twoPrunedStore 7).readout = .suspended ∧
      (ContextualDependentWorklist.run millerTower twoPrunedStore 8).readout = .commit := by
  decide +kernel

/-- **Driven by its rank, the Miller solver commits**, with no budget. -/
theorem twoPruned_rank_committed : (runRank millerTower twoPrunedStore).readout = .commit := by decide +kernel

/-- **The Miller family with its budget of 6 rounds declines.** -/
theorem twoPruned_miller_declined :
    (millerFamily 6 twoPrunedStore).isSettled = false ∧ (millerFamily 6 twoPrunedStore).isRefuted = false := by
  decide +kernel

/-- **Every family of the budgeted settler declines it.** -/
theorem twoPruned_all_declined :
    (firstDecisionAt setting.levels twoPrunedStore allFamilies).isSettled = false ∧
      (firstDecisionAt setting.levels twoPrunedStore allFamilies).isRefuted = false := by
  decide +kernel

/-- **The Miller family driven by its rank settles it**, along its trimmed answer. -/
theorem twoPruned_rank_settled : (millerRankFamily twoPrunedStore).isSettled = true := by decide +kernel

/-- **So does the settler with no budget.** -/
theorem twoPruned_rank_first : (firstDecisionAt setting.levels twoPrunedStore rankFamilies).isSettled = true := by
  decide +kernel

/-- A store the Miller family with no budget settles is decided by the families with no budget. -/
theorem decidedBy_of_millerSettled {Δ : Context setting.R} {I : EquationStore (TotalTerm Δ)}
    (settles : (millerRankFamily I).isSettled = true) : DecidedBy setting.levels rankFamilies I :=
  ⟨millerRankFamily, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
    decisive_of_isSettled settles⟩

/-- The store is decided by the families with no budget. -/
theorem twoPruned_decidedBy : DecidedBy setting.levels rankFamilies twoPrunedStore :=
  decidedBy_of_millerSettled twoPruned_rank_settled

/-- The store is not decided by the budgeted families. -/
theorem twoPruned_not_decidedBy_all : ¬ DecidedBy setting.levels allFamilies twoPrunedStore := by
  intro decided
  have decisive := firstDecisionAt_decisive setting.levels decided
  have declined := twoPruned_all_declined
  cases h : firstDecisionAt setting.levels twoPrunedStore allFamilies
  · rw [h] at declined
    cases declined.1
  · rw [h] at declined
    cases declined.2
  · rw [h] at decisive
    exact decisive

/-- **The settler with no budget settles it exactly because it is solvable**, as the semantic settler does. -/
theorem twoPruned_agrees :
    ((∃ (M : Context setting.R) (σ : M ⟶ ctxBBB)
        (initial : UnificationWithLevels.InitialSolution (frames setting.levels) twoPrunedStore σ),
        rankSettler twoPrunedStore = .settled M σ initial) ↔ (frames setting.levels).Solvable twoPrunedStore) ∧
      ((∃ (M : Context setting.R) (σ : M ⟶ ctxBBB)
        (initial : UnificationWithLevels.InitialSolution (frames setting.levels) twoPrunedStore σ),
        Settler.ideal setting.levels twoPrunedStore = .settled M σ initial) ↔
          (frames setting.levels).Solvable twoPrunedStore) :=
  ⟨(rank_agrees_ideal twoPruned_decidedBy).1, (rank_agrees_ideal twoPruned_decidedBy).2.1⟩

/-- The state reading the store: its frame `F G H`, the store as knowledge. -/
def twoPrunedState : State setting.R Nat := ⟨ctxBBB, twoPrunedStore, ∅, fun _ => Elimination.last ctxBB binBB⟩

/-- A firing at that state that reads its knowledge and makes nothing. -/
def twoPrunedFiring : Firing setting.levels twoPrunedState where
  helpers := .nil _
  taken := []
  read := []
  takes := []
  reads := []
  makes := []
  tells := []
  guards := []
  queries := []

/-- **The budgeted settler leaves the firing undecided.** -/
theorem twoPrunedFiring_all_undecided : admits? allFamilies twoPrunedFiring = none := by decide +kernel

/-- **The settler with no budget admits it**, settling along the trimmed answer. -/
theorem twoPrunedFiring_rank_decided : admits? rankFamilies twoPrunedFiring = some true := by decide +kernel

theorem twoPrunedFiring_rank_admitted : (convertingStep setting.levels Nat rankSettler).Admits twoPrunedFiring :=
  (admits?_sound rankFamilies twoPrunedFiring_rank_decided).mp rfl

/-! ## A chain for the tree's step -/

def un0 : TypeOver (empty setting.R) := formIn (empty setting.R) (famCode [u0] u0) (by decide +kernel)
abbrev c1 := extend (empty setting.R) un0
def un1 : TypeOver c1 := formIn c1 (famCode [u0] u0) (by decide +kernel)
abbrev c2 := extend c1 un1
def un2 : TypeOver c2 := formIn c2 (famCode [u0] u0) (by decide +kernel)
abbrev c3 := extend c2 un2
def un3 : TypeOver c3 := formIn c3 (famCode [u0] u0) (by decide +kernel)
abbrev c4 := extend c3 un3
def un4 : TypeOver c4 := formIn c4 (famCode [u0] u0) (by decide +kernel)
/-- `X₀ X₁ X₂ X₃ X₄ : U0 → U0`. -/
abbrev c5 := extend c4 un4
def unary5 : TypeOver c5 := formIn c5 (famCode [u0] u0) (by decide +kernel)

/-- `λ x. Xᵢ x ≐ λ x. Xᵢ₊₁ x` for `i < 4`. -/
def chainStore : EquationStore (TotalTerm c5) :=
  [(termIn c5 unary5 (.lam (.app (.var 5) (.var 0))) (by decide +kernel),
    termIn c5 unary5 (.lam (.app (.var 4) (.var 0))) (by decide +kernel)),
   (termIn c5 unary5 (.lam (.app (.var 4) (.var 0))) (by decide +kernel),
    termIn c5 unary5 (.lam (.app (.var 3) (.var 0))) (by decide +kernel)),
   (termIn c5 unary5 (.lam (.app (.var 3) (.var 0))) (by decide +kernel),
    termIn c5 unary5 (.lam (.app (.var 2) (.var 0))) (by decide +kernel)),
   (termIn c5 unary5 (.lam (.app (.var 2) (.var 0))) (by decide +kernel),
    termIn c5 unary5 (.lam (.app (.var 1) (.var 0))) (by decide +kernel))]

/-- **The tree's step needs 5 rounds**: cut off at 4, committed at 5. -/
theorem chain_budget :
    (ContextualDependentWorklist.run ContextualDependentWorklist.Controls.step chainStore 4).readout = .suspended ∧
      (ContextualDependentWorklist.run ContextualDependentWorklist.Controls.step chainStore 5).readout = .commit := by
  decide +kernel

/-- **The step family with its budget of 4 rounds declines.** -/
theorem chain_step_declined :
    (driverFamily setting.levels ContextualDependentWorklist.Controls.step 4 chainStore).isSettled = false ∧
      (driverFamily setting.levels ContextualDependentWorklist.Controls.step 4 chainStore).isRefuted = false := by
  decide +kernel

/-- **The step family driven by its rank settles it.** -/
theorem chain_rank_settled : (stepRankFamily chainStore).isSettled = true := by decide +kernel

/-! ## The family of the common rank -/

/-- **The family of the common rank refutes the occurs check at a codomain**, which the budgeted settler leaves
undecided. -/
theorem occ_rank_refuted : (mixedRankFamily UnificationWithLevels.TreeFibre.Controls.occStore).isRefuted = true := by
  decide +kernel

theorem occ_all_undecided :
    (firstDecisionAt setting.levels UnificationWithLevels.TreeFibre.Controls.occStore allFamilies).isSettled = false ∧
      (firstDecisionAt setting.levels UnificationWithLevels.TreeFibre.Controls.occStore allFamilies).isRefuted =
        false := by
  decide +kernel

/-- **It refutes a misfit head**, which the budgeted settler leaves undecided. -/
theorem mis_rank_refuted : (mixedRankFamily UnificationWithLevels.TreeFibre.Controls.misStore).isRefuted = true := by
  decide +kernel

theorem mis_all_undecided :
    (firstDecisionAt setting.levels UnificationWithLevels.TreeFibre.Controls.misStore allFamilies).isSettled = false ∧
      (firstDecisionAt setting.levels UnificationWithLevels.TreeFibre.Controls.misStore allFamilies).isRefuted =
        false := by
  decide +kernel

/-! ## D2's coerce firing, with no budget -/

/-- **D2's coerce store, settled by the older-unknown family with its budget, is decided with none.** -/
theorem coerce_rank_decided :
    (olderRankFamily ProgrammingOnTheStep.Refinement.coerceFiring.information).Decisive :=
  olderRankFamily_of_decisive (fuel := olderFuel)
    (decisive_of_isSettled OlderUnknown.Controls.coerce_older_settled)

theorem coerce_rank_decidedBy :
    DecidedBy setting.levels rankFamilies ProgrammingOnTheStep.Refinement.coerceFiring.information :=
  ⟨olderRankFamily, List.mem_cons_of_mem _ List.mem_cons_self, coerce_rank_decided⟩

/-- **The converting step with the settler with no budget admits D2's coerce firing**, as the semantic settler's
does. -/
theorem coerce_rank_admitted :
    (convertingStep setting.levels Nat rankSettler).Admits ProgrammingOnTheStep.Refinement.coerceFiring :=
  (rank_steps_iff_ideal coerce_rank_decidedBy).1.mpr
    (OlderUnknown.Controls.coerce_agrees.mp OlderUnknown.Controls.coerce_admitted)

/-! ## Negative control: removing the budget decides nothing outside the fragments -/

/-- **No family with no budget decides the cross store**: it is solvable and has no initial solution. -/
theorem cross_rank_undecided : ∀ F ∈ rankFamilies, ¬ (F ContextualDependentSweep.Witnesses.crossStore).Decisive :=
  fun F _ => OlderUnknown.Controls.cross_undecided F

/-- **The settler with no budget postpones it.** -/
theorem cross_rank_postponed : rankSettler ContextualDependentSweep.Witnesses.crossStore = .postponed :=
  cross_postponed _

end NativeTypesOnTheStep.RankSettler.Controls

#print axioms NativeTypesOnTheStep.RankSettler.Controls.twoPruned_inside
#print axioms NativeTypesOnTheStep.RankSettler.Controls.twoPruned_budget
#print axioms NativeTypesOnTheStep.RankSettler.Controls.twoPruned_rank_committed
#print axioms NativeTypesOnTheStep.RankSettler.Controls.twoPruned_miller_declined
#print axioms NativeTypesOnTheStep.RankSettler.Controls.twoPruned_all_declined
#print axioms NativeTypesOnTheStep.RankSettler.Controls.twoPruned_rank_settled
#print axioms NativeTypesOnTheStep.RankSettler.Controls.twoPruned_rank_first
#print axioms NativeTypesOnTheStep.RankSettler.Controls.decidedBy_of_millerSettled
#print axioms NativeTypesOnTheStep.RankSettler.Controls.twoPruned_decidedBy
#print axioms NativeTypesOnTheStep.RankSettler.Controls.twoPruned_not_decidedBy_all
#print axioms NativeTypesOnTheStep.RankSettler.Controls.twoPruned_agrees
#print axioms NativeTypesOnTheStep.RankSettler.Controls.twoPrunedFiring_all_undecided
#print axioms NativeTypesOnTheStep.RankSettler.Controls.twoPrunedFiring_rank_decided
#print axioms NativeTypesOnTheStep.RankSettler.Controls.twoPrunedFiring_rank_admitted
#print axioms NativeTypesOnTheStep.RankSettler.Controls.chain_budget
#print axioms NativeTypesOnTheStep.RankSettler.Controls.chain_step_declined
#print axioms NativeTypesOnTheStep.RankSettler.Controls.chain_rank_settled
#print axioms NativeTypesOnTheStep.RankSettler.Controls.occ_rank_refuted
#print axioms NativeTypesOnTheStep.RankSettler.Controls.occ_all_undecided
#print axioms NativeTypesOnTheStep.RankSettler.Controls.mis_rank_refuted
#print axioms NativeTypesOnTheStep.RankSettler.Controls.mis_all_undecided
#print axioms NativeTypesOnTheStep.RankSettler.Controls.coerce_rank_decided
#print axioms NativeTypesOnTheStep.RankSettler.Controls.coerce_rank_decidedBy
#print axioms NativeTypesOnTheStep.RankSettler.Controls.coerce_rank_admitted
#print axioms NativeTypesOnTheStep.RankSettler.Controls.cross_rank_undecided
#print axioms NativeTypesOnTheStep.RankSettler.Controls.cross_rank_postponed

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
