import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.MatchAdmission
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.CrossPostponed

/-!
# Settling on the unifier's decided fragments

On a decided fragment every store has an initial solution or no solution: this is what the tree's
solvers prove for their fragments (`UnificationWithLevels.TreeFibre.Miller.millerGlb_initial` for
Miller stores with codomains in any order, `UnificationWithLevels.TreeFibre.glbGroup_initial` for
glb groups, where the store is always solvable). Call such a store `Decided`.

* **The semantic settler never postpones a solvable decided store** (`ideal_settles_of_decided`).
* **On decided information, settled admission is admission after the match**
  (`ideal_admits_iff_of_decided`): one direction is completeness (`ideal_admits_of_admitsAfterMatch`),
  the other soundness up to agreement, which is exact for rows whose typing is closed under
  agreement.
* **Off the fragments the dichotomy fails**: the cross store is solvable and has no initial solution
  (`cross_not_decided`), which is where postponement is forced.

Deciding admission at the answer is then one check of each made row at the answer and of the guards
(`settled_admits_iff`); a solver that reaches the answer on the fragment computes the settler.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep

open _root_.CategoryTheory Opposite Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open Interface.DependentFull (Make State Firing)
open UnificationWithLevels (InitialSolution)

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head}
variable (levels : LevelModel rules L)

/-- **A decided store**: it has an initial solution, or it has no solution. -/
def Decided {Δ : Context rules} (I : EquationStore (TotalTerm Δ)) : Prop :=
  (∃ (M : Context rules) (σ : M ⟶ Δ), InitialSolution (frames levels) I σ) ∨ ¬ (frames levels).Solvable I

/-- **The semantic settler never postpones a solvable decided store.** -/
theorem ideal_settles_of_decided {Δ : Context rules} {I : EquationStore (TotalTerm Δ)}
    (decided : Decided levels I) (solvable : (frames levels).Solvable I) :
    ∃ (M : Context rules) (σ : M ⟶ Δ) (initial : InitialSolution (frames levels) I σ),
      Settler.ideal levels I = .settled M σ initial := by
  rcases decided with ⟨M, σ, initial⟩ | none
  · exact Settler.ideal_settles levels initial
  · exact absurd solvable none

variable {O : Type} [DecidableEq O]

/-- **On decided information, the semantic settling step realizes admission after the match**, and
admits nothing beyond admission up to agreement. -/
theorem ideal_admits_iff_of_decided {s : State rules O} {f : Firing levels s}
    (decided : Decided levels f.information) :
    (AdmitsAfterMatch levels f → (settlingStep levels O (Settler.ideal levels)).Admits f) ∧
      ((settlingStep levels O (Settler.ideal levels)).Admits f → AdmitsUpToAgreement levels f) := by
  refine ⟨fun admitted => ?_, settling_admitsUpToAgreement levels _⟩
  rcases decided with ⟨M, σ, initial⟩ | none
  · exact ideal_admits_of_admitsAfterMatch levels admitted initial
  · exact absurd admitted.2.2.1 none

/-- **The cross store is not decided**: it is solvable and has no initial solution. -/
theorem cross_not_decided : ¬ Decided crossSetting.levels ContextualDependentSweep.Witnesses.crossStore := by
  rintro (⟨M, σ, initial⟩ | none)
  · exact cross_no_initial M σ initial
  · exact none ContextualDependentSweep.Witnesses.fragment_without_principal_answer.2.1

end NativeTypesOnTheStep

#print axioms NativeTypesOnTheStep.ideal_settles_of_decided
#print axioms NativeTypesOnTheStep.ideal_admits_iff_of_decided
#print axioms NativeTypesOnTheStep.cross_not_decided

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
