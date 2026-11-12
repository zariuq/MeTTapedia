import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.FitSolver
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.LevelChoice

/-!
# Rule choice without a level valuation, for the solver of fitting groups

* **The step is stuck exactly when neither unknown fits the other** (`stepFit_stuck_iff`): two different unknowns,
  and the comparisons of domains and codomains decide neither orientation.
* **The reading is the same at every valuation of the tower** (`readFitData_valuation_free`).

The comparisons are `S.R.cumulative` between heads; in the tower they are entailments over all valuations
(`tower_cumulative_iff`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

namespace TreeFibre

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist

section General

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L} [DecidableEq Head]
  [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

/-- **The step on a read equation is stuck exactly when neither unknown fits the other.** -/
theorem stepFit_stuck_iff {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (all : AllFamilies Θ) (v : FitFlex e)
    (rest : EquationStore (TotalTerm Θ)) :
    stepFit facts roots heads algebra rigid complete all v rest = .stuck ↔
      v.left ≠ v.right ∧ ¬ (S.R.cumulative v.pl v.pr ∧ S.R.cumulative v.cr v.cl) ∧
        ¬ (S.R.cumulative v.pr v.pl ∧ S.R.cumulative v.cl v.cr) := by
  unfold stepFit
  constructor
  · intro h
    split_ifs at h with h1 h2 h3
    exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    rw [dif_neg h1, dif_neg h2, dif_neg h3]

end General

/-- **The reading of a unary equation is the same at every valuation of the tower.** -/
theorem readFitData_valuation_free (valuation valuation' : Nat → Nat) {Θ : Context (LevelTower.rules Nat)}
    (e : Equation (TotalTerm Θ)) :
    readFitData (S := TowerModel.setting valuation) e = readFitData (S := TowerModel.setting valuation') e := rfl

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
