import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.SeveralGroups
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.LevelChoice

/-!
# Rule choice of the true meet without a level valuation

The solvers of meet groups choose their step from the codes of the store and from comparisons by `S.R.cumulative`
only; in the tower that is the order of level expressions at every valuation (`tower_cumulative_iff`).

* **The step is stuck exactly when no comparison decides it** (`stepMeetGroup_stuck_iff`,
  `stepMeetGroupK_stuck_iff`): two different unknowns of which neither fits the other and which do not meet in
  either orientation. Nothing is refuted and no direction is guessed: the store is postponed, with an exact residual.
* **The reading is the same at every valuation** (`readFlexK_valuation_free`, `meetComparableKB_valuation_free`).
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
  [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

omit [∀ head, Decidable (S.R.isUniverse head)] in
/-- **The unary step is stuck exactly when neither unknown fits the other and they do not meet.** -/
theorem stepMeetGroup_stuck_iff {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (all : AllFamilies Θ)
    (v : FitFlex e) (rest : EquationStore (TotalTerm Θ)) :
    stepMeetGroup facts roots heads algebra rigid complete all v rest = .stuck ↔
      v.left ≠ v.right ∧ ¬ (S.R.cumulative v.pl v.pr ∧ S.R.cumulative v.cr v.cl) ∧
        ¬ (S.R.cumulative v.pr v.pl ∧ S.R.cumulative v.cl v.cr) ∧ ¬ Meets v ∧ ¬ Meets v.swap := by
  unfold stepMeetGroup
  constructor
  · intro h
    split_ifs at h with h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    rw [dif_neg h1, dif_neg h2, dif_neg h3, dif_neg h4, dif_neg h5]

/-- **The step with several parameters is stuck exactly when neither unknown fits the other and they do not meet.** -/
theorem stepMeetGroupK_stuck_iff {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (all : AllFamilies Θ)
    (v : FlexK e) (rest : EquationStore (TotalTerm Θ)) :
    stepMeetGroupK facts roots heads algebra rigid complete all v rest = .stuck ↔
      v.left ≠ v.right ∧ ¬ v.Fits ∧ ¬ v.swap.Fits ∧ ¬ v.Meets ∧ ¬ v.swap.Meets := by
  unfold stepMeetGroupK
  constructor
  · intro h
    split_ifs at h with h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    rw [dif_neg h1, dif_neg h2, dif_neg h3, dif_neg h4, dif_neg h5]

end General

/-- **The reading with several parameters is the same at every valuation of the tower.** -/
theorem readFlexK_valuation_free (valuation valuation' : Nat → Nat) {Θ : Context (LevelTower.rules Nat)}
    (e : Equation (TotalTerm Θ)) :
    readFlexK (S := TowerModel.setting valuation) e = readFlexK (S := TowerModel.setting valuation') e := rfl

/-- **So is the comparison of the declared views.** -/
theorem meetComparableKB_valuation_free (valuation valuation' : Nat → Nat) {n : Nat}
    (Γ : Ctx (LevelTower.Head Nat) n) :
    meetComparableKB (S := TowerModel.setting valuation) Γ = meetComparableKB (S := TowerModel.setting valuation') Γ :=
  rfl

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
