import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.FamilyControls

/-!
# Rule choice without a level valuation

The rules of `FamilySolver` choose their step from the codes of the store and from one comparison,
`S.R.cumulative`, between two codomain heads.

* **The step is stuck exactly when the comparison is undecided** (`stepOf_stuck_iff`): two different unknowns whose
  codomains lie below each other in neither direction. Nothing is refuted and no direction is guessed: the store is
  postponed, with an exact residual.
* **In the tower the comparison is an entailment** (`tower_cumulative_iff`): one universe lies below another exactly
  when its level expression is below at every valuation. The valuation that the tower's setting carries does not
  enter.
* **The reading is the same at every valuation** (`readFlexData_valuation_free`, `allFamiliesB_valuation_free`):
  over the tower's rules, reading a store at the settings of two valuations is one function.

Of the two ways to make the choice valuation-free, a `min` in the level language and the postponement of undecided
comparisons, this is the second. The tower's level language has `max` and no `min`; a meet of two incomparable
codomains is then not always a universe of the language, and where it is one, deciding the store by it needs every
solution's value to lie in that meet, which is a statement about the normal forms of the fibre.
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

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L} [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

/-- **The step on a read equation is stuck exactly when the comparison is undecided.** -/
theorem stepOf_stuck_iff {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (all : AllFamilies Θ) (v : FlexFlex e)
    (rest : EquationStore (TotalTerm Θ)) :
    stepOf facts roots heads algebra rigid complete all v rest = .stuck ↔
      v.left ≠ v.right ∧ ¬ S.R.cumulative v.cl v.cr ∧ ¬ S.R.cumulative v.cr v.cl := by
  unfold stepOf
  constructor
  · intro h
    split_ifs at h with h1 h2 h3
    exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    rw [dif_neg h1, dif_neg h2, dif_neg h3]

end General

section Tower

open UniverseLevel

/-- Whether a head of the tower is a universe, decided, at the setting of any valuation. -/
instance towerUniverseDecidable (valuation : Nat → Nat) (head : LevelTower.Head Nat) :
    Decidable ((TowerModel.setting valuation).R.isUniverse head) :=
  inferInstanceAs (Decidable (LevelTower.IsUniverse head))

/-- The comparison of the tower, decided, at the setting of any valuation. -/
instance towerCumulativeDecidable (valuation : Nat → Nat) :
    DecidableRel (TowerModel.setting valuation).R.cumulative :=
  fun first second => inferInstanceAs (Decidable (LevelTower.Cumulative first second))

/-- **In the tower the comparison is an entailment over all valuations**; the setting's own valuation does not
enter. -/
theorem tower_cumulative_iff (valuation : Nat → Nat) (l r : LevelExpr Nat) :
    (TowerModel.setting valuation).R.cumulative (.sort l) (.sort r) ↔ ∀ w, LevelExpr.eval w l ≤ LevelExpr.eval w r :=
  Iff.rfl

/-- **The reading of an equation is the same at every valuation of the tower.** -/
theorem readFlexData_valuation_free (valuation valuation' : Nat → Nat) {Θ : Context (LevelTower.rules Nat)}
    (e : Equation (TotalTerm Θ)) :
    readFlexData (S := TowerModel.setting valuation) e = readFlexData (S := TowerModel.setting valuation') e := rfl

/-- **So is the reading of the declarations.** -/
theorem allFamiliesB_valuation_free (valuation valuation' : Nat → Nat) (Θ : Context (LevelTower.rules Nat)) :
    allFamiliesB (S := TowerModel.setting valuation) Θ = allFamiliesB (S := TowerModel.setting valuation') Θ := rfl

end Tower

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
