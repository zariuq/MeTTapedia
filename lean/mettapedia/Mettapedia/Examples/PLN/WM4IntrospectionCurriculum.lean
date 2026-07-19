import Mathlib.Tactic
import Mettapedia.PLN.Bridges.HOL.Introspection

/-!
# WM-4 introspection curriculum example

This wrapper makes the proof-witness query surface easy to find from the PLN
examples room: why, how strongly, what breaks, and whether re-derivation is
worth the budget.
-/

namespace Mettapedia.Examples.PLN.WM4IntrospectionCurriculum

open Mettapedia.Logic.HOL
open Mettapedia.PLN.Bridges.HOL.Introspection
open scoped ENNReal

noncomputable section

universe u v

variable {Base : Type u} {Const : Ty Base → Type v}

/-! ## Positive case: a concrete proof witness exposes sources, strength, and cost -/

/-- The existing `top ∧ top` witness supplies source, strength, and cost
readouts in one concrete example. -/
theorem top_and_top_positive
    (T : ClosedTheorySet Const) :
    let claim : ClosedFormula Const :=
      .and (.top : ClosedFormula Const) (.top : ClosedFormula Const)
    let w := ClosedTheorySet.topAndTopWitness (Const := Const) T
    sourceBreaks (Const := Const) w ∈
        ClosedTheorySet.sourceIdeal (Const := Const) T claim ∧
      howStronglyCount (Const := Const) w = 1 ∧
      worthCost (Const := Const) w = 3 ∧
      3 ∈ ClosedTheorySet.costSpectrum (Const := Const) T claim ∧
      6 ∈ ClosedTheorySet.costSpectrum (Const := Const) T claim :=
  topAndTop_positive_example (Const := Const) T

/-- A stale proof at cost `3` is worth re-deriving under budget `3`. -/
def staleWithinBudgetPolicy
    (T : ClosedTheorySet Const) (φ : ClosedFormula Const)
    (threshold : Nat) : ReDerivationPolicy (Const := Const) T φ where
  stale := fun _ => True
  threshold := threshold

theorem top_and_top_worth_budget_three
    (T : ClosedTheorySet Const) :
    let claim : ClosedFormula Const :=
      .and (.top : ClosedFormula Const) (.top : ClosedFormula Const)
    let w := ClosedTheorySet.topAndTopWitness (Const := Const) T
    worthReDeriving (Const := Const)
      (staleWithinBudgetPolicy (Const := Const) T claim 3) w := by
  dsimp [staleWithinBudgetPolicy, worthReDeriving, worthCost, proofCost,
    ClosedTheorySet.topAndTopWitness]
  norm_num

/-! ## Negative case: source-free and over-budget reruns are rejected -/

/-- Generic negative source example: when every witness uses a source,
`whatBreaks` reports that removing it blocks a source-free proof. -/
theorem essential_source_what_breaks_negative
    {T : ClosedTheorySet Const} {φ : ClosedFormula Const}
    {s : DerivationTree.SourceToken (Base := Base) Const}
    (e : EssentialSource (Const := Const) T φ s)
    {pA pB pC sAB sBC : ℝ}
    (needs : DeductionExactnessNeeds pA pB pC sAB sBC) :
    let breaks := whatBreaks (Const := Const) e.witness needs
    breaks.sourceTokens ∈ ClosedTheorySet.sourceIdeal (Const := Const) T φ ∧
      ¬ TreeProvableAvoiding (Const := Const) T φ s :=
  whatBreaks_negative_example (Const := Const) e needs

/-- Negative budget example: the same stale proof is not worth re-deriving
under budget `2`. -/
theorem top_and_top_not_worth_budget_two
    (T : ClosedTheorySet Const) :
    let claim : ClosedFormula Const :=
      .and (.top : ClosedFormula Const) (.top : ClosedFormula Const)
    let w := ClosedTheorySet.topAndTopWitness (Const := Const) T
    ¬ worthReDeriving (Const := Const)
      (staleWithinBudgetPolicy (Const := Const) T claim 2) w := by
  dsimp [staleWithinBudgetPolicy, worthReDeriving, worthCost, proofCost,
    ClosedTheorySet.topAndTopWitness]
  norm_num

end

end Mettapedia.Examples.PLN.WM4IntrospectionCurriculum
