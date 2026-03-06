import Mettapedia.Logic.PLNWorldModelKripkeWeightedOverlap

/-!
# Weighted Overlap Regression Fixtures

Concrete positive/negative fixtures for provenance-overlap behavior:

* positive: disjoint sources recover additive revision via fallback,
* negative: overlapping sources reject merge and fallback to left state.
-/

namespace Mettapedia.Logic.PLNWorldModelKripkeWeightedOverlapRegression

open Mettapedia.Logic.PLNWorldModelKripkeWeighted
open Mettapedia.Logic.PLNWorldModelKripkeWeightedOverlap

abbrev PointedKripke := Mettapedia.Logic.PLNWorldModelKripkeWeighted.PointedKripke
abbrev WeightedSourcePointedKripke :=
  Mettapedia.Logic.PLNWorldModelKripkeWeighted.WeightedSourcePointedKripke
abbrev WeightedState := Mettapedia.Logic.PLNWorldModelKripkeWeighted.WeightedState

def wpLeft (pk : PointedKripke) : WeightedSourcePointedKripke :=
  { source := "srcA", weight := 2, point := pk }

def wpRightDisjoint (pk : PointedKripke) : WeightedSourcePointedKripke :=
  { source := "srcB", weight := 3, point := pk }

def wpRightOverlap (pk : PointedKripke) : WeightedSourcePointedKripke :=
  { source := "srcA", weight := 1, point := pk }

def leftState (pk : PointedKripke) : WeightedState :=
  ({wpLeft pk} : WeightedState)

def rightDisjointState (pk : PointedKripke) : WeightedState :=
  ({wpRightDisjoint pk} : WeightedState)

def rightOverlapState (pk : PointedKripke) : WeightedState :=
  ({wpRightOverlap pk} : WeightedState)

def forgetSrcB : String → Prop := fun s => s = "srcB"

instance forgetSrcBDecidablePred : DecidablePred forgetSrcB := by
  intro s
  unfold forgetSrcB
  infer_instance

/-- Positive fixture: disjoint-source states merge additively under fallback. -/
theorem fixture_disjoint_fallback_recovers_add
    (pkA pkB : PointedKripke) :
    fallbackRevision (leftState pkA) (rightDisjointState pkB) =
      (leftState pkA) + (rightDisjointState pkB) := by
  apply fallbackRevision_eq_add_of_compatible
  intro s hsL hsR
  have hsA : "srcA" = s := by
    simpa [sourceInState, leftState, wpLeft] using hsL
  have hsB : "srcB" = s := by
    simpa [sourceInState, rightDisjointState, wpRightDisjoint] using hsR
  have hEq : "srcA" = "srcB" := by
    calc
      "srcA" = s := hsA
      _ = "srcB" := hsB.symm
  simp at hEq

/-- Negative fixture: overlapping-source states do not merge and fallback keeps
the left state. -/
theorem fixture_overlap_fallback_rejects_to_left
    (pkA pkB : PointedKripke) :
    fallbackRevision (leftState pkA) (rightOverlapState pkB) = leftState pkA := by
  apply fallbackRevision_eq_left_of_not_compatible
  intro hcompat
  have hsL : sourceInState "srcA" (leftState pkA) := by
    simp [sourceInState, leftState, wpLeft]
  have hsR : sourceInState "srcA" (rightOverlapState pkB) := by
    simp [sourceInState, rightOverlapState, wpRightOverlap]
  exact hcompat "srcA" hsL hsR

theorem fixture_approx_safe_forgetting_preserves_left_sourceCount
    (pkA pkB : PointedKripke) :
    sourceCount "srcA"
        (fallbackRevision (leftState pkA)
          (forgetSources forgetSrcB (rightDisjointState pkB))) =
      sourceCount "srcA" (leftState pkA) := by
  have hcompat : compatible (leftState pkA) (rightDisjointState pkB) := by
    intro s hsL hsR
    have hsA : "srcA" = s := by
      simpa [sourceInState, leftState, wpLeft] using hsL
    have hsB : "srcB" = s := by
      simpa [sourceInState, rightDisjointState, wpRightDisjoint] using hsR
    have hEq : "srcA" = "srcB" := by
      calc
        "srcA" = s := hsA
        _ = "srcB" := hsB.symm
    simp at hEq
  have hsLeft : sourceInState "srcA" (leftState pkA) := by
    simp [sourceInState, leftState, wpLeft]
  exact
    approx_safe_forgetting_preserves_left_sourceCount
      (drop := forgetSrcB) (W₁ := leftState pkA) (W₂ := rightDisjointState pkB)
      hcompat hsLeft

theorem fixture_approx_safe_forgetting_no_double_count
    (pkA pkB : PointedKripke) :
    sourceCount "srcA" (leftState pkA) = 0 ∨
      sourceCount "srcA" (forgetSources forgetSrcB (rightDisjointState pkB)) = 0 := by
  have hcompat : compatible (leftState pkA) (rightDisjointState pkB) := by
    intro s hsL hsR
    have hsA : "srcA" = s := by
      simpa [sourceInState, leftState, wpLeft] using hsL
    have hsB : "srcB" = s := by
      simpa [sourceInState, rightDisjointState, wpRightDisjoint] using hsR
    have hEq : "srcA" = "srcB" := by
      calc
        "srcA" = s := hsA
        _ = "srcB" := hsB.symm
    simp at hEq
  exact
    approx_safe_forgetting_no_double_count_condition
      (drop := forgetSrcB) (W₁ := leftState pkA) (W₂ := rightDisjointState pkB)
      hcompat "srcA"

end Mettapedia.Logic.PLNWorldModelKripkeWeightedOverlapRegression
