import Mettapedia.Algorithms.NQueensSummary

/-!
# Positive and negative controls for N-queens summary correspondence

These controls concern the mathematical scans and summaries. They do not
claim that a MeTTa parser, runtime, or optimizer implements the transformation.
-/

namespace Mettapedia.Algorithms.NQueensSummary.Controls

set_option autoImplicit false

theorem safe_completion :
    ScanSafe 3 [1, 4, 2] 1 ∧ AllowedAt 3 3 (ofPlaced [1, 4, 2]) := by decide

theorem absolute_scan_agrees : AbsScanSafe 3 [1, 4, 2] 1 :=
  (absScanSafe_iff 3 [1, 4, 2] 1).mpr safe_completion.1

theorem column_collision :
    ¬ ScanSafe 4 [1, 4, 2] 1 ∧ ¬ AllowedAt 3 4 (ofPlaced [1, 4, 2]) := by decide

theorem ascending_diagonal_collision :
    ¬ ScanSafe 2 [1] 1 ∧ ¬ AllowedAt 1 2 (ofPlaced [1]) := by decide

theorem descending_diagonal_collision :
    ¬ ScanSafe 1 [2] 1 ∧ ¬ AllowedAt 1 1 (ofPlaced [2]) := by decide

/-- The second stored queen is two rows away, not one. -/
theorem older_queen_distance_matters :
    ¬ ScanSafe 3 [6, 1] 1 ∧ ¬ AllowedAt 2 3 (ofPlaced [6, 1]) := by decide

/-- Dropping one diagonal component admits a genuinely forbidden placement. -/
def missingDifference : Summary := { ofPlaced [1] with differenceDiagonals := ∅ }

theorem wrong_summary_admits_collision :
    AllowedAt 1 2 missingDifference ∧ ¬ ScanSafe 2 [1] 1 := by decide

/-- Truncated natural subtraction aliases distinct negative integer diagonals
and can reject a placement which the actual scan permits. -/
theorem natural_subtraction_false_collision :
    ScanSafe 3 [1, 6, 8, 10] 1 ∧
      AllowedAt 4 3 (ofPlaced [1, 6, 8, 10]) ∧
      ((3 : Nat) - 4 = (1 : Nat) - 3) ∧
      ((3 : Int) - 4 ≠ (1 : Int) - 3) := by decide

theorem bounds_not_erased :
    ScanSafe 5 [] 1 ∧ ¬ Permitted 4 [] 5 := by decide

/-- Repeated candidate occurrences remain repeated completed answers. -/
theorem repeated_choices_retained :
    enumerateScan [1, 1] 1 [] = [[1], [1]] ∧
      enumerateSummary [1, 1] 1 [] (ofPlaced []) = [[1], [1]] := by decide

theorem four_queen_answers :
    enumerateScan [1, 2, 3, 4] 4 [] = [[3, 1, 4, 2], [2, 4, 1, 3]] := by decide

theorem four_queen_summary_answers :
    enumerateSummary [1, 2, 3, 4] 4 [] (ofPlaced []) =
      [[3, 1, 4, 2], [2, 4, 1, 3]] := by
  rw [← enumeration_equal]
  exact four_queen_answers

end Mettapedia.Algorithms.NQueensSummary.Controls
