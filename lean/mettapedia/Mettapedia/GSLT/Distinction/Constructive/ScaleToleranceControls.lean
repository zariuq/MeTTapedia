import Mettapedia.GSLT.Distinction.Constructive.ScaleTolerance
import Mettapedia.GSLT.Distinction.Constructive.Controls

/-!
# Controls for scale-valued tolerances

* **A depth bound as a tolerance** (`cells_depthTolerance_metric`,
  `cells_read_half`).  The depth bounds of the cell system of `Controls`, over
  the integers with unit `2`, are metric tolerances without a choice principle;
  read into `ℚ`, the resting and the half cell are similar to degree `1/2`, a
  metric tolerance of the distinction calculus.
* **A tolerance that is not metric** (`threshold_not_metric`).  Over the
  integers with unit `2`, a similarity that identifies `0` with `1` and `1`
  with `2` but separates `0` from `2` satisfies the tolerance laws and not the
  triangle inequality: zero distance is not transitive.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction.Constructive.ScaleToleranceControls

open Mettapedia.GSLT.Distinction.Constructive
open Mettapedia.GSLT.Distinction.Constructive.Controls

/-! ## A depth bound as a tolerance -/

/-- **Positive**: every depth bound of the cell system is a metric tolerance
over the integers. -/
theorem cells_depthTolerance_metric (depth : ℕ) :
    (cells.depthTolerance cellVocabulary depth).Metric :=
  cells.depthTolerance_metric cellVocabulary depth

/-- The integers with unit `2`, read as halves. -/
def halves : RatReading halfScale.one := RatReading.integers 2 (by decide)

/-- **Positive**: read into `ℚ`, the depth-`0` tolerance relates the resting
and the half cell to degree `1/2`, and it is a metric tolerance of the
distinction calculus. -/
theorem cells_read_half :
    ((cells.depthTolerance cellVocabulary 0).read halves).similarity .rest .half = 1 / 2 ∧
      ((cells.depthTolerance cellVocabulary 0).read halves).Metric := by
  refine ⟨?_, depthTolerance_read_metric cells cellVocabulary 0 halves⟩
  change (((2 : ℤ) - cells.depthBound cellVocabulary 0 .rest .half : ℤ) : ℚ) / (2 : ℤ) = 1 / 2
  rw [cells_rest_half]
  norm_num

/-! ## A tolerance that is not metric -/

/-- `0` and `1` are similar, `1` and `2` are similar, `0` and `2` are not. -/
def threshold : ScaleTolerance (Fin 3) (2 : ℤ) where
  similarity x y := if (x = 0 ∧ y = 2) ∨ (x = 2 ∧ y = 0) then 0 else 2
  nonnegative := by decide
  bounded := by decide
  reflexive := by decide
  symmetric := by decide

/-- **Negative**: the tolerance laws hold and the triangle inequality fails;
zero distance is not transitive. -/
theorem threshold_not_metric :
    threshold.distance 0 1 = 0 ∧ threshold.distance 1 2 = 0 ∧ threshold.distance 0 2 = 2 ∧
      ¬ threshold.Metric := by
  refine ⟨by decide, by decide, by decide, fun metric => ?_⟩
  have triangle := metric 0 1 2
  revert triangle
  decide

end Mettapedia.GSLT.Distinction.Constructive.ScaleToleranceControls
