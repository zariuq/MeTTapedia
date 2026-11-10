import Mettapedia.Cybernetics.DistinctionCalculus.PreservationGrade

/-!
# Consumer-sensitive approximation contracts

Uniform error bounds transport through Lipschitz consumers and compose with
their amplification factor. A threshold decision is protected by a margin
certificate, not by a small value error alone. These statements use arbitrary
pseudometric value spaces; they do not force costs or other observations into
one bounded similarity scale.
-/
set_option autoImplicit false
namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DistinctionSensitivity

universe uS uV uW
variable {S : Type uS} {V : Type uV} {W : Type uW}
  [PseudoMetricSpace V] [PseudoMetricSpace W]

def Approximates (read estimate : S → V) (error : ℝ) : Prop :=
  ∀ s, dist (read s) (estimate s) ≤ error

theorem Approximates.consumer {read estimate : S → V} {error : ℝ}
    (bound : Approximates read estimate error) {L : NNReal} {consume : V → W}
    (sensitive : LipschitzWith L consume) :
    Approximates (consume ∘ read) (consume ∘ estimate) ((L : ℝ) * error) := by
  intro s
  exact (sensitive.dist_le_mul _ _).trans (mul_le_mul_of_nonneg_left (bound s) L.coe_nonneg)

/-- A later approximation adds to the amplified earlier error. -/
theorem Approximates.comp {read estimate : S → V} {output : S → W} {error later : ℝ}
    (first : Approximates read estimate error) {L : NNReal} {consume : V → W}
    (sensitive : LipschitzWith L consume)
    (second : Approximates (consume ∘ estimate) output later) :
    Approximates (consume ∘ read) output ((L : ℝ) * error + later) := by
  intro s
  exact (dist_triangle _ (consume (estimate s)) _).trans
    (add_le_add (first.consumer sensitive s) (second s))

omit [PseudoMetricSpace V] [PseudoMetricSpace W] in
/-- Strict distance from the decision boundary prevents an approximate value from crossing it. -/
theorem threshold_preserved_of_margin {x y threshold error : ℝ}
    (close : |x - y| ≤ error) (margin : error < |x - threshold|) :
    (threshold ≤ x ↔ threshold ≤ y) := by
  obtain ⟨lower, upper⟩ := abs_le.mp close
  by_cases hx : threshold ≤ x
  · rw [abs_of_nonneg (sub_nonneg.mpr hx)] at margin
    have hy : threshold ≤ y := by linarith
    exact iff_of_true hx hy
  · have negative : x - threshold ≤ 0 := by linarith
    rw [abs_of_nonpos negative] at margin
    have hy : ¬ threshold ≤ y := by linarith
    exact iff_of_false hx hy

namespace Controls

def act (value : ℚ) : Bool := decide ((1 : ℚ) / 2 ≤ value)

theorem small_value_error_changes_action :
    |(49 : ℚ) / 100 - 51 / 100| = 1 / 50 ∧
      act (49 / 100) = false ∧ act (51 / 100) = true := by
  norm_num [act]

theorem protected_threshold :
    ((1 : ℝ) / 2 ≤ 49 / 100 ↔ (1 : ℝ) / 2 ≤ 99 / 200) :=
  threshold_preserved_of_margin (error := 1 / 200) (by norm_num) (by norm_num)

/-- An expanding consumer makes the unamplified error assertion false. -/
theorem amplification_matters :
    |(0 : ℝ) - 1| = 1 ∧ |2 * (0 : ℝ) - 2 * 1| = 2 ∧
      ¬ |2 * (0 : ℝ) - 2 * 1| ≤ 1 := by norm_num

end Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DistinctionSensitivity
