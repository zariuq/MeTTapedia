import Mettapedia.GSLT.Scope.ReadoutDescent
import Mettapedia.GSLT.Dynamics.WeightedResumption
import Mettapedia.Algebra.RationalComplexAmplitude

/-!
# Views of weighted contributions

Readouts use the existing descent law. Erasing coefficients preserves physical
occurrence existence. A total coefficient can forget multiplicity, and an
answer-only view can forget coefficient totals. Cancellation separates the
existence of contributing work from nonzero aggregate support.

Equal Born intensity does not determine interference with a later amplitude:
the phase distinction must remain available for that consumer.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Scope.WeightedReadout

open scoped QuadraticAlgebra

open Mettapedia.GSLT.Core.NonFactorization
open Mettapedia.GSLT.Dynamics
open Mettapedia.GSLT.Dynamics.WeightedResumption
open Mettapedia.Algebra.RationalComplexAmplitude

universe u v

theorem occurrence_existence_factors_erasure {Answer : Type u} {V : Type v} :
    Factors (eraseCoefficients (Answer := Answer) (V := V))
      (fun answers => answers ≠ []) := by
  refine ⟨fun answers => answers ≠ [], fun answers => ?_⟩
  simp [eraseCoefficients]

def twoContributions : Contributions Unit Nat := [((), 2), ((), 3)]
def oneContribution : Contributions Unit Nat := [((), 5)]

theorem same_total_different_multiplicity :
    total twoContributions = total oneContribution ∧
      twoContributions.length ≠ oneContribution.length := by decide +kernel

theorem multiplicity_not_factors_total :
    ¬ Factors (total (Answer := Unit) (V := Nat)) List.length :=
  NonTrivialFiber.not_factors
    ⟨twoContributions, oneContribution, same_total_different_multiplicity.1,
      same_total_different_multiplicity.2⟩

theorem total_not_factors_answer_erasure :
    ¬ Factors (eraseCoefficients (Answer := Unit) (V := Nat)) total := by
  apply NonTrivialFiber.not_factors
  exact ⟨[((), 1)], [((), 2)], rfl, by decide +kernel⟩

/-- At total five, there may be two occurrences, but that is not certain. -/
theorem aggregate_liftings_disagree :
    total twoContributions ∈ total '' {answers : Contributions Unit Nat | 2 ≤ answers.length} ∧
      total twoContributions ∉ Set.kernImage total
        {answers : Contributions Unit Nat | 2 ≤ answers.length} := by
  refine ⟨⟨twoContributions, by decide +kernel, rfl⟩, ?_⟩
  intro allRepresentatives
  have tooShort := allRepresentatives (x := oneContribution)
    same_total_different_multiplicity.1.symm
  norm_num [oneContribution] at tooShort

def cancellingContributions : Contributions Unit Amplitude := [((), 1), ((), -1)]

theorem cancellation_retains_occurrences :
    total cancellingContributions = total ([] : Contributions Unit Amplitude) ∧
      eraseCoefficients cancellingContributions = [(), ()] := by
  simp [total, cancellingContributions, SemiringTraversal.weightSum, eraseCoefficients]

/-- A nonzero aggregate is insufficient to recover physical reachability in
an algebra that permits cancellation. -/
theorem occurrence_existence_not_factors_complex_total :
    ¬ Factors (total (Answer := Unit) (V := Amplitude)) (fun answers => answers ≠ []) :=
  (NonTrivialFiber.ofProp cancellation_retains_occurrences.1
    (by simp [cancellingContributions]) (by simp)).not_factors

def interferenceAfter (amplitude : Amplitude) : ℚ := born (amplitude + 1)

theorem same_intensity_different_future_interference :
    born (1 : Amplitude) = born (-1) ∧ interferenceAfter 1 ≠ interferenceAfter (-1) := by
  constructor
  · norm_num [born, QuadraticAlgebra.norm_def, Amplitude]
  · norm_num [interferenceAfter, born, QuadraticAlgebra.norm_def, Amplitude]

theorem future_interference_not_factors_born : ¬ Factors born interferenceAfter :=
  NonTrivialFiber.not_factors
    ⟨1, -1, same_intensity_different_future_interference.1,
      same_intensity_different_future_interference.2⟩

end Mettapedia.GSLT.Scope.WeightedReadout
