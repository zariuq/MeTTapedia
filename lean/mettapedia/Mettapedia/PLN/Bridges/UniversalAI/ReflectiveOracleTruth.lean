import Mettapedia.UniversalAI.ReflectiveOracles.Basic
import Mettapedia.PLN.TruthValues.PLNIndefiniteTruth

/-!
# Bridge: a queried machine carries a PLN indefinite truth value

This is a bridge between `UniversalAI/ReflectiveOracles` and
`PLN/TruthValues`.

A machine that may give no output does not determine the probability of output
`1`: it determines an interval. The lower end is the probability that it
outputs `1`; the upper end is one minus the probability that it outputs `0`;
the length is the probability that it gives no output.

This is the indefinite truth value of PLN (Goertzel, Iklé et al. 2009): lower
and upper probability together with a credibility. Here the credibility is the
probability that the machine gives an output at all, and

`width + credibility = 1`,

the law that `PLN/TruthValues/PLNIndefiniteTruth.lean` proves for Walley's
imprecise Dirichlet model. A machine that sometimes gives no output is exactly
the predictive interval of that model for the evidence counts

`n⁺ = P(output 1) / P(no output)`, `n⁻ = P(output 0) / P(no output)`

with prior strength one: one unit of prior weight for the runs without output.

Reflectivity then reads: the oracle answers `1` when the threshold lies below
the interval, `0` when it lies above, and may answer anything when the
threshold lies inside. A reflective oracle is a consistent way of answering
threshold questions about indefinite probabilities, including those of
machines that consult the oracle.

## Main statements

* `outputTruth`: the indefinite truth value of a query.
* `outputTruth_width`, `outputTruth_width_add_credibility`.
* `outputTruth_eq_fromWalleyIDMPredictive`: for a machine that gives no output
  with positive probability, the three components are those of the Walley
  predictive interval of `outputEvidence` with prior strength one.
* `outputTruth_point_of_noOutput_eq_zero`: a machine that almost surely gives
  an output has a point interval with credibility one.
* `reflectiveAt_iff_outputTruth`: the definition of a reflective oracle in
  terms of the interval.
-/

set_option autoImplicit false

namespace Mettapedia.PLN.Bridges.UniversalAI.ReflectiveOracleTruth

open scoped unitInterval ENNReal
open Mettapedia.UniversalAI.ReflectiveOracles
open Mettapedia.PLN.TruthValues.PLNIndefiniteTruth
open Mettapedia.PLN.Evidence.EvidenceQuantale

universe u

variable {Q : Type u} (S : QuerySystem Q)

/-- The indefinite truth value of "the queried machine outputs `1`": from the
probability of output `1` to one minus the probability of output `0`, with the
probability of an output as credibility. -/
noncomputable def outputTruth (q : Q) (O : Oracle Q) : ITV where
  lower := S.outputOne q O
  upper := S.upper q O
  credibility := S.outputOne q O + S.outputZero q O
  lower_le_upper := S.outputOne_le_upper q O
  lower_in_unit :=
    ⟨S.outputOne_nonneg q O, by linarith [S.output_le_one q O, S.outputZero_nonneg q O]⟩
  upper_in_unit := by
    unfold QuerySystem.upper
    exact ⟨by linarith [S.output_le_one q O, S.outputOne_nonneg q O],
      by linarith [S.outputZero_nonneg q O]⟩
  credibility_in_unit :=
    ⟨add_nonneg (S.outputOne_nonneg q O) (S.outputZero_nonneg q O), S.output_le_one q O⟩

/-- The width of the interval is the probability of no output. -/
theorem outputTruth_width (q : Q) (O : Oracle Q) :
    (outputTruth S q O).width = S.noOutput q O := by
  unfold ITV.width outputTruth
  exact S.upper_sub_outputOne q O

/-- Width and credibility add up to one: the law of Walley's predictive
intervals. -/
theorem outputTruth_width_add_credibility (q : Q) (O : Oracle Q) :
    (outputTruth S q O).width + (outputTruth S q O).credibility = 1 := by
  rw [outputTruth_width]
  unfold QuerySystem.noOutput outputTruth
  ring

/-- **A reflective oracle answers threshold questions about the interval.** -/
theorem reflectiveAt_iff_outputTruth (O : Oracle Q) (q : Q) :
    S.ReflectiveAt O q ↔
      (S.threshold q < (outputTruth S q O).lower → O q = 1) ∧
        ((outputTruth S q O).upper < S.threshold q → O q = 0) :=
  S.reflectiveAt_iff_interval O q

/-- A machine that almost surely gives an output has a point interval, with
credibility one. -/
theorem outputTruth_point_of_noOutput_eq_zero (q : Q) (O : Oracle Q)
    (halts : S.noOutput q O = 0) :
    (outputTruth S q O).lower = (outputTruth S q O).upper ∧
      (outputTruth S q O).credibility = 1 := by
  have width := outputTruth_width S q O
  have law := outputTruth_width_add_credibility S q O
  rw [halts] at width
  unfold ITV.width at width
  exact ⟨by linarith, by rw [show (outputTruth S q O).width = 0 from by
    unfold ITV.width; linarith] at law; linarith⟩

/-- The evidence counts behind the interval: the probabilities of the two
outputs, in units of the probability of no output. -/
noncomputable def outputEvidence (q : Q) (O : Oracle Q) : BinaryEvidence where
  pos := ENNReal.ofReal (S.outputOne q O / S.noOutput q O)
  neg := ENNReal.ofReal (S.outputZero q O / S.noOutput q O)

/-- **A machine that sometimes gives no output is a Walley predictive
interval.** Its indefinite truth value is the one obtained from the evidence
counts `outputEvidence` with prior strength one. -/
theorem outputTruth_eq_fromWalleyIDMPredictive (q : Q) (O : Oracle Q)
    (positive : 0 < S.noOutput q O) :
    (outputTruth S q O).lower =
        (ITV.fromWalleyIDMPredictive (outputEvidence S q O) 1 one_pos).lower ∧
      (outputTruth S q O).upper =
        (ITV.fromWalleyIDMPredictive (outputEvidence S q O) 1 one_pos).upper ∧
      (outputTruth S q O).credibility =
        (ITV.fromWalleyIDMPredictive (outputEvidence S q O) 1 one_pos).credibility := by
  have one := S.outputOne_nonneg q O
  have zero := S.outputZero_nonneg q O
  have positiveCount : (outputEvidence S q O).pos.toReal = S.outputOne q O / S.noOutput q O :=
    ENNReal.toReal_ofReal (div_nonneg one positive.le)
  have negativeCount : (outputEvidence S q O).neg.toReal = S.outputZero q O / S.noOutput q O :=
    ENNReal.toReal_ofReal (div_nonneg zero positive.le)
  have total : S.outputOne q O / S.noOutput q O + S.outputZero q O / S.noOutput q O + 1 =
      1 / S.noOutput q O := by
    unfold QuerySystem.noOutput at positive ⊢
    field_simp
    ring
  rw [ITV.fromWalleyIDMPredictive_lower, ITV.fromWalleyIDMPredictive_upper,
    ITV.fromWalleyIDMPredictive_credibility, positiveCount, negativeCount, total]
  unfold outputTruth QuerySystem.upper
  simp only
  unfold QuerySystem.noOutput at positive ⊢
  refine ⟨?_, ?_, ?_⟩
  · field_simp
  · field_simp
    ring
  · field_simp

end Mettapedia.PLN.Bridges.UniversalAI.ReflectiveOracleTruth
