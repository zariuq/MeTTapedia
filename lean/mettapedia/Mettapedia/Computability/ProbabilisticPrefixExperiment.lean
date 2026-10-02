import Mettapedia.Computability.ProbabilisticTM
import Mettapedia.Computability.BoundedTapeRuns

/-!
# The packed-prefix experiments as bounded runs

The runs of a code on the packed prefix of the tape (`ProbabilisticTM.lean`)
form a family bounded by a budget and by the prefix offered, and a run reads
only the prefix it is offered. So the results of `BoundedTapeRuns` apply to
every code: the output event is the increasing union of its stages, the
probability of a stage is an executable rational number, and these numbers
increase to the output probability.

This does not make the output of a code unique. On the packed encoding one
tape can give two outputs (`ProbabilisticTMBoundary`); uniqueness is a
consequence of prefix consistency (`ProbabilisticPrefixConsistency`).
-/

open MeasureTheory Measure Filter
open scoped ENNReal NNReal

namespace Mettapedia.Computability

/-- The runs of a code on an input, on the packed prefix of the tape. -/
def ptmRun (M : PTMIndex) (x : ℕ) : BoundedRun :=
  fun r fuel numBits => runPTMBounded M x r fuel numBits

theorem ptmRun_readsPrefix (M : PTMIndex) (x : ℕ) : (ptmRun M x).ReadsPrefix := by
  intro first second fuel numBits same
  simp only [ptmRun, runPTMBounded, encodeRandomBits_firstN first second numBits same]

theorem ptmRun_fuelMonotone (M : PTMIndex) (x : ℕ) : (ptmRun M x).FuelMonotone :=
  fun _ _ _ _ _ bound halted => Nat.Partrec.Code.evaln_mono bound halted

theorem ptmRun_outputSet (M : PTMIndex) (x output : ℕ) :
    (ptmRun M x).outputSet output = {r | PTMHaltsWithOutput M x r output} := rfl

/-- The probability that the code outputs 1 with budget and prefix at most the
stage. -/
noncomputable def stageOutputProb (M : PTMIndex) (x stage : ℕ) : ℝ≥0∞ :=
  coinMeasure ((ptmRun M x).stageSet 1 stage)

/-- **Convergence.** For every code the probabilities of the stages converge
to the output probability. -/
theorem stageOutputProb_tendsto (M : PTMIndex) (x : ℕ) :
    Tendsto (fun stage => stageOutputProb M x stage) atTop (nhds (outputProb M x)) :=
  (ptmRun M x).tendsto_measure_stageSet coinMeasure 1

/-- **Approximation of the one-output probability from below.** The rational
counts of accepted prefixes increase with the stage, never exceed
`outputProb M x`, and converge to it. The approximating sequence is the
explicit function `BoundedRun.fraction`; no witness is chosen. -/
theorem outputProb_approximated_from_below (M : PTMIndex) (x : ℕ) :
    Monotone ((ptmRun M x).fraction 1) ∧
      (∀ stage, ENNReal.ofReal ((ptmRun M x).fraction 1 stage : ℝ) ≤ outputProb M x) ∧
      Tendsto (fun stage => ENNReal.ofReal ((ptmRun M x).fraction 1 stage : ℝ)) atTop
        (nhds (outputProb M x)) :=
  (ptmRun_readsPrefix M x).approximated_from_below 1

end Mettapedia.Computability
