import Mettapedia.PLN.WorldModel.FiniteProbabilisticPrograms
import Mettapedia.PLN.WorldModel.BayesianObservationLedger
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-! # Finite scored programs denote the measurable observation update -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.PLN.WorldModel.ProgramObservationDenotation

open MeasureTheory
open Mettapedia.PLN.WorldModel.FiniteProbabilisticPrograms
open Mettapedia.PLN.WorldModel.BayesianObservationLedger
open scoped ENNReal

variable {α : Type} [MeasurableSpace α] [MeasurableSingletonClass α]

def denote : Program α → Measure α
  | .pure value => Measure.dirac value
  | .fail => 0
  | .choice p _ yes no => (p : ℝ≥0∞) • denote yes + ((1 - p : ℚ≥0) : ℝ≥0∞) • denote no
  | .score weight body => (weight : ℝ≥0∞) • denote body

theorem dirac_score (value : α) (likelihood : α → ℝ≥0∞) :
    (Measure.dirac value).withDensity likelihood = likelihood value • Measure.dirac value := by
  classical
  ext event measurable
  rw [withDensity_apply _ measurable, setLIntegral_dirac]
  by_cases member : value ∈ event <;>
    simp [Measure.smul_apply, Measure.dirac_apply', measurable, member]

/-- Program-level observation and measure-level density updating commute.
The assertion is proved by the real syntax induction, including weighted
branching and scoring; it is not an assumed compiler contract. -/
theorem observe_denote (program : Program α) (likelihood : α → ℚ≥0) :
    denote (program.observe likelihood) =
      (denote program).withDensity (fun value => (likelihood value : ℝ≥0∞)) := by
  induction program with
  | pure value => simpa [Program.observe, Program.bind, denote] using
      (dirac_score value (fun value => (likelihood value : ℝ≥0∞))).symm
  | fail => simp [Program.observe, Program.bind, denote]
  | choice p bounded yes no iy ino =>
      simpa only [Program.observe, Program.bind, denote, withDensity_add_measure,
        withDensity_smul_measure] using congrArg₂ (fun a b => (p : ℝ≥0∞) • a +
          ((1 - p : ℚ≥0) : ℝ≥0∞) • b) iy ino
  | score weight body ih =>
      simpa only [Program.observe, Program.bind, denote, withDensity_smul_measure] using
        congrArg (fun measure => (weight : ℝ≥0∞) • measure) ih

/-- Normalization after executing an observation is exactly the ledger's
Bayesian readout, including refusal at zero or infinite mass. -/
theorem observe_posterior (program : Program α) (likelihood : α → ℚ≥0) :
    posterior? (denote (program.observe likelihood)) =
      posterior? ((denote program).withDensity (fun value => (likelihood value : ℝ≥0∞))) := by
  rw [observe_denote]

private theorem cast_add (first second : ℚ≥0) :
    ((first + second : ℚ≥0) : ℝ≥0∞) = (first : ℝ≥0∞) + (second : ℝ≥0∞) := by
  change (((first + second : ℚ≥0) : NNReal) : ℝ≥0∞) = _
  rw [NNRat.cast_add, ENNReal.coe_add]
  rfl

private theorem cast_mul (first second : ℚ≥0) :
    ((first * second : ℚ≥0) : ℝ≥0∞) = (first : ℝ≥0∞) * (second : ℝ≥0∞) := by
  change (((first * second : ℚ≥0) : NNReal) : ℝ≥0∞) = _
  rw [NNRat.cast_mul, ENNReal.coe_mul]
  rfl

/-- The rational expectation interpreter and measure integration agree on
every rational nonnegative observable. -/
theorem expect_denote (program : Program α) (observable : α → ℚ≥0) :
    ∫⁻ value, (observable value : ℝ≥0∞) ∂denote program = (program.expect observable : ℝ≥0∞) := by
  induction program with
  | pure value => simp [denote, Program.expect]
  | fail => simp [denote, Program.expect, ← ENNReal.coe_nnratCast, NNRat.cast_zero]
  | choice p bounded yes no iy ino =>
      simp only [denote, Program.expect, lintegral_add_measure, lintegral_smul_measure, smul_eq_mul]
      rw [iy, ino, cast_add, cast_mul, cast_mul]
  | score weight body ih =>
      simp only [denote, Program.expect, lintegral_smul_measure, smul_eq_mul]
      rw [ih, cast_mul]

/-- Compile a history of conditional observation factors into the actual
scored program. History order agrees with the measurable ledger. -/
def executeHistory {Event : Type*} (program : Program α)
    (likelihood : List Event → Event → α → ℚ≥0) : List Event → Program α
  | [] => program
  | event :: history =>
      (executeHistory program likelihood history).observe (likelihood history event)

def rationalModel {Event : Type*} (likelihood : List Event → Event → α → ℚ≥0)
    (measurable : ∀ history event, Measurable (fun value =>
      (likelihood history event value : ℝ≥0∞))) : ObservationModel α Event :=
  ⟨fun history event value => (likelihood history event value : ℝ≥0∞), measurable⟩

/-- The program executor, measurable ledger and Bayes density update form
one commuting interpretation, for every finite observation history. -/
theorem executeHistory_denote {Event : Type*} (program : Program α)
    (likelihood : List Event → Event → α → ℚ≥0)
    (measurable : ∀ history event, Measurable (fun value =>
      (likelihood history event value : ℝ≥0∞))) (history : List Event) :
    denote (executeHistory program likelihood history) =
      (rationalModel likelihood measurable).denote (denote program) history := by
  induction history with
  | nil => simp [executeHistory, ObservationModel.denote, ObservationModel.density]
  | cons event history ih =>
      rw [executeHistory, observe_denote, ih]
      exact (withDensity_mul (denote program)
        ((rationalModel likelihood measurable).density_measurable history)
        (measurable history event)).symm

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
theorem executeHistory_replay {Event : Type*} [DecidableEq Event]
    (program : Program α) (likelihood : List Event → Event → α → ℚ≥0)
    (history : List Event) (event : Event) (seen : event ∈ history) :
    executeHistory program likelihood (ObservationModel.record history event) =
      executeHistory program likelihood history := by
  rw [ObservationModel.record_replay history event seen]

#print axioms observe_denote
#print axioms expect_denote
#print axioms executeHistory_denote

end Mettapedia.PLN.WorldModel.ProgramObservationDenotation
