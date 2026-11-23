import Mettapedia.DecisionTheory.ThresholdDecision
import Mettapedia.ProbabilityTheory.FiniteObservationSelection
import Mettapedia.ProbabilityTheory.StochasticInference.BinaryChangePoint
import Mettapedia.ProbabilityTheory.StochasticInference.BinaryLikelihoodEnvelope

/-! # Controls for benchmark information and decision contracts -/

set_option autoImplicit false

namespace Mettapedia.Examples.PLN.BenchmarkSemanticsControls

open Mettapedia.ProbabilityTheory
open StochasticInference
open BinaryLikelihoodEnvelope
open Mettapedia.DecisionTheory.ThresholdDecision

section Selection

open FiniteObservationSelection

theorem visible_selection_preserves_the_forecast :
    let shown : Bool × Bool → Bool := Prod.fst
    let accept : Bool × Bool → ℝ := fun w => if shown w then 2 / 3 else 1 / 10
    posterior accept shown Prod.snd = posterior (fun _ => 1) shown Prod.snd := by
  let shown : Bool × Bool → Bool := Prod.fst
  change posterior (fun w => if shown w then 2 / 3 else 1 / 10) shown Prod.snd = _
  simpa only [mul_one] using posterior_eq_of_constant (fun _ : Bool × Bool => 1)
    (fun w => if shown w then 2 / 3 else 1 / 10) shown (2 / 3) (by norm_num)
    (fun w present _ => by simp [present]) Prod.snd

theorem hidden_selection_can_change_the_forecast :
    posterior (fun w : Bool => if w then 1 else 0) (fun _ => true) id = 1 ∧
    posterior (fun _ : Bool => 1) (fun _ => true) id = 1 / 2 := by
  norm_num [posterior, FiniteEventMass.mass, Fintype.sum_bool]

end Selection

private def positivePair (no yes : UnitProbability) : Message := fun b => if b then yes else no

private def omittedTerminal : Message :=
  positivePair ⟨1, by decide, by decide⟩ ⟨0, by decide, by decide⟩

private def inspectedPath : List Kernel :=
  [positivePair ⟨1 / 16, by decide +kernel, by decide +kernel⟩
      ⟨15 / 16, by decide +kernel, by decide +kernel⟩,
    positivePair ⟨1 / 8, by decide +kernel, by decide +kernel⟩
      ⟨7 / 8, by decide +kernel, by decide +kernel⟩,
    positivePair ⟨1 / 10, by decide +kernel, by decide +kernel⟩
      ⟨9 / 10, by decide +kernel, by decide +kernel⟩]

private def afterLocal : UnitProbability := ⟨3 / 4, by decide +kernel, by decide +kernel⟩

def lateInterval (budget : Nat) : Option (ℚ × ℚ) :=
  (partialMass afterLocal (bounds budget omittedTerminal inspectedPath)).interval

theorem late_report_changes_the_decision :
    [lateInterval 0, lateInterval 1, lateInterval 2, lateInterval 3] =
      [some (0, 1), some (1 / 6, 45 / 46), some (33 / 86, 159 / 170), some (57 / 118, 57 / 118)] := by
  decide +kernel

private def action : Spec := ⟨1 / 2, 10, by decide⟩

theorem disagreement_costs_stakes_times_the_margin :
    action.regret (57 / 118) (action.act afterLocal.val) = 10 / 59 := by decide +kernel

theorem a_straddled_threshold_can_have_positive_value :
    action.valueOfSignal (fun _ : Bool => 1 / 2) (fun b => if b then 3 / 4 else 1 / 4) = 5 / 4 := by
  decide +kernel

theorem large_forecast_movement_can_have_zero_decision_value :
    action.valueOfSignal (fun _ : Bool => 1 / 2) (fun b => if b then 1 else 3 / 5) = 0 := by
  decide +kernel

private def quarter : UnitProbability := ⟨1 / 4, by decide +kernel, by decide +kernel⟩

theorem withdrawn_period_retains_a_reset_opportunity :
    BinaryChangePoint.forecast quarter [none, some true] = some (19 / 32) ∧
      BinaryChangePoint.forecast quarter [some true] = some (5 / 8) := by decide +kernel

private def absToHiddenRate (report : ℚ) : ℚ :=
  (3 / 4) * |report| + (1 / 4) * |1 - report|

private def brierToOutcome (report : ℚ) : ℚ :=
  (3 / 4) * report ^ 2 + (1 / 4) * (1 - report) ^ 2

theorem latent_absolute_loss_and_outcome_brier_rank_differently :
    absToHiddenRate 0 < absToHiddenRate (1 / 4) ∧ brierToOutcome (1 / 4) < brierToOutcome 0 := by
  decide +kernel

end Mettapedia.Examples.PLN.BenchmarkSemanticsControls
