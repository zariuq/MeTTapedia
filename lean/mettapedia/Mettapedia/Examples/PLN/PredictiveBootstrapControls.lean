import Mettapedia.PLN.WorldModel.PredictiveBootstrap
import Mettapedia.ProbabilityTheory.StochasticInference.RowStatistics
import Mettapedia.ProbabilityTheory.StochasticInference.Binary

/-!
# A split learned from paired sensor inputs

Two binary sensor readings can be jointly predictive even when they are
individually uninformative. The search needs access to a joint partition
before either of its constituent partitions is accepted.
-/

set_option autoImplicit false

namespace Mettapedia.Examples.PLN.PredictiveBootstrapControls

open Mettapedia.PLN.WorldModel.PredictiveBootstrap
open Mettapedia.ProbabilityTheory.StochasticInference

abbrev Input := Bool × Bool

inductive Model where
  | unconditioned
  | left
  | right
  | both
  deriving DecidableEq

def registry : Model → Candidate Input
  | .unconditioned => ⟨1, fun _ => 0, 1, by decide +kernel⟩
  | .left => ⟨2, fun input => bitValue input.1, 1 / 4, by decide +kernel⟩
  | .right => ⟨2, fun input => bitValue input.2, 1 / 4, by decide +kernel⟩
  | .both => ⟨4, fun input => ⟨2 * (bitValue input.1).val + (bitValue input.2).val, by
      have hl := (bitValue input.1).isLt
      have hr := (bitValue input.2).isLt
      omega⟩, 1 / 16, by decide +kernel⟩

def cases : List Input :=
  [(false, false), (false, true), (true, false), (true, true)]

abbrev Learner := LearningState Nat Input Model

def learn (repeats : Nat) : Option Learner :=
  let data := (List.replicate repeats cases).flatten.zipIdx
  data.foldlM (m := Option) (fun state (input, id) =>
    (state.revise id input (input.1 != input.2)).toOption.map Prod.snd)
    ⟨EvidenceLedger.empty, .unconditioned⟩

theorem single_splits_are_rejected :
    (learn 4).map (fun state => (state.search registry [.left, .right]).incumbent) =
      some .unconditioned := by decide +kernel

theorem small_batch_keeps_incumbent :
    (learn 1).map (fun state => (state.search registry [.left, .right, .both]).incumbent) =
      some .unconditioned := by decide +kernel

theorem compositional_proposal_is_learned :
    (learn 4).map (fun state =>
      let found := state.search registry [.left, .right, .both]
      (found.incumbent, (registry found.incumbent).prediction
        (Candidate.samples found.ledger) (true, false) true)) =
      some (.both, (5 / 6 : ℚ)) := by decide +kernel

theorem repeated_parameter_is_not_a_fresh_parameter :
    BetaPredictive.sequenceMass BetaPredictive.empty [true, true] = 1 / 3 ∧
      BetaPredictive.predictive BetaPredictive.empty true *
        BetaPredictive.predictive BetaPredictive.empty true = 1 / 4 := by decide +kernel

private def supportedPosterior : Option (State Nat (BinaryDomains 1)) := do
  let p := ⟨1 / 2, by decide +kernel, by decide +kernel⟩
  let state : State Nat (BinaryDomains 1) := .initial [bernoulli 0 p]
  let outcome := binaryEvent (0 : Fin 1) true
  let likelihood := outcome.weighted (binaryPositive 1) (3 / 4) (1 / 4)
    (by decide +kernel) (by decide +kernel)
  (state.observe 0 likelihood).toOption.map Prod.snd

/-- The same likelihood yields fractional sufficient statistics for a
present row and zero exposure for an inactive row. -/
theorem expected_counts_are_conditioned_on_row_exposure :
    (supportedPosterior.bind (fun state =>
      let active := Event.onScope (binaryPositive 1) [] (by simp) (fun _ => true)
      let outcome := binaryEvent (0 : Fin 1) true
      (state.expectedRowCounts? (binaryPositive 1) (.natural 1) active outcome).map
        (fun counts => (counts.pos, counts.neg)))) = some (3 / 4, 1 / 4) ∧
    (supportedPosterior.bind (fun state =>
      let inactive := Event.onScope (binaryPositive 1) [] (by simp) (fun _ => false)
      let outcome := binaryEvent (0 : Fin 1) true
      (state.expectedRowCounts? (binaryPositive 1) (.natural 1) inactive outcome).map
        (fun counts => (counts.pos, counts.neg)))) = some (0, 0) := by decide +kernel

end Mettapedia.Examples.PLN.PredictiveBootstrapControls
