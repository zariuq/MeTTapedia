import Mettapedia.ProbabilityTheory.StochasticInference.History
import Mettapedia.ProbabilityTheory.StochasticInference.ProofSearch
import Mettapedia.ProbabilityTheory.StochasticInference.MarkovLogic
import Mettapedia.ProbabilityTheory.StochasticInference.Counts

/-!
# Controls for model mixing, dependent histories, and symbolic inference
-/

set_option autoImplicit false

namespace Mettapedia.Examples.PLN.StochasticInferenceControls

open Mettapedia.ProbabilityTheory.StochasticInference
open Mettapedia.ProbabilityTheory.BayesianNetworks.ScopedFactorReadout (Masses)
open Mettapedia.Logic.BDDCore

private theorem positive : ∀ v, 0 < BinaryDomains 1 v := binaryPositive 1
private def present : Event (BinaryDomains 1) := binaryEvent 0 true
private def fair : UnitProbability := ⟨1 / 2, by decide +kernel, by decide +kernel⟩
private def report : Potential (BinaryDomains 1) :=
  present.weighted positive (3 / 4) (1 / 4) (by decide +kernel) (by decide +kernel)

private def copyModel : HistoryModel String Bool (BinaryDomains 1) where
  base := [bernoulli 0 fair]
  likelihood seen _ reading :=
    let event := if reading then present else present.neg positive
    match seen with
    | [] => event.weighted positive (3 / 4) (1 / 4) (by decide +kernel) (by decide +kernel)
    | (_, earlier) :: _ =>
      Potential.onScope positive [] (by simp) (fun _ => if reading = earlier then 1 else 0)
        (fun _ => by split <;> decide)

private def observations : Except String (EvidenceLedger String Bool) := do
  let (_, first) ← EvidenceLedger.empty.observe "original" true
  let (_, second) ← first.observe "copy" true
  pure second

/-- After withdrawal the remaining report is scored with its marginal law. -/
theorem withdrawal_recomputes_dependent_likelihood :
    (observations.toOption.map fun ledger =>
      [(copyModel.snapshot ledger).probability? positive (.natural 1) present,
       (copyModel.snapshot (ledger.retract "original")).probability? positive (.natural 1) present,
       ((copyModel.snapshot ledger).retract "original").probability? positive (.natural 1) present]) =
      some [some (3 / 4), some (3 / 4), some (1 / 2)] := by decide +kernel

theorem count_view_tracks_active_reports :
    (observations.toOption.map fun ledger =>
      ((ledger.counts id).pos, ((ledger.retract "original").counts id).pos)) =
      some (2, 1) := by decide +kernel

private def hypothesis (truth : Bool) (scale : ℚ) (nonneg : 0 ≤ scale) :
    Option (Candidate String (BinaryDomains 1)) := do
  let event := binaryEvent (0 : Fin 1) truth
  let model : State String (BinaryDomains 1) :=
    .initial [event.weighted positive scale 0 nonneg le_rfl]
  let (_, updated) ← (model.observe "report" report).toOption
  pure ⟨updated, 1 / 2, by decide +kernel⟩

theorem mixture_normalizes_each_prior :
    (do
      let yes ← hypothesis true 2 (by decide +kernel)
      let no ← hypothesis false 3 (by decide +kernel)
      let masses ← mixtureMasses? [yes, no] positive (.natural 1) present
      masses.posterior?) = some (3 / 4) := by decide +kernel

private def clause : MarkovLogic.Feature 2 :=
  ⟨[.neg 0, .pos 1], 3, 1, by decide +kernel, by decide +kernel⟩

theorem mln_conditional :
    (do
      let state : State String (BinaryDomains 2) := .initial [clause.factor]
      let (_, updated) ← (state.observe "a" (binaryEvent (0 : Fin 2) true).asPotential).toOption
      updated.probability? (binaryPositive 2) (.natural 2) (binaryEvent 1 true)) =
      some (3 / 4) := by decide +kernel

private def shared : HornClosure.Table 1 2 :=
  ⟨#[StatePredicates.bit 0, StatePredicates.falsity 1], rfl⟩

private def repeatedRule : List (HornClosure.Clause 2) := [⟨1, [0, 0]⟩]

theorem budgeted_proof_keeps_shared_premise :
    let completedRound := ProbLogic.budgetedHorn repeatedRule shared 1 (fun _ => true) 1
    let paused := ProbLogic.budgetedHorn repeatedRule shared 1 (fun _ => false) 1
    completedRound.productInterval? (fun _ => fair) (StatePredicates.truth 1) = some (1 / 2, 1) ∧
      paused.productInterval? (fun _ => fair) (StatePredicates.truth 1) = some (0, 1) := by
  simp [ProbLogic.budgetedHorn, ProbLogic.DiagramBounds.productInterval?, ProbLogic.productMasses,
    ProbLogic.productMass, Masses.posterior?, HornClosure.iterate, HornClosure.round,
    HornClosure.addHead, HornClosure.bodyDiagram, shared, repeatedRule, StatePredicates.truth,
    StatePredicates.conj, StatePredicates.disj, StatePredicates.falsity, StatePredicates.bit,
    RationalWMC.count, Vector.get, bddVar, mk, apply, fair]
  change RationalWMC.count (fun _ : Fin 1 => (2 : ℚ)⁻¹)
    (apply (· && ·) .one (.node 0 .zero .one)) = 2⁻¹ ∧
    RationalWMC.count (fun _ : Fin 1 => (2 : ℚ)⁻¹) (apply (· && ·) .one .zero) = 0
  simp [apply, mk, RationalWMC.count]

theorem invalid_lower_event_rejected :
    (ProbLogic.DiagramBounds.checked (StatePredicates.bit (0 : Fin 1))
      (StatePredicates.truth 1) (StatePredicates.truth 1)).isNone = true := by
  have unsound : ProbLogic.entails (StatePredicates.truth 1) (StatePredicates.bit (0 : Fin 1)) ≠ true := by
    intro accepted
    have invalid := (ProbLogic.entails_iff _ _).mp accepted (fun _ => false) rfl
    simp [StatePredicates.bit] at invalid
  simp [ProbLogic.DiagramBounds.checked, unsound]

end Mettapedia.Examples.PLN.StochasticInferenceControls
