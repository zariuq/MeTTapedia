import Mettapedia.ProbabilityTheory.StochasticInference

/-!
# A SupplyNet diagnosis with a shared sensor

Coordinates are front, blocked route, downstream delay, and sensor quality.
Even with a clear front, a route can block. A second delay report from the
same sensor contributes a second likelihood term conditional on sensor
quality, while replay of the first report contributes nothing new.
-/

set_option autoImplicit false

namespace Mettapedia.Examples.PLN.StochasticInferenceDiagnosis

open Mettapedia.ProbabilityTheory.StochasticInference
open Mettapedia.ProbabilityTheory.BayesianNetworks

abbrev Domains := BinaryDomains 4
abbrev Model := State String Domains

private theorem positive : ∀ v, 0 < Domains v := binaryPositive 4
private def schedule := Schedule.natural 4

private def p (value : ℚ) (nonneg : 0 ≤ value) (bounded : value ≤ 1) : UnitProbability :=
  ⟨value, nonneg, bounded⟩

private def half := p (1 / 2) (by decide +kernel) (by decide +kernel)
private def clear := (binaryEvent (0 : Fin 4) false).asPotential
private def blocked : Event Domains := binaryEvent 1 true
private def reportScope : List (Fin 4) := [2, 3]

def factors : List (Potential Domains) :=
  [bernoulli 0 half, binaryTransition 0 1 (by decide +kernel)
      (p (4 / 5) (by decide +kernel) (by decide +kernel)) (p (1 / 10) (by decide +kernel) (by decide +kernel)),
    binaryTransition 1 2 (by decide +kernel)
      (p (9 / 10) (by decide +kernel) (by decide +kernel)) (p (1 / 10) (by decide +kernel) (by decide +kernel)),
    bernoulli 3 half]

def report (reading : Bool) : Potential Domains :=
  Potential.onScope positive reportScope (by decide +kernel)
    (fun values =>
      let reliability := if (values 3 (by decide +kernel)).val = 1
        then p (19 / 20) (by decide +kernel) (by decide +kernel)
        else p (11 / 20) (by decide +kernel) (by decide +kernel)
      reliability.atOutcome (decide (values 2 (by decide +kernel) = bitValue reading)))
    (fun _ => UnitProbability.atOutcome_nonneg _ _)

private def independentReport : Potential Domains :=
  (binaryEvent (2 : Fin 4) true).weighted positive (3 / 4) (1 / 4) (by decide +kernel) (by decide +kernel)

private def read (model : Model) : Option ℚ :=
  model.probability? positive schedule blocked

private def record (model : Model) (id : String) (likelihood : Potential Domains) :
    Option Model :=
  match model.observe id likelihood with
  | .ok (.recorded, updated) => some updated
  | _ => none

private def start : Option Model := record (.initial factors) "front" clear

private def send (model : Model) (id : String) (value : Bool) : Option Model :=
  record model id (report value)

private def first : Option Model := start.bind (fun w => send w "delay/7" true)
private def second : Option Model := first.bind (fun w => send w "delay/8" true)

theorem forecast_and_diagnosis :
    start.bind read = some (1 / 10) ∧ first.bind read = some (7 / 34) ∧
      second.bind read = some (221 / 770) := by decide +kernel

private def replay (model : Model) : Option Model :=
  match model.observe "delay/7" (report true) with
  | .ok (.replay, same) => some same
  | _ => none

theorem replay_and_withdrawal :
    ((first.bind replay).bind read = some (7 / 34)) ∧
    (second.bind (fun w => read (w.retract "delay/8")) = some (7 / 34)) ∧
    (second.bind (fun w => (replay (w.retract "delay/7")).bind read) = some (7 / 34)) ∧
    (second.bind (fun w => read ((w.retract "delay/8").restore "delay/8")) = some (221 / 770)) := by
  decide +kernel

theorem conflicting_uses_of_one_id :
    (first.map (fun w => match w.observe "delay/7" (report false) with
      | .error id => id
      | .ok _ => "")) = some "delay/7" := by decide +kernel

theorem new_sensor_model_changes_the_answer :
    (do
      let w ← start
      let first ← record w "delay/7" independentReport
      let second ← record first "delay/8" independentReport
      read second) = some (41 / 122) := by decide +kernel

theorem zero_normalizer :
    (do
      let w ← start
      let impossible ← record w "opposite front" (binaryEvent (0 : Fin 4) true).asPotential
      pure (read impossible)) = some none := by decide +kernel

private def prepared :=
  let neutral := Potential.neutral positive reportScope (by decide +kernel)
  Retained.prepare positive
    ((factors ++ [clear, report true, neutral]).map Potential.table) [0, 2, 3]

private theorem allEliminated : ∀ v : Fin 4, v ∈ ([0, 2, 3] ++ [1] : List (Fin 4)) := by
  decide +kernel

private theorem queryRetained : ∀ v ∈ ([0, 2, 3] : List (Fin 4)), v ∉ blocked.table.scope := by
  decide +kernel

private theorem covered : ∀ v : Fin 4, ∃ slot : Fin 11, v ∈ prepared.factors[slot].scope := by
  intro v
  fin_cases v
  · exact ⟨⟨0, by decide +kernel⟩, by decide +kernel⟩
  · exact ⟨⟨1, by decide +kernel⟩, by decide +kernel⟩
  · exact ⟨⟨2, by decide +kernel⟩, by decide +kernel⟩
  · exact ⟨⟨3, by decide +kernel⟩, by decide +kernel⟩

private def cachedPosterior : Option (ℚ × Nat) := do
  let (edited, refreshed) ← prepared.tryReplace ⟨6, by decide +kernel⟩ (report true).table
  let result ← Retained.read? edited [1] blocked.table
  let posterior ← result.posterior?
  pure (posterior, refreshed)

theorem retained_message_replacement :
    (Retained.read? prepared [1] blocked.table >>= ScopedFactorReadout.Masses.posterior?) =
      some (7 / 34) ∧ cachedPosterior.map Prod.fst = some (221 / 770) := by
  constructor
  · rw [Retained.read_exact prepared [1] _ allEliminated queryRetained covered]
    decide +kernel
  · unfold cachedPosterior EliminationPlan.Runtime.tryReplace
    rw [dif_pos (by decide +kernel)]
    simp only [bind, Option.bind]
    erw [Retained.read_exact _ [1] _ allEliminated queryRetained covered]
    decide +kernel

theorem invalid_retained_payoff_is_rejected :
    (Retained.read? prepared [1] (binaryEvent (2 : Fin 4) true).table).isNone = true := by
  decide +kernel

end Mettapedia.Examples.PLN.StochasticInferenceDiagnosis
