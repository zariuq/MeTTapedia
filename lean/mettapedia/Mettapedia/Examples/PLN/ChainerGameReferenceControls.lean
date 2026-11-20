import Mettapedia.Algorithms.FiniteAdaptivePolicy
import Mettapedia.Algorithms.FiniteBudgetAllocation
import Mettapedia.PLN.WorldModel.CompositionalBootstrap
import Mettapedia.ProbabilityTheory.StochasticInference.BinaryChangePoint
import Mettapedia.ProbabilityTheory.StochasticInference.EvidenceInvariance
import Mettapedia.ProbabilityTheory.StochasticInference.Interventions
import Mettapedia.ProbabilityTheory.StochasticInference.ResidualMass

/-!
# Exact controls for stochastic reasoning benchmarks

The examples use independent observation identifiers and finite rational
models. All posterior values are obtained through the factor readout.
-/

set_option autoImplicit false

namespace Mettapedia.Examples.PLN.ChainerGameReferenceControls

open Mettapedia.ProbabilityTheory.StochasticInference
open Mettapedia.ProbabilityTheory.BayesianNetworks.ExecutableFactorTable (Config)

private def half : UnitProbability := ⟨1 / 2, by decide +kernel, by decide +kernel⟩
private def quarter : UnitProbability := ⟨1 / 4, by decide +kernel, by decide +kernel⟩
private def threeQuarters : UnitProbability := ⟨3 / 4, by decide +kernel, by decide +kernel⟩
private def one : UnitProbability := ⟨1, zero_le_one, le_rfl⟩
private def zero : UnitProbability := ⟨0, le_rfl, zero_le_one⟩

private def infer {n : Nat} (initial : State String (BinaryDomains n))
    (observations : List (String × Potential (BinaryDomains n))) (query : Event (BinaryDomains n)) :
    Option ℚ := do
  let state ← (observations.foldlM (m := Except String)
    (fun state (id, likelihood) => (state.observe id likelihood).map Prod.snd) initial).toOption
  state.probability? (binaryPositive n) (.natural n) query

section Collider

private def first : Event (BinaryDomains 2) := binaryEvent 0 true
private def rival : Event (BinaryDomains 2) := binaryEvent 1 true
private def alarm := Event.disj (binaryPositive 2) first rival

private def prior : State String (BinaryDomains 2) :=
  .initial [bernoulli 0 ⟨1 / 5, by decide +kernel, by decide +kernel⟩, bernoulli 1 quarter]

private def noisyAlarm :=
  alarm.weighted (binaryPositive 2) (3 / 4) (1 / 4) (by decide +kernel) (by decide +kernel)

private def noisyRival :=
  rival.weighted (binaryPositive 2) (3 / 4) (1 / 4) (by decide +kernel) (by decide +kernel)

def explainingAway : List (Option ℚ) :=
  [infer prior [] first, infer prior [("alarm", alarm.asPotential)] first,
    infer prior [("alarm", alarm.asPotential), ("rival", rival.asPotential)] first,
    infer prior [("alarm", noisyAlarm)] first,
    infer prior [("alarm", noisyAlarm), ("rival", noisyRival)] first]

theorem collider_reference :
    explainingAway = [some (1 / 5), some (1 / 2), some (1 / 5), some (1 / 3), some (3 / 11)] := by
  decide +kernel

theorem reversed_fixed_reports :
    infer prior [("rival", noisyRival), ("alarm", noisyAlarm)] first = some (3 / 11) := by
  decide +kernel

theorem replay_neutral_and_a_fresh_report_informative :
    infer prior [("first", noisyRival), ("first", noisyRival)] rival = some (1 / 2) ∧
      infer prior [("first", noisyRival), ("second", noisyRival)] rival = some (3 / 4) := by
  decide +kernel

theorem telling_back_an_entailed_hard_event :
    infer prior [("alarm", alarm.asPotential), ("derived", alarm.asPotential)] first =
      some (1 / 2) := by decide +kernel

end Collider

section Lures

private def chain : State String (BinaryDomains 3) :=
  .initial [bernoulli 0 half, binaryTransition 0 1 (by decide) threeQuarters quarter,
    binaryTransition 1 2 (by decide) ⟨9 / 10, by decide +kernel, by decide +kernel⟩
      ⟨1 / 10, by decide +kernel, by decide +kernel⟩]

private def separator := ("separator", (binaryEvent (1 : Fin 3) true).asPotential)
private def distant := ("lure", (binaryEvent (2 : Fin 3) true).asPotential)

def lureReadouts : List (Option ℚ) :=
  let query := binaryEvent (0 : Fin 3) true
  [infer chain [separator] query, infer chain [separator, distant] query, infer chain [distant] query]

theorem observing_the_separator_blocks_the_lure :
    lureReadouts = [some (3 / 4), some (3 / 4), some (7 / 10)] := by decide +kernel

end Lures

section Causal

open Interventions

private def root {n : Nat} (child : Fin n) (prior : UnitProbability) : Mechanism child :=
  ⟨[], by simp, by simp, fun _ => prior⟩

private def row {n : Nat} (parent child : Fin n) (before : parent < child)
    (yes no : UnitProbability) : Mechanism child :=
  ⟨[parent], by simp, by simpa using before,
    fun x => if (x parent (by simp)).val = 1 then yes else no⟩

private def pairModels (direct : Bool) : (child : Fin 3) → Mechanism child :=
  Fin.cases (root 0 half) (Fin.cases (row 0 1 (by decide) one zero)
    (Fin.cases (if direct then row 1 2 (by decide) one zero else row 0 2 (by decide) one zero)
      (fun impossible => Fin.elim0 impossible)))

private def noSetting {n : Nat} : Fin n → Option Bool := fun _ => none

def causalReadouts : List (Option ℚ) :=
  let treated := binaryEvent (1 : Fin 3) true
  let outcome := binaryEvent (2 : Fin 3) true
  let setTreatment := fun v => if v = (1 : Fin 3) then some true else none
  [infer (model (pairModels false) noSetting String) [("observed", treated.asPotential)] outcome,
    infer (model (pairModels false) setTreatment String) [] outcome,
    infer (model (pairModels true) setTreatment String) [] outcome]

theorem observationally_equivalent :
    ∀ x : Config (BinaryDomains 3),
      (model (pairModels false) noSetting String).unnormalized (binaryPositive 3) x =
        (model (pairModels true) noSetting String).unnormalized (binaryPositive 3) x := by
  decide +kernel

theorem intervention_discriminates_the_models :
    causalReadouts = [some 1, some (1 / 2), some 1] := by decide +kernel

-- Coordinates 2 and 3 are the factual outcome and the outcome after
-- setting the treatment false. Both mechanisms use the same root.
private def pairedOutcomes (direct : Bool) : (child : Fin 4) → Mechanism child :=
  Fin.cases (root 0 half) (Fin.cases (row 0 1 (by decide) one zero)
    (Fin.cases (if direct then row 1 2 (by decide) one zero else row 0 2 (by decide) one zero)
      (Fin.cases (if direct then root 3 zero else row 0 3 (by decide) one zero)
        (fun impossible => Fin.elim0 impossible))))

def butForReadouts : List (Option ℚ) :=
  let factual := [("treatment", (binaryEvent (1 : Fin 4) true).asPotential),
    ("outcome", (binaryEvent (2 : Fin 4) true).asPotential)]
  let prevented := binaryEvent (3 : Fin 4) false
  [infer (model (pairedOutcomes false) noSetting String) factual prevented,
    infer (model (pairedOutcomes true) noSetting String) factual prevented]

theorem but_for_given_the_factual_case :
    butForReadouts = [some 0, some 1] := by decide +kernel

private def stormRow (carry : Bool) : Mechanism (3 : Fin 4) :=
  ⟨[1, 2], by decide, by decide +kernel, fun x =>
    if (x 1 (by decide)).val == 1 || (carry && (x 2 (by decide)).val == 1) then one else zero⟩

private def persistence (carry : Bool) : (child : Fin 4) → Mechanism child :=
  Fin.cases (root 0 half) (Fin.cases (row 0 1 (by decide) one zero)
    (Fin.cases (row 0 2 (by decide) threeQuarters quarter)
      (Fin.cases (stormRow carry) (fun impossible => Fin.elim0 impossible))))

def persistenceReadouts : List (Option ℚ) :=
  let storm := binaryEvent (3 : Fin 4) true
  let initialFront := binaryEvent (0 : Fin 4) true
  [infer (model (persistence false) noSetting String) [("storm", storm.asPotential)] initialFront,
    infer (model (persistence true) noSetting String) [("storm", storm.asPotential)] initialFront]

theorem loopy_persistence_reference :
    persistenceReadouts = [some 1, some (4 / 5)] := by decide +kernel

private def crossRegion (secondLeg : Bool) : (child : Fin 4) → Mechanism child :=
  Fin.cases (root 0 half) (Fin.cases (row 0 1 (by decide) threeQuarters quarter)
    (Fin.cases (row 0 2 (by decide) threeQuarters quarter)
      (Fin.cases (stormRow secondLeg) (fun impossible => Fin.elim0 impossible))))

def crossRegionReadouts : List (Option ℚ) :=
  let delay := binaryEvent (3 : Fin 4) true
  let front := binaryEvent (0 : Fin 4) true
  [infer (model (crossRegion false) noSetting String) [("delay", delay.asPotential)] front,
    infer (model (crossRegion true) noSetting String) [("delay", delay.asPotential)] front]

theorem cross_region_legs_reference :
    crossRegionReadouts = [some (3 / 4), some (15 / 22)] := by decide +kernel

end Causal

section Regime

open BinaryChangePoint

def regimeReadouts : List (Option ℚ) :=
  let history := [some false, some false, some true, some true, some true, some true]
  [forecast quarter history, forecast zero history,
    forecast quarter [some false, some true], forecast quarter [none, some true],
    forecast quarter [some false, none]]

theorem changed_rate_and_withdrawal :
    regimeReadouts = [some (149725 / 384808), some (5 / 8), some (11 / 24),
      some (19 / 32), some (3 / 8)] := by decide +kernel

private def twoReports (reversed : Bool) : Option (EvidenceLedger Nat Bool) := do
  let reports := if reversed then [(1, true), (2, false)] else [(2, false), (1, true)]
  (reports.foldlM (m := Except Nat)
    (fun ledger (id, value) => (ledger.observe id value).map Prod.snd) EvidenceLedger.empty).toOption

theorem regime_replay_uses_period_order_and_retains_a_withdrawn_period :
    ((twoReports false).map (timeline [2, 1])) = (twoReports true).map (timeline [2, 1]) ∧
    ((twoReports true).map (fun s => timeline [2, 1] (s.retract 2))) = some [none, some true] := by
  decide +kernel

end Regime

section LateEvidence

open ResidualMass

private def masses (p n : Nat) : Masses := ⟨p, n, Nat.cast_nonneg _, Nat.cast_nonneg _⟩

def lateEvidenceReadouts : List (Option (ℚ × ℚ)) :=
  [Partial.interval ⟨masses 3 1, masses 1 8⟩,
    Partial.interval ⟨masses 3 6, masses 1 3⟩,
    Partial.interval ⟨masses 4 9, masses 0 0⟩,
    Partial.interval ⟨masses 0 0, masses 1 0⟩,
    Partial.interval ⟨masses 0 0, masses 0 0⟩]

theorem asymmetric_caps_refine_the_result :
    lateEvidenceReadouts = [some (1 / 4, 4 / 5), some (1 / 4, 2 / 5),
      some (4 / 13, 4 / 13), some (1, 1), none] := by decide +kernel

end LateEvidence

section Allocation

open Mettapedia.Algorithms.FiniteBudgetAllocation

private def valueOf (stakes prior accuracy : ℚ) : ℚ :=
  stakes * (accuracy - max prior (1 - prior))

private def tasks : Tasks :=
  [[⟨2, valueOf 1 (9 / 10) 1⟩], [⟨1, valueOf 2 (1 / 2) (3 / 4)⟩, ⟨2, valueOf 2 (1 / 2) 1⟩]]

def allocationScores : List ℚ :=
  (List.range 5).map (best tasks)

theorem allocation_maximizes_expected_gain :
    allocationScores = [0, 1 / 2, 1, 1, 11 / 10] := by decide +kernel

end Allocation

section Concepts

open Mettapedia.PLN.WorldModel.CompositionalBootstrap

private abbrev Input := Bool × Bool × Bool

private def tests : List (Input → Bool) := [Prod.fst, fun x => x.2.1, fun x => x.2.2]

private def data (repeats : Nat) : List (Input × Bool) :=
  let rows := (List.range 8).map fun i =>
    let input := (i.testBit 0, i.testBit 1, i.testBit 2)
    (input, (input.1 != input.2.1) != input.2.2)
  (List.replicate repeats rows).flatten

def learnedParity : List (List Bool) :=
  [bestPath quarter tests (data 1), bestPath quarter tests (data 2)]

theorem three_way_interaction_is_learned_with_enough_data :
    learnedParity = [[false, false, false], [true, true, true]] := by decide +kernel

end Concepts

section Probing

open Mettapedia.Algorithms.FiniteAdaptivePolicy

private abbrev FaultState := Bool × Bool × Bool

private def faultPrior (state : FaultState) : ℚ := if state.2.2 then 0 else 1 / 4
private def reward (state : FaultState) : ℚ := if state.2.2 then 1 else 0

private def probeTransition (action : Fin 4) (state : FaultState) : FaultState × Bool :=
  if action.val = 0 then (state, state.1)
  else if action.val = 1 then (state, state.2.1)
  else ((state.1, state.2.1, (state.1 != state.2.1) == (action.val == 3)), false)

private def probeKernel (action : Fin 4) (state : FaultState) (outcome : FaultState × Bool) : ℚ :=
  if outcome = probeTransition action state then 1 else 0

def probeScores : List ℚ :=
  [bestScore probeKernel reward 1 faultPrior, bestScore probeKernel reward 2 faultPrior,
    bestScore probeKernel reward 3 faultPrior]

set_option maxRecDepth 2048 in
set_option maxHeartbeats 2000000 in
theorem one_probe_is_uninformative_and_two_suffice :
    probeScores = [1 / 2, 1 / 2, 1] := by decide +kernel

end Probing

end Mettapedia.Examples.PLN.ChainerGameReferenceControls
