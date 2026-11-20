import Mettapedia.PLN.WorldModel.RelationalTemporalBootstrap

/-!
# Learning a two-period feature through a relation

A route's blockage label depends on a station it uses. A station's storm
and delay are observed at different lags. The proposal uses one station
for both tests.
-/

set_option autoImplicit false

namespace Mettapedia.Examples.PLN.RelationalTemporalBootstrapControls

open Mettapedia.PLN.WorldModel
open PredictiveBootstrap RelationalTemporalBootstrap
open Mettapedia.ProbabilityTheory.StochasticInference (EvidenceLedger)

inductive Entity where
  | route (exampleId : Nat)
  | station (exampleId : Nat) (second : Bool)
  deriving DecidableEq

inductive Link where
  | uses
  deriving DecidableEq

inductive Signal where
  | storm
  | delay
  deriving DecidableEq

def storm : Probe Signal := ⟨.storm, 1⟩
def delay : Probe Signal := ⟨.delay, 0⟩

def joined : Feature Link Signal := .related .uses [storm, delay]

private def history : History Entity Link Signal where
  neighbors := fun _ entity _ =>
    match entity with
    | .route index => [.station index false]
    | .station _ _ => []
  value := fun signal entity period =>
    match entity, signal, period with
    | .station index false, .storm, 0 => some (index % 2 = 1)
    | .station index false, .delay, 1 => some (index % 4 ≥ 2)
    | .station _ _, _, _ => some false
    | .route _, _, _ => none

private def forecast (index : Nat) : Forecast Entity := ⟨.route index, 2⟩

private def registry : Option (Feature Link Signal) → Candidate (Forecast Entity)
  | none => ⟨1, fun _ => 0, 1, by decide +kernel⟩
  | some feature => feature.partition history (1 / 8) (by decide +kernel)

private abbrev Learner := LearningState Nat (Forecast Entity) (Option (Feature Link Signal))

private def learn (size : Nat) : Option Learner :=
  (List.range size).foldlM (m := Option) (fun state index =>
    (state.revise index (forecast index) (index % 4 = 3)).toOption.map Prod.snd)
    ⟨EvidenceLedger.empty, none⟩

private def offered : List (Option (Feature Link Signal)) :=
  (proposals [.storm, .delay] [1, 0] [Link.uses] 2).map some

theorem discovered_from_the_vocabulary :
    (learn 16).map (fun state => (state.search registry offered).incumbent) = some (some joined) := by
  decide +kernel

theorem small_sample_leaves_the_baseline :
    (learn 4).map (fun state => (state.search registry offered).incumbent) = some none := by
  decide +kernel

private def differentWitnesses : History Entity Link Signal where
  neighbors := fun _ _ _ => [.station 0 false, .station 0 true]
  value := fun signal entity time =>
    some (match signal, entity, time with
      | .storm, .station _ false, 0 | .delay, .station _ true, 1 => true
      | _, _, _ => false)

theorem two_witnesses_do_not_satisfy_a_shared_binding :
    (Feature.related Link.uses [storm]).read differentWitnesses (forecast 0) = some true ∧
    (Feature.related Link.uses [delay]).read differentWitnesses (forecast 0) = some true ∧
    joined.read differentWitnesses (forecast 0) = some false := by
  decide +kernel

theorem missing_history_uses_a_distinct_cell :
    ((registry (some joined)).classify ⟨.route 3, 0⟩).val = 2 ∧
    ((registry (some joined)).classify (forecast 3)).val = 1 ∧
    ((registry (some joined)).classify (forecast 0)).val = 0 := by
  decide +kernel

end Mettapedia.Examples.PLN.RelationalTemporalBootstrapControls
