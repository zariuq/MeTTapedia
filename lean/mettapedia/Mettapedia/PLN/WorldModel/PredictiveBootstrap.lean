import Mettapedia.ProbabilityTheory.StochasticInference.BetaPredictive
import Mettapedia.ProbabilityTheory.StochasticInference.Ledger

/-!
# Structure learning by comparing conditional predictions

A candidate partitions the input space and assigns one unknown Bernoulli
parameter to each cell. Parameters start with independent uniform Beta
priors. Models predict the same outcomes conditional on the supplied inputs.
Each candidate score is its prior weight times its integrated likelihood.
The active evidence ledger is the common data for every candidate.
-/

set_option autoImplicit false

namespace Mettapedia.PLN.WorldModel.PredictiveBootstrap

open Mettapedia.ProbabilityTheory.BayesianNetworks.CPTLearning (BooleanCPTEntry)
open Mettapedia.ProbabilityTheory.StochasticInference
open BetaPredictive
open scoped BigOperators

structure Candidate (Input : Type*) where
  cells : Nat
  classify : Input → Fin cells
  priorWeight : ℚ
  priorPositive : 0 < priorWeight

namespace Candidate

variable {Input Id : Type*}

def counts (model : Candidate Input) (samples : List (Input × Bool)) (cell : Fin model.cells) :
    BooleanCPTEntry :=
  samples.foldr (fun (input, outcome) acc =>
    if model.classify input = cell then addOutcome acc outcome else acc) empty

def prediction (model : Candidate Input) (samples : List (Input × Bool))
    (input : Input) (outcome : Bool) : ℚ :=
  predictive (model.counts samples (model.classify input)) outcome

def evidenceMass (model : Candidate Input) (samples : List (Input × Bool)) : ℚ :=
  ((List.finRange model.cells).map (fun cell => wordMass (model.counts samples cell))).prod

theorem evidenceMass_eq_prod (model : Candidate Input) (samples : List (Input × Bool)) :
    model.evidenceMass samples = ∏ cell, wordMass (model.counts samples cell) := by
  have all : (List.finRange model.cells).toFinset = Finset.univ := by ext; simp
  rw [evidenceMass, ← List.prod_toFinset _ (List.nodup_finRange _), all]

theorem evidenceMass_step (model : Candidate Input) (samples : List (Input × Bool))
    (input : Input) (outcome : Bool) :
    model.evidenceMass ((input, outcome) :: samples) =
      model.evidenceMass samples * model.prediction samples input outcome := by
  rw [evidenceMass_eq_prod, evidenceMass_eq_prod]
  let target := model.classify input
  let boost : Fin model.cells → ℚ :=
    fun cell => if cell = target then model.prediction samples input outcome else 1
  have entry (cell : Fin model.cells) :
      wordMass (model.counts ((input, outcome) :: samples) cell) =
        wordMass (model.counts samples cell) * boost cell := by
    by_cases same : cell = target
    · subst cell
      simp [counts, target, boost, prediction, wordMass_step]
    · have different : model.classify input ≠ cell := Ne.symm same
      simp [counts, boost, same, different]
  rw [Finset.prod_congr rfl (fun cell _ => entry cell), Finset.prod_mul_distrib]
  congr 1
  rw [Finset.prod_eq_single target]
  · simp [boost]
  · intro cell _ other
    simp [boost, other]
  · simp

def samples (ledger : EvidenceLedger Id (Input × Bool)) : List (Input × Bool) :=
  ledger.active.map EvidenceEntry.payload

def score (model : Candidate Input) (ledger : EvidenceLedger Id (Input × Bool)) : ℚ :=
  model.priorWeight * model.evidenceMass (samples ledger)

theorem score_step [DecidableEq Id] [DecidableEq Input]
    (model : Candidate Input) (ledger next : EvidenceLedger Id (Input × Bool))
    (id : Id) (input : Input) (outcome : Bool) (fresh : ledger.lookup id = none)
    (entered : ledger.observe id (input, outcome) = .ok (.recorded, next)) :
    model.score next = model.score ledger * model.prediction (samples ledger) input outcome := by
  rw [EvidenceLedger.observe_fresh _ _ _ fresh] at entered
  have same := congrArg Prod.snd (Except.ok.inj entered)
  change _ = next at same
  subst next
  unfold score
  change model.priorWeight * model.evidenceMass ((input, outcome) :: samples ledger) = _
  rw [evidenceMass_step, mul_assoc]

end Candidate

/-- Compare proposals from a fixed, prior-weighted registry on their common
active data. Ties preserve the incumbent. -/
def select {Input Id Model : Type*} (registry : Model → Candidate Input)
    (ledger : EvidenceLedger Id (Input × Bool)) (incumbent : Model)
    (proposals : List Model) : Model :=
  let score := fun model => (registry model).score ledger
  proposals.foldl (fun best proposal => if score best < score proposal then proposal else best)
    incumbent

theorem select_score_ge {Input Id Model : Type*} (registry : Model → Candidate Input)
    (ledger : EvidenceLedger Id (Input × Bool)) (incumbent : Model) (proposals : List Model) :
    (registry incumbent).score ledger ≤ (registry (select registry ledger incumbent proposals)).score ledger := by
  induction proposals generalizing incumbent with
  | nil => exact le_rfl
  | cons proposal rest ih =>
    unfold select
    simp only [List.foldl_cons]
    split
    · exact le_trans (le_of_lt (by assumption)) (ih proposal)
    · exact ih incumbent

structure LearningState (Id Input Model : Type*) where
  ledger : EvidenceLedger Id (Input × Bool)
  incumbent : Model

namespace LearningState

variable {Id Input Model : Type*}

def revise [DecidableEq Id] [DecidableEq Input] (state : LearningState Id Input Model)
    (id : Id) (input : Input) (outcome : Bool) :
    Except Id (EvidenceLedger.Arrival × LearningState Id Input Model) :=
  match state.ledger.observe id (input, outcome) with
  | .error conflict => .error conflict
  | .ok (disposition, ledger) => .ok (disposition, { state with ledger := ledger })

theorem revise_replay [DecidableEq Id] [DecidableEq Input] (state : LearningState Id Input Model)
    (id : Id) (prior : EvidenceEntry Id (Input × Bool)) (seen : state.ledger.lookup id = some prior) :
    state.revise id prior.payload.1 prior.payload.2 = .ok (.replay, state) := by
  simp [revise, EvidenceLedger.observe_replay _ _ _ seen]

def search (state : LearningState Id Input Model) (registry : Model → Candidate Input)
    (proposals : List Model) : LearningState Id Input Model :=
  { state with incumbent := select registry state.ledger state.incumbent proposals }

theorem search_score_ge (state : LearningState Id Input Model) (registry : Model → Candidate Input)
    (proposals : List Model) :
    (registry state.incumbent).score state.ledger ≤
      (registry (state.search registry proposals).incumbent).score state.ledger :=
  select_score_ge registry state.ledger state.incumbent proposals

end LearningState

end Mettapedia.PLN.WorldModel.PredictiveBootstrap
