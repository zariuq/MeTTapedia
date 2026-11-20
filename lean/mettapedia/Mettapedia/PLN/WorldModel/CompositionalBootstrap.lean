import Mettapedia.PLN.WorldModel.PredictiveBootstrap
import Mettapedia.ProbabilityTheory.StochasticInference.AnytimeMixtures

/-!
# Learning conditional partitions by bounded composition

A grammar branch either skips a test or adds it to the context.
Its prior is fixed before seeing the evidence. A separate ranking can
learn which prefixes to visit from other tasks. The visited leaves
determine the amount of posterior mass still unaccounted for.
-/

set_option autoImplicit false

namespace Mettapedia.PLN.WorldModel.CompositionalBootstrap

open Mettapedia.ProbabilityTheory.StochasticInference
open AnytimeMixtures BetaPredictive Mettapedia.PLN.WorldModel.PredictiveBootstrap
open Mettapedia.ProbabilityTheory.BayesianNetworks.CPTLearning (BooleanCPTEntry exactPosteriorMean)

variable {Input : Type*}

def classify : (tests : List (Input → Bool)) → Input → Fin (2 ^ tests.length)
  | [], _ => 0
  | test :: rest, input =>
    let offset := (classify rest input).val
    let size := 2 ^ rest.length
    have fit : offset < size := (classify rest input).isLt
    ⟨if test input then size + offset else offset, by
      simp only [List.length_cons, pow_succ]
      split <;> omega⟩

def selected (tests : List (Input → Bool)) (path : List Bool) : List (Input → Bool) :=
  (tests.zip path).filterMap fun (test, included) => if included then some test else none

def model (tests : List (Input → Bool)) (path : List Bool) : Candidate Input :=
  let chosen := selected tests path
  ⟨2 ^ chosen.length, classify chosen, 1, zero_lt_one⟩

structure Fit (model : Candidate Input) where
  counts : Fin model.cells → BooleanCPTEntry
  evidence : ℚ
  positive : 0 < evidence
  bounded : evidence ≤ 1

theorem prediction_positive (candidate : Candidate Input) (samples : List (Input × Bool))
    (input : Input) (outcome : Bool) : 0 < candidate.prediction samples input outcome :=
  predictive_positive _ _

theorem prediction_le_one (counts : BooleanCPTEntry) (outcome : Bool) :
    predictive counts outcome ≤ 1 := by
  have total := predictive_total counts
  cases outcome
  · linarith [predictive_positive counts true]
  · linarith [predictive_positive counts false]

theorem evidence_supported (candidate : Candidate Input) (samples : List (Input × Bool)) :
    0 < candidate.evidenceMass samples ∧ candidate.evidenceMass samples ≤ 1 := by
  induction samples with
  | nil =>
    have one : candidate.evidenceMass [] = 1 := by
      simp [Candidate.evidenceMass_eq_prod, Candidate.counts]
    simp [one]
  | cons sample rest ih =>
    obtain ⟨input, outcome⟩ := sample
    rw [candidate.evidenceMass_step]
    exact ⟨mul_pos ih.1 (prediction_positive candidate rest input outcome),
      mul_le_one₀ ih.2 (prediction_positive candidate rest input outcome).le
        (prediction_le_one _ _)⟩

def fit (candidate : Candidate Input) (samples : List (Input × Bool)) : Fit candidate :=
  let table := Array.ofFn (candidate.counts samples)
  ⟨fun i => table[i.val]'(by simp [table, i.isLt]), candidate.evidenceMass samples,
    (evidence_supported candidate samples).1, (evidence_supported candidate samples).2⟩

def Fit.query {candidate : Candidate Input} (state : Fit candidate) (input : Input)
    (outcome : Bool) : Joint where
  masses := ⟨state.evidence * predictive (state.counts (candidate.classify input)) outcome,
    state.evidence⟩
  joint_nonneg := mul_nonneg state.positive.le (predictive_positive _ _).le
  included := mul_le_of_le_one_right state.positive.le (prediction_le_one _ _)
  evidence_le_one := state.bounded

def Fit.evidenceOnly {candidate : Candidate Input} (state : Fit candidate) : Joint :=
  ⟨⟨0, state.evidence⟩, le_rfl, state.positive.le, state.bounded⟩

def mixtureEvidence (prior : UnitProbability) (tests : List (Input → Bool))
    (samples : List (Input × Bool)) : ℚ :=
  (fullMass prior (fun path => (fit (model tests path) samples).evidenceOnly) tests.length).masses.evidence

theorem more_data_le_prior_evidence (prior : UnitProbability) (tests : List (Input → Bool))
    (samples : List (Input × Bool)) (input : Input) (outcome : Bool) (query : Input) :
    (fullMass prior (fun path => (fit (model tests path) ((input, outcome) :: samples)).query query true)
      tests.length).masses.evidence ≤ mixtureEvidence prior tests samples := by
  apply fullMass_evidence_mono
  intro path
  let m := model tests path
  change m.evidenceMass ((input, outcome) :: samples) ≤ m.evidenceMass samples
  rw [Candidate.evidenceMass_step]
  exact mul_le_of_le_one_right (evidence_supported m samples).1.le (prediction_le_one _ _)

def paths : Nat → List (List Bool)
  | 0 => [[]]
  | depth + 1 => (paths depth).map (false :: ·) ++ (paths depth).map (true :: ·)

def pathMass (priority : List ℚ) (path : List Bool) : ℚ :=
  ((priority.zip path).map fun (p, included) => if included then p else 1 - p).prod

def prefer (priority : List ℚ) (openPaths : List (List Bool)) : Option (List Bool) :=
  match openPaths with
  | [] => none
  | first :: rest =>
    some ((rest.foldl (fun (best, weight) path =>
      let next := pathMass priority path
      if weight < next then (path, next) else (best, weight)) (first, pathMass priority first)).1)

theorem prefer_mem (priority : List ℚ) (openPaths : List (List Bool)) (path : List Bool)
    (chosen : prefer priority openPaths = some path) : path ∈ openPaths := by
  let choose : (List Bool × ℚ) → List Bool → (List Bool × ℚ) := fun best rest =>
    let weight := pathMass priority rest
    if best.2 < weight then (rest, weight) else best
  have selects (rest : List (List Bool)) (best : List Bool × ℚ) :
      (rest.foldl choose best).1 ∈ best.1 :: rest := by
    induction rest generalizing best with
    | nil => simp
    | cons entry rest ih =>
      rw [List.foldl_cons]
      have fromRest := ih (choose best entry)
      by_cases prefers : best.2 < pathMass priority entry
      · simp only [choose, prefers, if_true, List.mem_cons] at fromRest ⊢
        exact Or.inr fromRest
      · simp only [choose, prefers, if_false, List.mem_cons] at fromRest ⊢
        exact fromRest.imp id Or.inr
  cases openPaths with
  | nil => simp [prefer] at chosen
  | cons first rest =>
    change some ((rest.foldl choose (first, pathMass priority first)).1) = some path at chosen
    rw [← Option.some.inj chosen]
    exact selects _ _

def run {depth : Nat} (priority : List ℚ) (budget : Nat) (trace : Trace depth) : Trace depth :=
  match budget with
  | 0 => trace
  | steps + 1 =>
    match prefer priority trace.pendingPaths with
    | none => trace
    | some next => run priority steps (trace.advance next)

theorem exhausts {depth : Nat} (priority : List ℚ) (budget : Nat) (trace : Trace depth)
    (enough : trace.workLeft ≤ budget) : (run priority budget trace).pendingPaths = [] := by
  induction budget generalizing trace with
  | zero =>
    exact trace.work_zero_iff.mp (Nat.le_zero.mp enough)
  | succ budget ih =>
    cases chosen : prefer priority trace.pendingPaths with
    | none =>
      rw [run, chosen]
      cases paths : trace.pendingPaths with
      | nil => rfl
      | cons first rest =>
        simp [paths, prefer] at chosen
    | some path =>
      rw [run, chosen]
      apply ih
      have spent := trace.advance_spends_one path (prefer_mem _ _ _ chosen)
      omega

def bestPath (prior : UnitProbability) (tests : List (Input → Bool))
    (samples : List (Input × Bool)) : List Bool :=
  let score := fun path => pathMass (List.replicate tests.length prior.val) path *
    (model tests path).evidenceMass samples
  ((paths tests.length).foldl (fun best path =>
    let value := score path
    if best.2 < value then (path, value) else best) (([] : List Bool), (-1 : ℚ))).1

/-- Learn branch preferences from model searches on separate tasks. These
preferences choose an order of work for later tasks. -/
def learnPriority (prior : UnitProbability) (tests : List (Input → Bool))
    (training : List (List (Input × Bool))) : List ℚ :=
  let winners := training.map (bestPath prior tests)
  (List.range tests.length).map fun i =>
    let positive := winners.countP (fun path => path[i]?.getD false)
    predictive ⟨positive, winners.length - positive⟩ true

end Mettapedia.PLN.WorldModel.CompositionalBootstrap
