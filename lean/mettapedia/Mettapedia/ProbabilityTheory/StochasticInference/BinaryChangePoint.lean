import Mettapedia.ProbabilityTheory.StochasticInference.BetaPredictive
import Mettapedia.ProbabilityTheory.StochasticInference.Binary
import Mettapedia.ProbabilityTheory.StochasticInference.Ledger

/-!
# Exact run-length inference for changing Bernoulli rates

Each regime starts with a uniform Beta prior. Between periods the rate
resets with the declared hazard. Missing data keeps the period and its
hazard, while contributing no observation likelihood. Input lists put
the most recent period first.
-/

set_option autoImplicit false

namespace Mettapedia.ProbabilityTheory.StochasticInference.BinaryChangePoint

open BetaPredictive
open Mettapedia.ProbabilityTheory.BayesianNetworks.CPTLearning (BooleanCPTEntry)

structure Run where
  length : Nat
  counts : BooleanCPTEntry
  weight : ℚ

def likelihood (counts : BooleanCPTEntry) (reading : Option Bool) : ℚ :=
  reading.elim 1 (predictive counts)

def incorporate (counts : BooleanCPTEntry) (reading : Option Bool) : BooleanCPTEntry :=
  reading.elim counts (addOutcome counts)

def stat (runs : List Run) (query : Nat → BooleanCPTEntry → ℚ) : ℚ :=
  (runs.map (fun run => run.weight * query run.length run.counts)).sum

private def seed (mass : ℚ) (reading : Option Bool) : Run :=
  ⟨1, incorporate empty reading, mass * likelihood empty reading⟩

private def grow (hazard : UnitProbability) (reading : Option Bool) (run : Run) : Run :=
  ⟨run.length + 1, incorporate run.counts reading,
    run.weight * (1 - hazard.val) * likelihood run.counts reading⟩

/-- All branches resetting at this period have the same new counts. -/
def advance (hazard : UnitProbability) (reading : Option Bool) (runs : List Run) : List Run :=
  seed (stat runs (fun _ _ => 1) * hazard.val) reading :: runs.map (grow hazard reading)

def filter (hazard : UnitProbability) : List (Option Bool) → List Run
  | [] => []
  | reading :: older =>
    if older.isEmpty then [seed 1 reading]
    else advance hazard reading (filter hazard older)

private def branch (hazard : UnitProbability) (reading : Option Bool) (runs : List Run) : List Run :=
  runs.flatMap fun run => [seed (run.weight * hazard.val) reading, grow hazard reading run]

/-- Direct enumeration of reset and continuation choices. -/
def enumerate (hazard : UnitProbability) : List (Option Bool) → List Run
  | [] => []
  | reading :: older =>
    if older.isEmpty then [seed 1 reading]
    else branch hazard reading (enumerate hazard older)

private def gain (hazard : UnitProbability) (reading : Option Bool)
    (query : Nat → BooleanCPTEntry → ℚ) (length : Nat) (counts : BooleanCPTEntry) : ℚ :=
  hazard.val * likelihood empty reading * query 1 (incorporate empty reading) +
    (1 - hazard.val) * likelihood counts reading * query (length + 1) (incorporate counts reading)

private theorem advance_stat (hazard : UnitProbability) (reading : Option Bool)
    (runs : List Run) (query : Nat → BooleanCPTEntry → ℚ) :
    stat (advance hazard reading runs) query = stat runs (gain hazard reading query) := by
  induction runs with
  | nil => simp [advance, stat, seed]
  | cons run tail ih =>
    simp only [advance, stat, List.map_cons, List.sum_cons, seed, List.map_map,
      Function.comp_def, grow, mul_one] at ih ⊢
    rw [← ih]
    unfold gain
    ring

private theorem branch_stat (hazard : UnitProbability) (reading : Option Bool)
    (runs : List Run) (query : Nat → BooleanCPTEntry → ℚ) :
    stat (branch hazard reading runs) query = stat runs (gain hazard reading query) := by
  induction runs with
  | nil => rfl
  | cons run tail ih =>
    have split : branch hazard reading (run :: tail) =
        seed (run.weight * hazard.val) reading :: grow hazard reading run ::
          branch hazard reading tail := rfl
    rw [split]
    simp only [stat, List.map_cons, List.sum_cons, seed, grow] at ih ⊢
    rw [ih]
    unfold gain
    ring

theorem filter_exact (hazard : UnitProbability) (history : List (Option Bool))
    (query : Nat → BooleanCPTEntry → ℚ) :
    stat (filter hazard history) query = stat (enumerate hazard history) query := by
  induction history generalizing query with
  | nil => rfl
  | cons reading older ih =>
    simp only [filter, enumerate]
    split
    · rfl
    · rw [advance_stat, branch_stat, ih]

theorem filter_length (hazard : UnitProbability) (history : List (Option Bool)) :
    (filter hazard history).length = history.length := by
  induction history with
  | nil => rfl
  | cons reading older ih =>
    cases older with
    | nil => rfl
    | cons previous rest =>
      change (advance hazard reading (filter hazard (previous :: rest))).length = _
      simp only [advance, List.length_cons, List.length_map, ih]

def nextProbability (hazard : UnitProbability) (runs : List Run) : Option ℚ :=
  let total := stat runs (fun _ _ => 1)
  if 0 < total then
    some (stat runs (fun _ counts => hazard.val / 2 + (1 - hazard.val) * predictive counts true) / total)
  else none

theorem nextProbability_exact (hazard : UnitProbability) (history : List (Option Bool)) :
    nextProbability hazard (filter hazard history) = nextProbability hazard (enumerate hazard history) := by
  simp only [nextProbability, filter_exact]

def forecast (hazard : UnitProbability) (history : List (Option Bool)) : Option ℚ :=
  if history.isEmpty then some (1 / 2) else nextProbability hazard (filter hazard history)

private theorem stat_affine (runs : List Run) (query : Nat → BooleanCPTEntry → ℚ) (a b : ℚ) :
    stat runs (fun length counts => a * query length counts + b) =
      a * stat runs query + b * stat runs (fun _ _ => 1) := by
  induction runs with
  | nil => simp [stat]
  | cons head tail ih =>
    simp only [stat, List.map_cons, List.sum_cons, mul_one] at ih ⊢
    rw [ih]
    ring

private theorem advance_missing_total (hazard : UnitProbability) (runs : List Run) :
    stat (advance hazard none runs) (fun _ _ => 1) = stat runs (fun _ _ => 1) := by
  rw [advance_stat]
  apply congrArg (stat runs)
  funext length counts
  simp [gain, likelihood]

/-- With no sample this period the forecast still changes, because one
more reset opportunity has passed. The shrinkage is toward the reset mean. -/
theorem missing_period_forecast (hazard : UnitProbability) (runs : List Run) :
    nextProbability hazard (advance hazard none runs) =
      (nextProbability hazard runs).map (fun p => hazard.val / 2 + (1 - hazard.val) * p) := by
  let predict : Nat → BooleanCPTEntry → ℚ :=
    fun _ counts => hazard.val / 2 + (1 - hazard.val) * predictive counts true
  have reset : predict 1 empty = 1 / 2 := by
    have initial : predictive empty true = 1 / 2 := by decide +kernel
    simp only [predict, initial]
    ring
  have step : stat (advance hazard none runs) predict =
      (1 - hazard.val) * stat runs predict + (hazard.val / 2) * stat runs (fun _ _ => 1) := by
    rw [advance_stat, ← stat_affine]
    apply congrArg (stat runs)
    funext length counts
    simp only [gain, likelihood, incorporate, Option.elim_none, mul_one]
    rw [reset]
    change hazard.val * (1 / 2) + (1 - hazard.val) * predict length counts = _
    ring
  unfold nextProbability
  dsimp only
  rw [advance_missing_total]
  by_cases evidence : 0 < stat runs (fun _ _ => 1)
  · simp only [if_pos evidence, Option.map_some]
    change some (stat (advance hazard none runs) predict / stat runs (fun _ _ => 1)) =
      some (hazard.val / 2 + (1 - hazard.val) * (stat runs predict / stat runs (fun _ _ => 1)))
    rw [step, add_div, mul_div_assoc, mul_div_cancel_right₀ _ evidence.ne']
    congr 1
    ring
  · simp [evidence]

/-- The period list controls the hazards. Withdrawn and unknown reports
leave their slot in the sequence. -/
def timeline {Id : Type*} [DecidableEq Id] (periods : List Id) (ledger : EvidenceLedger Id Bool) :
    List (Option Bool) :=
  periods.map fun id => (ledger.lookup id).bind fun row => if row.active then some row.payload else none

end Mettapedia.ProbabilityTheory.StochasticInference.BinaryChangePoint
