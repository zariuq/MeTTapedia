import Mettapedia.ProbabilityTheory.StochasticInference.BetaPredictive
import Mettapedia.ProbabilityTheory.StochasticInference.CachedLearning
import Mettapedia.PLN.WorldModel.PredictiveBootstrap

/-!
# Collapsed learning from noisy Bernoulli observations

A report is a pair of likelihoods under the two possible outcomes.
Integrating a shared Beta-distributed rate reduces the latent histories
to their success counts. A triangular table evaluates the recursion with
quadratic work in the number of reports.
-/

set_option autoImplicit false

namespace Mettapedia.ProbabilityTheory.StochasticInference.SoftBernoulliLearning

open Mettapedia.ProbabilityTheory.BayesianNetworks.ScopedFactorReadout (Masses)
open Mettapedia.ProbabilityTheory.BayesianNetworks.CPTLearning (BooleanCPTEntry)
open BinaryMixture (Likelihood)
open BetaPredictive

/-- The denotation sums over both choices for every latent outcome. -/
def worldMass (counts : BooleanCPTEntry) : List Likelihood → ℚ
  | [] => 1
  | report :: rest =>
    report.absent * predictive counts false * worldMass (addOutcome counts false) rest +
    report.present * predictive counts true * worldMass (addOutcome counts true) rest

private def countsAt (base : BooleanCPTEntry) (age successes : Nat) : BooleanCPTEntry :=
  ⟨base.n_pos + successes, base.n_neg + (age - successes)⟩

private theorem counts_false (base : BooleanCPTEntry) (age successes : Nat) (fit : successes ≤ age) :
    countsAt base (age + 1) successes = addOutcome (countsAt base age successes) false := by
  simp only [countsAt, addOutcome, BooleanCPTEntry.mk.injEq, true_and]
  omega

private theorem counts_true (base : BooleanCPTEntry) (age successes : Nat) :
    countsAt base (age + 1) (successes + 1) = addOutcome (countsAt base age successes) true := by
  simp only [countsAt, addOutcome, BooleanCPTEntry.mk.injEq]
  omega

def table (base : BooleanCPTEntry) : (age : Nat) → List Likelihood → Vector ℚ (age + 1)
  | age, [] => Vector.replicate (age + 1) 1
  | age, report :: rest =>
    let next := table base (age + 1) rest
    Vector.ofFn fun i =>
      let counts := countsAt base age i.val
      report.absent * predictive counts false * next[i.val]'(by omega) +
      report.present * predictive counts true * next[i.val + 1]'(by omega)

theorem table_exact (base : BooleanCPTEntry) (age : Nat) (data : List Likelihood)
    (index : Fin (age + 1)) :
    (table base age data)[index.val] = worldMass (countsAt base age index.val) data := by
  induction data generalizing age with
  | nil => simp [table, worldMass]
  | cons report data ih =>
    simp only [table, Vector.getElem_ofFn, worldMass]
    rw [ih (age + 1) ⟨index.val, by omega⟩, ih (age + 1) ⟨index.val + 1, by omega⟩]
    dsimp only
    rw [counts_false _ _ _ (by omega), counts_true]

def evidenceMass (base : BooleanCPTEntry) (data : List Likelihood) : ℚ :=
  (table base 0 data)[0]

theorem evidence_exact (base : BooleanCPTEntry) (data : List Likelihood) :
    evidenceMass base data = worldMass base data := by
  unfold evidenceMass
  simpa [countsAt] using table_exact base 0 data 0

def queryMasses (base : BooleanCPTEntry) (data : List Likelihood) : Masses :=
  ⟨predictive base true * evidenceMass (addOutcome base true) data, evidenceMass base data⟩

/-- A new unlabeled case can share the rate with the earlier reports.
The numerator is the evidence mass with that case constrained to true. -/
theorem query_exact (base : BooleanCPTEntry) (data : List Likelihood) :
    (queryMasses base data).joint = worldMass base (⟨0, 1, le_rfl, zero_le_one⟩ :: data) := by
  simp [queryMasses, evidence_exact, worldMass]

open Mettapedia.PLN.WorldModel.PredictiveBootstrap (Candidate)

def partitionMasses {Input : Type*} (candidate : Candidate Input)
    (data : List (Input × Likelihood)) (input : Input) : Masses :=
  let rows := (List.finRange candidate.cells).map (fun cell =>
    let reports := data.filterMap fun (x, report) =>
      if candidate.classify x = cell then some report else none
    (cell, queryMasses empty reports))
  let joint := rows.map (fun entry =>
    if candidate.classify input = entry.1 then entry.2.joint else entry.2.evidence)
  Masses.mk joint.prod (rows.map (fun entry => entry.2.evidence)).prod

namespace Controls

private def signal : Likelihood :=
  ⟨1 / 4, 3 / 4, by decide +kernel, by decide +kernel⟩

private def quiet : Likelihood :=
  ⟨1 / 2, 1 / 2, by decide +kernel, by decide +kernel⟩

theorem soft_report_moves_shared_prediction :
    (queryMasses empty [quiet]).posterior? = some (1 / 2) ∧
      (queryMasses empty [signal]).posterior? = some (7 / 12) ∧
      (queryMasses empty [signal, signal]).posterior? = some (17 / 26) := by decide +kernel

private def splitModel : Candidate Bool := ⟨2, bitValue, 1, zero_lt_one⟩

theorem soft_report_updates_its_partition :
    (partitionMasses splitModel [(false, signal)] false).posterior? = some (7 / 12) ∧
      (partitionMasses splitModel [(false, signal)] true).posterior? = some (1 / 2) := by
  decide +kernel

end Controls
end Mettapedia.ProbabilityTheory.StochasticInference.SoftBernoulliLearning
