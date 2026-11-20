import Mettapedia.PLN.WorldModel.ProbabilisticWitnessComposition

/-! # Exact factor messages and dependence counterexamples -/

set_option autoImplicit false

namespace Mettapedia.PLN.WorldModel.ProbabilisticWitnessComposition.Controls

open scoped BigOperators

noncomputable section

def bit (x : Bool) : ℝ := if x then 1 else 0
def report (hypothesis : Bool) : ℝ := if hypothesis then 3 / 4 else 1 / 4

/-- Two observations are conditionally independent given the root, as
specified by this factorization. Each observed report is true. -/
def twoReports : Factors Bool (.fork .leaf .leaf) :=
  .fork (fun _ => 1 / 2)
    (fun h r => if r then report h else 1 - report h)
    (fun h r => if r then report h else 1 - report h)
    (.leaf bit) (.leaf bit)

theorem twoReports_nonnegative : twoReports.Nonnegative := by
  simp only [twoReports, Factors.Nonnegative]
  constructor
  · intro x; norm_num
  constructor
  · intro x y; cases x <;> cases y <;> norm_num [report]
  constructor
  · intro x y; cases x <;> cases y <;> norm_num [report]
  constructor <;> intro x <;> cases x <;> norm_num [bit]

/-- The root messages retain both likelihood contributions. -/
theorem messages_two_reports :
    rootWeight twoReports true = 9 / 32 ∧ rootWeight twoReports false = 1 / 32 := by
  norm_num [twoReports, rootWeight, Fintype.sum_bool, bit, report]

theorem messages_posterior : readout (rootWeight twoReports) (fun _ => 1) bit = some (9 / 10) := by
  norm_num [readout, twoReports, rootWeight, Fintype.sum_bool, bit, report]

/-- All eight full configurations and the separator calculation agree. -/
theorem full_tree_posterior :
    readout (weight twoReports) (fun _ => 1) (fun c => bit (root c)) = some (9 / 10) := by
  have h := tree_readout twoReports (fun _ => 1) bit
  simpa only using h.trans messages_posterior

def fair (_ : Bool) : ℝ := 1 / 2

theorem one_report : readout fair (ledgerLikelihood ({0} : Finset ℕ) (fun _ => report)) bit =
    some (3 / 4) := by
  norm_num [readout, ledgerLikelihood, fair, report, bit, Fintype.sum_bool]

/-- Merging two witnesses backed by one event does not manufacture a second
observation. Naive multiplication instead changes the posterior. -/
theorem replay_differs_from_independent_copy :
    readout fair (ledgerLikelihood (({0} : Finset ℕ) ∪ {0}) (fun _ => report)) bit = some (3 / 4) ∧
      readout fair (fun x => ledgerLikelihood ({0} : Finset ℕ) (fun _ => report) x *
        ledgerLikelihood ({0} : Finset ℕ) (fun _ => report) x) bit = some (9 / 10) := by
  constructor
  · simpa using one_report
  · norm_num [readout, ledgerLikelihood, fair, report, bit, Fintype.sum_bool]

/-- One identical support event remains one event after proof composition. -/
def firstWitness : QueryWitness (Event := ℕ) (fun x : Bool => bit x * 1) bit where
  observations := {0}
  agrees _ := mul_one _

def secondWitness : QueryWitness (Event := ℕ) bit (fun x : Bool => 1 * bit x) where
  observations := {0}
  agrees _ := (one_mul _).symm

theorem composed_support_once :
    (firstWitness.comp secondWitness).observations = {0} := by
  simp [QueryWitness.comp, firstWitness, secondWitness]

theorem composed_witness_posterior :
    readout fair (ledgerLikelihood (firstWitness.comp secondWitness).observations
      (fun _ => report)) (fun x => bit x * 1) = some (3 / 4) := by
  simpa [composed_support_once] using one_report

/-- The observed true bit licenses replacing that bit's query by true only
on the worlds retained by its evidence. -/
def conditionalWitness : LocalWitness (fun (_ : ℕ) => bit) bit (fun _ => 1) where
  observations := {0}
  agrees x possible := by
    cases x
    · simp [ledgerLikelihood, bit] at possible
    · rfl

theorem conditional_witness_readout :
    readout fair (ledgerLikelihood conditionalWitness.observations (fun (_ : ℕ) => bit)) bit = some 1 := by
  norm_num [readout, conditionalWitness, ledgerLikelihood, bit, fair, Fintype.sum_bool]

/-- Removing a witness's supporting observation invalidates its local
transformation under the prior. -/
theorem dropping_witness_support_changes_answer :
    readout fair (fun _ => 1) bit ≠ readout fair (fun _ => 1) (fun _ => 1) := by
  norm_num [readout, bit, fair, Fintype.sum_bool]

/-! ## Equal marginals can hide opposing joint dependence -/

def correlated (world : Bool × Bool) : ℝ := if world.1 = world.2 then 1 / 2 else 0
def anticorrelated (world : Bool × Bool) : ℝ := if world.1 = world.2 then 0 else 1 / 2

theorem equal_current_marginals :
    readout correlated (fun _ => 1) (fun x => bit x.1) = some (1 / 2) ∧
      readout anticorrelated (fun _ => 1) (fun x => bit x.1) = some (1 / 2) ∧
      readout correlated (fun _ => 1) (fun x => bit x.2) = some (1 / 2) ∧
      readout anticorrelated (fun _ => 1) (fun x => bit x.2) = some (1 / 2) := by
  norm_num [readout, correlated, anticorrelated, bit, Fintype.sum_prod_type, Fintype.sum_bool]

theorem future_evidence_splits :
    readout correlated (fun x => bit x.2) (fun x => bit x.1) = some 1 ∧
      readout anticorrelated (fun x => bit x.2) (fun x => bit x.1) = some 0 := by
  norm_num [readout, correlated, anticorrelated, bit, Fintype.sum_prod_type, Fintype.sum_bool]

theorem not_behaviorally_equivalent :
    ¬ BehavioralEquivalent (fun (_ : Unit) (x : Bool × Bool) => bit x.2)
      (fun (_ : Unit) (x : Bool × Bool) => bit x.1) correlated anticorrelated := by
  intro h
  have next := h [()] ()
  change readout correlated (fun x => bit x.2 * 1) (fun x => bit x.1) =
    readout anticorrelated (fun x => bit x.2 * 1) (fun x => bit x.1) at next
  simp only [mul_one] at next
  rw [future_evidence_splits.1, future_evidence_splits.2] at next
  norm_num at next

/-! ## Positivity is necessary for a quantitative probability bound -/

/-- Small absolute weight errors can hide a unit posterior error when the
normalizer has no positive margin. -/
theorem unsupported_normalization_unstable (ε : ℝ) (positive : 0 < ε) :
    readout (fun x : Bool => if x then ε else 0) (fun _ => 1) bit = some 1 ∧
      readout (fun x : Bool => if x then 0 else ε) (fun _ => 1) bit = some 0 := by
  simp [readout, bit, ne_of_gt positive]

#print axioms tree_elimination
#print axioms tree_readout
#print axioms normalized_error
#print axioms tree_approximation_error
#print axioms LocalWitness.readout_preserved
#print axioms behavioral_of_pushforward
#print axioms replay_differs_from_independent_copy
#print axioms not_behaviorally_equivalent

end

end Mettapedia.PLN.WorldModel.ProbabilisticWitnessComposition.Controls
