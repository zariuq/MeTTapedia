import Mettapedia.ProbabilityTheory.BayesianNetworks.ScopedFactorQueries
import Mettapedia.ProbabilityTheory.FiniteEventMass

/-!
# Joint evidence in ProofWriter RelNoneg-OWA-D5-683

In the structured theory, Q5 has three published proofs. With the rules
and other facts fixed, its minimal fact supports are {11, 3} and {11, 4}.
The Python corpus audit checks the reduction against Horn closure in all
eight premise configurations. Here we check the Bayesian readout of that
event through the executable WM factor query. The observation model is a
controlled extension of the benchmark.
-/

set_option autoImplicit false

namespace Mettapedia.Examples.PLN.ProofWriterEvidenceReplay

open Mettapedia.ProbabilityTheory
open Mettapedia.ProbabilityTheory.BayesianNetworks
open ExecutableFactorTable ScopedFactorReadout

def domains (_ : Fin 5) : Nat := 2

theorem positive (v : Fin 5) : 0 < domains v := by simp [domains]

/-- Variable 0 is the source reliability mode, 1–3 are facts 11, 3, 4,
and 4 records whether the query has a proof. -/
def proofIndicator : Table domains :=
  tabulate domains positive [1, 2, 3, 4] (by decide) fun cfg =>
    let proved := (cfg 1).val = 1 ∧ ((cfg 2).val = 1 ∨ (cfg 3).val = 1)
    if ((cfg 4).val = 1) ↔ proved then 1 else 0

def fairBit (v : Fin 5) : Table domains :=
  tabulate domains positive [v] (by simp) fun _ => 1 / 2

inductive Report
  | sharedPremise
  | leftPremise
  | rightPremise
  | confirmation
  | disagreement
  deriving DecidableEq

def Report.premise : Report → Fin 5
  | .leftPremise => 2
  | .rightPremise => 3
  | _ => 1

def Report.signedLikelihood (report : Report) (value : Nat) (accuracy : ℚ) : ℚ :=
  if (value = 1) ↔ report ≠ .disagreement then accuracy else 1 - accuracy

def Report.factor (sharedSource : Bool) (report : Report) : Table domains :=
  if sharedSource && report != .confirmation && report != .disagreement then
    tabulate domains positive [0, report.premise] (by cases report <;> decide) fun cfg =>
      report.signedLikelihood (cfg report.premise).val (if (cfg 0).val = 1 then 1 else 1 / 2)
  else
    tabulate domains positive [report.premise] (by simp) fun cfg =>
      report.signedLikelihood (cfg report.premise).val (3 / 4)

def factors (sharedSource : Bool) (reports : List Report) : List (Table domains) :=
  proofIndicator :: [0, 1, 2, 3].map fairBit ++
    reports.eraseDups.map (Report.factor sharedSource)

def present (v : Fin 5) : Constraint domains := ⟨v, ⟨1, by simp [domains]⟩⟩

def readout (sharedSource : Bool) (reports : List Report) : Option Masses :=
  conditionalMasses? positive (factors sharedSource reports) []
    [present 4] [0, 1, 2, 3, 4]

def initial : List Report := [.sharedPremise, .leftPremise, .rightPremise]

theorem prior : readout false [] = some ⟨3 / 8, 1⟩ := by decide +kernel

theorem independent : readout false initial = some ⟨45 / 512, 1 / 8⟩ := by decide +kernel

theorem commonSource : readout true initial = some ⟨11 / 128, 1 / 8⟩ := by decide +kernel

theorem replay (sharedSource : Bool) :
    readout sharedSource (initial ++ [.sharedPremise]) = readout sharedSource initial := by
  have same : (initial ++ [Report.sharedPremise]).eraseDups = initial.eraseDups := by decide
  unfold readout factors
  rw [same]

theorem confirmation : readout false (initial ++ [.confirmation]) = some ⟨135 / 2048, 5 / 64⟩ := by
  decide +kernel

theorem disagreement : readout false (initial ++ [.disagreement]) = some ⟨45 / 2048, 3 / 64⟩ := by
  decide +kernel

theorem commonSourceConfirmation :
    readout true (initial ++ [.confirmation]) = some ⟨33 / 512, 5 / 64⟩ := by
  decide +kernel

theorem commonSourceDisagreement :
    readout true (initial ++ [.disagreement]) = some ⟨11 / 512, 3 / 64⟩ := by
  decide +kernel

/-- Condition additionally on the existence of a proof and read a premise. -/
def premiseGivenProof (sharedSource : Bool) (premise : Fin 5) : Option Masses :=
  conditionalMasses? positive (factors sharedSource initial) [present 4]
    [present premise] [0, 1, 2, 3, 4]

theorem independentAbduction : premiseGivenProof false 2 = some ⟨9 / 128, 45 / 512⟩ := by
  decide +kernel

theorem commonSourceAbduction : premiseGivenProof true 2 = some ⟨5 / 64, 11 / 128⟩ := by
  decide +kernel

section DependenceBounds

open FiniteEventMass

abbrev Premises := Bool × Bool × Bool

def entailed (w : Premises) : Bool := w.1 && (w.2.1 || w.2.2)

/-- With only the premise marginals, the query lies between the mass
guaranteed by either route and the mass of their common prerequisite. -/
theorem dependenceBounds (weight : Premises → ℝ) (nonneg : ∀ w, 0 ≤ weight w)
    (total : mass weight (fun _ => true) = 1)
    (shared : mass weight (fun w => w.1) = 3 / 4)
    (left : mass weight (fun w => w.2.1) = 3 / 4) :
    1 / 2 ≤ mass weight entailed ∧ mass weight entailed ≤ 3 / 4 := by
  have lower := (branch_frechet weight nonneg (·.1) (fun _ => true) (·.2.1)).1
  simp only [Bool.and_true, Bool.true_and, total, shared, left] at lower
  have routeLe : mass weight (fun w => w.1 && w.2.1) ≤ mass weight entailed := by
    apply mono weight nonneg
    intro w route
    simp_all [entailed, Bool.and_eq_true]
  have sharedLe : mass weight entailed ≤ mass weight (fun w => w.1) := by
    apply mono weight nonneg
    intro w proved
    simp_all [entailed, Bool.and_eq_true]
  constructor
  · linarith [le_max_right (0 : ℝ) (3 / 4 + 3 / 4 - 1)]
  · rwa [shared] at sharedLe

noncomputable def lowerCoupling (w : Premises) : ℝ :=
  if w = (true, true, true) then 1 / 2
  else if w = (true, false, false) ∨ w = (false, true, true) then 1 / 4
  else 0

noncomputable def upperCoupling (w : Premises) : ℝ :=
  if w = (true, true, true) then 3 / 4 else if w = (false, false, false) then 1 / 4 else 0

theorem lowerAttained :
    (∀ w, 0 ≤ lowerCoupling w) ∧ mass lowerCoupling (fun _ => true) = 1 ∧
    mass lowerCoupling (fun w => w.1) = 3 / 4 ∧ mass lowerCoupling (fun w => w.2.1) = 3 / 4 ∧
    mass lowerCoupling (fun w => w.2.2) = 3 / 4 ∧ mass lowerCoupling entailed = 1 / 2 := by
  refine ⟨?_, ?_⟩
  · intro ⟨s, a, b⟩
    cases s <;> cases a <;> cases b <;> norm_num [lowerCoupling]
  · norm_num [mass, entailed, lowerCoupling, Fintype.sum_prod_type, Fintype.sum_bool]

theorem upperAttained :
    (∀ w, 0 ≤ upperCoupling w) ∧ mass upperCoupling (fun _ => true) = 1 ∧
    mass upperCoupling (fun w => w.1) = 3 / 4 ∧ mass upperCoupling (fun w => w.2.1) = 3 / 4 ∧
    mass upperCoupling (fun w => w.2.2) = 3 / 4 ∧ mass upperCoupling entailed = 3 / 4 := by
  refine ⟨?_, ?_⟩
  · intro ⟨s, a, b⟩
    cases s <;> cases a <;> cases b <;> norm_num [upperCoupling]
  · norm_num [mass, entailed, upperCoupling, Fintype.sum_prod_type, Fintype.sum_bool]

end DependenceBounds

end Mettapedia.Examples.PLN.ProofWriterEvidenceReplay
