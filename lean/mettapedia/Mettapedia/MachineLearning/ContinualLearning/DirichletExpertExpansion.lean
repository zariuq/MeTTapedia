import Mathlib

/-!
# Responsibility algebra for task-free expert expansion

Lee et al.'s *A Neural Dirichlet Process Mixture Model for Task-Free
Continual Learning* (ICLR 2020), Equations (2), (8), and Algorithm 1,
assigns an incoming example to existing experts with scores equal to stored
mass times likelihood, and to a candidate new expert with score equal to the
Dirichlet concentration times its base likelihood.

This file isolates the finite normalization algebra used by that mechanism.
The combined responsibilities conserve unit mass and preserve every pairwise
existing-expert odds ratio.  If the candidate is rejected, conditioning on
the existing experts cancels the candidate score exactly and again conserves
unit mass.  Updating stored counts with those conditional responsibilities
therefore adds one example exactly once.

The second normalization in Algorithm 1 is load-bearing.  If combined
responsibilities are added to existing counts without conditioning away a
positive candidate responsibility, the total existing count grows by
strictly less than one.  A two-expert fixture makes this failure executable.

These results concern finite nonnegative score normalization.  They do not
prove that neural likelihoods are calibrated, that a Dirichlet-process
approximation discovers a true task partition, or that expert expansion
improves continual-learning efficacy.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

namespace DirichletExpertExpansion

noncomputable section

open scoped BigOperators

variable {Expert : Type*} [Fintype Expert]

/-! ## Source score and responsibility maps -/

/-- Sum of the unnormalized scores of all existing experts. -/
def existingTotal (existingScore : Expert → ℝ) : ℝ :=
  ∑ expert, existingScore expert

/-- Sum of existing-expert scores and the candidate-new-expert score. -/
def totalScore (existingScore : Expert → ℝ) (newScore : ℝ) : ℝ :=
  existingTotal existingScore + newScore

/-- Responsibility of one existing expert before the new/existing decision. -/
def existingResponsibility
    (existingScore : Expert → ℝ) (newScore : ℝ) (expert : Expert) : ℝ :=
  existingScore expert / totalScore existingScore newScore

/-- Responsibility of the candidate new expert. -/
def newResponsibility
    (existingScore : Expert → ℝ) (newScore : ℝ) : ℝ :=
  newScore / totalScore existingScore newScore

/-- Responsibility conditioned on the sample belonging to an existing expert. -/
def conditionalExistingResponsibility
    (existingScore : Expert → ℝ) (expert : Expert) : ℝ :=
  existingScore expert / existingTotal existingScore

/-- Equation (8)'s existing-expert score: accumulated mass times likelihood. -/
def sourceExistingScore
    (storedMass likelihood : Expert → ℝ) (expert : Expert) : ℝ :=
  storedMass expert * likelihood expert

/-- Equation (8)'s candidate score: concentration times base likelihood. -/
def sourceNewScore (concentration baseLikelihood : ℝ) : ℝ :=
  concentration * baseLikelihood

omit [Fintype Expert] in
theorem sourceExistingScore_nonneg
    (storedMass likelihood : Expert → ℝ)
    (hmass : ∀ expert, 0 ≤ storedMass expert)
    (hlikelihood : ∀ expert, 0 ≤ likelihood expert)
    (expert : Expert) :
    0 ≤ sourceExistingScore storedMass likelihood expert :=
  mul_nonneg (hmass expert) (hlikelihood expert)

theorem sourceNewScore_nonneg
    {concentration baseLikelihood : ℝ}
    (hconcentration : 0 ≤ concentration)
    (hlikelihood : 0 ≤ baseLikelihood) :
    0 ≤ sourceNewScore concentration baseLikelihood :=
  mul_nonneg hconcentration hlikelihood

theorem existingTotal_nonneg
    (existingScore : Expert → ℝ)
    (hscore : ∀ expert, 0 ≤ existingScore expert) :
    0 ≤ existingTotal existingScore := by
  exact Finset.sum_nonneg fun expert _ => hscore expert

/-! ## Normalization and decision boundaries -/

/-- Existing and candidate responsibilities together conserve unit mass. -/
theorem sum_existingResponsibility_add_newResponsibility
    (existingScore : Expert → ℝ) (newScore : ℝ)
    (htotal : 0 < totalScore existingScore newScore) :
    (∑ expert, existingResponsibility existingScore newScore expert) +
        newResponsibility existingScore newScore =
      1 := by
  rw [show (∑ expert, existingResponsibility existingScore newScore expert) =
      existingTotal existingScore / totalScore existingScore newScore by
    simp only [existingResponsibility, existingTotal, Finset.sum_div]]
  unfold newResponsibility totalScore
  rw [← add_div]
  simpa [totalScore] using
    (div_self htotal.ne' : totalScore existingScore newScore /
      totalScore existingScore newScore = 1)

/-- The total responsibility assigned to existing experts is their score
mass divided by the complete score mass. -/
theorem sum_existingResponsibility
    (existingScore : Expert → ℝ) (newScore : ℝ) :
    (∑ expert, existingResponsibility existingScore newScore expert) =
      existingTotal existingScore / totalScore existingScore newScore := by
  simp only [existingResponsibility, existingTotal, Finset.sum_div]

/-- Conditioning on the existing experts conserves unit mass. -/
theorem sum_conditionalExistingResponsibility
    (existingScore : Expert → ℝ)
    (hexisting : 0 < existingTotal existingScore) :
    ∑ expert, conditionalExistingResponsibility existingScore expert = 1 := by
  simp only [conditionalExistingResponsibility, ← Finset.sum_div,
    existingTotal]
  simpa [existingTotal] using
    (div_self hexisting.ne' :
      existingTotal existingScore / existingTotal existingScore = 1)

/-- Algorithm 1's second normalization cancels the candidate score exactly. -/
theorem renormalize_combinedResponsibility_eq_conditional
    (existingScore : Expert → ℝ) (newScore : ℝ)
    (hexisting : 0 < existingTotal existingScore)
    (htotal : 0 < totalScore existingScore newScore)
    (expert : Expert) :
    existingResponsibility existingScore newScore expert /
        (∑ other, existingResponsibility existingScore newScore other) =
      conditionalExistingResponsibility existingScore expert := by
  rw [sum_existingResponsibility]
  unfold existingResponsibility conditionalExistingResponsibility
  field_simp [hexisting.ne', htotal.ne']

/-- Adding a candidate changes absolute responsibilities but preserves every
pairwise existing-expert odds ratio in cross-multiplied form. -/
theorem existingResponsibility_preserves_pairwiseOdds
    (existingScore : Expert → ℝ) (newScore : ℝ)
    (first second : Expert) :
    existingResponsibility existingScore newScore first *
        existingScore second =
      existingResponsibility existingScore newScore second *
        existingScore first := by
  unfold existingResponsibility
  ring

/-- The candidate beats one existing expert after normalization exactly when
its unnormalized score beats that expert's score. -/
theorem existingResponsibility_le_newResponsibility_iff
    (existingScore : Expert → ℝ) (newScore : ℝ)
    (htotal : 0 < totalScore existingScore newScore)
    (expert : Expert) :
    existingResponsibility existingScore newScore expert ≤
        newResponsibility existingScore newScore ↔
      existingScore expert ≤ newScore := by
  unfold existingResponsibility newResponsibility
  exact div_le_div_iff_of_pos_right htotal

/-- The candidate is maximal among all responsibilities exactly when its raw
score is maximal.  This removes normalization from the expansion decision. -/
theorem candidateMaximal_iff_rawScoreMaximal
    (existingScore : Expert → ℝ) (newScore : ℝ)
    (htotal : 0 < totalScore existingScore newScore) :
    (∀ expert,
        existingResponsibility existingScore newScore expert ≤
          newResponsibility existingScore newScore) ↔
      ∀ expert, existingScore expert ≤ newScore := by
  constructor
  · intro h expert
    exact (existingResponsibility_le_newResponsibility_iff
      existingScore newScore htotal expert).mp (h expert)
  · intro h expert
    exact (existingResponsibility_le_newResponsibility_iff
      existingScore newScore htotal expert).mpr (h expert)

/-- A candidate-responsibility threshold can be tested without division. -/
theorem threshold_lt_newResponsibility_iff
    (existingScore : Expert → ℝ) (newScore threshold : ℝ)
    (htotal : 0 < totalScore existingScore newScore) :
    threshold < newResponsibility existingScore newScore ↔
      threshold * existingTotal existingScore <
        (1 - threshold) * newScore := by
  unfold newResponsibility
  rw [lt_div_iff₀ htotal]
  unfold totalScore
  constructor <;> intro h <;> nlinarith

/-- A positive candidate score makes the unconditioned existing mass strictly
less than one. -/
theorem sum_existingResponsibility_lt_one
    (existingScore : Expert → ℝ) (newScore : ℝ)
    (htotal : 0 < totalScore existingScore newScore)
    (hnew : 0 < newScore) :
    (∑ expert, existingResponsibility existingScore newScore expert) < 1 := by
  rw [sum_existingResponsibility]
  apply (div_lt_one htotal).2
  unfold totalScore
  linarith

/-! ## Exactly-once count updates -/

/-- Add a responsibility packet to each stored expert count. -/
def updateCount
    (storedCount responsibility : Expert → ℝ) (expert : Expert) : ℝ :=
  storedCount expert + responsibility expert

/-- A normalized responsibility packet increases total stored count by one. -/
theorem sum_updateCount_eq_add_one
    (storedCount responsibility : Expert → ℝ)
    (hnormalized : ∑ expert, responsibility expert = 1) :
    ∑ expert, updateCount storedCount responsibility expert =
      (∑ expert, storedCount expert) + 1 := by
  simp only [updateCount, Finset.sum_add_distrib, hnormalized]

/-- Conditioning on the existing experts makes the source count update an
exactly-once update. -/
theorem conditionalExisting_update_adds_one
    (storedCount existingScore : Expert → ℝ)
    (hexisting : 0 < existingTotal existingScore) :
    ∑ expert,
        updateCount storedCount
          (conditionalExistingResponsibility existingScore) expert =
      (∑ expert, storedCount expert) + 1 := by
  apply sum_updateCount_eq_add_one
  exact sum_conditionalExistingResponsibility existingScore hexisting

/-- Updating counts with the unconditioned existing responsibilities adds
only their surviving mass. -/
theorem combinedExisting_update_mass
    (storedCount existingScore : Expert → ℝ) (newScore : ℝ) :
    ∑ expert,
        updateCount storedCount
          (existingResponsibility existingScore newScore) expert =
      (∑ expert, storedCount expert) +
        existingTotal existingScore / totalScore existingScore newScore := by
  simp only [updateCount, Finset.sum_add_distrib,
    sum_existingResponsibility]

/-- Omitting Algorithm 1's second normalization loses count mass whenever the
candidate has positive score. -/
theorem combinedExisting_update_adds_lt_one
    (storedCount existingScore : Expert → ℝ) (newScore : ℝ)
    (htotal : 0 < totalScore existingScore newScore)
    (hnew : 0 < newScore) :
    (∑ expert,
        updateCount storedCount
          (existingResponsibility existingScore newScore) expert) <
      (∑ expert, storedCount expert) + 1 := by
  rw [combinedExisting_update_mass]
  have hmass := sum_existingResponsibility_lt_one
    existingScore newScore htotal hnew
  rw [sum_existingResponsibility] at hmass
  linarith

/-! ## Executable two-expert fixtures -/

def twoExistingScore (expert : Fin 2) : ℝ :=
  if expert = 0 then 2 else 1

theorem twoExpert_combinedResponsibilities :
    existingResponsibility twoExistingScore 1 0 = 1 / 2 ∧
      existingResponsibility twoExistingScore 1 1 = 1 / 4 ∧
      newResponsibility twoExistingScore 1 = 1 / 4 := by
  norm_num [existingResponsibility, newResponsibility, totalScore,
    existingTotal, twoExistingScore, Fin.sum_univ_two]

theorem twoExpert_conditionalResponsibilities :
    conditionalExistingResponsibility twoExistingScore 0 = 2 / 3 ∧
      conditionalExistingResponsibility twoExistingScore 1 = 1 / 3 := by
  norm_num [conditionalExistingResponsibility, existingTotal,
    twoExistingScore, Fin.sum_univ_two]

/-- Negative fixture: without conditioning away the candidate, an incoming
example adds only `3/4` to the existing counts instead of one. -/
theorem twoExpert_missingRenormalization_loses_mass :
    (∑ expert : Fin 2,
        updateCount (fun _ => 0)
          (existingResponsibility twoExistingScore 1) expert) =
        3 / 4 ∧
      (∑ expert : Fin 2,
        updateCount (fun _ => 0)
          (conditionalExistingResponsibility twoExistingScore) expert) =
        1 := by
  norm_num [updateCount, existingResponsibility,
    conditionalExistingResponsibility, totalScore, existingTotal,
    twoExistingScore, Fin.sum_univ_two]

#print axioms sum_existingResponsibility_add_newResponsibility
#print axioms renormalize_combinedResponsibility_eq_conditional
#print axioms candidateMaximal_iff_rawScoreMaximal
#print axioms threshold_lt_newResponsibility_iff
#print axioms conditionalExisting_update_adds_one
#print axioms combinedExisting_update_adds_lt_one
#print axioms twoExpert_missingRenormalization_loses_mass

end

end DirichletExpertExpansion

end Mettapedia.MachineLearning.ContinualLearning
