import Mettapedia.MachineLearning.NeuralNetworks.Architecture.LogitPriorAdjustment

/-!
# Finite sliding-window class-prior estimation

Huang et al., *Online Continual Learning via Logit Adjusted Softmax*
(arXiv:2311.06460), estimate a changing class prior by counting labels in a
finite sliding window of incoming and replay batches.  Here `Sample` is the
flattened finite index of that window.

The raw estimator is normalized and a class has positive estimated prior
exactly when it occurs in the window.  That exact support law exposes an
important executable boundary: an absent but still legal action family receives
prior zero, outside the positive-prior hypothesis of logarithmic adjustment.
The additive-smoothed estimator below is a proved generalization.  It remains
normalized, assigns every finite class positive mass, and reduces to the source
estimator at pseudocount zero.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.Architecture

noncomputable section

variable {Sample Class : Type*}

/-- Number of occurrences of one label in a finite window, represented in
`ℝ` so it composes directly with softmax logits. -/
def empiricalLabelMass [Fintype Sample] [DecidableEq Class]
    (labelOf : Sample → Class) (label : Class) : ℝ :=
  ∑ sample, if labelOf sample = label then 1 else 0

/-- The source paper's finite-window empirical class prior. -/
def empiricalLabelPrior [Fintype Sample] [Fintype Class]
    [DecidableEq Class]
    (labelOf : Sample → Class) (label : Class) : ℝ :=
  empiricalLabelMass labelOf label / Fintype.card Sample

/-- Additive pseudocount smoothing over the same finite class set. -/
def smoothedEmpiricalPrior [Fintype Sample] [Fintype Class]
    [DecidableEq Class] (pseudoCount : ℝ)
    (labelOf : Sample → Class) (label : Class) : ℝ :=
  (empiricalLabelMass labelOf label + pseudoCount) /
    (Fintype.card Sample + pseudoCount * Fintype.card Class)

theorem empiricalLabelMass_nonneg [Fintype Sample] [DecidableEq Class]
    (labelOf : Sample → Class) (label : Class) :
    0 ≤ empiricalLabelMass labelOf label := by
  unfold empiricalLabelMass
  positivity

/-- Double counting the finite sample/label incidence relation. -/
theorem sum_empiricalLabelMass [Fintype Sample] [Fintype Class]
    [DecidableEq Class] (labelOf : Sample → Class) :
    ∑ label, empiricalLabelMass labelOf label = Fintype.card Sample := by
  classical
  simp only [empiricalLabelMass]
  rw [Finset.sum_comm]
  simp

/-- A nonempty empirical window defines a normalized categorical prior. -/
theorem sum_empiricalLabelPrior_eq_one
    [Fintype Sample] [Nonempty Sample] [Fintype Class]
    [DecidableEq Class] (labelOf : Sample → Class) :
    ∑ label, empiricalLabelPrior labelOf label = 1 := by
  classical
  simp only [empiricalLabelPrior, ← Finset.sum_div]
  rw [sum_empiricalLabelMass]
  norm_num [Fintype.card_ne_zero]

/-- A label has positive count exactly when it occurs in the finite window. -/
theorem empiricalLabelMass_pos_iff
    [Fintype Sample] [DecidableEq Class]
    (labelOf : Sample → Class) (label : Class) :
    0 < empiricalLabelMass labelOf label ↔
      ∃ sample, labelOf sample = label := by
  classical
  constructor
  · intro massPositive
    by_contra absent
    push Not at absent
    have massZero : empiricalLabelMass labelOf label = 0 := by
      simp [empiricalLabelMass, absent]
    linarith
  · rintro ⟨sample, sampleHasLabel⟩
    unfold empiricalLabelMass
    apply Finset.sum_pos'
    · intro item _
      split <;> norm_num
    · exact ⟨sample, Finset.mem_univ _, by simp [sampleHasLabel]⟩

/-- The empirical prior inherits the same exact support when the window is
nonempty. -/
theorem empiricalLabelPrior_pos_iff
    [Fintype Sample] [Nonempty Sample] [Fintype Class]
    [DecidableEq Class]
    (labelOf : Sample → Class) (label : Class) :
    0 < empiricalLabelPrior labelOf label ↔
      ∃ sample, labelOf sample = label := by
  have cardPositive : 0 < (Fintype.card Sample : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have massNonnegative := empiricalLabelMass_nonneg labelOf label
  rw [empiricalLabelPrior, div_pos_iff]
  constructor
  · rintro (positive | negative)
    · exact (empiricalLabelMass_pos_iff labelOf label).mp positive.1
    · exact (not_lt_of_ge massNonnegative negative.1).elim
  · intro present
    exact Or.inl
      ⟨(empiricalLabelMass_pos_iff labelOf label).mpr present,
        cardPositive⟩

@[simp] theorem smoothedEmpiricalPrior_zero
    [Fintype Sample] [Fintype Class] [DecidableEq Class]
    (labelOf : Sample → Class) (label : Class) :
    smoothedEmpiricalPrior 0 labelOf label =
      empiricalLabelPrior labelOf label := by
  simp [smoothedEmpiricalPrior, empiricalLabelPrior]

/-- Every class receives positive mass under a positive pseudocount. -/
theorem smoothedEmpiricalPrior_pos
    [Fintype Sample] [Fintype Class] [Nonempty Class]
    [DecidableEq Class] (pseudoCount : ℝ)
    (pseudoCountPositive : 0 < pseudoCount)
    (labelOf : Sample → Class) (label : Class) :
    0 < smoothedEmpiricalPrior pseudoCount labelOf label := by
  have classCardPositive : 0 < (Fintype.card Class : ℝ) := by
    exact_mod_cast Fintype.card_pos
  apply div_pos
  · exact add_pos_of_nonneg_of_pos
      (empiricalLabelMass_nonneg labelOf label) pseudoCountPositive
  · positivity

/-- Positive-pseudocount smoothing remains exactly normalized, even for an
empty sample window. -/
theorem sum_smoothedEmpiricalPrior_eq_one
    [Fintype Sample] [Fintype Class] [Nonempty Class]
    [DecidableEq Class] (pseudoCount : ℝ)
    (pseudoCountPositive : 0 < pseudoCount)
    (labelOf : Sample → Class) :
    ∑ label, smoothedEmpiricalPrior pseudoCount labelOf label = 1 := by
  classical
  have classCardPositive : 0 < (Fintype.card Class : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have denominatorPositive :
      0 < (Fintype.card Sample : ℝ) +
          pseudoCount * Fintype.card Class := by
    positivity
  simp only [smoothedEmpiricalPrior, ← Finset.sum_div,
    Finset.sum_add_distrib, sum_empiricalLabelMass]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp [ne_of_gt denominatorPositive]

/-- Positive smoothing discharges the positivity premise needed by logarithmic
prior adjustment for every class. -/
theorem exp_logitAdjustedScore_smoothedPrior
    [Fintype Sample] [Fintype Class] [Nonempty Class]
    [DecidableEq Class]
    (pseudoCount temperature : ℝ)
    (pseudoCountPositive : 0 < pseudoCount)
    (labelOf : Sample → Class) (logit : Class → ℝ) (label : Class) :
    Real.exp
        (logitAdjustedScore logit
          (smoothedEmpiricalPrior pseudoCount labelOf) temperature label) =
      Real.exp (logit label) *
        smoothedEmpiricalPrior pseudoCount labelOf label ^ temperature :=
  exp_logitAdjustedScore logit
    (smoothedEmpiricalPrior pseudoCount labelOf) temperature label
    (smoothedEmpiricalPrior_pos pseudoCount pseudoCountPositive
      labelOf label)

/-! ## Finite-window fixtures -/

def twoNewOneOldWindow : Fin 3 → Bool :=
  ![false, true, true]

/-- A flattened three-sample window recovers the exact one-to-two frequencies. -/
theorem twoNewOneOldWindow_prior :
    empiricalLabelPrior twoNewOneOldWindow false = 1 / 3 ∧
      empiricalLabelPrior twoNewOneOldWindow true = 2 / 3 := by
  norm_num [empiricalLabelPrior, empiricalLabelMass,
    twoNewOneOldWindow, Fin.sum_univ_succ]
  norm_cast

def allTrueWindow : Fin 2 → Bool := fun _ => true

/-- Negative boundary and its proved repair: an absent legal class receives raw
prior zero, while unit pseudocount smoothing assigns it one quarter and keeps
the observed class at three quarters. -/
theorem absentLabel_zeroPrior_smoothedPositive :
    empiricalLabelPrior allTrueWindow false = 0 ∧
      smoothedEmpiricalPrior 1 allTrueWindow false = 1 / 4 ∧
      smoothedEmpiricalPrior 1 allTrueWindow true = 3 / 4 := by
  norm_num [empiricalLabelPrior, smoothedEmpiricalPrior,
    empiricalLabelMass, allTrueWindow, Fin.sum_univ_succ]

#print axioms sum_empiricalLabelMass
#print axioms sum_empiricalLabelPrior_eq_one
#print axioms empiricalLabelMass_pos_iff
#print axioms empiricalLabelPrior_pos_iff
#print axioms smoothedEmpiricalPrior_zero
#print axioms smoothedEmpiricalPrior_pos
#print axioms sum_smoothedEmpiricalPrior_eq_one
#print axioms exp_logitAdjustedScore_smoothedPrior
#print axioms twoNewOneOldWindow_prior
#print axioms absentLabel_zeroPrior_smoothedPositive

end

end Mettapedia.MachineLearning.NeuralNetworks.Architecture
