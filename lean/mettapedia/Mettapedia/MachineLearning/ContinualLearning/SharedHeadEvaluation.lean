import Mathlib

/-!
# Shared-head and task-oracle evaluation

Farquhar and Gal, *Towards Robust Evaluations of Continual Learning*
(2019, arXiv:1805.09733), Desiderata B--C and Section 4.2.2, distinguish
evaluation with one shared output head from evaluation that supplies the task
identity and restricts prediction to that task's labels.

This file makes the resulting optimism boundary exact.  If the true label is
retained, correctness against every label implies correctness against a
restricted task head.  Consequently, the number of task-oracle-correct
examples is at least the number of shared-head-correct examples.  The converse
is false: an out-of-task distractor can defeat the shared head while remaining
invisible to the task oracle.

Membership of the true label is part of the restricted-head predicate.  A
negative fixture shows that omitting this condition makes an empty head
vacuously "correct".

The order-based predicates deliberately allow ties.  No theorem claims that a
particular tie-breaking implementation selects the true label.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

namespace SharedHeadEvaluation

noncomputable section

variable {Label Sample : Type*}

/-- The true label has score at least that of every label in the shared head. -/
def SharedCorrect
    (score : Label → ℝ) (truth : Label) : Prop :=
  ∀ candidate, score candidate ≤ score truth

/-- The true label belongs to the task head and has score at least that of
every label retained by that head. -/
def OracleHeadCorrect
    (allowed : Finset Label) (score : Label → ℝ) (truth : Label) : Prop :=
  truth ∈ allowed ∧
    ∀ candidate ∈ allowed, score candidate ≤ score truth

/-- A shared-head-correct prediction remains correct after an oracle restricts
the candidates, provided the true label is retained. -/
theorem sharedCorrect_implies_oracleHeadCorrect
    [DecidableEq Label]
    (allowed : Finset Label)
    (score : Label → ℝ)
    (truth : Label)
    (truth_allowed : truth ∈ allowed)
    (correct : SharedCorrect score truth) :
    OracleHeadCorrect allowed score truth := by
  exact ⟨truth_allowed, fun candidate _ => correct candidate⟩

/-- Correctness on a larger oracle head implies correctness on every smaller
head that still contains the true label. -/
theorem oracleHeadCorrect_antitone
    [DecidableEq Label]
    {smaller larger : Finset Label}
    (subset : smaller ⊆ larger)
    (score : Label → ℝ)
    (truth : Label)
    (truth_smaller : truth ∈ smaller)
    (correct : OracleHeadCorrect larger score truth) :
    OracleHeadCorrect smaller score truth := by
  refine ⟨truth_smaller, ?_⟩
  intro candidate candidate_small
  exact correct.2 candidate (subset candidate_small)

/-- On the complete finite label universe, oracle-head correctness is exactly
shared-head correctness. -/
theorem oracleHeadCorrect_univ_iff
    [Fintype Label] [DecidableEq Label]
    (score : Label → ℝ)
    (truth : Label) :
    OracleHeadCorrect Finset.univ score truth ↔
      SharedCorrect score truth := by
  constructor
  · intro correct candidate
    exact correct.2 candidate (Finset.mem_univ candidate)
  · intro correct
    exact sharedCorrect_implies_oracleHeadCorrect
      Finset.univ score truth (Finset.mem_univ truth) correct

/-- Examples correct under the shared output head. -/
def sharedCorrectSamples
    (samples : Finset Sample)
    (score : Sample → Label → ℝ)
    (truth : Sample → Label) : Finset Sample := by
  classical
  exact samples.filter fun sample =>
    SharedCorrect (score sample) (truth sample)

/-- Examples correct when a task oracle supplies an allowed label head. -/
def oracleCorrectSamples
    [DecidableEq Label]
    (samples : Finset Sample)
    (allowed : Sample → Finset Label)
    (score : Sample → Label → ℝ)
    (truth : Sample → Label) : Finset Sample := by
  classical
  exact samples.filter fun sample =>
    OracleHeadCorrect (allowed sample) (score sample) (truth sample)

/-- Supplying a task oracle cannot reduce the number of order-correct examples
when every task head retains its true label. -/
theorem sharedCorrectSamples_subset_oracleCorrectSamples
    [DecidableEq Sample] [DecidableEq Label]
    (samples : Finset Sample)
    (allowed : Sample → Finset Label)
    (score : Sample → Label → ℝ)
    (truth : Sample → Label)
    (truth_allowed :
      ∀ sample ∈ samples, truth sample ∈ allowed sample) :
    sharedCorrectSamples samples score truth ⊆
      oracleCorrectSamples samples allowed score truth := by
  intro sample sample_shared
  simp only [sharedCorrectSamples, Finset.mem_filter] at sample_shared
  simp only [oracleCorrectSamples, Finset.mem_filter]
  exact ⟨sample_shared.1,
    sharedCorrect_implies_oracleHeadCorrect
      (allowed sample) (score sample) (truth sample)
      (truth_allowed sample sample_shared.1) sample_shared.2⟩

/-- Cardinal form of the task-oracle optimism inequality. -/
theorem sharedCorrectCount_le_oracleCorrectCount
    [DecidableEq Sample] [DecidableEq Label]
    (samples : Finset Sample)
    (allowed : Sample → Finset Label)
    (score : Sample → Label → ℝ)
    (truth : Sample → Label)
    (truth_allowed :
      ∀ sample ∈ samples, truth sample ∈ allowed sample) :
    (sharedCorrectSamples samples score truth).card ≤
      (oracleCorrectSamples samples allowed score truth).card :=
  Finset.card_le_card
    (sharedCorrectSamples_subset_oracleCorrectSamples
      samples allowed score truth truth_allowed)

/-! ## Executable boundaries -/

/-- Three labels where an out-of-task distractor outranks the true label. -/
def distractorScore : Fin 3 → ℝ
  | 0 => 1
  | 1 => 0
  | 2 => 2

/-- The oracle for the first task hides label `2`. -/
def firstTaskHead : Finset (Fin 3) := {0, 1}

/-- Positive fixture: restricting to the true task makes the prediction
order-correct. -/
theorem distractorScore_oracle_correct :
    OracleHeadCorrect firstTaskHead distractorScore 0 := by
  constructor
  · simp [firstTaskHead]
  · intro candidate candidate_allowed
    have cases : candidate = 0 ∨ candidate = 1 := by
      simpa [firstTaskHead] using candidate_allowed
    rcases cases with rfl | rfl <;> norm_num [distractorScore]

/-- Negative fixture: the same scores are not correct under the shared head. -/
theorem distractorScore_not_shared_correct :
    ¬ SharedCorrect distractorScore 0 := by
  intro correct
  have bound := correct (2 : Fin 3)
  norm_num [distractorScore] at bound

/-- One sample witnesses strict inflation from a task-oracle head. -/
theorem taskOracle_can_strictly_inflate_correct_count :
    let samples : Finset Unit := {()}
    let allowed : Unit → Finset (Fin 3) := fun _ => firstTaskHead
    let score : Unit → Fin 3 → ℝ := fun _ => distractorScore
    let truth : Unit → Fin 3 := fun _ => 0
    (sharedCorrectSamples samples score truth).card = 0 ∧
      (oracleCorrectSamples samples allowed score truth).card = 1 := by
  simp only
    [sharedCorrectSamples, oracleCorrectSamples, Finset.filter_singleton,
      distractorScore_not_shared_correct, distractorScore_oracle_correct,
      if_false, if_true, Finset.card_empty, Finset.card_singleton]
  exact ⟨trivial, trivial⟩

/-- A naive restriction predicate without true-label membership. -/
def NaiveRestrictedCorrect
    (allowed : Finset Label) (score : Label → ℝ) (truth : Label) : Prop :=
  ∀ candidate ∈ allowed, score candidate ≤ score truth

/-- Negative boundary: an empty naive head is vacuously correct even though
the proper oracle-head predicate rejects it. -/
theorem empty_naive_head_is_vacuous_but_oracle_head_rejects
    [DecidableEq Label]
    (score : Label → ℝ)
    (truth : Label) :
    NaiveRestrictedCorrect ∅ score truth ∧
      ¬ OracleHeadCorrect ∅ score truth := by
  simp [NaiveRestrictedCorrect, OracleHeadCorrect]

end

end SharedHeadEvaluation

end Mettapedia.MachineLearning.ContinualLearning

#print axioms Mettapedia.MachineLearning.ContinualLearning.SharedHeadEvaluation.sharedCorrect_implies_oracleHeadCorrect
#print axioms Mettapedia.MachineLearning.ContinualLearning.SharedHeadEvaluation.oracleHeadCorrect_antitone
#print axioms Mettapedia.MachineLearning.ContinualLearning.SharedHeadEvaluation.sharedCorrectCount_le_oracleCorrectCount
#print axioms Mettapedia.MachineLearning.ContinualLearning.SharedHeadEvaluation.taskOracle_can_strictly_inflate_correct_count
#print axioms Mettapedia.MachineLearning.ContinualLearning.SharedHeadEvaluation.empty_naive_head_is_vacuous_but_oracle_head_rejects
