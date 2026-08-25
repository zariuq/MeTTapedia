import Mettapedia.Enactive.Finite
import Mathlib.Algebra.BigOperators.Field

/-!
# Finite weakness weights and the task-coverage prior

Michael Timothy Bennett's Remark 1 in *The Optimal Choice of Hypothesis Is
the Weakest, Not the Shortest* (2023, arXiv:2301.12987) associates a statement
`h` with the ratio

`2 ^ |E_h| / 2 ^ |L_v|`,

where `E_h` is the statement's extension and `L_v` is the finite implementable
language.  The ratio has an exact probability interpretation: under the
uniform distribution on all subsets of `L_v`, it is the probability that the
sampled subset lies inside `E_h`.  It is therefore a task-coverage event
probability for each `h`; the family of these overlapping event probabilities
need not be a normalized distribution over hypotheses.

This file proves that exact interpretation, gives a concrete counterexample to
global hypothesis normalization, and defines the separately normalized finite
weakness prior obtained by normalizing the weights `2 ^ |E_h|` over the
hypothesis language.  The correction preserves Bennett's hypothesis ordering.

The construction is deliberately kept separate from Solomonoff's algorithmic
semimeasure: the former rewards semantic freedom in a fixed finite abstraction
layer, while the latter rewards short descriptions relative to a universal
prefix machine (Solomonoff, *A Formal Theory of Inductive Inference*, 1964).
-/

set_option autoImplicit false

namespace Mettapedia.UniversalAI.WeaknessPrior

open scoped BigOperators
open Mettapedia.Enactive.Finite

universe uWorld

variable {World : Type uWorld} [Fintype World] [DecidableEq World]

namespace Layer

variable (finiteLayer : Mettapedia.Enactive.Finite.Layer World)

/-- The finite hypothesis language `L_v`, with the membership proof retained
in each statement. -/
def language : Finset finiteLayer.Statement :=
  finiteLayer.statements.attach

@[simp]
theorem card_language : (language finiteLayer).card = finiteLayer.statements.card := by
  simp [language]

/-- Uniform task sample space used in Bennett's Remark 1: every subset of the
finite statement language is one outcome. -/
def taskSampleSpace : Finset (Finset finiteLayer.Statement) :=
  (language finiteLayer).powerset

/-- The favorable outcomes for `hypothesis` are the subsets made entirely of
statements in its extension. -/
def favorableTaskOutcomes (hypothesis : finiteLayer.Statement) :
    Finset (Finset finiteLayer.Statement) :=
  (finiteLayer.extension hypothesis).powerset

theorem card_taskSampleSpace :
    (taskSampleSpace finiteLayer).card = 2 ^ (language finiteLayer).card := by
  simp [taskSampleSpace]

theorem card_favorableTaskOutcomes (hypothesis : finiteLayer.Statement) :
    (favorableTaskOutcomes finiteLayer hypothesis).card =
      2 ^ finiteLayer.weakness hypothesis := by
  simp [favorableTaskOutcomes, Mettapedia.Enactive.Finite.Layer.weakness]

/-- Bennett's Remark 1 ratio, interpreted as a rational event probability. -/
def taskCoverageProbability (hypothesis : finiteLayer.Statement) : ℚ :=
  (2 ^ finiteLayer.weakness hypothesis : ℚ) /
    (2 ^ (language finiteLayer).card : ℚ)

/-- The published power-of-two ratio is exactly favorable-outcome count over
sample-space count. -/
theorem taskCoverageProbability_eq_card_ratio
    (hypothesis : finiteLayer.Statement) :
    taskCoverageProbability finiteLayer hypothesis =
      ((favorableTaskOutcomes finiteLayer hypothesis).card : ℚ) /
        (taskSampleSpace finiteLayer).card := by
  rw [taskCoverageProbability, card_favorableTaskOutcomes,
    card_taskSampleSpace]
  simp only [Nat.cast_pow, Nat.cast_ofNat]

/-- Task coverage is monotone in Bennett weakness. -/
theorem taskCoverageProbability_mono
    {left right : finiteLayer.Statement}
    (ordered : finiteLayer.weakness left ≤ finiteLayer.weakness right) :
    taskCoverageProbability finiteLayer left ≤
      taskCoverageProbability finiteLayer right := by
  unfold taskCoverageProbability
  apply div_le_div_of_nonneg_right
  · exact_mod_cast Nat.pow_le_pow_right (by decide : 0 < 2) ordered
  · positivity

/-- The unnormalized hypothesis weight obtained from task coverage. -/
def weaknessWeight (hypothesis : finiteLayer.Statement) : ℕ :=
  2 ^ finiteLayer.weakness hypothesis

/-- Total weight of all hypotheses in the finite language. -/
def weaknessNormalizer : ℕ :=
  (language finiteLayer).sum (weaknessWeight finiteLayer)

theorem weaknessWeight_pos (hypothesis : finiteLayer.Statement) :
    0 < weaknessWeight finiteLayer hypothesis := by
  simp [weaknessWeight]

theorem language_nonempty [Nonempty World] : (language finiteLayer).Nonempty := by
  refine ⟨⟨∅, ?_⟩, ?_⟩
  · rw [Mettapedia.Enactive.Finite.Layer.mem_statements]
    exact ⟨Finset.empty_subset _, ⟨Classical.choice inferInstance, by simp [Realizes]⟩⟩
  · simp [language]

theorem weaknessNormalizer_pos [Nonempty World] :
    0 < weaknessNormalizer finiteLayer := by
  obtain ⟨hypothesis, member⟩ := language_nonempty finiteLayer
  exact Finset.sum_pos' (fun statement _ => Nat.zero_le _)
    ⟨hypothesis, member, weaknessWeight_pos finiteLayer hypothesis⟩

/-- A genuine finite probability distribution over hypotheses, obtained by
normalizing Bennett's task-coverage weights over `L_v`. -/
def normalizedWeaknessPrior (hypothesis : finiteLayer.Statement) : ℚ :=
  (weaknessWeight finiteLayer hypothesis : ℚ) /
    weaknessNormalizer finiteLayer

theorem normalizedWeaknessPrior_nonneg (hypothesis : finiteLayer.Statement) :
    0 ≤ normalizedWeaknessPrior finiteLayer hypothesis := by
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- The corrected hypothesis prior is exactly normalized. -/
theorem sum_normalizedWeaknessPrior [Nonempty World] :
    ∑ hypothesis ∈ language finiteLayer,
        normalizedWeaknessPrior finiteLayer hypothesis = 1 := by
  simp_rw [normalizedWeaknessPrior]
  rw [← Finset.sum_div]
  change ((∑ hypothesis ∈ language finiteLayer,
      (weaknessWeight finiteLayer hypothesis : ℚ)) /
        (weaknessNormalizer finiteLayer : ℚ)) = 1
  rw [show (∑ hypothesis ∈ language finiteLayer,
      (weaknessWeight finiteLayer hypothesis : ℚ)) =
        (weaknessNormalizer finiteLayer : ℚ) by
      simp [weaknessNormalizer]]
  exact div_self (by exact_mod_cast (ne_of_gt (weaknessNormalizer_pos finiteLayer)))

/-- Normalization preserves and reflects the Bennett weakness ordering. -/
theorem normalizedWeaknessPrior_le_iff
    [Nonempty World]
    (left right : finiteLayer.Statement) :
    normalizedWeaknessPrior finiteLayer left ≤
        normalizedWeaknessPrior finiteLayer right ↔
      finiteLayer.weakness left ≤ finiteLayer.weakness right := by
  unfold normalizedWeaknessPrior weaknessWeight
  rw [div_le_div_iff_of_pos_right]
  · exact_mod_cast Nat.pow_le_pow_iff_right (by decide : 1 < 2)
  · exact_mod_cast weaknessNormalizer_pos finiteLayer

end Layer

/-! ## Positive and negative controls -/

namespace Canary

open Mettapedia.Enactive.Finite.Canary

theorem bool_language_card : (Layer.language boolLayer).card = 6 := by
  decide

/-- The unconstrained Boolean statement covers every task outcome, so its
task-coverage event has probability one. -/
theorem emptyStatement_taskCoverageProbability :
    Layer.taskCoverageProbability boolLayer emptyStatement = 1 := by
  rw [Layer.taskCoverageProbability, emptyStatement_weakness,
    bool_language_card]
  norm_num

/-- A true-only statement covers only one sixteenth of the Boolean task
sample space. -/
theorem trueStatement_taskCoverageProbability :
    Layer.taskCoverageProbability boolLayer trueStatement = 1 / 16 := by
  rw [Layer.taskCoverageProbability, trueStatement_weakness,
    bool_language_card]
  norm_num

/-- Negative normalization control: the published task-coverage scores are
not a probability distribution over hypotheses.  Already two hypotheses have
total mass greater than one because their favorable task events overlap. -/
theorem raw_taskCoverageScores_not_hypothesis_distribution :
    Layer.taskCoverageProbability boolLayer emptyStatement +
        Layer.taskCoverageProbability boolLayer trueStatement ≠ 1 := by
  rw [emptyStatement_taskCoverageProbability,
    trueStatement_taskCoverageProbability]
  norm_num

/-- Positive normalization control: the corrected prior sums to one over the
entire finite Boolean language. -/
theorem normalized_bool_prior_sums_to_one :
    ∑ hypothesis ∈ Layer.language boolLayer,
        Layer.normalizedWeaknessPrior boolLayer hypothesis = 1 :=
  Layer.sum_normalizedWeaknessPrior boolLayer

end Canary

#print axioms Layer.taskCoverageProbability_eq_card_ratio
#print axioms Layer.taskCoverageProbability_mono
#print axioms Layer.sum_normalizedWeaknessPrior
#print axioms Layer.normalizedWeaknessPrior_le_iff
#print axioms Canary.raw_taskCoverageScores_not_hypothesis_distribution

end Mettapedia.UniversalAI.WeaknessPrior
