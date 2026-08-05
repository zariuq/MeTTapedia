import Mettapedia.MachineLearning.NeuralNetworks.TwoTimescaleAdaptation.Attention
import Mettapedia.MachineLearning.NeuralNetworks.Architecture.RoutingExpansion

/-!
# Prefix-prompt attention and its exact preservation boundary

Wang et al., *DualPrompt: Complementary Prompting for Rehearsal-free
Continual Learning* (ECCV 2022, arXiv:2204.04799), distinguish prompt tuning
from prefix tuning in Equations 4--5.  Prompt tuning prepends prompts to the
query, key, and value sequences, so prompt positions also become output query
positions.  Prefix tuning prepends prompts only to keys and values, leaving
the number of output query positions unchanged.

This file isolates one scalar coordinate of one attention head.  Appending a
nonempty key--value prefix changes the token-only attention output by exactly
the prefix softmax-mass fraction times the difference between the prefix-only
and token-only outputs.  Consequently, a nonempty prefix preserves the
original token output exactly if and only if those two independently
normalized outputs agree.  Positive and neutral fixtures exhibit both sides
of this boundary.

The source's learned general and expert prompts, task-key matching, prompt
placement across transformer layers, and empirical rehearsal-free
continual-learning claims are outside this scalar attention theorem.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

namespace DualPromptAttention

open Mettapedia.MachineLearning.NeuralNetworks.TwoTimescaleAdaptation
open Mettapedia.MachineLearning.NeuralNetworks.Architecture

/-! ## Positive softmax mass -/

/-- Every finite scalar softmax context has nonnegative unnormalized mass. -/
theorem softmaxMass_nonnegative (context : List (ℝ × ℝ)) :
    0 ≤ softmaxMass context := by
  induction context with
  | nil => simp [softmaxMass]
  | cons head tail induction_hypothesis =>
      simp only [softmaxMass, List.map_cons, List.sum_cons]
      exact add_nonneg (Real.exp_pos head.1).le induction_hypothesis

/-- Every nonempty finite scalar softmax context has strictly positive mass. -/
theorem softmaxMass_positive_of_nonempty
    {context : List (ℝ × ℝ)}
    (nonempty : context ≠ []) :
    0 < softmaxMass context := by
  cases context with
  | nil => exact False.elim (nonempty rfl)
  | cons head tail =>
      simp only [softmaxMass, List.map_cons, List.sum_cons]
      exact add_pos_of_pos_of_nonneg
        (Real.exp_pos head.1) (softmaxMass_nonnegative tail)

/-! ## Exact prefix-attention displacement -/

/-- Exact change caused by prepending a nonempty scalar key--value prefix.
The prefactor is the prefix's share of the combined unnormalized softmax
mass. -/
theorem scalarPrefixAttention_sub_tokenAttention
    (prompt tokens : List (ℝ × ℝ))
    (prompt_nonempty : prompt ≠ [])
    (tokens_nonempty : tokens ≠ []) :
    scalarSoftmaxAttention (prompt ++ tokens) -
        scalarSoftmaxAttention tokens =
      softmaxMass prompt *
          (scalarSoftmaxAttention prompt -
            scalarSoftmaxAttention tokens) /
        (softmaxMass prompt + softmaxMass tokens) := by
  have prompt_positive :
      0 < softmaxMass prompt :=
    softmaxMass_positive_of_nonempty prompt_nonempty
  have tokens_positive :
      0 < softmaxMass tokens :=
    softmaxMass_positive_of_nonempty tokens_nonempty
  rw [scalarSoftmaxAttention_append prompt tokens
    prompt_positive.ne' tokens_positive.ne'
    (add_pos prompt_positive tokens_positive).ne']
  have displacement :=
    expandedRouteReadout_sub_oldValue
      (oldMass := softmaxMass tokens)
      (newMass := softmaxMass prompt)
      (oldValue := scalarSoftmaxAttention tokens)
      (newValue := scalarSoftmaxAttention prompt)
      (add_pos tokens_positive prompt_positive).ne'
  simpa [normalizedContextMerge, expandedRouteReadout, add_comm] using
    displacement

/-- Exact preservation boundary for a nonempty prefix: the token output is
unchanged precisely when the separately normalized prefix and token outputs
already agree. -/
theorem scalarPrefixAttention_eq_tokenAttention_iff
    (prompt tokens : List (ℝ × ℝ))
    (prompt_nonempty : prompt ≠ [])
    (tokens_nonempty : tokens ≠ []) :
    scalarSoftmaxAttention (prompt ++ tokens) =
        scalarSoftmaxAttention tokens ↔
      scalarSoftmaxAttention prompt =
        scalarSoftmaxAttention tokens := by
  have prompt_positive :
      0 < softmaxMass prompt :=
    softmaxMass_positive_of_nonempty prompt_nonempty
  have tokens_positive :
      0 < softmaxMass tokens :=
    softmaxMass_positive_of_nonempty tokens_nonempty
  rw [scalarSoftmaxAttention_append prompt tokens
    prompt_positive.ne' tokens_positive.ne'
    (add_pos prompt_positive tokens_positive).ne']
  have preservation :=
    expandedRouteReadout_eq_oldValue_iff
      (oldMass := softmaxMass tokens)
      (newMass := softmaxMass prompt)
      (oldValue := scalarSoftmaxAttention tokens)
      (newValue := scalarSoftmaxAttention prompt)
      prompt_positive.ne'
      (add_pos tokens_positive prompt_positive).ne'
  simpa [normalizedContextMerge, expandedRouteReadout, add_comm] using
    preservation

/-! ## Prompt-tuning versus prefix-tuning output arity -/

/-- Prompt tuning prepends prompts to queries as well as keys and values. -/
def promptTuningQueryCount
    (promptTokens inputTokens : ℕ) : ℕ :=
  promptTokens + inputTokens

/-- Prefix tuning prepends prompts only to keys and values. -/
def prefixTuningQueryCount
    (_promptTokens inputTokens : ℕ) : ℕ :=
  inputTokens

/-- Prompt tuning and prefix tuning have equal output-query counts exactly
at the zero-prompt boundary. -/
theorem promptTuningQueryCount_eq_prefixTuningQueryCount_iff
    (promptTokens inputTokens : ℕ) :
    promptTuningQueryCount promptTokens inputTokens =
        prefixTuningQueryCount promptTokens inputTokens ↔
      promptTokens = 0 := by
  simp [promptTuningQueryCount, prefixTuningQueryCount]

/-- Every positive prompt length makes prompt tuning expose strictly more
output-query positions than prefix tuning. -/
theorem prefixTuning_preserves_queryCount_promptTuning_increases
    {promptTokens inputTokens : ℕ}
    (positive : 0 < promptTokens) :
    prefixTuningQueryCount promptTokens inputTokens <
      promptTuningQueryCount promptTokens inputTokens := by
  simp only [prefixTuningQueryCount, promptTuningQueryCount]
  omega

/-! ## Executable boundaries -/

/-- A prefix whose independently normalized value differs from the token
value strictly changes the resulting token output. -/
theorem prefix_changes :
    scalarSoftmaxAttention ([(0, 3)] ++ [(0, 1)]) = 2 ∧
      scalarSoftmaxAttention [(0, 1)] = 1 ∧
      scalarSoftmaxAttention ([(0, 3)] ++ [(0, 1)]) ≠
        scalarSoftmaxAttention [(0, 1)] := by
  norm_num [scalarSoftmaxAttention, softmaxMass, softmaxNumerator]

/-- A nonempty prefix can be exactly neutral when its independently
normalized value equals the token-only output. -/
theorem prefix_neutral :
    scalarSoftmaxAttention ([(0, 1)] ++ [(0, 1)]) =
      scalarSoftmaxAttention [(0, 1)] := by
  norm_num [scalarSoftmaxAttention, softmaxMass, softmaxNumerator]

end DualPromptAttention

end Mettapedia.MachineLearning.ContinualLearning
