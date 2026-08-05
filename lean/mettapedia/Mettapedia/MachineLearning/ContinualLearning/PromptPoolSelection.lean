import Mathlib

/-!
# Finite prompt-pool selection and frequency diversification

Wang et al., *Learning to Prompt for Continual Learning* (CVPR 2022,
arXiv:2112.08654), select `N` distinct prompt keys by minimizing the sum of
their query--key matching costs (Equation 3).  During training, their optional
task-boundary variant multiplies each matching cost by the prompt's historical
selection frequency (Equation 4).

This file isolates the exact finite optimization problem.  For a feasible
fixed-cardinality selection, global minimum total cost is equivalent to a
pairwise boundary condition: every selected prompt costs no more than every
unselected prompt in the pool.  The reverse implication is proved by pairing
the two equal-cardinality set differences, so ties and arbitrary finite prompt
types are covered.

Uniform positive frequency preserves every minimizer.  Nonuniform frequency
does not: a two-prompt fixture uses strictly positive frequencies to reverse
the unique raw-cost selection.  Thus Equation 4 is a genuine training-time
change of query policy, not merely a harmless rescaling of Equation 3.

The prompt tensors, concatenation in Equation 2, learned query/key maps,
surrogate loss in Equation 5, and empirical continual-learning claims are
outside this finite selection theorem.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

namespace PromptPoolSelection

open scoped BigOperators

variable {Prompt : Type*}

/-! ## Source-shaped finite selection problem -/

/-- A selection is feasible when it contains exactly `count` distinct members
of the declared prompt pool. -/
def FeasibleSelection
    [DecidableEq Prompt]
    (pool : Finset Prompt)
    (count : ℕ)
    (selection : Finset Prompt) : Prop :=
  selection ⊆ pool ∧ selection.card = count

/-- Total query--key matching cost of a finite prompt selection. -/
def selectionCost
    (cost : Prompt → ℝ)
    (selection : Finset Prompt) : ℝ :=
  selection.sum cost

/-- Global minimum-cost selection among all feasible selections of the same
declared cardinality. -/
def MinimizesSelectionCost
    [DecidableEq Prompt]
    (pool : Finset Prompt)
    (count : ℕ)
    (cost : Prompt → ℝ)
    (selection : Finset Prompt) : Prop :=
  FeasibleSelection pool count selection ∧
    ∀ alternative, FeasibleSelection pool count alternative →
      selectionCost cost selection ≤ selectionCost cost alternative

/-- Pairwise top-`N` boundary condition, with ties allowed. -/
def NoCrossBoundaryInversion
    [DecidableEq Prompt]
    (pool : Finset Prompt)
    (cost : Prompt → ℝ)
    (selection : Finset Prompt) : Prop :=
  ∀ selected ∈ selection, ∀ rejected ∈ pool, rejected ∉ selection →
    cost selected ≤ cost rejected

/-- A global minimum cannot contain a prompt that is more costly than a
rejected prompt: swapping the pair would strictly improve the selection. -/
theorem minimizer_noCrossBoundaryInversion
    [DecidableEq Prompt]
    {pool selection : Finset Prompt}
    {count : ℕ}
    {cost : Prompt → ℝ}
    (minimum : MinimizesSelectionCost pool count cost selection) :
    NoCrossBoundaryInversion pool cost selection := by
  intro selected selected_mem rejected rejected_pool rejected_not_selected
  let alternative := insert rejected (selection.erase selected)
  have rejected_not_erased : rejected ∉ selection.erase selected := by
    intro rejected_erased
    exact rejected_not_selected (Finset.mem_of_mem_erase rejected_erased)
  have alternative_subset : alternative ⊆ pool := by
    intro prompt prompt_mem
    rcases Finset.mem_insert.mp prompt_mem with rfl | prompt_erased
    · exact rejected_pool
    · exact minimum.1.1 (Finset.mem_of_mem_erase prompt_erased)
  have alternative_card : alternative.card = count := by
    dsimp [alternative]
    rw [Finset.card_insert_of_notMem rejected_not_erased]
    exact
      (Finset.card_erase_add_one selected_mem).trans minimum.1.2
  have cost_le :=
    minimum.2 alternative ⟨alternative_subset, alternative_card⟩
  have selection_sum :
      selection.sum cost =
        (selection.erase selected).sum cost + cost selected := by
    rw [Finset.sum_erase_add _ _ selected_mem]
  have alternative_sum :
      alternative.sum cost =
        cost rejected + (selection.erase selected).sum cost := by
    dsimp [alternative]
    rw [Finset.sum_insert rejected_not_erased]
  dsimp [selectionCost] at cost_le
  rw [selection_sum, alternative_sum] at cost_le
  linarith

/-- Conversely, the pairwise boundary condition is sufficient for global
minimum total cost at fixed cardinality.  The proof pairs every selected-only
prompt with one alternative-only prompt. -/
theorem noCrossBoundaryInversion_minimizer
    [DecidableEq Prompt]
    {pool selection : Finset Prompt}
    {count : ℕ}
    {cost : Prompt → ℝ}
    (feasible : FeasibleSelection pool count selection)
    (no_inversion : NoCrossBoundaryInversion pool cost selection) :
    MinimizesSelectionCost pool count cost selection := by
  refine ⟨feasible, ?_⟩
  intro alternative alternative_feasible
  let selected_only : Finset Prompt := selection \ alternative
  let alternative_only : Finset Prompt := alternative \ selection
  have difference_card :
      selected_only.card = alternative_only.card := by
    dsimp [selected_only, alternative_only]
    exact Finset.card_sdiff_comm
      (feasible.2.trans alternative_feasible.2.symm)
  let pairing :
      {prompt // prompt ∈ selected_only} ≃
        {prompt // prompt ∈ alternative_only} :=
    Fintype.equivOfCardEq (by simpa using difference_card)
  have paired_cost :
      ∀ prompt : {prompt // prompt ∈ selected_only},
        cost prompt.1 ≤ cost (pairing prompt).1 := by
    intro prompt
    have selected_mem : prompt.1 ∈ selection :=
      (Finset.mem_sdiff.mp prompt.2).1
    have alternative_mem : (pairing prompt).1 ∈ alternative :=
      (Finset.mem_sdiff.mp (pairing prompt).2).1
    have not_selected : (pairing prompt).1 ∉ selection :=
      (Finset.mem_sdiff.mp (pairing prompt).2).2
    exact no_inversion prompt.1 selected_mem (pairing prompt).1
      (alternative_feasible.1 alternative_mem) not_selected
  have difference_cost :
      selected_only.sum cost ≤ alternative_only.sum cost := by
    have selected_subtype_sum :
        selected_only.sum cost =
          ∑ prompt : {prompt // prompt ∈ selected_only}, cost prompt.1 := by
      exact (Finset.sum_coe_sort selected_only cost).symm
    have alternative_subtype_sum :
        alternative_only.sum cost =
          ∑ prompt : {prompt // prompt ∈ alternative_only}, cost prompt.1 := by
      exact (Finset.sum_coe_sort alternative_only cost).symm
    rw [selected_subtype_sum, alternative_subtype_sum]
    calc
      (∑ prompt : {prompt // prompt ∈ selected_only}, cost prompt.1) ≤
          ∑ prompt : {prompt // prompt ∈ selected_only},
            cost (pairing prompt).1 := by
        exact Finset.sum_le_sum fun prompt _ => paired_cost prompt
      _ = ∑ prompt : {prompt // prompt ∈ alternative_only},
          cost prompt.1 := by
        exact Equiv.sum_comp pairing
          (fun prompt : {prompt // prompt ∈ alternative_only} =>
            cost prompt.1)
  have selection_sum :
      selection.sum cost =
        selected_only.sum cost + (selection ∩ alternative).sum cost := by
    have union_sum :=
      Finset.sum_union (f := cost)
        (Finset.disjoint_sdiff_inter selection alternative)
    change
      (selection \ alternative ∪ selection ∩ alternative).sum cost = _
        at union_sum
    rw [Finset.sdiff_union_inter selection alternative] at union_sum
    simpa [selected_only] using union_sum
  have alternative_sum :
      alternative.sum cost =
        alternative_only.sum cost + (selection ∩ alternative).sum cost := by
    have union_sum :=
      Finset.sum_union (f := cost)
        (Finset.disjoint_sdiff_inter alternative selection)
    change
      (alternative \ selection ∪ alternative ∩ selection).sum cost = _
        at union_sum
    rw [Finset.sdiff_union_inter alternative selection] at union_sum
    simpa [alternative_only, Finset.inter_comm] using union_sum
  dsimp [selectionCost]
  rw [selection_sum, alternative_sum]
  linarith

/-- Exact top-`N` characterization for a declared feasible selection. -/
theorem minimizesSelectionCost_iff_noCrossBoundaryInversion
    [DecidableEq Prompt]
    {pool selection : Finset Prompt}
    {count : ℕ}
    {cost : Prompt → ℝ}
    (feasible : FeasibleSelection pool count selection) :
    MinimizesSelectionCost pool count cost selection ↔
      NoCrossBoundaryInversion pool cost selection := by
  constructor
  · exact minimizer_noCrossBoundaryInversion
  · exact noCrossBoundaryInversion_minimizer feasible

/-! ## Frequency-weighted training query -/

/-- Equation 4's multiplicative historical-frequency modification. -/
def frequencyWeightedCost
    (rawCost frequency : Prompt → ℝ) :
    Prompt → ℝ :=
  fun prompt => rawCost prompt * frequency prompt

@[simp] theorem frequencyWeightedCost_one
    (rawCost : Prompt → ℝ) :
    frequencyWeightedCost rawCost (fun _ => 1) = rawCost := by
  funext prompt
  simp [frequencyWeightedCost]

/-- Nonnegative matching costs remain nonnegative under valid nonnegative
historical frequencies. -/
theorem frequencyWeightedCost_nonnegative_of_nonnegative
    {pool : Finset Prompt}
    {rawCost frequency : Prompt → ℝ}
    (raw_nonnegative : ∀ prompt ∈ pool, 0 ≤ rawCost prompt)
    (frequency_nonnegative : ∀ prompt ∈ pool, 0 ≤ frequency prompt) :
    ∀ prompt ∈ pool,
      0 ≤ frequencyWeightedCost rawCost frequency prompt := by
  intro prompt prompt_mem
  exact mul_nonneg
    (raw_nonnegative prompt prompt_mem)
    (frequency_nonnegative prompt prompt_mem)

/-- A uniform frequency is a scalar multiplier of the whole selection cost. -/
theorem selectionCost_frequencyWeightedCost_uniform
    (rawCost : Prompt → ℝ)
    (frequency : ℝ)
    (selection : Finset Prompt) :
    selectionCost
        (frequencyWeightedCost rawCost (fun _ => frequency)) selection =
      frequency * selectionCost rawCost selection := by
  simp only [selectionCost, frequencyWeightedCost]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro prompt _
  ring

/-- Multiplication of every prompt cost by the same positive scale preserves
the complete set of minimizers. -/
theorem minimizesSelectionCost_positive_scale_iff
    [DecidableEq Prompt]
    {pool selection : Finset Prompt}
    {count : ℕ}
    {cost : Prompt → ℝ}
    {scale : ℝ}
    (scale_pos : 0 < scale) :
    MinimizesSelectionCost pool count
        (fun prompt => scale * cost prompt) selection ↔
      MinimizesSelectionCost pool count cost selection := by
  constructor
  · intro scaled_minimum
    refine ⟨scaled_minimum.1, ?_⟩
    intro alternative alternative_feasible
    have scaled_inequality :
        scale * selectionCost cost selection ≤
          scale * selectionCost cost alternative := by
      simpa only [selectionCost, Finset.mul_sum] using
        scaled_minimum.2 alternative alternative_feasible
    exact le_of_mul_le_mul_left scaled_inequality scale_pos
  · intro minimum
    refine ⟨minimum.1, ?_⟩
    intro alternative alternative_feasible
    have cost_inequality :=
      minimum.2 alternative alternative_feasible
    have scaled_inequality :=
      mul_le_mul_of_nonneg_left cost_inequality scale_pos.le
    simpa only [selectionCost, Finset.mul_sum] using scaled_inequality

/-- Equation 4 recovers exactly the Equation 3 minimizers when every prompt
has the same strictly positive historical frequency. -/
theorem minimizesSelectionCost_uniformFrequency_iff
    [DecidableEq Prompt]
    {pool selection : Finset Prompt}
    {count : ℕ}
    {rawCost : Prompt → ℝ}
    {frequency : ℝ}
    (frequency_pos : 0 < frequency) :
    MinimizesSelectionCost pool count
        (frequencyWeightedCost rawCost (fun _ => frequency)) selection ↔
      MinimizesSelectionCost pool count rawCost selection := by
  have cost_identity :
      frequencyWeightedCost rawCost (fun _ => frequency) =
        fun prompt => frequency * rawCost prompt := by
    funext prompt
    simp only [frequencyWeightedCost]
    ring
  rw [cost_identity]
  exact minimizesSelectionCost_positive_scale_iff frequency_pos

/-! ## Executable strict-diversification boundary -/

abbrev TwoPrompts := Fin 2

def twoPromptPool : Finset TwoPrompts :=
  Finset.univ

def firstPrompt : Finset TwoPrompts :=
  {0}

def secondPrompt : Finset TwoPrompts :=
  {1}

/-- Prompt zero is the unique lower raw query cost. -/
def rawQueryCost (prompt : TwoPrompts) : ℝ :=
  prompt.1 + 1

/-- Both frequencies are positive, but prompt zero has been selected three
times as often as prompt one. -/
def positiveReuseFrequency (prompt : TwoPrompts) : ℝ :=
  if prompt = 0 then 3 else 1

theorem firstPrompt_feasible :
    FeasibleSelection twoPromptPool 1 firstPrompt := by
  simp [FeasibleSelection, twoPromptPool, firstPrompt]

theorem secondPrompt_feasible :
    FeasibleSelection twoPromptPool 1 secondPrompt := by
  simp [FeasibleSelection, twoPromptPool, secondPrompt]

/-- Equation 3 chooses prompt zero in the two-prompt fixture. -/
theorem firstPrompt_raw_minimizer :
    MinimizesSelectionCost twoPromptPool 1 rawQueryCost firstPrompt := by
  apply noCrossBoundaryInversion_minimizer firstPrompt_feasible
  intro selected selected_mem rejected _ rejected_not_selected
  fin_cases selected <;> fin_cases rejected <;>
    simp_all [firstPrompt, rawQueryCost]

/-- Equation 4 instead chooses prompt one, although both historical
frequencies are strictly positive. -/
theorem secondPrompt_positiveFrequency_minimizer :
    MinimizesSelectionCost twoPromptPool 1
      (frequencyWeightedCost rawQueryCost positiveReuseFrequency)
      secondPrompt := by
  apply noCrossBoundaryInversion_minimizer secondPrompt_feasible
  intro selected selected_mem rejected _ rejected_not_selected
  fin_cases selected <;> fin_cases rejected <;>
    simp_all [secondPrompt, frequencyWeightedCost, rawQueryCost,
      positiveReuseFrequency]
  norm_num

/-- The raw-cost winner is not even tied after positive nonuniform frequency
weighting; the policy has genuinely changed. -/
theorem firstPrompt_not_positiveFrequency_minimizer :
    ¬ MinimizesSelectionCost twoPromptPool 1
      (frequencyWeightedCost rawQueryCost positiveReuseFrequency)
      firstPrompt := by
  intro purported_minimum
  have wrong_inequality :=
    purported_minimum.2 secondPrompt secondPrompt_feasible
  norm_num [selectionCost, firstPrompt, secondPrompt, frequencyWeightedCost,
    rawQueryCost, positiveReuseFrequency] at wrong_inequality

/-- The strict flip does not exploit a zero or negative historical
frequency. -/
theorem positiveReuseFrequency_positive :
    ∀ prompt ∈ twoPromptPool, 0 < positiveReuseFrequency prompt := by
  intro prompt _
  fin_cases prompt <;> norm_num [positiveReuseFrequency]

#print axioms minimizer_noCrossBoundaryInversion
#print axioms noCrossBoundaryInversion_minimizer
#print axioms minimizesSelectionCost_iff_noCrossBoundaryInversion
#print axioms frequencyWeightedCost_nonnegative_of_nonnegative
#print axioms minimizesSelectionCost_positive_scale_iff
#print axioms minimizesSelectionCost_uniformFrequency_iff
#print axioms firstPrompt_raw_minimizer
#print axioms secondPrompt_positiveFrequency_minimizer
#print axioms firstPrompt_not_positiveFrequency_minimizer
#print axioms positiveReuseFrequency_positive

end PromptPoolSelection

end Mettapedia.MachineLearning.ContinualLearning
