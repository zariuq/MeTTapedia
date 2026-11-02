import Mettapedia.Computability.KolmogorovComplexity.FeatureBDecomposition
import Mettapedia.Computability.KolmogorovComplexity.FeatureCompressionChain
import Mettapedia.Computability.KolmogorovComplexity.FeatureRationalScheme
import Mathlib.Data.Nat.Dist

/-!
# Incremental information and orthogonality for shortest b-features

Each step retains minimum b-programs and its actual bounded residual. The
uniform information budget is proved from these programs, not assumed as a
chain field. Geometric successful-step bounds reuse the ordinary BChain owner.
-/

set_option autoImplicit false

namespace KolmogorovComplexity.FeatureTheory

open ConditionalInformationTransport

inductive ShortestBChain (U : ConditionalAlgorithm) (factor : ℝ) : BinString → List BinString → BinString → Prop
  | nil (source) : ShortestBChain U factor source [] source
  | cons {source residual final feature descriptive features}
      (minimumFeature : ShortestBFeature U factor feature source)
      (minimumMap : ShortestBDescriptiveMap U factor feature descriptive source)
      (extracts : residual ∈ U descriptive source)
      (rest : ShortestBChain U factor residual features final) :
      ShortestBChain U factor source (feature :: features) final

theorem ShortestBChain.toBChain {U : ConditionalAlgorithm} {factor : ℝ}
    {source final : BinString} {features : List BinString}
    (chain : ShortestBChain U factor source features final) : BChain U factor source features final := by
  induction chain with
  | nil source => exact .nil source
  | cons _ minimumMap extracts _ ih =>
      obtain ⟨reconstructs, smaller, ratio, _length⟩ := shortest_b_descriptive_actual_output minimumMap extracts
      exact .cons extracts reconstructs smaller ratio ih

theorem ShortestBChain.reconstruct {U : ConditionalAlgorithm} {factor : ℝ}
    {source final : BinString} {features : List BinString}
    (chain : ShortestBChain U factor source features final) :
    source ∈ restoreFeatures U features final := by
  induction chain with
  | nil source => simp [restoreFeatures]
  | cons _ minimumMap extracts _ ih =>
      exact Part.mem_bind ih (shortest_b_descriptive_actual_output minimumMap extracts).1

theorem RationalScheme.toShortestBChain {U : ConditionalAlgorithm} {numerator denominator cutoff : Nat}
    {source final : BinString} {features : List BinString}
    (scheme : RationalScheme U numerator denominator cutoff source features final) :
    ShortestBChain U (rationalFactor numerator denominator) source features final := by
  induction scheme with
  | stop_small source _ => exact .nil source
  | stop_incompressible source _ => exact .nil source
  | cons _ _ minimumFeature minimumMap extracts _ ih =>
      exact .cons minimumFeature minimumMap extracts ih

theorem ShortestBChain.residual_le {U : ConditionalAlgorithm} {factor : ℝ}
    {source final : BinString} {features : List BinString}
    (chain : ShortestBChain U factor source features final) : final.length ≤ source.length :=
  le_trans (Nat.le_add_left final.length features.length) chain.toBChain.length_bound

theorem ShortestBChain.split {U : ConditionalAlgorithm} {factor : ℝ}
    {source final : BinString} {pre suffix : List BinString}
    (chain : ShortestBChain U factor source (pre ++ suffix) final) :
    ∃ intermediate, ShortestBChain U factor source pre intermediate ∧
      ShortestBChain U factor intermediate suffix final := by
  induction pre generalizing source with
  | nil => exact ⟨source, .nil source, chain⟩
  | cons first rest ih =>
      cases chain with
      | cons minimumFeature minimumMap extracts later =>
          obtain ⟨intermediate, before, after⟩ := ih later
          exact ⟨intermediate, .cons minimumFeature minimumMap extracts before, after⟩

theorem ShortestBChain.feature_length_le {U : ConditionalAlgorithm} {factor : ℝ}
    {source final feature : BinString} {pre suffix : List BinString}
    (chain : ShortestBChain U factor source (pre ++ feature :: suffix) final) :
    feature.length ≤ source.length := by
  obtain ⟨intermediate, before, after⟩ := chain.split
  have priorLength := before.residual_le
  cases after with
  | cons _ minimumMap extracts _ =>
      have smaller := (shortest_b_descriptive_actual_output minimumMap extracts).2.1
      omega

/-- IC Lemma 3.5's b-version of Theorem 3.6. The budget constant is fixed
before the factor, the source and the complete shortest chain. -/
theorem incremental_b_information_bound (U : ConditionalAlgorithm) (V : ConditionalPrefixFreeMachine)
    (universal : IsUniversalConditional U) (effective : Partrec₂ U) (reference : IsReferenceMachine V)
    (chainRule : StrongConditionalChainRule V) (simulations : ReferenceMachineSimulations V) :
    ∃ overhead : Nat, ∀ factor, 1 ≤ factor → ∀ source features final,
      ShortestBChain U factor source features final →
      |((conditionalComplexity V source [] : Int) -
        ((features.map List.length).sum + conditionalComplexity V final []))| ≤
          (features.length * (22 * Nat.log 2 (source.length + 1) + overhead) : Nat) := by
  obtain ⟨overhead, oneStep⟩ := shortest_b_maps_length_partition U V universal effective reference chainRule simulations
  refine ⟨overhead, fun factor large source features final chain => ?_⟩
  induction chain with
  | nil source => simp
  | @cons source residual final feature descriptive features minimumFeature minimumMap extracts _rest ih =>
      have stepBound := oneStep factor large feature descriptive source residual minimumFeature minimumMap extracts
      have smaller := (shortest_b_descriptive_actual_output minimumMap extracts).2.1
      have logarithm := Nat.log_mono_right (b := 2) (show residual.length + 1 ≤ source.length + 1 by omega)
      have larger : features.length * (22 * Nat.log 2 (residual.length + 1) + overhead) ≤
          features.length * (22 * Nat.log 2 (source.length + 1) + overhead) :=
        Nat.mul_le_mul_left _ (by omega)
      have largerInt : (features.length * (22 * Nat.log 2 (residual.length + 1) + overhead) : Int) ≤
          (features.length * (22 * Nat.log 2 (source.length + 1) + overhead) : Int) := by exact_mod_cast larger
      have triangle := abs_add_le
        ((conditionalComplexity V source [] : Int) - (feature.length + conditionalComplexity V residual []))
        ((conditionalComplexity V residual [] : Int) - ((features.map List.length).sum + conditionalComplexity V final []))
      have composed := triangle.trans (add_le_add stepBound (ih.trans largerInt))
      have telescope : ((conditionalComplexity V source [] : Int) - (feature.length + conditionalComplexity V residual [])) +
          ((conditionalComplexity V residual [] : Int) - ((features.map List.length).sum + conditionalComplexity V final [])) =
          (conditionalComplexity V source [] : Int) -
            (feature.length + ((features.map List.length).sum + conditionalComplexity V final [])) := by ring
      rw [telescope] at composed
      simpa only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_mul,
        Nat.cast_one, Nat.cast_ofNat, add_mul, one_mul, add_assoc, add_comm, add_left_comm] using composed

/-- The logarithmic iteration bound and uniform per-step bound give the
paper's squared-logarithmic information overhead. Empty terminal residuals
are included; only the chain itself is required to be nonempty. -/
theorem incremental_b_logarithmic_overhead (U : ConditionalAlgorithm) (V : ConditionalPrefixFreeMachine)
    (universal : IsUniversalConditional U) (effective : Partrec₂ U) (reference : IsReferenceMachine V)
    (chainRule : StrongConditionalChainRule V) (simulations : ReferenceMachineSimulations V) :
    ∃ overhead : Nat, ∀ factor, 1 < factor → ∀ source features final,
      ShortestBChain U factor source features final → features ≠ [] →
      |((conditionalComplexity V source [] : ℝ) -
        ((features.map List.length).sum + conditionalComplexity V final []))| ≤
          (Real.log source.length / Real.log factor + 1) *
            (22 * (Nat.log 2 (source.length + 1) : ℝ) + overhead) := by
  obtain ⟨overhead, bound⟩ := incremental_b_information_bound U V universal effective reference chainRule simulations
  refine ⟨overhead, fun factor greater source features final chain nonempty => ?_⟩
  have information := bound factor greater.le source features final chain
  have informationReal :
      |((conditionalComplexity V source [] : ℝ) -
        ((features.map List.length).sum + conditionalComplexity V final []))| ≤
        (features.length : ℝ) * (22 * (Nat.log 2 (source.length + 1) : ℝ) + overhead) := by
    exact_mod_cast information
  have iterations := chain.toBChain.logarithmic_length greater nonempty
  have nonnegative : 0 ≤ 22 * (Nat.log 2 (source.length + 1) : ℝ) + overhead := by positivity
  exact informationReal.trans (mul_le_mul_of_nonneg_right iterations nonnegative)

theorem later_b_feature_description (U : ConditionalAlgorithm) (V : ConditionalPrefixFreeMachine)
    (universal : IsUniversalConditional U) (effective : Partrec₂ U) (reference : IsReferenceMachine V)
    (chainRule : StrongConditionalChainRule V) (simulations : ReferenceMachineSimulations V) :
    ∃ overhead : Nat, ∀ factor, 1 ≤ factor → ∀ source pre feature suffix final,
      ShortestBChain U factor source (pre ++ feature :: suffix) final →
      conditionalComplexity V feature source ≤
        (pre.length + 1) * (10 * Nat.log 2 (source.length + 1) + overhead) := by
  obtain ⟨featureCost, featureBound⟩ :=
    reference_shortest_b_feature_source_bound U V universal effective reference chainRule simulations
  obtain ⟨residualCost, residualBound⟩ :=
    shortest_b_map_residual_information U V universal effective reference chainRule simulations
  let composeCost := chainRule.constant + simulations.headCondition.compilerPrefix.length +
    simulations.secondOutput.compilerPrefix.length
  refine ⟨featureCost + residualCost + composeCost, fun factor large source pre feature suffix final chain => ?_⟩
  induction pre generalizing source with
  | nil =>
      cases chain with
      | cons minimumFeature _ _ _ =>
          have bounded := featureBound factor large source feature minimumFeature
          simp only [List.length_nil, zero_add, one_mul]
          omega
  | cons first pre ih =>
      cases chain with
      | @cons source residual final first descriptive features minimumFeature minimumMap extracts rest =>
          have remaining := ih residual rest
          have residualInformation := residualBound factor large first descriptive source residual minimumFeature minimumMap extracts
          have composed := conditional_triangle V reference chainRule simulations source residual feature
          have smaller := (shortest_b_descriptive_actual_output minimumMap extracts).2.1
          have logarithm := Nat.log_mono_right (b := 2)
            (show residual.length + 1 ≤ source.length + 1 by omega)
          let budget := 10 * Nat.log 2 (source.length + 1) + featureCost + residualCost + composeCost
          have raised : conditionalComplexity V feature residual ≤ (pre.length + 1) * budget := by
            apply remaining.trans
            exact Nat.mul_le_mul_left _ (by dsimp [budget]; omega)
          have extra : 10 * Nat.log 2 (source.length + 1) + residualCost + composeCost ≤ budget := by
            dsimp [budget]
            omega
          have total : conditionalComplexity V feature source ≤ (pre.length + 1) * budget + budget := by
            dsimp only [composeCost] at extra
            omega
          simpa only [List.length_cons, Nat.succ_eq_add_one, Nat.add_mul, Nat.one_mul,
            budget, Nat.add_assoc] using total

private theorem absorb_step_slack (steps cost slack : Nat) (positive : 1 ≤ steps) :
    steps * cost + slack ≤ steps * (cost + slack) := by
  rw [Nat.mul_add]
  exact Nat.add_le_add_left (by simpa using Nat.mul_le_mul_right slack positive) _

theorem shortest_b_chain_pairwise_information (U : ConditionalAlgorithm) (V : ConditionalPrefixFreeMachine)
    (universal : IsUniversalConditional U) (effective : Partrec₂ U) (reference : IsReferenceMachine V)
    (chainRule : StrongConditionalChainRule V) (simulations : ReferenceMachineSimulations V) :
    ∃ overhead : Nat, ∀ factor, 1 ≤ factor → ∀ source pre first middle second suffix final,
      ShortestBChain U factor source (pre ++ first :: (middle ++ second :: suffix)) final →
      |directedAlgorithmicInformation V first second| ≤
        ((middle.length + 1) * (22 * Nat.log 2 (source.length + 1) + overhead) : Nat) ∧
      |directedAlgorithmicInformation V second first| ≤
        ((middle.length + 1) * (22 * Nat.log 2 (source.length + 1) + overhead) : Nat) := by
  obtain ⟨descriptionCost, descriptionBound⟩ := later_b_feature_description U V universal effective reference chainRule simulations
  obtain ⟨independenceCost, independenceBound⟩ := reference_b_residual_independence U V universal effective reference chainRule simulations
  obtain ⟨dataCost, dataBound⟩ := information_data_processing V reference chainRule simulations
  obtain ⟨symmetryCost, symmetryBound⟩ := information_symmetry_uniform V reference chainRule simulations
  obtain ⟨ignoreCost, ignoreBound⟩ := reference_ignore_condition V reference
  let totalCost := descriptionCost + independenceCost + dataCost + symmetryCost + ignoreCost
  refine ⟨totalCost, fun factor large source pre first middle second suffix final chain => ?_⟩
  obtain ⟨intermediate, before, after⟩ := chain.split
  have intermediateLength := before.residual_le
  cases after with
  | @cons intermediate residual final first descriptive features minimumFeature minimumMap extracts rest =>
      obtain ⟨reconstructs, smaller, ratio, _length⟩ := shortest_b_descriptive_actual_output minimumMap extracts
      have firstLength : first.length ≤ source.length := by omega
      have residualLength : residual.length ≤ source.length := by omega
      have secondLength : second.length ≤ source.length := rest.feature_length_le.trans residualLength
      have firstLog := Nat.log_mono_right (b := 2) (Nat.add_le_add_right firstLength 1)
      have residualLog := Nat.log_mono_right (b := 2) (Nat.add_le_add_right residualLength 1)
      have secondLog := Nat.log_mono_right (b := 2) (Nat.add_le_add_right secondLength 1)
      have independent := independenceBound factor first descriptive intermediate residual minimumFeature extracts reconstructs smaller ratio
      change |directedAlgorithmicInformation V first residual| ≤ _ at independent
      have independentUpper := (abs_le.mp independent).2
      have later := descriptionBound factor large residual middle second suffix final rest
      have laterRaised : conditionalComplexity V second residual ≤
          (middle.length + 1) * (10 * Nat.log 2 (source.length + 1) + descriptionCost) :=
        later.trans (Nat.mul_le_mul_left _ (by omega))
      have processing := dataBound first residual second
      have rawForward : directedAlgorithmicInformation V first second ≤
          ((middle.length + 1) * (10 * Nat.log 2 (source.length + 1) + descriptionCost) +
            (6 * Nat.log 2 (source.length + 1) + independenceCost + dataCost) : Nat) := by omega
      have promoted := absorb_step_slack (middle.length + 1)
        (10 * Nat.log 2 (source.length + 1) + descriptionCost)
        (6 * Nat.log 2 (source.length + 1) + independenceCost + dataCost) (by omega)
      have normalized :
          (10 * Nat.log 2 (source.length + 1) + descriptionCost) +
            (6 * Nat.log 2 (source.length + 1) + independenceCost + dataCost) =
          16 * Nat.log 2 (source.length + 1) + descriptionCost + independenceCost + dataCost := by ring
      rw [normalized] at promoted
      have promotedInt :
          (((middle.length + 1) * (10 * Nat.log 2 (source.length + 1) + descriptionCost) +
            (6 * Nat.log 2 (source.length + 1) + independenceCost + dataCost) : Nat) : Int) ≤
          ((middle.length + 1) *
            (16 * Nat.log 2 (source.length + 1) + descriptionCost + independenceCost + dataCost) : Nat) := by
        exact_mod_cast promoted
      have forward := rawForward.trans promotedInt
      have symmetry := symmetryBound first second
      have symmetricGap :
          |directedAlgorithmicInformation V first second - directedAlgorithmicInformation V second first| ≤
            (4 * Nat.log 2 (source.length + 1) + symmetryCost : Nat) := by omega
      have gap := (abs_le.mp symmetricGap).1
      have reverseRaw : directedAlgorithmicInformation V second first ≤
          ((middle.length + 1) *
            (16 * Nat.log 2 (source.length + 1) + descriptionCost + independenceCost + dataCost) +
            (4 * Nat.log 2 (source.length + 1) + symmetryCost) : Nat) := by omega
      have promotedReverse := absorb_step_slack (middle.length + 1)
        (16 * Nat.log 2 (source.length + 1) + descriptionCost + independenceCost + dataCost)
        (4 * Nat.log 2 (source.length + 1) + symmetryCost) (by omega)
      have normalizedReverse :
          (16 * Nat.log 2 (source.length + 1) + descriptionCost + independenceCost + dataCost) +
            (4 * Nat.log 2 (source.length + 1) + symmetryCost) =
          20 * Nat.log 2 (source.length + 1) + descriptionCost + independenceCost + dataCost + symmetryCost := by ring
      rw [normalizedReverse] at promotedReverse
      have promotedReverseInt :
          (((middle.length + 1) *
            (16 * Nat.log 2 (source.length + 1) + descriptionCost + independenceCost + dataCost) +
            (4 * Nat.log 2 (source.length + 1) + symmetryCost) : Nat) : Int) ≤
          ((middle.length + 1) *
            (20 * Nat.log 2 (source.length + 1) + descriptionCost + independenceCost + dataCost + symmetryCost) : Nat) := by
        exact_mod_cast promotedReverse
      have reverse := reverseRaw.trans promotedReverseInt
      have forwardBudget := Nat.mul_le_mul_left (middle.length + 1)
        (show 16 * Nat.log 2 (source.length + 1) + descriptionCost + independenceCost + dataCost ≤
          22 * Nat.log 2 (source.length + 1) + totalCost by dsimp [totalCost]; omega)
      have reverseBudget := Nat.mul_le_mul_left (middle.length + 1)
        (show 20 * Nat.log 2 (source.length + 1) + descriptionCost + independenceCost + dataCost + symmetryCost ≤
          22 * Nat.log 2 (source.length + 1) + totalCost by dsimp [totalCost]; omega)
      have forwardInt :
          (((middle.length + 1) * (16 * Nat.log 2 (source.length + 1) + descriptionCost + independenceCost + dataCost) : Nat) : Int) ≤
          ((middle.length + 1) * (22 * Nat.log 2 (source.length + 1) + totalCost) : Nat) := by exact_mod_cast forwardBudget
      have reverseInt :
          (((middle.length + 1) * (20 * Nat.log 2 (source.length + 1) + descriptionCost + independenceCost + dataCost + symmetryCost) : Nat) : Int) ≤
          ((middle.length + 1) * (22 * Nat.log 2 (source.length + 1) + totalCost) : Nat) := by exact_mod_cast reverseBudget
      have positiveBudget : ignoreCost ≤ (middle.length + 1) * (22 * Nat.log 2 (source.length + 1) + totalCost) := by
        have amplified := Nat.mul_le_mul_right (22 * Nat.log 2 (source.length + 1) + totalCost)
          (show 1 ≤ middle.length + 1 by omega)
        dsimp only [totalCost] at amplified ⊢
        omega
      have costInt : (ignoreCost : Int) ≤
          ((middle.length + 1) * (22 * Nat.log 2 (source.length + 1) + totalCost) : Nat) := by exact_mod_cast positiveBudget
      have ignoredForward := ignoreBound second first
      have ignoredReverse := ignoreBound first second
      constructor
      · rw [abs_le]
        constructor
        · simp only [directedAlgorithmicInformation, inducedPrefixComplexity]
          omega
        · exact forward.trans forwardInt
      · rw [abs_le]
        constructor
        · simp only [directedAlgorithmicInformation, inducedPrefixComplexity]
          omega
        · exact reverse.trans reverseInt

private theorem split_at_indices {α : Type*} (items : List α) (i j : Nat)
    (hi : i < items.length) (hj : j < items.length) (ordered : i < j) :
    items = items.take i ++ items[i] ::
      ((items.drop (i + 1)).take (j - i - 1) ++ items[j] :: items.drop (j + 1)) := by
  have later : (items.drop (i + 1)).drop (j - i - 1) = items[j] :: items.drop (j + 1) := by
    calc
      (items.drop (i + 1)).drop (j - i - 1) = items.drop j := by
        rw [List.drop_drop]
        congr 1
        omega
      _ = items[j] :: items.drop (j + 1) :=
        (List.cons_getElem_drop_succ (l := items) (n := j) (h := hj)).symm
  have rest : items.drop (i + 1) =
      (items.drop (i + 1)).take (j - i - 1) ++ items[j] :: items.drop (j + 1) := by
    calc
      items.drop (i + 1) = (items.drop (i + 1)).take (j - i - 1) ++
          (items.drop (i + 1)).drop (j - i - 1) := (List.take_append_drop _ _).symm
      _ = _ := by rw [later]
  calc
    items = items.take i ++ items.drop i := (List.take_append_drop _ _).symm
    _ = items.take i ++ items[i] :: items.drop (i + 1) := by
      rw [(List.cons_getElem_drop_succ (l := items) (n := i) (h := hi)).symm]
    _ = _ := congrArg (fun tail => items.take i ++ items[i] :: tail) rest

/-- IC Lemma 3.5's b-version of Theorem 3.5, including both information
directions, all distinct positions and one overhead independent of b. -/
theorem shortest_b_chain_orthogonality (U : ConditionalAlgorithm) (V : ConditionalPrefixFreeMachine)
    (universal : IsUniversalConditional U) (effective : Partrec₂ U) (reference : IsReferenceMachine V)
    (chainRule : StrongConditionalChainRule V) (simulations : ReferenceMachineSimulations V) :
    ∃ overhead : Nat, ∀ factor, 1 ≤ factor → ∀ source features final,
      ShortestBChain U factor source features final →
      ∀ i j (hi : i < features.length) (hj : j < features.length), i ≠ j →
        |directedAlgorithmicInformation V features[i] features[j]| ≤
          (Nat.dist i j * (22 * Nat.log 2 (source.length + 1) + overhead) : Nat) := by
  obtain ⟨overhead, bound⟩ := shortest_b_chain_pairwise_information U V universal effective reference chainRule simulations
  refine ⟨overhead, fun factor large source features final chain i j hi hj different => ?_⟩
  rcases Nat.lt_or_gt_of_ne different with ordered | ordered
  · have decomposition := split_at_indices features i j hi hj ordered
    have rewritten : ShortestBChain U factor source
        (features.take i ++ features[i] :: ((features.drop (i + 1)).take (j - i - 1) ++
          features[j] :: features.drop (j + 1))) final := by rw [← decomposition]; exact chain
    have pair := (bound factor large source _ _ _ _ _ final rewritten).1
    have count : ((features.drop (i + 1)).take (j - i - 1)).length + 1 = j - i := by
      rw [List.length_take, List.length_drop, Nat.min_eq_left (by omega)]
      omega
    simpa only [count, Nat.dist_eq_sub_of_le ordered.le] using pair
  · have decomposition := split_at_indices features j i hj hi ordered
    have rewritten : ShortestBChain U factor source
        (features.take j ++ features[j] :: ((features.drop (j + 1)).take (i - j - 1) ++
          features[i] :: features.drop (i + 1))) final := by rw [← decomposition]; exact chain
    have pair := (bound factor large source _ _ _ _ _ final rewritten).2
    have count : ((features.drop (j + 1)).take (i - j - 1)).length + 1 = i - j := by
      rw [List.length_take, List.length_drop, Nat.min_eq_left (by omega)]
      omega
    simpa only [count, Nat.dist_eq_sub_of_le_right ordered.le] using pair

#print axioms ShortestBChain.toBChain
#print axioms ShortestBChain.reconstruct
#print axioms RationalScheme.toShortestBChain
#print axioms ShortestBChain.residual_le
#print axioms ShortestBChain.split
#print axioms ShortestBChain.feature_length_le
#print axioms incremental_b_information_bound
#print axioms incremental_b_logarithmic_overhead
#print axioms later_b_feature_description
#print axioms shortest_b_chain_pairwise_information
#print axioms shortest_b_chain_orthogonality

end KolmogorovComplexity.FeatureTheory
