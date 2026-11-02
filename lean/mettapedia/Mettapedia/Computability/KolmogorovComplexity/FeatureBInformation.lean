import Mettapedia.Computability.KolmogorovComplexity.BoundedFeature
import Mettapedia.Computability.KolmogorovComplexity.FeatureResidualCap
import Mettapedia.Computability.KolmogorovComplexity.FeatureDecompositionInformation

/-!
# Information bounds for shortest residual-bounded features

The residual constraint is retained when constructing every competitor. In
particular, a minimum b-feature need not be an unrestricted minimum feature.
One constant precedes all factors, sources and decompositions. Real factors
are never executed: their finite natural residual caps are explicit data.
-/

set_option autoImplicit false

namespace KolmogorovComplexity.FeatureTheory

open scoped Classical

theorem reference_b_feature_incompressibility (U : ConditionalAlgorithm)
    (V : ConditionalPrefixFreeMachine) (universal : IsUniversalConditional U)
    (effective : Partrec₂ U) (reference : IsReferenceMachine V) :
    ∃ lower upper : Nat, ∀ factor source feature, ShortestBFeature U factor feature source →
      feature.length ≤ conditionalComplexity V feature [] + lower ∧
      conditionalComplexity V feature [] ≤ feature.length + 2 * Nat.log 2 (feature.length + 1) + upper := by
  obtain ⟨lower, lowerBound⟩ := shortest_b_feature_plain_lower U universal effective
  obtain ⟨translation, translate⟩ := plain_le_reference U V universal reference
  obtain ⟨upper, upperBound⟩ := reference_literal_bound U V universal effective reference
  refine ⟨lower + translation, upper, fun factor source feature minimum => ?_⟩
  have first := lowerBound factor feature source minimum
  have second := translate feature []
  exact ⟨by omega, upperBound feature []⟩

theorem reference_shortest_b_independence (U : ConditionalAlgorithm)
    (V : ConditionalPrefixFreeMachine) (universal : IsUniversalConditional U)
    (effective : Partrec₂ U) (reference : IsReferenceMachine V) :
    ∃ overhead : Nat, ∀ factor feature descriptive source residual,
      ShortestBFeature U factor feature source → residual ∈ U descriptive source →
      source ∈ U feature residual → feature.length + residual.length < source.length →
      factor * residual.length ≤ source.length →
      |((conditionalComplexity V feature [] : Int) - conditionalComplexity V feature residual)| ≤
        (2 * Nat.log 2 (feature.length + 1) + overhead : Nat) := by
  obtain ⟨forward, forwardBound⟩ := reference_b_feature_information U V universal effective reference
  obtain ⟨backward, backwardBound⟩ := reference_ignore_condition V reference
  refine ⟨max forward backward, fun factor feature descriptive source residual minimum extracts reconstructs smaller ratio => ?_⟩
  have first := forwardBound factor feature feature descriptive source residual minimum extracts reconstructs smaller ratio
  have second := backwardBound feature residual
  rw [abs_le]
  constructor <;> omega

/-- The split-description competitor handles the case where the shortest
source description is longer than the permitted residual. Neither the factor
nor the source is part of the compiler constant. -/
theorem reference_shortest_b_feature_source_bound (U : ConditionalAlgorithm)
    (V : ConditionalPrefixFreeMachine) (universal : IsUniversalConditional U)
    (effective : Partrec₂ U) (reference : IsReferenceMachine V)
    (chain : StrongConditionalChainRule V) (simulations : ReferenceMachineSimulations V) :
    ∃ overhead : Nat, ∀ factor, 1 ≤ factor → ∀ source feature,
      ShortestBFeature U factor feature source →
      conditionalComplexity V feature source ≤ 6 * Nat.log 2 (source.length + 1) + overhead := by
  obtain ⟨fixed, works⟩ := exists_universal_feature U universal effective
  obtain ⟨compiler, compiles⟩ := split_description_compiler U universal effective
  obtain ⟨literalCost, literalBound⟩ := reference_literal_bound U V universal effective reference
  obtain ⟨residualCost, residualBound⟩ := reference_residual_description U V effective reference
  obtain ⟨exchangeCost, exchangeBound⟩ := reference_conditional_exchange V reference chain simulations
  obtain ⟨plainCost, plainBound⟩ := plain_le_reference U V universal reference
  let slack := max fixed.length compiler.length
  refine ⟨max (fixed.length + 2 * Nat.log 2 (fixed.length + 1) + literalCost)
    (slack + plainCost + literalCost + residualCost + exchangeCost),
    fun factor large source feature minimum => ?_⟩
  have positive : 0 < factor := lt_of_lt_of_le zero_lt_one large
  obtain ⟨descriptive, residual, extracts, reconstructs, smaller, ratio⟩ := minimum.1
  have residualWidth := (residualCap_iff positive source residual).mpr ratio
  have literal := literalBound feature []
  have rest := residualBound feature residual source reconstructs
  have exchange := exchangeBound source feature
  have sourceBound := plainBound source []
  have featureLog := Nat.log_mono_right (b := 2)
    (show feature.length + 1 ≤ source.length + 1 by omega)
  have residualLog := Nat.log_mono_right (b := 2)
    (show residual.length + 1 ≤ source.length + 1 by omega)
  by_cases margin : plainConditionalComplexity U source [] + slack < source.length
  · by_cases enough : plainConditionalComplexity U source [] ≤ residualCap factor source
    · have fixedMargin : plainConditionalComplexity U source [] + fixed.length < source.length :=
        lt_of_le_of_lt (Nat.add_le_add_left (le_max_left _ _) _) margin
      obtain ⟨step, same, width⟩ := works source fixedMargin
      have admitted : BFeature U factor fixed source := by
        refine ⟨step.descriptiveProgram, step.residual, step.extracts, ?_, ?_, ?_⟩
        · simpa only [same] using step.reconstructs
        · simpa only [same] using step.compresses
        · exact (residualCap_iff positive source _).mp (by simpa only [width] using enough)
      have length := minimum.2 fixed admitted
      have bounded := literalBound feature source
      have logarithm := Nat.log_mono_right (b := 2) (Nat.add_le_add_right length 1)
      omega
    · obtain ⟨description, computes, length⟩ := exists_program_of_plainConditionalComplexity U [] source
        (universalConditional_hasProgram U universal [] source)
      have capWidth : residualCap factor source ≤ description.length := by omega
      have saving : compiler.length + description.length < source.length := by
        have bounded := le_max_right fixed.length compiler.length
        dsimp only [slack] at margin
        omega
      have admitted := split_description_b_feature universal positive compiles computes capWidth saving
      have smallest := minimum.2 _ admitted
      have splitLength := (compiles description source _ computes capWidth).2.1
      have bounded : feature.length + residualCap factor source ≤
          plainConditionalComplexity U source [] + slack := by
        have compilerBound := le_max_right fixed.length compiler.length
        dsimp only [slack]
        omega
      omega
  · omega

/-- IC Lemma 3.5's b-version of the polynomial counting conclusion. -/
theorem shortest_b_feature_polynomial_count (U : ConditionalAlgorithm)
    (V : ConditionalPrefixFreeMachine) (universal : IsUniversalConditional U)
    (effective : Partrec₂ U) (reference : IsReferenceMachine V)
    (chain : StrongConditionalChainRule V) (simulations : ReferenceMachineSimulations V) :
    ∃ coefficient : Nat, ∀ factor, 1 ≤ factor → ∀ source (features : Finset BinString),
      (∀ feature ∈ features, ShortestBFeature U factor feature source) →
      features.card < coefficient * (source.length + 1) ^ 6 := by
  obtain ⟨overhead, bound⟩ := reference_shortest_b_feature_source_bound U V universal effective reference chain simulations
  refine ⟨2 ^ (overhead + 1), fun factor large source features minimum => ?_⟩
  have counted := conditional_output_card_lt V reference source features
    (6 * Nat.log 2 (source.length + 1) + overhead)
    (fun feature member => bound factor large source feature (minimum feature member))
  have powered := Nat.pow_le_pow_left (Nat.pow_log_le_self 2 (Nat.succ_ne_zero source.length)) 6
  have scale : 2 ^ (6 * Nat.log 2 (source.length + 1) + overhead + 1) ≤
      2 ^ (overhead + 1) * (source.length + 1) ^ 6 := by
    rw [Nat.add_assoc, Nat.pow_add, Nat.mul_comm 6, Nat.pow_mul, Nat.mul_comm]
    exact Nat.mul_le_mul_left _ powered
  exact counted.trans_le scale

theorem reference_b_feature_joint_information (U : ConditionalAlgorithm)
    (V : ConditionalPrefixFreeMachine) (universal : IsUniversalConditional U)
    (effective : Partrec₂ U) (reference : IsReferenceMachine V)
    (chain : StrongConditionalChainRule V) (simulations : ReferenceMachineSimulations V) :
    ∃ overhead : Nat, ∀ factor shortest feature descriptive source residual,
      ShortestBFeature U factor shortest source → residual ∈ U descriptive source →
      source ∈ U feature residual → feature.length + residual.length < source.length →
      factor * residual.length ≤ source.length →
      conditionalComplexity V residual [] + conditionalComplexity V feature [] ≤
        conditionalComplexity V (pairCondition residual feature) [] + (feature.length - shortest.length) +
          2 * Nat.log 2 (feature.length + 1) + 2 * Nat.log 2 (residual.length + 1) + overhead := by
  obtain ⟨information, infoBound⟩ := reference_b_feature_information U V universal effective reference
  let headerConstant := 2 * Nat.log 2 (simulations.literal.compilerPrefix.length + 2) + 5
  refine ⟨information + chain.constant + simulations.indexedCondition.compilerPrefix.length + headerConstant + 2,
    fun factor shortest feature descriptive source residual minimum extracts reconstructs smaller ratio => ?_⟩
  have featureBound := infoBound factor shortest feature descriptive source residual minimum extracts reconstructs smaller ratio
  have indexed := remove_complexity_index reference simulations feature residual
  have joint := chain.lower [] residual feature (reference.hasProgram _ _) (reference.hasProgram _ _)
  have header := complexityIndexHeader_le_log simulations.literal
    (show residual.length < residual.length + 1 by omega)
  have shift := log_add_constant_le residual.length 1
  dsimp only [headerConstant]
  omega

theorem reference_b_feature_first_joint_information (U : ConditionalAlgorithm)
    (V : ConditionalPrefixFreeMachine) (universal : IsUniversalConditional U)
    (effective : Partrec₂ U) (reference : IsReferenceMachine V)
    (chain : StrongConditionalChainRule V) (simulations : ReferenceMachineSimulations V) :
    ∃ overhead : Nat, ∀ factor shortest feature descriptive source residual,
      ShortestBFeature U factor shortest source → residual ∈ U descriptive source →
      source ∈ U feature residual → feature.length + residual.length < source.length →
      factor * residual.length ≤ source.length →
      conditionalComplexity V feature [] + conditionalComplexity V residual [] ≤
        conditionalComplexity V (pairCondition feature residual) [] + (feature.length - shortest.length) +
          2 * Nat.log 2 (feature.length + 1) + 2 * Nat.log 2 (residual.length + 1) + overhead := by
  obtain ⟨jointCost, jointBound⟩ := reference_b_feature_joint_information U V universal effective reference chain simulations
  obtain ⟨swapCost, swapBound⟩ := reference_pair_swap V reference
  refine ⟨jointCost + swapCost, fun factor shortest feature descriptive source residual minimum extracts reconstructs smaller ratio => ?_⟩
  have joint := jointBound factor shortest feature descriptive source residual minimum extracts reconstructs smaller ratio
  have swap := swapBound residual feature []
  omega

theorem reference_b_residual_independence (U : ConditionalAlgorithm)
    (V : ConditionalPrefixFreeMachine) (universal : IsUniversalConditional U)
    (effective : Partrec₂ U) (reference : IsReferenceMachine V)
    (chain : StrongConditionalChainRule V) (simulations : ReferenceMachineSimulations V) :
    ∃ overhead : Nat, ∀ factor feature descriptive source residual,
      ShortestBFeature U factor feature source → residual ∈ U descriptive source →
      source ∈ U feature residual → feature.length + residual.length < source.length →
      factor * residual.length ≤ source.length →
      |((conditionalComplexity V residual [] : Int) - conditionalComplexity V residual feature)| ≤
        (2 * Nat.log 2 (feature.length + 1) + 2 * Nat.log 2 (residual.length + 1) + overhead : Nat) := by
  obtain ⟨jointCost, jointBound⟩ := reference_b_feature_joint_information U V universal effective reference chain simulations
  obtain ⟨swapCost, swapBound⟩ := reference_pair_swap V reference
  obtain ⟨ignoreCost, ignoreBound⟩ := reference_ignore_condition V reference
  refine ⟨max (jointCost + swapCost + chain.constant + simulations.headCondition.compilerPrefix.length) ignoreCost,
    fun factor feature descriptive source residual minimum extracts reconstructs smaller ratio => ?_⟩
  have lower := jointBound factor feature feature descriptive source residual minimum extracts reconstructs smaller ratio
  have swap := swapBound residual feature []
  have upper := chain.upper [] feature residual (reference.hasProgram _ _) (reference.hasProgram _ _)
  obtain ⟨program, runs, shortest⟩ := exists_program_of_conditionalComplexity V feature residual (reference.hasProgram _ _)
  have indexed : IsProgram (headConditionMachine V) program
      (chainCondition [] feature (conditionalComplexity V feature [])) residual :=
    headConditionMachine_program runs
  have indexBound := conditionalComplexity_le_simulated_program simulations.headCondition indexed
  rw [shortest] at indexBound
  have ignored := ignoreBound residual feature
  rw [abs_le]
  constructor <;> omega

theorem reference_b_joint_independence (U : ConditionalAlgorithm)
    (V : ConditionalPrefixFreeMachine) (universal : IsUniversalConditional U)
    (effective : Partrec₂ U) (reference : IsReferenceMachine V)
    (chain : StrongConditionalChainRule V) (simulations : ReferenceMachineSimulations V) :
    ∃ overhead : Nat, ∀ factor feature descriptive source residual,
      ShortestBFeature U factor feature source → residual ∈ U descriptive source →
      source ∈ U feature residual → feature.length + residual.length < source.length →
      factor * residual.length ≤ source.length →
      |((conditionalComplexity V (pairCondition feature residual) [] : Int) -
          (conditionalComplexity V feature [] + conditionalComplexity V residual []))| ≤
        (2 * Nat.log 2 (feature.length + 1) + 2 * Nat.log 2 (residual.length + 1) + overhead : Nat) := by
  obtain ⟨jointCost, jointBound⟩ := reference_b_feature_first_joint_information U V universal effective reference chain simulations
  obtain ⟨upperCost, upperBound⟩ := reference_joint_upper reference chain
  refine ⟨max jointCost upperCost, fun factor feature descriptive source residual minimum extracts reconstructs smaller ratio => ?_⟩
  have lower := jointBound factor feature feature descriptive source residual minimum extracts reconstructs smaller ratio
  have upper := upperBound feature residual
  rw [abs_le]
  constructor <;> omega

#print axioms reference_b_feature_incompressibility
#print axioms reference_shortest_b_independence
#print axioms reference_shortest_b_feature_source_bound
#print axioms shortest_b_feature_polynomial_count
#print axioms reference_b_feature_joint_information
#print axioms reference_b_feature_first_joint_information
#print axioms reference_b_residual_independence
#print axioms reference_b_joint_independence

end KolmogorovComplexity.FeatureTheory
