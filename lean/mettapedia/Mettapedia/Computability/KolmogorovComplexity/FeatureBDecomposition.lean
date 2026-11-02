import Mettapedia.Computability.KolmogorovComplexity.FeatureBInformation

/-!
# Effective b-residual selection and information decomposition

One compiler takes a self-delimited natural residual cap followed by a prefix
description of the feature. It tests the cap before selecting a residual.
Every header bit is charged. No comparison with a noncomputable real factor
occurs inside the search.
-/

set_option autoImplicit false

namespace KolmogorovComplexity.FeatureTheory

open scoped Classical

def cappedResidualSearchStep (code : Nat.Partrec.Code) (input : Nat × ResidualSearchInput) : Option BinString :=
  guardedResidualSearchStep code (cappedResidualGuard input.1) input.2

theorem cappedResidualSearchStep_primrec (code : Nat.Partrec.Code) :
    Primrec (cappedResidualSearchStep code) := by
  have check : Primrec fun context : (Nat × ResidualSearchInput) × BinString =>
      decide (context.2.length ≤ context.1.1) :=
    (Primrec.nat_le.comp (Primrec.list_length.comp Primrec.snd)
      (Primrec.fst.comp Primrec.fst)).decide
  exact Primrec.option_bind ((residualSearchStep_primrec code).comp Primrec.snd)
    (check.cond (Primrec.option_some.comp Primrec.snd) (Primrec.const none)).to₂

def cappedResidualSearch (code : Nat.Partrec.Code) : (Nat × (BinString × BinString)) →. BinString :=
  fun input => Nat.rfindOpt fun rank => cappedResidualSearchStep code (input.1, input.2, rank)

theorem cappedResidualSearch_partrec (code : Nat.Partrec.Code) : Partrec (cappedResidualSearch code) := by
  have steps : Primrec fun input : (Nat × (BinString × BinString)) × Nat =>
      cappedResidualSearchStep code (input.1.1, input.1.2, input.2) :=
    (cappedResidualSearchStep_primrec code).comp
      ((Primrec.fst.comp Primrec.fst).pair ((Primrec.snd.comp Primrec.fst).pair Primrec.snd))
  exact Partrec.rfindOpt steps.to_comp

theorem cappedResidualSearch_sound {U : ConditionalAlgorithm} {code : Nat.Partrec.Code}
    (codeSpec : Nat.Partrec.Code.eval code = encodedConditionalAlgorithm U)
    {cap : Nat} {feature source residual : BinString}
    (selected : residual ∈ cappedResidualSearch code (cap, feature, source)) :
    source ∈ U feature residual ∧ feature.length + residual.length < source.length ∧ residual.length ≤ cap := by
  have checked := guardedResidualSearch_sound codeSpec (guard := cappedResidualGuard cap) selected
  exact ⟨checked.1, checked.2.1, by simpa only [cappedResidualGuard, decide_eq_true_eq] using checked.2.2⟩

theorem cappedResidualSearch_complete {U : ConditionalAlgorithm} {code : Nat.Partrec.Code}
    (codeSpec : Nat.Partrec.Code.eval code = encodedConditionalAlgorithm U)
    {cap : Nat} {feature source residual : BinString}
    (reconstructs : source ∈ U feature residual) (smaller : feature.length + residual.length < source.length)
    (bounded : residual.length ≤ cap) :
    ∃ selected, selected ∈ cappedResidualSearch code (cap, feature, source) := by
  exact guardedResidualSearch_complete codeSpec reconstructs smaller
    (guard := cappedResidualGuard cap) (by simpa only [cappedResidualGuard, decide_eq_true_eq] using bounded)

def describedCappedResidualSearch (V : ConditionalPrefixFreeMachine) (code : Nat.Partrec.Code) : ConditionalAlgorithm :=
  fun packet source => (Part.ofOption (e1decode packet)).bind fun fields =>
    (Part.ofOption (V.compute fields.2 source)).bind fun feature =>
      cappedResidualSearch code (ofBinaryBits fields.1, feature, source)

theorem describedCappedResidualSearch_partrec {V : ConditionalPrefixFreeMachine}
    (effective : Effective V) (code : Nat.Partrec.Code) : Partrec₂ (describedCappedResidualSearch V code) := by
  have parsed : Partrec fun input : BinString × BinString => Part.ofOption (e1decode input.1) :=
    (e1decode_primrec.comp Primrec.fst).to_comp.ofOption
  have feature : Partrec fun context : (BinString × BinString) × (BinString × BinString) =>
      Part.ofOption (V.compute context.2.2 context.1.2) :=
    effective.comp (Computable.snd.comp Computable.snd) (Computable.snd.comp Computable.fst)
  have search : Partrec fun context : ((BinString × BinString) × (BinString × BinString)) × BinString =>
      cappedResidualSearch code (ofBinaryBits context.1.2.1, context.2, context.1.1.2) :=
    (cappedResidualSearch_partrec code).comp
      (((ofBinaryBits_primrec.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))).pair
        (Primrec.snd.pair (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))).to_comp)
  exact parsed.bind (feature.bind search.to₂).to₂

theorem describedCappedResidualSearch_encoded (V : ConditionalPrefixFreeMachine) (code : Nat.Partrec.Code)
    (cap : Nat) (description source : BinString) :
    describedCappedResidualSearch V code (e1encode (binaryBits cap) ++ description) source =
      (Part.ofOption (V.compute description source)).bind fun feature =>
        guardedResidualSearch code (cappedResidualGuard cap) feature source := by
  simp [describedCappedResidualSearch, e1decode_e1encode_append,
    ofBinaryBits_binaryBits, cappedResidualSearch, cappedResidualSearchStep, guardedResidualSearch]

/-- A single compiler serves every cap and every source. The cap is encoded
as data, so the constant is independent even of the real compression factor. -/
theorem b_descriptive_map_from_feature_description (U : ConditionalAlgorithm)
    (V : ConditionalPrefixFreeMachine) (universal : IsUniversalConditional U)
    (effective : Partrec₂ U) (reference : IsReferenceMachine V) :
    ∃ overhead : Nat, ∀ factor, 1 ≤ factor → ∀ source feature, BFeature U factor feature source →
      ∃ descriptive, BDescriptiveMap U factor feature descriptive source ∧
        descriptive.length ≤ conditionalComplexity V feature source +
          2 * Nat.log 2 (source.length + 1) + overhead := by
  obtain ⟨code, codeSpec⟩ := exists_conditional_algorithm_code effective
  obtain ⟨compiler, compiles⟩ := universal (describedCappedResidualSearch V code)
    (describedCappedResidualSearch_partrec reference.1 code)
  refine ⟨compiler.length + 3, fun factor large source feature present => ?_⟩
  have positive : 0 < factor := lt_of_lt_of_le zero_lt_one large
  obtain ⟨oldMap, residual, _extracts, reconstructs, smaller, ratio⟩ := present
  let cap := residualCap factor source
  have width : residual.length ≤ cap := (residualCap_iff positive source residual).mpr ratio
  have admitted : cappedResidualGuard cap ((feature, source), residual) = true := by
    simpa only [cappedResidualGuard, decide_eq_true_eq] using width
  obtain ⟨selected, finds⟩ := guardedResidualSearch_complete codeSpec reconstructs smaller admitted
  obtain ⟨description, describes, length⟩ := exists_program_of_conditionalComplexity V source feature
    (reference.hasProgram _ _)
  have decoded : feature ∈ Part.ofOption (V.compute description source) := by simpa [IsProgram] using describes
  let packet := e1encode (binaryBits cap) ++ description
  have output : selected ∈ describedCappedResidualSearch V code packet source := by
    rw [describedCappedResidualSearch_encoded]
    exact Part.mem_bind decoded finds
  have checked := guardedResidualSearch_sound codeSpec finds
  have capBound := residualCap_le_length large source
  have header := binaryBits_length cap
  have logarithm := Nat.log_mono_right (b := 2) (show cap ≤ source.length + 1 by omega)
  refine ⟨compiler ++ packet, ⟨selected, compiles packet source selected output,
    checked.1, checked.2.1, (residualCap_iff positive source selected).mp ?_⟩, ?_⟩
  · simpa only [cappedResidualGuard, decide_eq_true_eq] using checked.2.2
  · simp only [List.length_append, packet, e1encode_length, length]
    omega

theorem shortest_b_descriptive_logarithmic (U : ConditionalAlgorithm)
    (V : ConditionalPrefixFreeMachine) (universal : IsUniversalConditional U)
    (effective : Partrec₂ U) (reference : IsReferenceMachine V)
    (chain : StrongConditionalChainRule V) (simulations : ReferenceMachineSimulations V) :
    ∃ overhead : Nat, ∀ factor, 1 ≤ factor → ∀ feature descriptive source,
      ShortestBFeature U factor feature source → ShortestBDescriptiveMap U factor feature descriptive source →
      descriptive.length ≤ 8 * Nat.log 2 (source.length + 1) + overhead := by
  obtain ⟨featureCost, featureBound⟩ := reference_shortest_b_feature_source_bound U V universal effective reference chain simulations
  obtain ⟨extractorCost, extractorBound⟩ := b_descriptive_map_from_feature_description U V universal effective reference
  refine ⟨featureCost + extractorCost, fun factor large feature descriptive source minimumFeature minimumMap => ?_⟩
  obtain ⟨competitor, admitted, bounded⟩ := extractorBound factor large source feature minimumFeature.1
  have minimum := minimumMap.2 competitor admitted
  have information := featureBound factor large source feature minimumFeature
  omega

theorem log_of_eight_log_bound {length size overhead : Nat}
    (bounded : length ≤ 8 * Nat.log 2 (size + 1) + overhead) :
    Nat.log 2 (length + 1) ≤ Nat.log 2 (size + 1) + overhead + 4 := by
  have first := Nat.log_mono_right (b := 2) (Nat.add_le_add_right bounded 1)
  have shift := log_add_constant_le (8 * Nat.log 2 (size + 1)) overhead
  have small := Nat.log_le_self 2 (size + 1)
  have scaled := Nat.log_mono_right (b := 2)
    (show 8 * Nat.log 2 (size + 1) + 1 ≤ (size + 1) * 2 * 2 * 2 * 2 by omega)
  have double := Nat.log_mul_base (b := 2) (by decide) (Nat.succ_ne_zero size)
  have quadruple := Nat.log_mul_base (b := 2) (by decide) (show (size + 1) * 2 ≠ 0 by omega)
  have octuple := Nat.log_mul_base (b := 2) (by decide) (show (size + 1) * 2 * 2 ≠ 0 by omega)
  have sixteen := Nat.log_mul_base (b := 2) (by decide) (show (size + 1) * 2 * 2 * 2 ≠ 0 by omega)
  simp only [Nat.succ_eq_add_one] at double
  omega

theorem shortest_b_map_residual_information (U : ConditionalAlgorithm)
    (V : ConditionalPrefixFreeMachine) (universal : IsUniversalConditional U)
    (effective : Partrec₂ U) (reference : IsReferenceMachine V)
    (chain : StrongConditionalChainRule V) (simulations : ReferenceMachineSimulations V) :
    ∃ overhead : Nat, ∀ factor, 1 ≤ factor → ∀ feature descriptive source residual,
      ShortestBFeature U factor feature source → ShortestBDescriptiveMap U factor feature descriptive source →
      residual ∈ U descriptive source →
      conditionalComplexity V residual source ≤ 10 * Nat.log 2 (source.length + 1) + overhead := by
  obtain ⟨mapCost, mapBound⟩ := shortest_b_descriptive_logarithmic U V universal effective reference chain simulations
  obtain ⟨programCost, programBound⟩ := reference_program_description U V effective reference
  refine ⟨3 * mapCost + programCost + 8, fun factor large feature descriptive source residual minimumFeature minimumMap extracts => ?_⟩
  have length := mapBound factor large feature descriptive source minimumFeature minimumMap
  have logarithm := log_of_eight_log_bound length
  have bound := programBound descriptive source residual extracts
  omega

theorem shortest_b_maps_no_superfluous_information (U : ConditionalAlgorithm)
    (V : ConditionalPrefixFreeMachine) (universal : IsUniversalConditional U)
    (effective : Partrec₂ U) (reference : IsReferenceMachine V)
    (chain : StrongConditionalChainRule V) (simulations : ReferenceMachineSimulations V) :
    ∃ overhead : Nat, ∀ factor, 1 ≤ factor → ∀ feature descriptive source residual,
      ShortestBFeature U factor feature source → ShortestBDescriptiveMap U factor feature descriptive source →
      residual ∈ U descriptive source →
      conditionalComplexity V (pairCondition feature residual) source ≤
        16 * Nat.log 2 (source.length + 1) + overhead := by
  obtain ⟨featureCost, featureBound⟩ := reference_shortest_b_feature_source_bound U V universal effective reference chain simulations
  obtain ⟨residualCost, residualBound⟩ := shortest_b_map_residual_information U V universal effective reference chain simulations
  obtain ⟨pairCost, pairBound⟩ := reference_conditional_pair_upper V reference chain
  refine ⟨featureCost + residualCost + pairCost, fun factor large feature descriptive source residual minimumFeature minimumMap extracts => ?_⟩
  have information := featureBound factor large source feature minimumFeature
  have rest := residualBound factor large feature descriptive source residual minimumFeature minimumMap extracts
  have pair := pairBound feature residual source
  omega

theorem shortest_b_maps_information_partition (U : ConditionalAlgorithm)
    (V : ConditionalPrefixFreeMachine) (universal : IsUniversalConditional U)
    (effective : Partrec₂ U) (reference : IsReferenceMachine V)
    (chain : StrongConditionalChainRule V) (simulations : ReferenceMachineSimulations V) :
    ∃ overhead : Nat, ∀ factor, 1 ≤ factor → ∀ feature descriptive source residual,
      ShortestBFeature U factor feature source → ShortestBDescriptiveMap U factor feature descriptive source →
      residual ∈ U descriptive source →
      |((conditionalComplexity V source [] : Int) -
        (conditionalComplexity V feature [] + conditionalComplexity V residual []))| ≤
          (20 * Nat.log 2 (source.length + 1) + overhead : Nat) := by
  obtain ⟨pairCost, pairBound⟩ := shortest_b_maps_no_superfluous_information U V universal effective reference chain simulations
  obtain ⟨jointCost, jointBound⟩ := reference_b_feature_first_joint_information U V universal effective reference chain simulations
  obtain ⟨upperCost, upperBound⟩ := reference_joint_upper reference chain
  obtain ⟨reconstructionCost, reconstructionBound⟩ := reference_postprocess V reference
    (reconstructFeaturePair U) (reconstructFeaturePair_partrec effective)
  obtain ⟨projection⟩ := reference.2 (secondOutputMachine V) (secondOutputMachine_effective V reference.1)
  refine ⟨max (upperCost + reconstructionCost)
    (pairCost + jointCost + chain.constant + simulations.headCondition.compilerPrefix.length + projection.compilerPrefix.length),
    fun factor large feature descriptive source residual minimumFeature minimumMap extracts => ?_⟩
  obtain ⟨reconstructs, smaller, ratio, _length⟩ := shortest_b_descriptive_actual_output minimumMap extracts
  have actualReconstruction : source ∈ reconstructFeaturePair U (pairCondition feature residual) := by
    simpa [reconstructFeaturePair, unpairCondition_pairCondition] using reconstructs
  have sourceUpper := reconstructionBound _ source [] actualReconstruction
  have jointUpper := upperBound feature residual
  have independent := jointBound factor feature feature descriptive source residual minimumFeature extracts reconstructs smaller ratio
  have conditionalPair := pairBound factor large feature descriptive source residual minimumFeature minimumMap extracts
  let pair := pairCondition feature residual
  have chainUpper := chain.upper [] source pair (reference.hasProgram _ _) (reference.hasProgram _ _)
  obtain ⟨program, runs, length⟩ := exists_program_of_conditionalComplexity V source pair (reference.hasProgram _ _)
  have lifted := headConditionMachine_program (condition := pairCondition (binaryBits (conditionalComplexity V source [])) []) runs
  have liftBound := conditionalComplexity_le_simulated_program simulations.headCondition lifted
  rw [length] at liftBound
  obtain ⟨jointProgram, jointRuns, jointLength⟩ := exists_program_of_conditionalComplexity V [] (pairCondition source pair)
    (reference.hasProgram _ _)
  have projected := conditionalComplexity_le_simulated_program projection (secondOutputMachine_program jointRuns)
  rw [jointLength] at projected
  have featureLog := Nat.log_mono_right (b := 2) (show feature.length + 1 ≤ source.length + 1 by omega)
  have residualLog := Nat.log_mono_right (b := 2) (show residual.length + 1 ≤ source.length + 1 by omega)
  dsimp only [pair] at chainUpper liftBound projected
  change conditionalComplexity V (pairCondition feature residual) (chainCondition [] source (conditionalComplexity V source [])) ≤ _ at liftBound
  rw [abs_le]
  constructor <;> omega

theorem shortest_b_maps_length_partition (U : ConditionalAlgorithm)
    (V : ConditionalPrefixFreeMachine) (universal : IsUniversalConditional U)
    (effective : Partrec₂ U) (reference : IsReferenceMachine V)
    (chain : StrongConditionalChainRule V) (simulations : ReferenceMachineSimulations V) :
    ∃ overhead : Nat, ∀ factor, 1 ≤ factor → ∀ feature descriptive source residual,
      ShortestBFeature U factor feature source → ShortestBDescriptiveMap U factor feature descriptive source →
      residual ∈ U descriptive source →
      |((conditionalComplexity V source [] : Int) -
        (feature.length + conditionalComplexity V residual []))| ≤
          (22 * Nat.log 2 (source.length + 1) + overhead : Nat) := by
  obtain ⟨partitionCost, partition⟩ := shortest_b_maps_information_partition U V universal effective reference chain simulations
  obtain ⟨lowerCost, upperCost, incompressibility⟩ := reference_b_feature_incompressibility U V universal effective reference
  refine ⟨partitionCost + max lowerCost upperCost,
    fun factor large feature descriptive source residual minimumFeature minimumMap extracts => ?_⟩
  have split := partition factor large feature descriptive source residual minimumFeature minimumMap extracts
  have featureBounds := incompressibility factor source feature minimumFeature
  have smaller := (shortest_b_descriptive_actual_output minimumMap extracts).2.1
  have logarithm := Nat.log_mono_right (b := 2) (show feature.length + 1 ≤ source.length + 1 by omega)
  rw [abs_le] at split ⊢
  constructor <;> omega

#print axioms cappedResidualSearchStep_primrec
#print axioms cappedResidualSearch_partrec
#print axioms cappedResidualSearch_sound
#print axioms cappedResidualSearch_complete
#print axioms describedCappedResidualSearch_partrec
#print axioms describedCappedResidualSearch_encoded
#print axioms b_descriptive_map_from_feature_description
#print axioms shortest_b_descriptive_logarithmic
#print axioms log_of_eight_log_bound
#print axioms shortest_b_map_residual_information
#print axioms shortest_b_maps_no_superfluous_information
#print axioms shortest_b_maps_information_partition
#print axioms shortest_b_maps_length_partition

end KolmogorovComplexity.FeatureTheory
