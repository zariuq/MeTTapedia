import Mettapedia.Computability.KolmogorovComplexity.FeatureBChain
import Mettapedia.Examples.Compression.FeatureIncrementalControls
import Mettapedia.Examples.Compression.FeatureConstrainedSearchControls

/-!
# Shortest b-feature information controls

Actual canonical interpreters discharge every machine premise. A finite
two-stage chain tests both nonempty and empty residuals. A separate machine
shows that b-minimality does not imply unrestricted minimality. Cap framing
and a divergent earlier residual are checked independently of those minima.
-/

set_option autoImplicit false

namespace Mettapedia.Examples.Compression.FeatureBControls

open KolmogorovComplexity KolmogorovComplexity.FeatureTheory
open FeatureCompressionChainControls
open scoped Classical

def separation : ConditionalAlgorithm := fun program condition =>
  if program = [false] ∧ condition = fourTrue then Part.some eight
  else if program = [true, false] ∧ condition = [true] then Part.some eight
  else if program = [true] ∧ condition = eight then Part.some fourTrue
  else if program = [false, true] ∧ condition = eight then Part.some [true]
  else Part.none

theorem shortest_b_not_unrestricted :
    ShortestBFeature separation 4 [true, false] eight ∧
      ¬ ShortestFeature separation [true, false] eight := by
  have admitted : BFeature separation 4 [true, false] eight := by
    refine ⟨[false, true], [true], ?_, ?_, ?_, ?_⟩ <;>
      norm_num [separation, eight, fourTrue]
  constructor
  · refine ⟨admitted, fun other present => ?_⟩
    obtain ⟨descriptive, residual, _extracts, reconstructs, _smaller, ratio⟩ := present
    unfold separation at reconstructs
    split_ifs at reconstructs with short longer extractLong extractShort
    · have same : residual = fourTrue := short.2
      subst residual
      norm_num [fourTrue, eight] at ratio
    · simp [longer.1]
    · simp [eight, fourTrue] at reconstructs
    · simp [eight] at reconstructs
    · simp at reconstructs
  · intro alleged
    have ordinary : Feature separation [false] eight := by
      refine ⟨[true], fourTrue, ?_, ?_, ?_⟩ <;> simp [separation, eight, fourTrue]
    have impossible := alleged.2 [false] ordinary
    simp at impossible

theorem ratio_three_cap : residualCap 3 eight = 2 := by
  change ⌊(8 : ℝ) / 3⌋₊ = 2
  apply (Nat.floor_eq_iff (by norm_num : (0 : ℝ) ≤ 8 / 3)).mpr
  norm_num

theorem nonintegral_cap : residualCap (3 / 2) eight = 5 := by
  change ⌊(8 : ℝ) / (3 / 2)⌋₊ = 5
  apply (Nat.floor_eq_iff (by norm_num : (0 : ℝ) ≤ 8 / (3 / 2))).mpr
  norm_num

theorem cap_accepts_boundary_rejects_next :
    cappedResidualGuard (residualCap 3 eight) (([false], eight), [true, true]) = true ∧
      cappedResidualGuard (residualCap 3 eight) (([false], eight), [true, true, true]) = false := by
  rw [ratio_three_cap]
  decide

theorem empty_cap_still_has_a_header :
    (e1encode (binaryBits 0)).length = 1 := by decide

theorem cap_header_preserves_context (cap : Nat) (context : BinString) :
    e1decode (e1encode (binaryBits cap) ++ context) = some (binaryBits cap, context) :=
  e1decode_e1encode_append _ _

theorem missing_cap_header_refused (V : ConditionalPrefixFreeMachine) (code : Nat.Partrec.Code)
    (source : BinString) : describedCappedResidualSearch V code [] source = Part.none := by
  simp [describedCappedResidualSearch, e1decode, countLeadingTrues]

theorem capped_search_reaches_later_residual :
    ∃ residual, residual ∈ cappedResidualSearch FeatureDecompositionControls.waitingCode
        (1, [], FeatureDecompositionControls.source) ∧ residual ≠ [] ∧ residual.length ≤ 1 := by
  obtain ⟨residual, selected⟩ := guardedResidualSearch_complete FeatureDecompositionControls.waitingCode_spec
    (guard := cappedResidualGuard 1) (feature := []) (residual := [false])
    (source := FeatureDecompositionControls.source)
    (by simp [FeatureDecompositionControls.waitingAlgorithm])
    (by simp [FeatureDecompositionControls.source]) (by decide)
  have checked := guardedResidualSearch_sound FeatureDecompositionControls.waitingCode_spec selected
  refine ⟨residual, selected, ?_, ?_⟩
  · intro empty
    simp [FeatureDecompositionControls.waitingAlgorithm, empty] at checked
  · simpa only [cappedResidualGuard, decide_eq_true_eq] using checked.2.2

theorem empty_cap_cannot_invent_a_residual :
    ¬ ∃ residual, residual ∈ cappedResidualSearch FeatureDecompositionControls.waitingCode
      (0, [], FeatureDecompositionControls.source) := by
  rintro ⟨residual, selected⟩
  have checked := cappedResidualSearch_sound FeatureDecompositionControls.waitingCode_spec selected
  have empty : residual = [] := by
    have width : residual.length ≤ 0 := checked.2.2
    exact List.length_eq_zero_iff.mp (by omega)
  simp [FeatureDecompositionControls.waitingAlgorithm, empty] at checked

theorem two_stage_shortest_b_chain : ShortestBChain twoStage 2 eight [[false], [false]] [] := by
  have firstMap : BDescriptiveMap twoStage 2 [false] [true] eight :=
    ⟨fourTrue, by simp [twoStage, eight, fourTrue], by simp [twoStage, eight, fourTrue],
      by simp [eight, fourTrue], by norm_num [eight, fourTrue]⟩
  have secondMap : BDescriptiveMap twoStage 2 [false] [true] fourTrue :=
    ⟨[], by simp [twoStage, eight, fourTrue], by simp [twoStage], by simp [fourTrue], by norm_num [fourTrue]⟩
  have minimumFeature {input : BinString} (present : BFeature twoStage 2 [false] input) :
      ShortestBFeature twoStage 2 [false] input :=
    ⟨present, fun other admitted =>
      (FeatureIncrementalControls.one_bit_feature_minimum present.feature).2 other admitted.feature⟩
  have minimumMap {input : BinString} (present : BDescriptiveMap twoStage 2 [false] [true] input) :
      ShortestBDescriptiveMap twoStage 2 [false] [true] input := by
    refine ⟨present, fun other admitted => ?_⟩
    obtain ⟨residual, extracts, reconstructs, smaller, _ratio⟩ := admitted
    exact (FeatureIncrementalControls.one_bit_map_minimum
      ⟨present.choose, present.choose_spec.1, present.choose_spec.2.1, present.choose_spec.2.2.1⟩).2 other
      ⟨residual, extracts, reconstructs, smaller⟩
  exact .cons (minimumFeature ⟨[true], firstMap⟩) (minimumMap firstMap)
    (by simp [twoStage, eight, fourTrue])
    (.cons (minimumFeature ⟨[true], secondMap⟩) (minimumMap secondMap)
      (by simp [twoStage, eight, fourTrue]) (.nil []))

theorem two_stage_split :
    ∃ residual, ShortestBChain twoStage 2 eight [[false]] residual ∧
      ShortestBChain twoStage 2 residual [[false]] [] :=
  ShortestBChain.split two_stage_shortest_b_chain

theorem real_ratio_iteration_bound :
    (2 : ℝ) ≤ Real.log eight.length / Real.log 2 + 1 :=
  two_stage_shortest_b_chain.toBChain.logarithmic_length (by norm_num) (by simp)

theorem two_stage_reconstruction : eight ∈ restoreFeatures twoStage [[false], [false]] [] :=
  two_stage_shortest_b_chain.reconstruct

theorem unit_constraint_does_not_change_minima :
    ShortestBFeature twoStage 1 [false] eight ↔ ShortestFeature twoStage [false] eight :=
  unit_shortest_b_feature_iff twoStage [false] eight

theorem canonical_b_source_information :
    ∃ overhead : Nat, ∀ factor, 1 ≤ factor → ∀ source feature,
      ShortestBFeature universalConditionalAlgorithm factor feature source →
      conditionalComplexity trimmedIndexedHost feature source ≤ 6 * Nat.log 2 (source.length + 1) + overhead :=
  reference_shortest_b_feature_source_bound universalConditionalAlgorithm trimmedIndexedHost
    universalConditionalAlgorithm_isUniversal universalConditionalAlgorithm_partrec
    isReferenceMachine_trimmedIndexedHost KraftChaitin.trimmedIndexedHostStrongConditionalChainRule
    trimmedReferenceMachineSimulations

theorem canonical_b_polynomial_count :
    ∃ coefficient : Nat, ∀ factor, 1 ≤ factor → ∀ source (features : Finset BinString),
      (∀ feature ∈ features, ShortestBFeature universalConditionalAlgorithm factor feature source) →
      features.card < coefficient * (source.length + 1) ^ 6 :=
  shortest_b_feature_polynomial_count universalConditionalAlgorithm trimmedIndexedHost
    universalConditionalAlgorithm_isUniversal universalConditionalAlgorithm_partrec
    isReferenceMachine_trimmedIndexedHost KraftChaitin.trimmedIndexedHostStrongConditionalChainRule
    trimmedReferenceMachineSimulations

theorem canonical_b_map_information :
    ∃ overhead : Nat, ∀ factor, 1 ≤ factor → ∀ feature descriptive source,
      ShortestBFeature universalConditionalAlgorithm factor feature source →
      ShortestBDescriptiveMap universalConditionalAlgorithm factor feature descriptive source →
      descriptive.length ≤ 8 * Nat.log 2 (source.length + 1) + overhead :=
  shortest_b_descriptive_logarithmic universalConditionalAlgorithm trimmedIndexedHost
    universalConditionalAlgorithm_isUniversal universalConditionalAlgorithm_partrec
    isReferenceMachine_trimmedIndexedHost KraftChaitin.trimmedIndexedHostStrongConditionalChainRule
    trimmedReferenceMachineSimulations

theorem canonical_b_incremental_information :
    ∃ overhead : Nat, ∀ factor, 1 ≤ factor → ∀ source features final,
      ShortestBChain universalConditionalAlgorithm factor source features final →
      |((conditionalComplexity trimmedIndexedHost source [] : Int) -
        ((features.map List.length).sum + conditionalComplexity trimmedIndexedHost final []))| ≤
          (features.length * (22 * Nat.log 2 (source.length + 1) + overhead) : Nat) :=
  incremental_b_information_bound universalConditionalAlgorithm trimmedIndexedHost
    universalConditionalAlgorithm_isUniversal universalConditionalAlgorithm_partrec
    isReferenceMachine_trimmedIndexedHost KraftChaitin.trimmedIndexedHostStrongConditionalChainRule
    trimmedReferenceMachineSimulations

theorem canonical_b_orthogonality :
    ∃ overhead : Nat, ∀ factor, 1 ≤ factor → ∀ source features final,
      ShortestBChain universalConditionalAlgorithm factor source features final →
      ∀ i j (hi : i < features.length) (hj : j < features.length), i ≠ j →
        |directedAlgorithmicInformation trimmedIndexedHost features[i] features[j]| ≤
          (Nat.dist i j * (22 * Nat.log 2 (source.length + 1) + overhead) : Nat) :=
  shortest_b_chain_orthogonality universalConditionalAlgorithm trimmedIndexedHost
    universalConditionalAlgorithm_isUniversal universalConditionalAlgorithm_partrec
    isReferenceMachine_trimmedIndexedHost KraftChaitin.trimmedIndexedHostStrongConditionalChainRule
    trimmedReferenceMachineSimulations

theorem canonical_b_logarithmic_overhead :
    ∃ overhead : Nat, ∀ factor, 1 < factor → ∀ source features final,
      ShortestBChain universalConditionalAlgorithm factor source features final → features ≠ [] →
      |((conditionalComplexity trimmedIndexedHost source [] : ℝ) -
        ((features.map List.length).sum + conditionalComplexity trimmedIndexedHost final []))| ≤
          (Real.log source.length / Real.log factor + 1) *
            (22 * (Nat.log 2 (source.length + 1) : ℝ) + overhead) :=
  incremental_b_logarithmic_overhead universalConditionalAlgorithm trimmedIndexedHost
    universalConditionalAlgorithm_isUniversal universalConditionalAlgorithm_partrec
    isReferenceMachine_trimmedIndexedHost KraftChaitin.trimmedIndexedHostStrongConditionalChainRule
    trimmedReferenceMachineSimulations

theorem canonical_b_bounds_are_nonvacuous :
    ∃ overhead : Nat, ∀ size : Nat, ∃ source feature descriptive residual,
      size < source.length ∧
      ShortestBChain universalConditionalAlgorithm (3 / 2) source [feature] residual ∧
      conditionalComplexity trimmedIndexedHost feature source ≤ 6 * Nat.log 2 (source.length + 1) + overhead ∧
      residual ∈ universalConditionalAlgorithm descriptive source ∧
      (3 / 2 : ℝ) * residual.length ≤ source.length := by
  obtain ⟨overhead, bound⟩ := canonical_b_source_information
  refine ⟨overhead, fun size => ?_⟩
  obtain ⟨source, feature, descriptive, large, minimumFeature, minimumMap⟩ :=
    FeatureConstrainedSearchControls.arbitrarily_large_rational_instances size
  obtain ⟨residual, extracts, reconstructs, smaller, ratio⟩ := minimumMap.1
  exact ⟨source, feature, descriptive, residual, large, .cons minimumFeature minimumMap extracts (.nil _),
    bound (3 / 2) (by norm_num) source feature minimumFeature, extracts, ratio⟩

end Mettapedia.Examples.Compression.FeatureBControls

open Lean Elab Command

run_cmd do
  let modules := #[`Mettapedia.Computability.KolmogorovComplexity.FeatureResidualCap,
    `Mettapedia.Computability.KolmogorovComplexity.FeatureBInformation,
    `Mettapedia.Computability.KolmogorovComplexity.FeatureBDecomposition,
    `Mettapedia.Computability.KolmogorovComplexity.FeatureBChain]
  let namespaces := #[`KolmogorovComplexity.FeatureTheory,
    `Mettapedia.Examples.Compression.FeatureBControls]
  let allowed := #[``propext, ``Quot.sound, ``Classical.choice]
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut regular : NameSet := {}
  let mut names : Array Name := #[]
  for moduleName in modules do
    let some index := env.header.moduleNames.toList.idxOf? moduleName | throwError "missing module {moduleName}"
    let data := env.header.moduleData[index]!
    names := names ++ data.constNames ++ data.extraConstNames
    for name in data.constNames do regular := regular.insert name
  for (name, _) in env.constants.toList do
    if namespaces[1]!.isPrefixOf name then
      names := names.push name
      regular := regular.insert name
  let mut safe := 0
  let mut compilerImplementations := 0
  let mut theorems := 0
  let mut audited : Array Json := #[]
  for name in names do
    if seen.contains name then continue
    seen := seen.insert name
    let some info := env.checked.get.find? name | do
      if regular.contains name then throwError "missing declaration {name}"
      continue
    if info.isUnsafe || info.isPartial then
      unless name.toString.endsWith "._unsafe_rec" do throwError "nonlogical declaration {name}"
      compilerImplementations := compilerImplementations + 1
      continue
    if info matches .axiomInfo _ then throwError "added axiom {name}"
    let dependencies ← liftCoreM <| collectAxioms name
    for dependency in dependencies do
      unless allowed.contains dependency do throwError "unpermitted dependency {name}: {dependency}"
    safe := safe + 1
    if info matches .thmInfo _ then
      theorems := theorems + 1
      audited := audited.push (Json.mkObj [("name", toJson name.toString),
        ("axioms", toJson (dependencies.map Name.toString))])
  liftIO <| IO.println (Json.mkObj [("safeKernelDeclarations", toJson safe), ("theorems", toJson theorems),
    ("separateCompilerImplementations", toJson compilerImplementations), ("auditedTheorems", toJson audited)]).compress
