import Mettapedia.Computability.KolmogorovComplexity.FeatureRandomnessConverse
import Lean.Util.CollectAxioms
import Lean.Data.Json.Printer

/-! Positive and negative finite-string tests, stable residual addresses,
prefix padding and a nonempty converse on the concrete effective host. -/

namespace Mettapedia.Examples.Compression.FeatureRandomnessControls

open KolmogorovComplexity
open KolmogorovComplexity.FeatureTheory
open KolmogorovComplexity.FeatureTheory.Randomness
open KolmogorovComplexity.FiniteBitStrings
open Mettapedia.UniversalAI.TimeBoundedAIXI
open scoped Classical

theorem fixed_width_index_zero_preserves_zeros : fixedRank [false, false, false] = 0 := by decide

theorem fixed_width_last_index : fixedRank [true, true, true] = 7 := by decide

theorem duplicate_discovery_does_not_allocate_another_index :
    appendNew [[true, false], [false, false]] (some [true, false]) = [[true, false], [false, false]] := by decide

theorem later_lexicographically_earlier_discovery_keeps_the_first_index :
    (appendNew [[true]] (some [false]))[0]? = some [true] := by decide

theorem sorting_would_change_the_residual_meaning :
    (appendNew [[true]] (some [false]))[0]? ≠ ([[false], [true]] : List BinString)[0]? := by decide

theorem zero_threshold_minimum_padding : parseThreshold (e1encode (binaryBits 0) ++ machinePrefix 0) = some 0 := by decide

theorem arbitrary_trailing_zeros_are_not_prefix_padding :
    parseThreshold (e1encode (binaryBits 7) ++ [false, false]) = none := by decide

theorem padding_delimiter_is_required : parseThreshold (e1encode (binaryBits 7) ++ [true, true]) = none := by decide

theorem suffix_after_padding_delimiter_is_rejected :
    parseThreshold ((e1encode (binaryBits 7) ++ machinePrefix 2) ++ [false]) = none := by decide

theorem normalized_program_pays_the_entire_padding (compiler : BinString) :
    ∃ threshold padding, 0 < threshold ∧
      (compiler ++ (e1encode (binaryBits threshold) ++ machinePrefix padding)).length + 1 = threshold := by
  obtain ⟨threshold, padding, positive, length⟩ := exists_normalized_program compiler
  exact ⟨threshold, padding, positive, by omega⟩

def badEmptyDeficiency (source : BinString) : Nat := if source = [] then 1 else 0

theorem truncated_exponent_accepts_an_invalid_level :
    (level badEmptyDeficiency 0 1).card = 1 ∧
    (level badEmptyDeficiency 0 1).card ≤ 2 ^ (0 - 1) ∧
    ¬(2 ^ 1 * (level badEmptyDeficiency 0 1).card ≤ 2 ^ 0) := by decide

theorem invalid_empty_test_is_refused : ¬ UniformTest badEmptyDeficiency := by
  intro test
  have empty := test.empty_above_length 0 1 (by decide)
  have present : ([] : BinString) ∈ level badEmptyDeficiency 0 1 := by decide
  simp [empty] at present

def allOutputsScore (source : BinString) : Nat := source.length - 1

/-- A relation that printed every source from the same empty residual
would give this score. It cannot replace a deterministic partial interpreter. -/
theorem arbitrary_many_answer_relations_do_not_supply_the_rarity_bound :
    (level allOutputsScore 2 1).card = 4 ∧
      ¬(2 ^ 1 * (level allOutputsScore 2 1).card ≤ 2 ^ 2) := by decide

def identityInterpreter : ConditionalAlgorithm := fun _program residual => Part.some residual

theorem identityInterpreter_effective : Partrec₂ identityInterpreter := Computable.snd.partrec

theorem identity_has_zero_deficiency (feature source : BinString) : deficiency identityInterpreter feature source = 0 := by
  apply deficiency_zero_of_no_compression
  intro residual ⟨shorter, reconstructs⟩
  have same : source = residual := by simpa [identityInterpreter] using reconstructs
  have lengths := congrArg List.length same
  omega

theorem zero_test_is_uniform : UniformTest (fun _source => 0) := by
  have same : deficiency identityInterpreter [] = (fun _source => 0) := funext (identity_has_zero_deficiency [])
  simpa only [same] using feature_deficiencies_are_uniform_tests identityInterpreter identityInterpreter_effective []

theorem zero_test_is_not_unbounded : ¬(∀ bound : Nat, ∃ source : BinString, bound < (fun _source => 0) source) := by
  intro unbounded
  obtain ⟨source, impossible⟩ := unbounded 0
  change (0 : Nat) < 0 at impossible
  exact (Nat.lt_irrefl 0) impossible

theorem concrete_compression_has_positive_deficiency :
    deficiency finiteCompressionAlgorithm [false] fourTrue = 3 := by
  have lower := deficiency_ge_of_reconstruction finiteCompressionStep.reconstructs finiteCompressionStep.compresses
  have upper := deficiency_le_pred_length finiteCompressionAlgorithm [false] fourTrue
  change 4 - 0 - 1 ≤ deficiency finiteCompressionAlgorithm [false] fourTrue at lower
  change deficiency finiteCompressionAlgorithm [false] fourTrue ≤ 4 - 1 at upper
  omega

def duplicationMachine : ConditionalPrefixFreeMachine where
  compute := fun program condition => if program = [] then some (condition ++ condition) else none
  prefix_free := by
    intro condition program extension isPrefix different halts
    have empty : program = [] := by simpa using halts
    have nonempty : extension ≠ [] := by simpa [empty] using different.symm
    simp [nonempty]

theorem duplicationMachine_effective : Effective duplicationMachine := by
  have compute : Primrec₂ fun (program condition : BinString) =>
      if program = [] then some (condition ++ condition) else none :=
    (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const []))
      (Primrec.option_some.comp (Primrec.list_append.comp Primrec.snd Primrec.snd)) (Primrec.const none)).to₂
  exact compute.to_comp.ofOption

/-- The test class and the converse have real witnesses: one fixed prefix
program doubles arbitrarily long residuals on the shared concrete host. -/
theorem concrete_host_has_unbounded_feature_test :
    ∃ feature, UniformTest (deficiency (prefixAlgorithm trimmedIndexedHost) feature) ∧
      ∀ bound, ∃ source, bound < deficiency (prefixAlgorithm trimmedIndexedHost) feature source := by
  obtain ⟨simulation⟩ := trimmedIndexedHost_simulates_effective duplicationMachine duplicationMachine_effective
  let feature := simulation.compilerPrefix
  refine ⟨feature, feature_deficiencies_are_uniform_tests (prefixAlgorithm trimmedIndexedHost) trimmedIndexedHost_effective feature,
    fun bound => ?_⟩
  let residual : BinString := List.replicate (feature.length + bound + 2) true
  let source := residual ++ residual
  have produces : IsProgram trimmedIndexedHost feature residual source := by
    simpa [feature] using simulation.program (p := []) (condition := residual) (x := source)
      (by simp [IsProgram, duplicationMachine, source])
  have reconstructs := (prefixAlgorithm_runs _ _ _ _).mpr produces
  have shorter : feature.length + residual.length < source.length := by
    simp only [source, residual, List.length_append, List.length_replicate]
    omega
  have lower := deficiency_ge_of_reconstruction reconstructs shorter
  refine ⟨source, ?_⟩
  have large : bound < source.length - residual.length - 1 := by
    simp only [source, residual, List.length_append, List.length_replicate]
    omega
  exact large.trans_le lower

theorem concrete_prefix_test_converse_is_nonvacuous :
    ∃ testFeature feature,
      UniformTest (deficiency (prefixAlgorithm trimmedIndexedHost) testFeature) ∧
      (∃ source, feature.length < deficiency (prefixAlgorithm trimmedIndexedHost) testFeature source) ∧
      ∀ source, feature.length < deficiency (prefixAlgorithm trimmedIndexedHost) testFeature source →
        Feature (prefixAlgorithm trimmedIndexedHost) feature source := by
  obtain ⟨testFeature, uniform, unbounded⟩ := concrete_host_has_unbounded_feature_test
  obtain ⟨feature, present, shared⟩ := trimmed_host_unbounded_test_common_feature _ uniform unbounded
  exact ⟨testFeature, feature, uniform, present, shared⟩

theorem concrete_prefix_test_has_one_shared_extractor_and_decoder :
    ∃ testFeature feature descriptive,
      UniformTest (deficiency (prefixAlgorithm trimmedIndexedHost) testFeature) ∧
      (∃ source, feature.length < deficiency (prefixAlgorithm trimmedIndexedHost) testFeature source) ∧
      ∀ source, feature.length < deficiency (prefixAlgorithm trimmedIndexedHost) testFeature source →
        DescriptiveMap (prefixAlgorithm trimmedIndexedHost) feature descriptive source := by
  obtain ⟨testFeature, uniform, unbounded⟩ := concrete_host_has_unbounded_feature_test
  obtain ⟨feature, descriptive, present, shared⟩ := trimmed_host_unbounded_test_autoencoder _ uniform unbounded
  exact ⟨testFeature, feature, descriptive, uniform, present, shared⟩

end Mettapedia.Examples.Compression.FeatureRandomnessControls

open Lean Elab Command

run_cmd do
  let modules := #[`Mettapedia.Computability.FiniteBitStrings,
    `Mettapedia.Computability.KolmogorovComplexity.FeatureRandomness,
    `Mettapedia.Computability.KolmogorovComplexity.RandomnessLevelSearch,
    `Mettapedia.Computability.KolmogorovComplexity.FeatureRandomnessConverse]
  let namespaces := #[`KolmogorovComplexity.FiniteBitStrings,
    `KolmogorovComplexity.FeatureTheory.Randomness,
    `Mettapedia.Examples.Compression.FeatureRandomnessControls]
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
    if namespaces[2]!.isPrefixOf name then
      names := names.push name
      regular := regular.insert name
  let mut safe := 0
  let mut compilerImplementations := 0
  let mut theorems := 0
  let mut audited : Array Json := #[]
  for name in names do
    if seen.contains name then continue
    seen := seen.insert name
    unless namespaces.any (fun space => space.isPrefixOf name) do continue
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
