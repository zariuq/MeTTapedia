import Mettapedia.Computability.KolmogorovComplexity.CompressiveFeature
import Mettapedia.Computability.KolmogorovComplexity.FeaturePredicates

/-!
# Feature minima over the common conditional-machine foundation

The mathematical source is Arthur Franz, Oleksandr Antonenko and Roman
Soletskyi, "A theory of incremental compression", Information Sciences 547
(2021), 28-48, https://doi.org/10.1016/j.ins.2020.08.035
(preprint: https://arxiv.org/abs/1908.03781).
The separate https://github.com/dmacd/ic-theory and
https://github.com/af271/ic-theory developments informed the formalization
audit. This module develops the statements over Mettapedia's common
conditional-machine foundation rather than importing their theorem claims.

The feature and descriptive-map definitions have the quantifiers of the IC
paper's Definition 2.1. Their executable witness is exactly the existing
`CompressionStep`; descriptive-map length is minimized separately and is not
silently included in the feature-plus-residual compression condition.

Shortest-program arguments apply to any conditional partial algorithm. The
complexity used here is the existing minimum program-length functional. No
prefix-free, symmetry-of-information or shortest-feature hypothesis is inferred
from a practical learner's decreasing encoded cost.
-/

namespace KolmogorovComplexity.FeatureTheory

open scoped Classical

theorem step_feature {U : ConditionalAlgorithm} {source : BinString}
    (step : CompressionStep U source) : Feature U step.featureProgram source :=
  ⟨step.descriptiveProgram, step.residual, step.extracts, step.reconstructs, step.compresses⟩

/-- The relational paper interface and shared executable witness agree. -/
theorem feature_iff_step (U : ConditionalAlgorithm) (feature source : BinString) :
    Feature U feature source ↔ ∃ step : CompressionStep U source, step.featureProgram = feature := by
  constructor
  · rintro ⟨descriptive, residual, extracts, reconstructs, smaller⟩
    exact ⟨⟨feature, descriptive, residual, extracts, reconstructs, smaller⟩, rfl⟩
  · rintro ⟨step, rfl⟩
    exact step_feature step

theorem exists_shortest_feature (U : ConditionalAlgorithm) (source : BinString)
    (existsFeature : ∃ feature, Feature U feature source) :
    ∃ feature, ShortestFeature U feature source := by
  let lengths : Set Nat := {n | ∃ feature, Feature U feature source ∧ feature.length = n}
  have inhabited : lengths.Nonempty := by
    obtain ⟨feature, present⟩ := existsFeature
    exact ⟨feature.length, feature, present, rfl⟩
  obtain ⟨feature, present, minimal⟩ := Nat.sInf_mem inhabited
  refine ⟨feature, present, fun other otherPresent => ?_⟩
  rw [minimal]
  exact Nat.sInf_le ⟨other, otherPresent, rfl⟩

theorem exists_shortest_descriptive (U : ConditionalAlgorithm) (feature source : BinString)
    (present : Feature U feature source) :
    ∃ descriptive, ShortestDescriptiveMap U feature descriptive source := by
  let lengths : Set Nat :=
    {n | ∃ descriptive, DescriptiveMap U feature descriptive source ∧ descriptive.length = n}
  have inhabited : lengths.Nonempty := by
    obtain ⟨descriptive, present⟩ := present
    exact ⟨descriptive.length, descriptive, present, rfl⟩
  obtain ⟨descriptive, valid, minimal⟩ := Nat.sInf_mem inhabited
  refine ⟨descriptive, valid, fun other otherPresent => ?_⟩
  rw [minimal]
  exact Nat.sInf_le ⟨other, otherPresent, rfl⟩

/-- IC Lemma 3.1, feature half. The shortest descriptive-map assumption is
unnecessary for this half; its actual residual witness is sufficient. -/
theorem shortest_feature_conditional {U : ConditionalAlgorithm}
    {feature descriptive source residual : BinString}
    (shortest : ShortestFeature U feature source)
    (extracts : residual ∈ U descriptive source)
    (reconstructs : source ∈ U feature residual)
    (smaller : feature.length + residual.length < source.length) :
    feature.length = plainConditionalComplexity U source residual := by
  have upper := plainConditionalComplexity_le_of_program U residual source feature reconstructs
  obtain ⟨program, runs, minimal⟩ :=
    exists_program_of_plainConditionalComplexity U residual source ⟨feature, reconstructs⟩
  have competitor : Feature U program source := by
    refine ⟨descriptive, residual, extracts, runs, ?_⟩
    omega
  have lower := shortest.2 program competitor
  omega

/-- IC Lemma 3.1, descriptive-map half, for any feature with this residual. -/
theorem shortest_descriptive_conditional {U : ConditionalAlgorithm}
    {feature descriptive source residual : BinString}
    (shortest : ShortestDescriptiveMap U feature descriptive source)
    (extracts : residual ∈ U descriptive source)
    (reconstructs : source ∈ U feature residual)
    (smaller : feature.length + residual.length < source.length) :
    descriptive.length = plainConditionalComplexity U residual source := by
  have upper := plainConditionalComplexity_le_of_program U source residual descriptive extracts
  obtain ⟨program, runs, minimal⟩ :=
    exists_program_of_plainConditionalComplexity U source residual ⟨descriptive, extracts⟩
  have competitor : DescriptiveMap U feature program source :=
    ⟨residual, runs, reconstructs, smaller⟩
  have lower := shortest.2 program competitor
  omega

theorem shortest_maps_conditional {U : ConditionalAlgorithm}
    {feature descriptive source : BinString}
    (shortestFeature : ShortestFeature U feature source)
    (shortestDescriptive : ShortestDescriptiveMap U feature descriptive source) :
    ∃ residual, residual ∈ U descriptive source ∧ source ∈ U feature residual ∧
      feature.length = plainConditionalComplexity U source residual ∧
      descriptive.length = plainConditionalComplexity U residual source := by
  obtain ⟨residual, extracts, reconstructs, smaller⟩ := shortestDescriptive.1
  exact ⟨residual, extracts, reconstructs,
    shortest_feature_conditional shortestFeature extracts reconstructs smaller,
    shortest_descriptive_conditional shortestDescriptive extracts reconstructs smaller⟩

/-- One fixed extractor suffices for all singleton decompositions. The
compiler prefix is chosen before the source, so this is a uniform witness. -/
theorem universal_empty_extractor (U : ConditionalAlgorithm) (universal : IsUniversalConditional U) :
    ∃ descriptive, ∀ source, ([] : BinString) ∈ U descriptive source := by
  obtain ⟨compiler, compiles⟩ := universal (constantConditionalAlgorithm [])
    (constantConditionalAlgorithm_partrec [])
  refine ⟨compiler, fun source => ?_⟩
  simpa using compiles [] source [] (by simp [constantConditionalAlgorithm])

/-- IC Lemma 2.1 at the parameterized minimum-program layer. A concrete plain
universal machine may instantiate this theorem, but no prefix claim follows. -/
theorem singleton_of_compressible (U : ConditionalAlgorithm) (universal : IsUniversalConditional U)
    (source : BinString) (compressible : plainConditionalComplexity U source [] < source.length) :
    ∃ step : CompressionStep U source,
      step.residual = [] ∧ step.featureProgram.length = plainConditionalComplexity U source [] := by
  obtain ⟨descriptive, extracts⟩ := universal_empty_extractor U universal
  obtain ⟨program, reconstructs, minimal⟩ := exists_program_of_plainConditionalComplexity U [] source
    (universalConditional_hasProgram U universal [] source)
  refine ⟨⟨program, descriptive, [], extracts source, reconstructs, ?_⟩, rfl, minimal⟩
  simpa [minimal] using compressible

theorem shortest_feature_le_unconditional (U : ConditionalAlgorithm)
    (universal : IsUniversalConditional U) (feature source : BinString)
    (shortest : ShortestFeature U feature source)
    (compressible : plainConditionalComplexity U source [] < source.length) :
    feature.length ≤ plainConditionalComplexity U source [] := by
  obtain ⟨step, _, minimal⟩ := singleton_of_compressible U universal source compressible
  simpa [minimal] using shortest.2 step.featureProgram (step_feature step)

def UniversalFeatureWithConstant (U : ConditionalAlgorithm) (feature : BinString) (overhead : Nat) : Prop :=
  ∀ source, plainConditionalComplexity U source [] + overhead < source.length → Feature U feature source

/-- A fixed program interprets its residual as an unconditional program.
The feature and its overhead precede the source quantifier. Computability of
the simulated interpreter is an explicit premise, not supplied by universality. -/
theorem exists_universal_feature (U : ConditionalAlgorithm)
    (universal : IsUniversalConditional U) (computable : Partrec₂ U) :
    ∃ feature, ∀ source,
      plainConditionalComplexity U source [] + feature.length < source.length →
      ∃ step : CompressionStep U source, step.featureProgram = feature ∧
        step.residual.length = plainConditionalComplexity U source [] := by
  have runner : Partrec₂ (fun (_program : BinString) residual => U residual []) := by
    exact (computable.comp Computable.snd (Computable.const [])).to₂
  obtain ⟨feature, compiles⟩ := universal _ runner
  refine ⟨feature, fun source margin => ?_⟩
  obtain ⟨program, produces, minimal⟩ := exists_program_of_plainConditionalComplexity U [] source
    (universalConditional_hasProgram U universal [] source)
  obtain ⟨descriptive, extracts⟩ := universalConditional_hasProgram U universal source program
  have reconstructs : source ∈ U feature program := by
    simpa using compiles [] program source produces
  refine ⟨⟨feature, descriptive, program, extracts, reconstructs, ?_⟩, rfl, minimal⟩
  omega

theorem universal_feature_with_length_constant (U : ConditionalAlgorithm)
    (universal : IsUniversalConditional U) (computable : Partrec₂ U) :
    ∃ feature, UniversalFeatureWithConstant U feature feature.length := by
  obtain ⟨feature, works⟩ := exists_universal_feature U universal computable
  refine ⟨feature, fun source margin => ?_⟩
  obtain ⟨step, same, _⟩ := works source margin
  simpa [same] using step_feature step

theorem shortest_feature_constant_bound {U : ConditionalAlgorithm}
    {feature universal source : BinString} {overhead : Nat}
    (shortest : ShortestFeature U feature source)
    (works : UniversalFeatureWithConstant U universal overhead)
    (margin : plainConditionalComplexity U source [] + overhead < source.length) :
    feature.length ≤ universal.length :=
  shortest.2 universal (works source margin)

/-! ## Explicit bridge to the existing prefix-machine minimum -/

/-- Semantic embedding only. This does not assert that the Option-valued
machine is computable or provide a total halting decision. -/
def prefixAlgorithm (U : ConditionalPrefixFreeMachine) : ConditionalAlgorithm :=
  fun program condition => Part.ofOption (U.compute program condition)

theorem prefixAlgorithm_runs (U : ConditionalPrefixFreeMachine)
    (program condition output : BinString) :
    output ∈ prefixAlgorithm U program condition ↔ IsProgram U program condition output := by
  simp [prefixAlgorithm, IsProgram]

/-- The set-infimum and represented-output Nat.find definitions coincide.
The absent-output branch is handled explicitly, not mistaken for a zero-bit
program producing that output. -/
theorem prefix_complexity_agrees (U : ConditionalPrefixFreeMachine)
    (output condition : BinString) :
    plainConditionalComplexity (prefixAlgorithm U) output condition = conditionalComplexity U output condition := by
  by_cases represented : HasProgram U condition output
  · obtain ⟨p, produces, minimal⟩ := exists_program_of_conditionalComplexity U condition output represented
    have first := plainConditionalComplexity_le_of_program (prefixAlgorithm U) condition output p
      ((prefixAlgorithm_runs U p condition output).mpr produces)
    obtain ⟨q, computes, shortest⟩ := exists_program_of_plainConditionalComplexity (prefixAlgorithm U)
      condition output ⟨p, (prefixAlgorithm_runs U p condition output).mpr produces⟩
    have second := conditionalComplexity_le_program_length U condition output q
      ((prefixAlgorithm_runs U q condition output).mp computes)
    omega
  · rw [conditionalComplexity_eq_zero_of_not_hasProgram U condition output represented]
    have empty : conditionalPlainLengthsFor (prefixAlgorithm U) condition output = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro n ⟨program, produces, _⟩
      exact represented ⟨program, (prefixAlgorithm_runs U program condition output).mp produces⟩
    simp [plainConditionalComplexity, empty]

/-- Paper Lemma 3.1 in the prefix notation used by the existing foundation.
This uses real shortest-feature/map hypotheses; successful practical search
does not manufacture them. -/
theorem shortest_maps_prefix (U : ConditionalPrefixFreeMachine)
    {feature descriptive source : BinString}
    (shortestFeature : ShortestFeature (prefixAlgorithm U) feature source)
    (shortestDescriptive : ShortestDescriptiveMap (prefixAlgorithm U) feature descriptive source) :
    ∃ residual, IsProgram U descriptive source residual ∧ IsProgram U feature residual source ∧
      feature.length = conditionalComplexity U source residual ∧
      descriptive.length = conditionalComplexity U residual source := by
  obtain ⟨residual, extracts, reconstructs, first, second⟩ :=
    shortest_maps_conditional shortestFeature shortestDescriptive
  exact ⟨residual, (prefixAlgorithm_runs _ _ _ _).mp extracts,
    (prefixAlgorithm_runs _ _ _ _).mp reconstructs,
    first.trans (prefix_complexity_agrees _ _ _), second.trans (prefix_complexity_agrees _ _ _)⟩

example : Feature finiteCompressionAlgorithm [false] fourTrue := step_feature finiteCompressionStep

/-- Exact reconstruction alone does not create a feature. -/
example : ¬ Feature (fun _ condition => Part.some condition) [] fourTrue := by
  rintro ⟨descriptive, residual, extracts, _, smaller⟩
  have same : residual = fourTrue := by simpa using extracts
  simp [same] at smaller

private def paddedAlgorithm : ConditionalAlgorithm := fun program condition =>
  if (program = [false] ∨ program = [false, false]) ∧ condition = [] then Part.some fourTrue
  else if program = [true] ∧ condition = fourTrue then Part.some []
  else Part.none

private def paddedStep : CompressionStep paddedAlgorithm fourTrue where
  featureProgram := [false, false]
  descriptiveProgram := [true]
  residual := []
  extracts := by simp [paddedAlgorithm, fourTrue]
  reconstructs := by simp [paddedAlgorithm]
  compresses := by simp [fourTrue]

/-- A successful strict compression step need not use a shortest feature. -/
theorem strict_step_not_necessarily_shortest :
    ∃ (U : ConditionalAlgorithm) (source : BinString) (step : CompressionStep U source),
      ¬ ShortestFeature U step.featureProgram source := by
  refine ⟨paddedAlgorithm, fourTrue, paddedStep, ?_⟩
  intro shortest
  have competitor : Feature paddedAlgorithm [false] fourTrue := by
    refine ⟨[true], [], ?_, ?_, ?_⟩ <;> simp [paddedAlgorithm, fourTrue]
  have impossible := shortest.2 [false] competitor
  simp [paddedStep] at impossible

end KolmogorovComplexity.FeatureTheory
