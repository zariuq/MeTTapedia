import Mettapedia.Computability.KolmogorovComplexity.FeatureInformation
import Mettapedia.Computability.KolmogorovComplexity.FeatureBPredicates
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Features with a prescribed residual-compression ratio

The b-feature condition retains both strict feature-plus-residual saving and
the additional bound `b * |residual| ≤ |source|`. Real factors include the
paper's full range `b > 1`; natural program lengths remain exact.

The source complexity is the stated conditional interpreter's minimum at the
empty condition. Its universal feature uses precisely such a shortest source
description as residual. Prefix-reference information remains a separately
proved comparison, not a change of the source interpreter.
-/

set_option autoImplicit false

namespace KolmogorovComplexity.FeatureTheory

open scoped Classical

theorem BFeature.feature {U : ConditionalAlgorithm} {factor : ℝ} {feature source : BinString}
    (present : BFeature U factor feature source) : Feature U feature source := by
  obtain ⟨descriptive, residual, extracts, reconstructs, smaller, _⟩ := present
  exact ⟨descriptive, residual, extracts, reconstructs, smaller⟩

theorem exists_shortest_b_feature (U : ConditionalAlgorithm) (factor : ℝ) (source : BinString)
    (present : ∃ feature, BFeature U factor feature source) :
    ∃ feature, ShortestBFeature U factor feature source := by
  let lengths : Set Nat := {n | ∃ feature, BFeature U factor feature source ∧ feature.length = n}
  have inhabited : lengths.Nonempty := by
    obtain ⟨feature, admitted⟩ := present
    exact ⟨feature.length, feature, admitted, rfl⟩
  obtain ⟨feature, admitted, minimal⟩ := Nat.sInf_mem inhabited
  refine ⟨feature, admitted, fun other otherAdmitted => ?_⟩
  rw [minimal]
  exact Nat.sInf_le ⟨other, otherAdmitted, rfl⟩

theorem exists_shortest_b_descriptive (U : ConditionalAlgorithm) (factor : ℝ) (feature source : BinString)
    (present : BFeature U factor feature source) :
    ∃ descriptive, ShortestBDescriptiveMap U factor feature descriptive source := by
  let lengths : Set Nat :=
    {n | ∃ descriptive, BDescriptiveMap U factor feature descriptive source ∧ descriptive.length = n}
  have inhabited : lengths.Nonempty := by
    obtain ⟨descriptive, admitted⟩ := present
    exact ⟨descriptive.length, descriptive, admitted, rfl⟩
  obtain ⟨descriptive, admitted, minimal⟩ := Nat.sInf_mem inhabited
  refine ⟨descriptive, admitted, fun other otherAdmitted => ?_⟩
  rw [minimal]
  exact Nat.sInf_le ⟨other, otherAdmitted, rfl⟩

/-- The same residual still meets the ratio bound after replacing a
reconstruction program by a shorter one. -/
theorem shortest_b_feature_conditional {U : ConditionalAlgorithm} {factor : ℝ}
    {feature descriptive source residual : BinString}
    (minimal : ShortestBFeature U factor feature source)
    (extracts : residual ∈ U descriptive source) (reconstructs : source ∈ U feature residual)
    (smaller : feature.length + residual.length < source.length)
    (ratio : factor * residual.length ≤ source.length) :
    feature.length = plainConditionalComplexity U source residual := by
  have upper := plainConditionalComplexity_le_of_program U residual source feature reconstructs
  obtain ⟨program, runs, length⟩ := exists_program_of_plainConditionalComplexity U residual source ⟨feature, reconstructs⟩
  have competitor : BFeature U factor program source :=
    ⟨descriptive, residual, extracts, runs, by omega, ratio⟩
  have lower := minimal.2 program competitor
  omega

theorem shortest_b_descriptive_conditional {U : ConditionalAlgorithm} {factor : ℝ}
    {feature descriptive source residual : BinString}
    (minimal : ShortestBDescriptiveMap U factor feature descriptive source)
    (extracts : residual ∈ U descriptive source) (reconstructs : source ∈ U feature residual)
    (smaller : feature.length + residual.length < source.length)
    (ratio : factor * residual.length ≤ source.length) :
    descriptive.length = plainConditionalComplexity U residual source := by
  have upper := plainConditionalComplexity_le_of_program U source residual descriptive extracts
  obtain ⟨program, runs, length⟩ := exists_program_of_plainConditionalComplexity U source residual ⟨descriptive, extracts⟩
  have competitor : BDescriptiveMap U factor feature program source :=
    ⟨residual, runs, reconstructs, smaller, ratio⟩
  have lower := minimal.2 program competitor
  omega

/-- The actual output of a minimum ratio-restricted map retains the ratio
of its existential witness, by determinacy of the partial interpreter. -/
theorem shortest_b_descriptive_actual_output {U : ConditionalAlgorithm} {factor : ℝ}
    {feature descriptive source residual : BinString}
    (minimum : ShortestBDescriptiveMap U factor feature descriptive source)
    (selected : residual ∈ U descriptive source) :
    source ∈ U feature residual ∧ feature.length + residual.length < source.length ∧
      factor * residual.length ≤ source.length ∧
      descriptive.length = plainConditionalComplexity U residual source := by
  obtain ⟨witness, extracts, reconstructs, smaller, ratio⟩ := minimum.1
  have same : witness = residual := Part.mem_unique extracts selected
  subst witness
  exact ⟨reconstructs, smaller, ratio,
    shortest_b_descriptive_conditional minimum selected reconstructs smaller ratio⟩

theorem shortest_b_maps_conditional {U : ConditionalAlgorithm} {factor : ℝ}
    {feature descriptive source : BinString}
    (minimalFeature : ShortestBFeature U factor feature source)
    (minimalDescriptive : ShortestBDescriptiveMap U factor feature descriptive source) :
    ∃ residual, residual ∈ U descriptive source ∧ source ∈ U feature residual ∧
      factor * residual.length ≤ source.length ∧
      feature.length = plainConditionalComplexity U source residual ∧
      descriptive.length = plainConditionalComplexity U residual source := by
  obtain ⟨residual, extracts, reconstructs, smaller, ratio⟩ := minimalDescriptive.1
  exact ⟨residual, extracts, reconstructs, ratio,
    shortest_b_feature_conditional minimalFeature extracts reconstructs smaller ratio,
    shortest_b_descriptive_conditional minimalDescriptive extracts reconstructs smaller ratio⟩

theorem singleton_b_feature (U : ConditionalAlgorithm) (universal : IsUniversalConditional U)
    (factor : ℝ) (source : BinString)
    (compressible : plainConditionalComplexity U source [] < source.length) :
    ∃ feature, BFeature U factor feature source ∧ feature.length = plainConditionalComplexity U source [] := by
  obtain ⟨step, residual, length⟩ := singleton_of_compressible U universal source compressible
  refine ⟨step.featureProgram, ⟨step.descriptiveProgram, step.residual, step.extracts,
    step.reconstructs, step.compresses, ?_⟩, length⟩
  simp [residual]

/-- IC Theorem 3.7: one universal feature and its length constant are fixed
before the ratio or source is selected. The exact threshold and both kinds
of shortest-feature bounds are retained. -/
theorem b_compressible_feature_bound (U : ConditionalAlgorithm)
    (universal : IsUniversalConditional U) (effective : Partrec₂ U) :
    ∃ universalFeature : BinString, ∀ (factor : ℝ), 1 < factor → ∀ source,
      factor * plainConditionalComplexity U source [] ≤ source.length →
      (((universalFeature.length : ℝ) * factor < (factor - 1) * source.length) →
        BFeature U factor universalFeature source) ∧
      (∀ feature, ShortestFeature U feature source →
        (feature.length : ℝ) ≤ max (universalFeature.length : ℝ) (universalFeature.length / (factor - 1))) ∧
      (∀ feature, ShortestBFeature U factor feature source →
        (feature.length : ℝ) ≤ max (universalFeature.length : ℝ) (universalFeature.length / (factor - 1))) := by
  obtain ⟨fixed, works⟩ := exists_universal_feature U universal effective
  refine ⟨fixed, fun factor factorLarge source compression => ?_⟩
  have factorPositive : 0 < factor := by linarith
  have differencePositive : 0 < factor - 1 := by linarith
  have largeCase (large : (fixed.length : ℝ) * factor < (factor - 1) * source.length) :
      BFeature U factor fixed source := by
    have marginReal : (plainConditionalComplexity U source [] : ℝ) + fixed.length < source.length := by
      nlinarith
    have margin : plainConditionalComplexity U source [] + fixed.length < source.length := by exact_mod_cast marginReal
    obtain ⟨step, same, residualLength⟩ := works source margin
    refine ⟨step.descriptiveProgram, step.residual, step.extracts, ?_, ?_, ?_⟩
    · simpa only [same] using step.reconstructs
    · simpa only [same] using step.compresses
    · simpa only [residualLength] using compression
  have smallBound (small : ¬ (fixed.length : ℝ) * factor < (factor - 1) * source.length) :
      (plainConditionalComplexity U source [] : ℝ) ≤ fixed.length / (factor - 1) := by
    apply (le_div_iff₀ differencePositive).mpr
    have scaled := mul_le_mul_of_nonneg_left compression (le_of_lt differencePositive)
    have smallLe := le_of_not_gt small
    nlinarith
  refine ⟨largeCase, ?_, ?_⟩
  · intro feature minimal
    by_cases large : (fixed.length : ℝ) * factor < (factor - 1) * source.length
    · have bounded := minimal.2 fixed (largeCase large).feature
      exact le_trans (show (feature.length : ℝ) ≤ fixed.length by exact_mod_cast bounded) (le_max_left _ _)
    · obtain ⟨descriptive, residual, _, _, smaller⟩ := minimal.1
      have sourcePositive : 0 < (source.length : ℝ) := by exact_mod_cast (show 0 < source.length by omega)
      have compressibleReal : (plainConditionalComplexity U source [] : ℝ) < source.length := by nlinarith
      have compressible : plainConditionalComplexity U source [] < source.length := by exact_mod_cast compressibleReal
      have bounded := shortest_feature_le_unconditional U universal feature source minimal compressible
      exact le_trans (show (feature.length : ℝ) ≤ plainConditionalComplexity U source [] by exact_mod_cast bounded)
        ((smallBound large).trans (le_max_right _ _))
  · intro feature minimal
    by_cases large : (fixed.length : ℝ) * factor < (factor - 1) * source.length
    · have bounded := minimal.2 fixed (largeCase large)
      exact le_trans (show (feature.length : ℝ) ≤ fixed.length by exact_mod_cast bounded) (le_max_left _ _)
    · obtain ⟨descriptive, residual, _, _, smaller, _⟩ := minimal.1
      have sourcePositive : 0 < (source.length : ℝ) := by exact_mod_cast (show 0 < source.length by omega)
      have compressibleReal : (plainConditionalComplexity U source [] : ℝ) < source.length := by nlinarith
      have compressible : plainConditionalComplexity U source [] < source.length := by exact_mod_cast compressibleReal
      obtain ⟨single, admitted, length⟩ := singleton_b_feature U universal factor source compressible
      have bounded := minimal.2 single admitted
      rw [length] at bounded
      exact le_trans (show (feature.length : ℝ) ≤ plainConditionalComplexity U source [] by exact_mod_cast bounded)
        ((smallBound large).trans (le_max_right _ _))

#print axioms shortest_b_feature_conditional
#print axioms shortest_b_descriptive_conditional
#print axioms shortest_b_descriptive_actual_output
#print axioms singleton_b_feature
#print axioms b_compressible_feature_bound

end KolmogorovComplexity.FeatureTheory
