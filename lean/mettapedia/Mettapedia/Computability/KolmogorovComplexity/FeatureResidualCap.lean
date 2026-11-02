import Mettapedia.Computability.KolmogorovComplexity.FeatureConstrainedSearch
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Finite residual caps and real compression factors

A real compression factor is a mathematical observation, not an executable
comparison oracle. Its constraint on natural residual lengths is exactly a
finite natural cap. Algorithms receive that cap as explicit data.
-/

set_option autoImplicit false

namespace KolmogorovComplexity.FeatureTheory

open scoped Classical

noncomputable def residualCap (factor : ℝ) (source : BinString) : Nat :=
  ⌊(source.length : ℝ) / factor⌋₊

theorem residualCap_iff {factor : ℝ} (positive : 0 < factor)
    (source residual : BinString) :
    residual.length ≤ residualCap factor source ↔
      factor * residual.length ≤ source.length := by
  rw [residualCap, Nat.le_floor_iff (div_nonneg (Nat.cast_nonneg _) positive.le),
    le_div_iff₀ positive]
  rw [mul_comm]

theorem residualCap_le_length {factor : ℝ} (large : 1 ≤ factor) (source : BinString) :
    residualCap factor source ≤ source.length := by
  have positive : 0 < factor := lt_of_lt_of_le zero_lt_one large
  have floored := Nat.floor_le (div_nonneg (Nat.cast_nonneg source.length) positive.le)
  have bounded : (source.length : ℝ) / factor ≤ source.length := by
    apply (div_le_iff₀ positive).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) source.length]
  exact_mod_cast floored.trans bounded

def cappedResidualGuard (cap : Nat) : ResidualGuard :=
  fun input => decide (input.2.length ≤ cap)

theorem cappedResidualGuard_primrec (cap : Nat) : Primrec (cappedResidualGuard cap) :=
  (Primrec.nat_le.comp (Primrec.list_length.comp Primrec.snd) (Primrec.const cap)).decide

theorem capped_guarded_map_iff {factor : ℝ} (positive : 0 < factor)
    (U : ConditionalAlgorithm) (feature descriptive source : BinString) :
    GuardedDescriptiveMap U (cappedResidualGuard (residualCap factor source))
      feature descriptive source ↔ BDescriptiveMap U factor feature descriptive source := by
  simp only [GuardedDescriptiveMap, BDescriptiveMap, cappedResidualGuard,
    decide_eq_true_eq, residualCap_iff positive]

theorem unit_b_descriptive_iff (U : ConditionalAlgorithm) (feature descriptive source : BinString) :
    BDescriptiveMap U 1 feature descriptive source ↔ DescriptiveMap U feature descriptive source := by
  constructor
  · rintro ⟨residual, extracts, reconstructs, smaller, _ratio⟩
    exact ⟨residual, extracts, reconstructs, smaller⟩
  · rintro ⟨residual, extracts, reconstructs, smaller⟩
    refine ⟨residual, extracts, reconstructs, smaller, ?_⟩
    norm_num only [one_mul]
    exact_mod_cast (show residual.length ≤ source.length by omega)

theorem unit_b_feature_iff (U : ConditionalAlgorithm) (feature source : BinString) :
    BFeature U 1 feature source ↔ Feature U feature source := by
  simp only [BFeature, Feature, unit_b_descriptive_iff]

theorem unit_shortest_b_feature_iff (U : ConditionalAlgorithm) (feature source : BinString) :
    ShortestBFeature U 1 feature source ↔ ShortestFeature U feature source := by
  simp only [ShortestBFeature, ShortestFeature, unit_b_feature_iff]

theorem unit_shortest_b_descriptive_iff (U : ConditionalAlgorithm) (feature descriptive source : BinString) :
    ShortestBDescriptiveMap U 1 feature descriptive source ↔ ShortestDescriptiveMap U feature descriptive source := by
  simp only [ShortestBDescriptiveMap, ShortestDescriptiveMap, unit_b_descriptive_iff]

/-- The compiler fixes a suffix and executes the concatenation of the
residual prefix and that suffix as a source description. -/
def splitDescriptionApplication (U : ConditionalAlgorithm) : ConditionalAlgorithm :=
  fun suffix initial => U (initial ++ suffix) []

theorem splitDescriptionApplication_partrec {U : ConditionalAlgorithm} (effective : Partrec₂ U) :
    Partrec₂ (splitDescriptionApplication U) :=
  (effective.comp (Primrec.list_append.comp Primrec.snd Primrec.fst).to_comp
    (Computable.const [])).to₂

/-- A single actual compiler realizes every split, including empty parts.
The residual's width and every compiler bit remain explicit. -/
theorem split_description_compiler (U : ConditionalAlgorithm)
    (universal : IsUniversalConditional U) (effective : Partrec₂ U) :
    ∃ compiler : BinString, ∀ description source cap,
      source ∈ U description [] → cap ≤ description.length →
      source ∈ U (compiler ++ description.drop cap) (description.take cap) ∧
        (compiler ++ description.drop cap).length = compiler.length + description.length - cap ∧
        (description.take cap).length = cap := by
  obtain ⟨compiler, compiles⟩ := universal (splitDescriptionApplication U)
    (splitDescriptionApplication_partrec effective)
  refine ⟨compiler, fun description source cap computes width => ?_⟩
  have run : source ∈ splitDescriptionApplication U (description.drop cap) (description.take cap) := by
    simpa only [splitDescriptionApplication, List.take_append_drop] using computes
  exact ⟨compiles _ _ _ run, by simp only [List.length_append, List.length_drop]; omega,
    by simp only [List.length_take, Nat.min_eq_left width]⟩

/-- The split description supplies a real competing b-feature, not merely
a reconstruction program. A source-specific extractor exists by universality. -/
theorem split_description_b_feature {U : ConditionalAlgorithm}
    (universal : IsUniversalConditional U) {factor : ℝ} (positive : 0 < factor)
    {compiler description source : BinString}
    (compiles : ∀ description source cap,
      source ∈ U description [] → cap ≤ description.length →
      source ∈ U (compiler ++ description.drop cap) (description.take cap) ∧
        (compiler ++ description.drop cap).length = compiler.length + description.length - cap ∧
        (description.take cap).length = cap)
    (computes : source ∈ U description [])
    (width : residualCap factor source ≤ description.length)
    (saving : compiler.length + description.length < source.length) :
    BFeature U factor (compiler ++ description.drop (residualCap factor source)) source := by
  obtain ⟨reconstructs, length, residualLength⟩ := compiles description source _ computes width
  obtain ⟨extractor, extracts⟩ := universalConditional_hasProgram U universal source
    (description.take (residualCap factor source))
  refine ⟨extractor, description.take (residualCap factor source), extracts, reconstructs, ?_, ?_⟩
  · rw [length, residualLength]
    omega
  · exact (residualCap_iff positive source _).mp (by rw [residualLength])

#print axioms residualCap_iff
#print axioms residualCap_le_length
#print axioms cappedResidualGuard_primrec
#print axioms capped_guarded_map_iff
#print axioms unit_b_descriptive_iff
#print axioms unit_b_feature_iff
#print axioms unit_shortest_b_feature_iff
#print axioms unit_shortest_b_descriptive_iff
#print axioms splitDescriptionApplication_partrec
#print axioms split_description_compiler
#print axioms split_description_b_feature

end KolmogorovComplexity.FeatureTheory
