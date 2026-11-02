import Mettapedia.Computability.KolmogorovComplexity.FeaturePredicates
import Mathlib.Data.Real.Basic

/-!
# Residual-bounded feature predicates

The real factor describes the mathematical constraint on natural word lengths.
This interface makes no assumption that comparison with the factor is an
effective operation, and does not identify restricted and unrestricted minima.
-/

set_option autoImplicit false

namespace KolmogorovComplexity.FeatureTheory

def BDescriptiveMap (U : ConditionalAlgorithm) (factor : ℝ)
    (feature descriptive source : List Bool) : Prop :=
  ∃ residual, residual ∈ U descriptive source ∧ source ∈ U feature residual ∧
    feature.length + residual.length < source.length ∧ factor * residual.length ≤ source.length

def BFeature (U : ConditionalAlgorithm) (factor : ℝ) (feature source : List Bool) : Prop :=
  ∃ descriptive, BDescriptiveMap U factor feature descriptive source

def ShortestBFeature (U : ConditionalAlgorithm) (factor : ℝ) (feature source : List Bool) : Prop :=
  BFeature U factor feature source ∧ ∀ other, BFeature U factor other source → feature.length ≤ other.length

def ShortestBDescriptiveMap (U : ConditionalAlgorithm) (factor : ℝ)
    (feature descriptive source : List Bool) : Prop :=
  BDescriptiveMap U factor feature descriptive source ∧
    ∀ other, BDescriptiveMap U factor feature other source → descriptive.length ≤ other.length

end KolmogorovComplexity.FeatureTheory
