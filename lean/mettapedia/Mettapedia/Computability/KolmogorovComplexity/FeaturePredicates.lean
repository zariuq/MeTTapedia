import Mettapedia.Computability.KolmogorovComplexity.ConditionalProgramModel

/-!
# Feature predicates over the shared conditional-program model

Only the execution relation and physical word lengths enter these definitions.
They do not assume universality, prefix freeness or a particular program codec.
Minimum feature and minimum descriptive-map lengths are separate predicates.
-/

set_option autoImplicit false

namespace KolmogorovComplexity.FeatureTheory

def DescriptiveMap (U : ConditionalAlgorithm) (feature descriptive source : List Bool) : Prop :=
  ∃ residual, residual ∈ U descriptive source ∧ source ∈ U feature residual ∧
    feature.length + residual.length < source.length

def Feature (U : ConditionalAlgorithm) (feature source : List Bool) : Prop :=
  ∃ descriptive, DescriptiveMap U feature descriptive source

def ShortestFeature (U : ConditionalAlgorithm) (feature source : List Bool) : Prop :=
  Feature U feature source ∧ ∀ other, Feature U other source → feature.length ≤ other.length

def ShortestDescriptiveMap (U : ConditionalAlgorithm)
    (feature descriptive source : List Bool) : Prop :=
  DescriptiveMap U feature descriptive source ∧
    ∀ other, DescriptiveMap U feature other source → descriptive.length ≤ other.length

end KolmogorovComplexity.FeatureTheory
