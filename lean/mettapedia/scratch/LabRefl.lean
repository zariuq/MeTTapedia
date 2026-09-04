import Mettapedia.GSLT.LanguageDef.CostSemanticAtomReifyCongruence

namespace Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- PREDICTION: a reflexive relation makes every pattern leaf-aligned to
itself, via the `.leaf` arm. -/
theorem patternLeafAligned_refl {relation : Pattern → Pattern → Prop}
    (reflexive : ∀ pattern, relation pattern pattern) (pattern : Pattern) :
    PatternLeafAligned relation pattern pattern :=
  .leaf (reflexive pattern)

/-- Consequence: equal patterns are leaf-aligned under any reflexive
relation. -/
theorem patternLeafAligned_of_eq {relation : Pattern → Pattern → Prop}
    (reflexive : ∀ pattern, relation pattern pattern)
    {left right : Pattern} (equal : left = right) :
    PatternLeafAligned relation left right :=
  equal ▸ patternLeafAligned_refl reflexive left

end Mettapedia.GSLT.LanguageDef
