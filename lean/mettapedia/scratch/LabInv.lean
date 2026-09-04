import Mettapedia.GSLT.LanguageDef.CostSemanticAtomReifyCongruence

namespace Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- Two applications with different constructors can only be leaf-aligned. -/
theorem relation_of_patternLeafAligned_apply_apply_of_ne
    {relation : Pattern → Pattern → Prop}
    {leftConstructor rightConstructor : String}
    {leftArguments rightArguments : List Pattern}
    (different : leftConstructor ≠ rightConstructor)
    (aligned : PatternLeafAligned relation
      (.apply leftConstructor leftArguments)
      (.apply rightConstructor rightArguments)) :
    relation (.apply leftConstructor leftArguments)
      (.apply rightConstructor rightArguments) := by
  cases aligned with
  | leaf related => exact related
  | apply constructor arguments => exact absurd rfl different

end Mettapedia.GSLT.LanguageDef
