import Mettapedia.GSLT.LanguageDef.CostCanonicalSection
import Mettapedia.GSLT.LanguageDef.CostRegionTree

namespace Mettapedia.GSLT.LanguageDef

/-- PROBE: two preimages of one declared constructor share a source label. -/
theorem CostStaticConstructorPreimage.sourceLabel_eq {source : CIGSLT}
    {color : CostStaticColor} {constructor : source.DeclaredCostConstructor}
    (first second : CostStaticConstructorPreimage source color constructor) :
    first.sourceConstructor.1.label = second.sourceConstructor.1.label :=
  CostStaticColor.symbols_constructor_injective source color
    (first.labelMap.symm.trans second.labelMap)

end Mettapedia.GSLT.LanguageDef
