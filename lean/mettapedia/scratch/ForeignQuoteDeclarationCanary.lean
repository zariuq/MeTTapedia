import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryMatchedFramesProvenancedAlignment

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef

/-- An authored Quote transported into a static colour is that colour's own
Quote constructor. -/
example (color : CostStaticColor) :
    (color.symbols rhoCIGSLT).constructor
        rhoReflectivePresentation.quoteConstructor =
      (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation).quoteConstructor := by
  simp [costStaticReflectivePresentationDecl_eq_map,
    Mettapedia.GSLT.LanguageDef.ReflectionExtension.mapReflectivePresentation]

/-- The same transported Quote is foreign only to the opposite declaration
used for the raw canonical stop. -/
example {declarationColor color : CostStaticColor}
    (foreign : declarationColor ≠ color) :
    (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation).quoteConstructor ≠
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation).quoteConstructor := by
  exact costStaticReflectivePresentationDecl_quoteConstructor_ne
    (Ne.symm foreign) _

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
