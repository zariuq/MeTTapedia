import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostCanonicalReachableDomain
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryCanonical

/-! Strict descent for canonical rho pairs with colour-specific presentations. -/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

/-- The provider's strictly-smaller recursion callback, named once so the
obligations below can carry it without restating the telescope.

Threading it is not a convenience.  Withholding it makes an obligation
strictly stronger than its call site requires, and in one case fatally so:
`RhoCollapsingLeafExposure` pins the partner's normal form to the collapsed
node's (`RhoCollapsingLeafExposure.normalize_eq`), so a callback-free exposure
obligation *is* mixed-pair hereditary-normalization soundness — the very thing
the cost layer seal exists to establish.  Every producer in the tree whose partner
pattern is unconstrained takes this callback; the ones that do not, pin the
partner to a variable or demand a pre-built normalization alignment. -/
def RhoPairCloseSmaller (declarationColor : CostStaticColor)
    (targetFree : FreeTypeContext) (parentMeasure : Nat) : Prop :=
  CostCanonicalPairElaboration.CloseBelow rhoCanonicalRecursiveTypeDomain
    rhoHereditaryNormalizationKernel
    (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
      rhoReflectivePresentation.toReflectivePresentationDecl)
    targetFree parentMeasure

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
