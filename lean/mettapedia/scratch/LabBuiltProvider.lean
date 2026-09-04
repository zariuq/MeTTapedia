import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryProviderBuilt

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.GSLT.LanguageDef Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

example (declarationColor : CostStaticColor) :
    RhoCanonicalStaticPairSemanticCutProviderInDomainBuilt declarationColor := by
  intro targetFree available outer leftPattern rightPattern type admissible
    leftWellSorted rightWellSorted canonical staticShape closeSmaller rootCase
  cases rootCase with
  | aligned color leftView rightView roots => skip
  | leftCollapsing leftColor leftView collapsing => skip
  | rightCollapsing rightColor rightView collapsing => skip

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
