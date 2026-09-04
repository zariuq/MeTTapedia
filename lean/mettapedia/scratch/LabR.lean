import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryProviderBuilt
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryCollapsingRestoration

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.GSLT.LanguageDef Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

example : RhoStaticViewPairRestorationAligned := by
  intro targetFree available outer leftPattern rightPattern type left right
    leftColor rightColor declarationColor leftView rightView canonical
  apply RhoStaticFramesRestorationAligned.ofFramesRestoreTogether

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
