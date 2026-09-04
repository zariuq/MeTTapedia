import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryExposureClosure
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryProviderExposure

/-! LAB: is B's ApplyRoute vacuous at the Name fibre?
    PREDICTION: yes — no_structural_apply_at_rhoName gives False from the
    partner's own non-staticness, with no other hypothesis needed. -/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.GSLT.LanguageDef Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

example {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {label : String} {arguments : List Pattern} {color : CostStaticColor}
    (other : CostRegionTree rhoCIGSLT targetFree available outer
      (.apply label arguments)
      (.base (color.mapLangSort rhoCIGSLT rhoName).1))
    (structural : other.rootIsStatic = false) : False :=
  CostHereditaryExposureClosure.no_structural_apply_at_rhoName other structural

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
