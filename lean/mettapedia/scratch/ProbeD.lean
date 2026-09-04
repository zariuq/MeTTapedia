import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryLeafDichotomyProbe
namespace ProbeD
open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

-- Is the Name sort shared across the two static colours?
theorem name_shared :
    mapTypeExpr (CostStaticColor.base.symbols rhoCIGSLT) (.base "Name") =
    mapTypeExpr (CostStaticColor.wrapped.symbols rhoCIGSLT) (.base "Name") := by
  decide

-- Is the Proc sort shared?  (expected: NO)
theorem proc_not_shared :
    mapTypeExpr (CostStaticColor.base.symbols rhoCIGSLT) (.base "Proc") ≠
    mapTypeExpr (CostStaticColor.wrapped.symbols rhoCIGSLT) (.base "Proc") := by
  decide

end ProbeD
