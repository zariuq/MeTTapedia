import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryExposureClosure

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.GSLT.LanguageDef
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

/-- PREDICTION: sorts are colour-invariant, so colour-mixing is well-sorted. -/
example (color : CostStaticColor) :
    (color.mapLangSort rhoCIGSLT rhoProc).1 = costBaseSortName "Proc" := by
  cases color <;> rfl

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
