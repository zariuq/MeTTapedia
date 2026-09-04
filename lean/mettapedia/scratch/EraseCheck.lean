import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryProviderBuilt

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus
def proEraseConstructor (constructor : String) : String :=
  if constructor.startsWith costBaseConstructorTag then
    (constructor.drop costBaseConstructorTag.length).toString
  else if constructor.startsWith costWrappedConstructorTag then
    (constructor.drop costWrappedConstructorTag.length).toString
  else constructor

def proLeftPlus : String := ! proEraseConstructor (costWrappedConstructorName "NQuote")

#eval! proEraseConstructor (costWrappedConstructorName "NQuote")
#eval! (costWrappedConstructorName "NQuote").startsWith costWrappedConstructorTag
#eval! costWrappedConstructorTag.length
#eval! (costWrappedConstructorName "NQuote").length
#eval! ((costWrappedConstructorName "NQuote").drop costWrappedConstructorTag.length).toString
#eval! ((costWrappedConstructorName "NQuote") == "$cost:wrapped-constructor:NQuote")
#eval! (proEraseConstructor (costWrappedConstructorName "NQuote") == "NQuote")
theorem t1 : proEraseConstructor (costWrappedConstructorName "NQuote") = "NQuote" := by decide
theorem t2 : proEraseConstructor (costBaseConstructorName "NQuote") = "NQuote" := by decide
end Mettapedia.Languages.ProcessCalculi.RhoCalculus
