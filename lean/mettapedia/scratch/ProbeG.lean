import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryLeafDichotomyProbe
namespace ProbeG
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

def nameT : TypeExpr := .base (costBaseSortName "Name")
def w : Pattern := .apply (costWrappedConstructorName "NQuote")
    [.apply (costWrappedConstructorName "PDrop") [.bvar 0]]
def b : Pattern := .apply (costBaseConstructorName "NQuote")
    [.apply (costBaseConstructorName "PDrop") [.bvar 0]]

-- which conjunct fails?  (checkHasType, binderMetadata, objectPattern, scopeSafe)
#eval! (checkHasType rhoCIGSLT.costWholeLanguage FreeTypeContext.empty [nameT] w nameT,
        w.hasCanonicalBinderMetadata, isObjectPattern w, checkScopeSafeAt 1 w)
#eval! (checkHasType rhoCIGSLT.costWholeLanguage FreeTypeContext.empty [nameT] b nameT,
        b.hasCanonicalBinderMetadata, isObjectPattern b, checkScopeSafeAt 1 b)
-- does the SAME body typecheck when the bvar is replaced by a free variable?
def wf : Pattern := .apply (costWrappedConstructorName "NQuote")
    [.apply (costWrappedConstructorName "PDrop") [.fvar "x"]]
#eval! checkHasType rhoCIGSLT.costWholeLanguage
    (FreeTypeContext.ofList [("x", nameT)]) [nameT] wf nameT
-- and with support [] but the quote body closed?
#eval! checkHasType rhoCIGSLT.costWholeLanguage FreeTypeContext.empty [nameT]
    (.apply (costWrappedConstructorName "NQuote")
      [.apply (costWrappedConstructorName "PZero") []]) nameT
end ProbeG
