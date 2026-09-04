import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryLeafDichotomyProbe
namespace ProbeF
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

def nameT : TypeExpr := .base (costBaseSortName "Name")
def wProc : TypeExpr := .base costWrappedSortName
def bProc : TypeExpr := .base (costBaseSortName "Proc")
def chk (sup : List TypeExpr) (ty : TypeExpr) (p : Pattern) : Bool :=
  ReflectiveWellSorted.checkOpenPatternWellSorted
    rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
    FreeTypeContext.empty sup ty p

-- baseline: bare bvar at Name
#eval! chk [nameT] nameT (.bvar 0)
-- RIGHT pattern piece: base drop over the bvar, at base Proc
#eval! chk [nameT] bProc (.apply (costBaseConstructorName "PDrop") [.bvar 0])
-- wrapped drop over the bvar, at wrapped Proc
#eval! chk [nameT] wProc (.apply (costWrappedConstructorName "PDrop") [.bvar 0])
-- wrapped zero at wrapped Proc  (canary says NQuote_w(PZero_w) works)
#eval! chk [] wProc (.apply (costWrappedConstructorName "PZero") [])
-- wrapped quote over wrapped zero, at Name  (canary: TRUE)
#eval! chk [] nameT (.apply (costWrappedConstructorName "NQuote")
    [.apply (costWrappedConstructorName "PZero") []])
-- same but with a nonempty support
#eval! chk [nameT] nameT (.apply (costWrappedConstructorName "NQuote")
    [.apply (costWrappedConstructorName "PZero") []])
-- wrapped quote over wrapped drop over bvar, at Name  (the witness)
#eval! chk [nameT] nameT (.apply (costWrappedConstructorName "NQuote")
    [.apply (costWrappedConstructorName "PDrop") [.bvar 0]])
-- base quote over base drop over bvar, at Name (same-colour analogue)
#eval! chk [nameT] nameT (.apply (costBaseConstructorName "NQuote")
    [.apply (costBaseConstructorName "PDrop") [.bvar 0]])
end ProbeF
