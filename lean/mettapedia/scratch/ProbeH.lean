import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryForeignBoundaryWitness
namespace ProbeH
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
def nameT : TypeExpr := .base (costBaseSortName "Name")
def bProc : TypeExpr := .base (costBaseSortName "Proc")
-- THE LEFT WITNESS PATTERN
def leftW : Pattern := .apply (costBaseConstructorName "PDrop")
  [.apply (costWrappedConstructorName "NQuote")
    [.apply (costWrappedConstructorName "PDrop") [.bvar 0]]]
-- THE RIGHT WITNESS PATTERN
def rightW : Pattern := .apply (costBaseConstructorName "PDrop") [.bvar 0]
#eval! ReflectiveWellSorted.checkOpenPatternWellSorted
  rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
  FreeTypeContext.empty [nameT] bProc leftW
#eval! ReflectiveWellSorted.checkOpenPatternWellSorted
  rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
  FreeTypeContext.empty [nameT] bProc rightW
-- and with a CLOSED quote body (no ambient binder) the left analogue is fine:
def leftClosed : Pattern := .apply (costBaseConstructorName "PDrop")
  [.apply (costWrappedConstructorName "NQuote")
    [.apply (costWrappedConstructorName "PZero") []]]
#eval! ReflectiveWellSorted.checkOpenPatternWellSorted
  rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
  FreeTypeContext.empty [nameT] bProc leftClosed
end ProbeH
