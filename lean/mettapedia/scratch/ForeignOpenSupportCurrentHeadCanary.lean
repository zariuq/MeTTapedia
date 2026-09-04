import ForeignSupportMismatchCanary

/-!
# Open current-head foreign-boundary canary

This negative control tests the smallest shape that could make a semantic
atom imitate a current-colour structural application at one restoration depth
and diverge at another.  The foreign Quote/Drop shell would expose a current
name containing a bound variable, but reflective Quote safety must reject the
open payload.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus
namespace ForeignOpenSupportCurrentHeadCanary

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open ForeignSupportMismatchCanary

def openCurrentName : Pattern :=
  .apply (costBaseConstructorName "NQuote")
    [.apply (costBaseConstructorName "PDrop") [.bvar 0]]

def foreignQuoteDropShell : Pattern :=
  .apply (costWrappedConstructorName "NQuote")
    [.apply (costWrappedConstructorName "PDrop") [openCurrentName]]

def exposedProcess : Pattern :=
  .apply (costBaseConstructorName "PDrop") [foreignQuoteDropShell]

def structuralProcess : Pattern :=
  .apply (costBaseConstructorName "PDrop") [openCurrentName]

example :
    ReflectiveWellSorted.checkOpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      FreeTypeContext.empty available processType exposedProcess = false := by
  decide

example :
    ReflectiveWellSorted.checkOpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      FreeTypeContext.empty available processType structuralProcess = false := by
  decide

end ForeignOpenSupportCurrentHeadCanary
end Mettapedia.Languages.ProcessCalculi.RhoCalculus
