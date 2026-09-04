import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryLeafDichotomyProbe
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryRouteBreadthCanary

namespace ProbeE

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

/-- The shared rho name type. -/
def nameType : TypeExpr := .base (costBaseSortName "Name")

/-- One ambient name binder. -/
def support : List TypeExpr := [nameType]

/-- Foreign (wrapped) quote/drop over the ambient name binder. -/
def foreignQuoteContent : Pattern :=
  .apply (costWrappedConstructorName "NQuote")
    [.apply (costWrappedConstructorName "PDrop") [.bvar 0]]

-- THE DECISION POINT: does this typecheck at the shared Name sort?
#eval! ReflectiveWellSorted.checkOpenPatternWellSorted
  rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
  FreeTypeContext.empty support nameType foreignQuoteContent

end ProbeE
