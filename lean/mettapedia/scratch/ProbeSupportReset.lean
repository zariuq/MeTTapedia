import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryProviderBuilt
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryExposureClosure

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

/-- The authored rho quotation is a quote constructor of the reflection. -/
theorem rho_isQuoteConstructor_NQuote :
    ReflectiveContextSupport.isQuoteConstructor rhoCIGSLT.reflection.1 "NQuote"
      = true := by decide

/-- and the drop is not. -/
theorem rho_isQuoteConstructor_PDrop :
    ReflectiveContextSupport.isQuoteConstructor rhoCIGSLT.reflection.1 "PDrop"
      = false := by decide
