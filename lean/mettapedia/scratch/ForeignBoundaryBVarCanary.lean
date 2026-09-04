import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryBoundarySideCell

/-!
# Foreign-declaration boundary/bvar canary

This fixture tests the tempting foreign boundary/bound-variable obstruction.
The wrapped declaration collapses the selected Quote/Drop, but reflective
scope safety rejects the left source before any static plan can be built.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus
namespace ForeignBoundaryBVarCanary

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

def nameType : TypeExpr := .base (costBaseSortName "Name")

def available : List TypeExpr := [nameType]

def wrappedDeclaration : ReflectivePresentationDecl :=
  costStaticReflectivePresentationDecl rhoCIGSLT .wrapped
    rhoReflectivePresentation.toReflectivePresentationDecl

def wrappedQuoteDropBVar : Pattern :=
  .apply (costWrappedConstructorName "NQuote")
    [.apply (costWrappedConstructorName "PDrop") [.bvar 0]]

def leftPattern : Pattern :=
  .apply (costBaseConstructorName "NQuote")
    [.apply (costBaseConstructorName "PDrop") [wrappedQuoteDropBVar]]

def rightPattern : Pattern :=
  .apply (costBaseConstructorName "NQuote")
    [.apply (costBaseConstructorName "PDrop") [.bvar 0]]

theorem wrappedQuoteDropBVar_not_checked :
    ReflectiveWellSorted.checkOpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      FreeTypeContext.empty available nameType wrappedQuoteDropBVar = false := by
  decide

theorem leftPattern_not_checked :
    ReflectiveWellSorted.checkOpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      FreeTypeContext.empty available nameType leftPattern = false := by
  decide

theorem rightPattern_not_checked :
    ReflectiveWellSorted.checkOpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      FreeTypeContext.empty available nameType rightPattern = false := by
  decide

theorem foreignCanonical :
    canonicalize wrappedDeclaration leftPattern =
      canonicalize wrappedDeclaration rightPattern := by
  decide

end ForeignBoundaryBVarCanary
end Mettapedia.Languages.ProcessCalculi.RhoCalculus
