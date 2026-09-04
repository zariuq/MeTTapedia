import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryProviderBuilt
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryExposureClosure

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

theorem decode_drop (color : CostStaticColor) :
    decodeCostStaticConstructor color
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl).dropConstructor =
      some "PDrop" := by
  cases color <;> decide

theorem decode_quote (color : CostStaticColor) :
    decodeCostStaticConstructor color
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl).quoteConstructor =
      some "NQuote" := by
  cases color <;> decide

theorem decode_parallelUnit (color : CostStaticColor) :
    decodeCostStaticConstructor color
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl).parallelUnitConstructor =
      some "PZero" := by
  cases color <;> decide

theorem decodeDeclared_drop (color : CostStaticColor) :
    decodeDeclaredCostStaticConstructor rhoCIGSLT color
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl).dropConstructor =
      some "PDrop" := by
  cases color <;> decide

theorem decodeDeclared_quote (color : CostStaticColor) :
    decodeDeclaredCostStaticConstructor rhoCIGSLT color
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl).quoteConstructor =
      some "NQuote" := by
  cases color <;> decide
