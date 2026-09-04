import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryParallelFrontier

/-!
# Foreign rigid-tie typing canary

The tempting depth-sensitive parallel witness places an ambient bound process
below an authored quotation.  The full reflective well-sortedness premise
rejects that shape: quotation resets reflective availability before the bound
variable is checked.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus
namespace ForeignRigidTieTypingCanary

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

def processType : TypeExpr := .base (costBaseSortName "Proc")
def available : List TypeExpr := [processType]

def foreignQuote : Pattern :=
  .apply (costBaseConstructorName "NQuote") [.bvar 0]

def selectedShell : Pattern :=
  .apply (costWrappedConstructorName "NQuote")
    [.apply (costWrappedConstructorName "PDrop") [foreignQuote]]

def boundaryLeaf : Pattern :=
  .apply (costBaseConstructorName "PDrop") [selectedShell]

def rigidLeaf : Pattern :=
  .apply (costBaseConstructorName "PDrop") [foreignQuote]

def leftPattern : Pattern :=
  .collection .hashBag [boundaryLeaf, rigidLeaf] none

/-- The proposed exposed-boundary/rigid tie is not in the Cost domain. -/
theorem not_leftWellSorted :
    ¬ ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      FreeTypeContext.empty available processType leftPattern := by
  intro wellSorted
  have safe := wellSorted.2
    (costStaticReflectivePresentationDecl rhoCIGSLT .base
      rhoReflectivePresentation.toReflectivePresentationDecl)
    (by
      rw [CIGSLT.costWholeReflectionProfile_presentations]
      change
        costStaticReflectivePresentationDecl rhoCIGSLT .base
            rhoReflectivePresentation.toReflectivePresentationDecl ∈
          [costStaticReflectivePresentationDecl rhoCIGSLT .base
              rhoReflectivePresentation.toReflectivePresentationDecl,
            costStaticReflectivePresentationDecl rhoCIGSLT .wrapped
              rhoReflectivePresentation.toReflectivePresentationDecl]
      simp)
  simp [leftPattern, boundaryLeaf, rigidLeaf, selectedShell, foreignQuote,
    available, binderSafeAt, binderSafeListAt,
    CostStaticColor.reflectiveSymbols, costBaseStaticReflectiveSymbols,
    costBaseStaticSymbols, costBasePresentationSymbols,
    ReflectionExtension.mapReflectivePresentation,
    rhoReflectivePresentation] at safe

end ForeignRigidTieTypingCanary
end Mettapedia.Languages.ProcessCalculi.RhoCalculus
