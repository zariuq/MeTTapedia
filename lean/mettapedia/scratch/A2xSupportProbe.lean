import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryCrossColorQuadrantCanary

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

namespace A2xSupportProbe

open CostHereditaryProviderCrossColorReachedCanary

def processType : TypeExpr := .base (costBaseSortName "Proc")
def nameType : TypeExpr := .base (costBaseSortName "Name")
def available : List TypeExpr := [processType]

theorem reachedWellSorted :
    ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      FreeTypeContext.empty available nameType reachedPattern := by
  refine ⟨checkOpenPatternWellSorted_sound (by
    unfold available processType nameType
    decide), ?_⟩
  intro reflected _membership
  simp [available, reachedPattern, rightPattern, binderSafeAt,
    binderSafeListAt]

noncomputable def tree : CostRegionTree rhoCIGSLT FreeTypeContext.empty
    available [] reachedPattern nameType :=
  (CostRegionTree.build? available [] reachedPattern nameType).get
    (CostRegionTree.build?_isSome_of_wellSorted reachedWellSorted)

theorem rootStatic : tree.rootIsStatic = true := by decide

noncomputable def viewPair : Σ color, tree.StaticRootView color :=
  tree.staticRootView_of_rootIsStatic rootStatic

theorem color : viewPair.1 = .base := by decide

theorem entriesLength :
    viewPair.2.node.finiteBoundaryTable.entries.length = 1 := by decide

noncomputable def entry :=
  viewPair.2.node.finiteBoundaryTable.entries[0]'(by rw [entriesLength]; decide)

theorem boundarySupport_is_empty :
    entry.boundary.targetSupport = [] := by decide

theorem boundarySupport_ne_available :
    entry.boundary.targetSupport ≠ available := by decide

end A2xSupportProbe
end Mettapedia.Languages.ProcessCalculi.RhoCalculus
