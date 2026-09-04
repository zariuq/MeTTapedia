import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryParallelFrontier
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryMatchedFramesApex

/-!
# Foreign bare-parallel depth-separation canary

An exposed foreign boundary normalizes to a foreign quotation containing the
ambient bound variable zero.  The same foreign quotation is retained directly
on the other route.  The two occurrences are placed in opposite orders under
an admitted base-colour parallel root.  Common restoration lifts the opaque
boundary assignment, while direct reflective substitution resets below the
foreign quote.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus
namespace ForeignRigidTieOrderCanary

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

def nameType : TypeExpr := .base (costBaseSortName "Name")
def processType : TypeExpr := .base (costBaseSortName "Proc")
def available : List TypeExpr := [processType]

def declaration : ReflectivePresentationDecl :=
  costStaticReflectivePresentationDecl rhoCIGSLT .wrapped
    rhoReflectivePresentation.toReflectivePresentationDecl

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

def rightPattern : Pattern :=
  .collection .hashBag [rigidLeaf, boundaryLeaf] none

theorem leftWellSorted :
    ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      FreeTypeContext.empty available processType leftPattern := by
  refine ⟨checkOpenPatternWellSorted_sound (by decide), ?_⟩
  intro reflected membership
  rw [CIGSLT.costWholeReflectionProfile_presentations] at membership
  change reflected ∈
    [costStaticReflectivePresentationDecl rhoCIGSLT .base
      rhoReflectivePresentation.toReflectivePresentationDecl,
     costStaticReflectivePresentationDecl rhoCIGSLT .wrapped
      rhoReflectivePresentation.toReflectivePresentationDecl] at membership
  simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
  rcases membership with rfl | rfl <;>
    simp [leftPattern, boundaryLeaf, rigidLeaf, selectedShell, foreignQuote,
      available,
      binderSafeAt, binderSafeListAt,
      CostStaticColor.reflectiveSymbols, costBaseStaticReflectiveSymbols,
      costWrappedStaticReflectiveSymbols, costBaseStaticSymbols,
      costWrappedStaticSymbols, costBasePresentationSymbols,
      ReflectionExtension.mapReflectivePresentation, rhoReflectivePresentation]

theorem rightWellSorted :
    ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      FreeTypeContext.empty available processType rightPattern := by
  refine ⟨checkOpenPatternWellSorted_sound (by decide), ?_⟩
  intro reflected membership
  rw [CIGSLT.costWholeReflectionProfile_presentations] at membership
  change reflected ∈
    [costStaticReflectivePresentationDecl rhoCIGSLT .base
      rhoReflectivePresentation.toReflectivePresentationDecl,
     costStaticReflectivePresentationDecl rhoCIGSLT .wrapped
      rhoReflectivePresentation.toReflectivePresentationDecl] at membership
  simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
  rcases membership with rfl | rfl <;>
    simp [rightPattern, boundaryLeaf, rigidLeaf, selectedShell, foreignQuote,
      available,
      binderSafeAt, binderSafeListAt,
      CostStaticColor.reflectiveSymbols, costBaseStaticReflectiveSymbols,
      costWrappedStaticReflectiveSymbols, costBaseStaticSymbols,
      costWrappedStaticSymbols, costBasePresentationSymbols,
      ReflectionExtension.mapReflectivePresentation, rhoReflectivePresentation]

theorem foreignCanonicalEq :
    canonicalize declaration leftPattern =
      canonicalize declaration rightPattern := by
  change canonicalize declaration
      (.collection declaration.parallelCollection
        [boundaryLeaf, rigidLeaf] none) =
    canonicalize declaration
      (.collection declaration.parallelCollection
        [rigidLeaf, boundaryLeaf] none)
  exact canonicalize_parallel_permutation declaration
    (List.Perm.swap boundaryLeaf rigidLeaf []).symm

noncomputable def leftTree :
    CostRegionTree rhoCIGSLT FreeTypeContext.empty available [] leftPattern
      processType :=
  (CostRegionTree.build? available [] leftPattern processType).get
    (CostRegionTree.build?_isSome_of_wellSorted leftWellSorted)

noncomputable def rightTree :
    CostRegionTree rhoCIGSLT FreeTypeContext.empty available [] rightPattern
      processType :=
  (CostRegionTree.build? available [] rightPattern processType).get
    (CostRegionTree.build?_isSome_of_wellSorted rightWellSorted)

theorem leftRootStatic : leftTree.rootIsStatic = true := by decide
theorem rightRootStatic : rightTree.rootIsStatic = true := by decide

noncomputable def leftViewPair : Σ color, leftTree.StaticRootView color :=
  leftTree.staticRootView_of_rootIsStatic leftRootStatic

noncomputable def rightViewPair : Σ color, rightTree.StaticRootView color :=
  rightTree.staticRootView_of_rootIsStatic rightRootStatic

theorem leftColor : leftViewPair.1 = .base := by decide
theorem rightColor : rightViewPair.1 = .base := by decide

noncomputable def leftView : leftTree.StaticRootView .base :=
  leftColor ▸ leftViewPair.2

noncomputable def rightView : rightTree.StaticRootView .base :=
  rightColor ▸ rightViewPair.2

theorem leftSupports :
    leftView.node.finiteBoundaryTable.entries.map
      (·.boundary.targetSupport) = [available] := by
  decide

theorem rightSupports :
    rightView.node.finiteBoundaryTable.entries.map
      (·.boundary.targetSupport) = [available] := by
  decide

end ForeignRigidTieOrderCanary
end Mettapedia.Languages.ProcessCalculi.RhoCalculus
