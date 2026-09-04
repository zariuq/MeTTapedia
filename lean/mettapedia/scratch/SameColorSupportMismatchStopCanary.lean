import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostTypedMixedColorApexCounterexample
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryBoundarySideCell

/-!
# Same-colour support-mismatch stop canary

This fixture places an exposed foreign Quote and the same Quote sealed under
the selected colour's Quote/Drop shell below two static roots of that selected
colour.  It tests whether the complete canonical-plan-stop telescope admits
the unequal-support configuration before any terminal apex is assumed.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus
namespace SameColorSupportMismatchStopCanary

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open CostTypedMixedColorApexCounterexample

def processType : TypeExpr := .base (costBaseSortName "Proc")
def endpointType : TypeExpr := .base costWrappedSortName
def available : List TypeExpr := [processType, processType, processType]

def declaration : ReflectivePresentationDecl :=
  costStaticReflectivePresentationDecl rhoCIGSLT .wrapped
    rhoReflectivePresentation.toReflectivePresentationDecl

def exposedName : Pattern := typedApexForeignQuote
def sealedName : Pattern := typedApexSelectedQuoteDrop

def leftPattern : Pattern :=
  .apply (costWrappedConstructorName "PDrop") [exposedName]

def rightPattern : Pattern :=
  .apply (costWrappedConstructorName "PDrop") [sealedName]

private def wrappedDropConstructor :
    StructuralMorphism.AuthoredConstructor rhoIGSLT.presentation.presentation :=
  ⟨rhoCalc.terms[1], List.getElem_mem _⟩

private theorem wrappedDrop_selected :
    wrappedDropConstructor ∈ rhoContinuationRetyping.wrappedConstructors := by
  apply (rhoContinuationRetyping.mem_wrappedConstructors_iff
    wrappedDropConstructor).2
  constructor <;> decide

private theorem wrappedDrop_mem :
    costWrappedConstructor (theory := rhoIGSLT) rhoCalc.terms[1] ∈
      rhoCIGSLT.costWholeLanguage.terms := by
  change costWrappedConstructor (theory := rhoCIGSLT.theory)
      wrappedDropConstructor.1 ∈ rhoCIGSLT.costWholeLanguage.terms
  exact rhoCIGSLT.costWrappedConstructor_mem_costWhole
    wrappedDropConstructor wrappedDrop_selected

private theorem leftTyped :
    HasType rhoCIGSLT.costWholeLanguage
      typedApexCospan.commonTargetFreeContext [] leftPattern endpointType := by
  apply HasType.constructor
      (rule := costWrappedConstructor (theory := rhoIGSLT) rhoCalc.terms[1])
  · exact wrappedDrop_mem
  · rw [usesBareCollection_costWrappedConstructor_iff]
    simp [UsesBareCollection, rhoCalc, TypeExpr.name, TypeExpr.proc,
      TypeExpr.baseType]
  · rw [rho_costWrappedDropConstructor_params]
    exact .cons (by trivial) rfl typedApexForeignQuote_typed .nil

private theorem rightTyped :
    HasType rhoCIGSLT.costWholeLanguage
      typedApexCospan.commonTargetFreeContext [] rightPattern endpointType := by
  apply HasType.constructor
      (rule := costWrappedConstructor (theory := rhoIGSLT) rhoCalc.terms[1])
  · exact wrappedDrop_mem
  · rw [usesBareCollection_costWrappedConstructor_iff]
    simp [UsesBareCollection, rhoCalc, TypeExpr.name, TypeExpr.proc,
      TypeExpr.baseType]
  · rw [rho_costWrappedDropConstructor_params]
    exact .cons (by trivial) rfl typedApexSelectedQuoteDrop_typed .nil

theorem leftWellSorted :
    ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      typedApexCospan.commonTargetFreeContext available endpointType
        leftPattern := by
  have zero : ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      typedApexCospan.commonTargetFreeContext [] endpointType leftPattern := by
    refine ⟨⟨leftTyped, rfl, rfl, leftTyped.isWellScopedAt⟩, ?_⟩
    intro reflected _membership
    simp [leftPattern, exposedName, typedApexForeignQuote, typedApexRaw,
      typedApexFirstAtom, typedApexSecondAtom, binderSafeAt,
      binderSafeListAt]
  simpa only [List.nil_append] using zero.extendOuter available

theorem rightWellSorted :
    ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      typedApexCospan.commonTargetFreeContext available endpointType
        rightPattern := by
  have zero : ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      typedApexCospan.commonTargetFreeContext [] endpointType rightPattern := by
    refine ⟨⟨rightTyped, rfl, rfl, rightTyped.isWellScopedAt⟩, ?_⟩
    intro reflected _membership
    simp [rightPattern, sealedName, typedApexSelectedQuoteDrop,
      typedApexForeignQuote, typedApexRaw, typedApexFirstAtom,
      typedApexSecondAtom, binderSafeAt, binderSafeListAt]
  simpa only [List.nil_append] using zero.extendOuter available

theorem canonical_eq :
    canonicalize declaration leftPattern =
      canonicalize declaration rightPattern := by
  unfold leftPattern rightPattern
  rw [canonicalize_apply_of_ne_quote declaration (by decide),
    canonicalize_apply_of_ne_quote declaration (by decide)]
  exact congrArg (Pattern.apply (costWrappedConstructorName "PDrop"))
    (congrArg List.singleton typedApexMixedColor_canonical_eq.symm)

noncomputable def leftTree :
    CostRegionTree rhoCIGSLT typedApexCospan.commonTargetFreeContext available []
      leftPattern endpointType :=
  (CostRegionTree.build? available [] leftPattern endpointType).get
    (CostRegionTree.build?_isSome_of_wellSorted leftWellSorted)

noncomputable def rightTree :
    CostRegionTree rhoCIGSLT typedApexCospan.commonTargetFreeContext available []
      rightPattern endpointType :=
  (CostRegionTree.build? available [] rightPattern endpointType).get
    (CostRegionTree.build?_isSome_of_wellSorted rightWellSorted)

private def wrappedDropDeclared : rhoCIGSLT.DeclaredCostConstructor :=
  ⟨.wrapped ⟨rhoCalc.terms[1], List.getElem_mem _⟩, wrappedDrop_selected⟩

private theorem wrappedDropRole :
    rhoCIGSLT.declaredCostConstructorRole wrappedDropDeclared =
      .static .wrapped := rfl

private theorem wrappedDropDecoded :
    rhoCIGSLT.decodeDeclaredCostConstructor
        (costWrappedConstructorName "PDrop") =
      some wrappedDropDeclared := by
  simpa [wrappedDropDeclared, CIGSLT.renderDeclaredCostConstructor,
    CIGSLT.renderGeneratedCostConstructor, CostConstructor.render, rhoCalc]
    using rhoCIGSLT.decodeDeclaredCostConstructor_render wrappedDropDeclared

private def leftStaticShape : CostStaticRootShape rhoCIGSLT leftPattern
    endpointType := by
  apply CostStaticRootShape.application .wrapped wrappedDropDeclared
  · exact wrappedDropDecoded
  · exact wrappedDropRole

private def rightStaticShape : CostStaticRootShape rhoCIGSLT rightPattern
    endpointType := by
  apply CostStaticRootShape.application .wrapped wrappedDropDeclared
  · exact wrappedDropDecoded
  · exact wrappedDropRole

theorem leftTree_rootIsStatic : leftTree.rootIsStatic = true := by
  exact leftStaticShape.rootIsStatic leftTree

theorem rightTree_rootIsStatic : rightTree.rootIsStatic = true := by
  exact rightStaticShape.rootIsStatic rightTree

theorem wrapped_proc_sort :
    (CostStaticColor.wrapped.mapLangSort rhoCIGSLT rhoProc).1 =
      costWrappedSortName := by
  rfl

end SameColorSupportMismatchStopCanary
end Mettapedia.Languages.ProcessCalculi.RhoCalculus
