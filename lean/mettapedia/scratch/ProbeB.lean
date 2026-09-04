import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryExposureBridge

namespace ProbeB

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

#check @rhoProc

theorem parallelRule_mem :
    rhoCalc.terms[3] ∈
      rhoCIGSLT.theory.presentation.presentation.language.terms := by
  change rhoCalc.terms[3] ∈ rhoCalc.terms
  simp [rhoCalc]

def parallelChoice : CostCollectionTypingChoice :=
  .bare rhoCalc.terms[3] (.base "Proc")

theorem parallelChoice_mem :
    parallelChoice ∈
      costStaticCollectionTypingChoices rhoCIGSLT .base
        FreeTypeContext.empty [] .hashBag []
        (mapTypeExpr (CostStaticColor.base.symbols rhoCIGSLT)
          (.base rhoProc.1)) := by
  apply mem_costStaticCollectionTypingChoices_complete
  right
  refine ⟨rhoCalc.terms[3], .base "Proc", rfl, parallelRule_mem,
    ?_, rfl, "ps", rfl, rfl⟩
  apply rhoCIGSLT.bareCollectionConstructorsWrapped _ parallelRule_mem
  exact ⟨"ps", .hashBag, .base "Proc", rfl⟩

def emptyPlan :
    CostStaticRegionPlan rhoCIGSLT .base FreeTypeContext.empty
      (CostStaticBinderThinning.sourceContextOfTarget rhoCIGSLT .base [])
      [] (CostStaticBinderThinning.ofTargetThinning rhoCIGSLT .base [])
      [] .hole (.collection .hashBag [] none) (.base rhoProc.1) :=
  .collection parallelChoice parallelChoice_mem .nil

def emptyTerm :
    ReflectiveWellSorted.OpenTerm rhoCIGSLT.costWholeReflectionProfile
      rhoCIGSLT.costWholeLanguage FreeTypeContext.empty []
      (CostStaticColor.base.mapLangSort rhoCIGSLT rhoProc) := by
  refine ⟨.collection .hashBag [] none, ⟨?_, rfl, rfl, rfl⟩, ?_⟩
  · apply HasType.collectionConstructor
      (rule := costBaseConstructor rhoCIGSLT.cut rhoCalc.terms[3])
      (parameterName := "ps")
      (elementType := .base (costBaseSortName "Proc"))
    · exact rhoCIGSLT.costBaseConstructor_mem_costWhole _ parallelRule_mem
    · exact rho_costBaseParallelConstructor_params
    · exact .nil [] _
  · intro presentation membership
    rfl

def emptyNode : CostStaticRegionNode rhoCIGSLT .base FreeTypeContext.empty :=
  CostStaticRegionNode.ofPlan emptyTerm.toCore emptyPlan rfl

theorem emptyNode_entries : emptyNode.finiteBoundaryTable.entries = [] := by rfl

theorem emptyNode_term : emptyNode.term.1 = .collection .hashBag [] none := by rfl

theorem emptyNode_skeleton : emptyNode.skeleton.1 = .collection .hashBag [] none := by rfl

theorem emptyNode_targetBound : emptyNode.targetBound = [] := by rfl

theorem emptyNode_sourceSort : emptyNode.sourceSort = rhoProc := by rfl

namespace Kill

theorem entryEmbedding_nil_elim {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext}
    {entry : TypedCostRegionBoundary source color targetFree}
    {small : List (TypedCostRegionBoundary source color targetFree)}
    (embedding : CostStaticPlanEntryEmbedding source color targetFree
      (entry :: small) []) : False := by
  cases embedding

theorem collapsing (declarationColor : CostStaticColor) :
    CollapsingRoot
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation.toReflectivePresentationDecl)
      emptyNode.term.1 := by
  refine Or.inr ⟨[], ?_⟩
  cases declarationColor <;> rfl

theorem canonicalize_empty_parallel_eq_unit
    (decl : ReflectivePresentationDecl)
    (hcoll : decl.parallelCollection = .hashBag)
    (hne : decl.parallelUnitConstructor ≠ decl.quoteConstructor) :
    canonicalize decl (.collection .hashBag [] none) =
      canonicalize decl (.apply decl.parallelUnitConstructor []) := by
  rw [← hcoll, canonicalize_parallel, canonicalize_apply_of_ne_quote decl hne]
  simp [normalizeParallelElements, collapseParallel,
    Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatterns]

theorem decl_parallelCollection (dc : CostStaticColor) :
    (costStaticReflectivePresentationDecl rhoCIGSLT dc
      rhoReflectivePresentation.toReflectivePresentationDecl
      ).parallelCollection = .hashBag := by
  cases dc <;> rfl

theorem decl_unit_ne_quote (dc : CostStaticColor) :
    (costStaticReflectivePresentationDecl rhoCIGSLT dc
      rhoReflectivePresentation.toReflectivePresentationDecl
      ).parallelUnitConstructor ≠
    (costStaticReflectivePresentationDecl rhoCIGSLT dc
      rhoReflectivePresentation.toReflectivePresentationDecl
      ).quoteConstructor := by
  cases dc <;> decide

theorem canonicalEq (dc : CostStaticColor) :
    canonicalize (costStaticReflectivePresentationDecl rhoCIGSLT dc
        rhoReflectivePresentation.toReflectivePresentationDecl)
      emptyNode.term.1 =
    canonicalize (costStaticReflectivePresentationDecl rhoCIGSLT dc
        rhoReflectivePresentation.toReflectivePresentationDecl)
      (.apply (costStaticReflectivePresentationDecl rhoCIGSLT dc
        rhoReflectivePresentation.toReflectivePresentationDecl
        ).parallelUnitConstructor []) := by
  rw [emptyNode_term]
  exact canonicalize_empty_parallel_eq_unit _ (decl_parallelCollection dc)
    (decl_unit_ne_quote dc)

theorem not_apply (dc : CostStaticColor) :
    ¬ RhoCollapsingApplyLeafBoundary dc := by
  intro boundary
  obtain ⟨payload, state, ⟨embedding⟩, _, _, _, _⟩ :=
    boundary emptyNode (collapsing dc) (canonicalEq dc)
  rw [emptyNode_entries] at embedding
  exact entryEmbedding_nil_elim embedding

#print axioms not_apply

end Kill

end ProbeB
