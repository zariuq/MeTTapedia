import Mettapedia.GSLT.LanguageDef.CostSemanticAtomTreeAlignment
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryRouteBreadthCanary

/-!
# Rho canaries for boundary-tree semantic-atom alignment

The positive canary compares genuinely different boundary contents: a
base-colour Quote/Drop redex and the structural free variable to which its
child tree hereditarily normalizes.  Their source and target fibres agree,
so the generic child-to-parent theorem identifies their semantic atoms.

The negative canary changes only the authored source type.  Even with an
identical target value, the complete semantic keys remain distinct.  Thus
same-fibre evidence is load-bearing rather than a proof-engineering
convenience.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostSemanticAtomTreeAlignmentCanary

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostGeneratorInvariantCounterexample
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryCanonicalCanary
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryRouteBreadthCanary

/-- The wrapped static image of `Name` is its base-tagged generated sort. -/
theorem rhoBreadthWrappedNameTypeForAtomCanary :
    (.base (costBaseSortName "Name") : TypeExpr) =
      mapTypeExpr (CostStaticColor.wrapped.symbols rhoCIGSLT)
        (.base "Name") := by
  simp [mapTypeExpr, CostStaticColor.symbols,
    costWrappedStaticSymbols, rhoCIGSLT, rhoIGSLT,
    rhoInteractivePresentation, rhoCalc, TypeDecl.plain,
    show "Name" ≠ "Proc" by decide]

/-- The structural endpoint of the `a`-cell, reindexed to the exact wrapped
boundary target type. -/
def rhoBreadthStructuralBoundaryATree :
    CostRegionTree rhoCIGSLT rhoCutOrderFree [] [] (.fvar "a")
      (mapTypeExpr (CostStaticColor.wrapped.symbols rhoCIGSLT)
        (.base "Name")) :=
  CostRegionTree.reindexType rhoBreadthWrappedNameTypeForAtomCanary
    rhoCutOrderAStructuralTree

/-- A proof-relevant boundary for the structural endpoint.  Its fibre is
the same one certified for the Quote/Drop content, while the content itself
is deliberately different. -/
def rhoBreadthStructuralBoundaryA :
    TypedCostRegionBoundary rhoCIGSLT .wrapped rhoCutOrderFree where
  boundary :=
    { type := .base "Name"
      support := []
      targetType := mapTypeExpr
        (CostStaticColor.wrapped.symbols rhoCIGSLT) (.base "Name")
      targetSupport := []
      content := .fvar "a" }
  contentTyped := by
    rw [← rhoBreadthWrappedNameTypeForAtomCanary]
    exact .fvar (by simp [rhoCutOrderFree, FreeTypeContext.ofList])
  contentCanonicalBinderMetadata := rfl
  contentObjectPattern := rfl
  contentReflectiveScopeSafe := by
    intro declaration membership
    rfl

/-- Certification and the explicit structural endpoint recover the same
complete source/target fibre. -/
theorem rhoBreadthBoundaryA_sameFiber_structural :
    CostRegionBoundary.SameFiber
      rhoBreadthBoundaryWitnessA.typed.boundary
      rhoBreadthStructuralBoundaryA.boundary := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact certifyCostRegionBoundary?_sourceType_eq
      rhoBreadthBoundaryWitnessA_spec
  · exact certifyCostRegionBoundary?_sourceSupport_eq
      (availableSource := []) rhoBreadthBoundaryWitnessA_spec
  · exact rhoBreadthBoundaryWitnessA.targetType_eq
  · exact rhoBreadthBoundaryWitnessA.targetSupport_eq

/-- The selected Quote/Drop child and its structural contractum are aligned
before either is packaged as a parent semantic atom. -/
noncomputable def rhoBreadthBoundaryChildA_structuralAlignment :
    CostRegionTreeNormalizationAlignment rhoCIGSLT
      rhoHereditaryNormalizationKernel rhoCutOrderFree
      rhoBreadthBoundaryChildA rhoBreadthStructuralBoundaryATree := by
  refine .semanticAtom rhoBreadthBoundaryChildA
    rhoBreadthStructuralBoundaryATree ?_
  exact rhoBreadthBaseRedexANodeSemanticAtomJoin.transport
    (rhoBreadthBoundaryChildA_normalizeHereditary.trans
      rhoBreadthBaseRedexANode_normalizeHereditary.symm)
    (by
      change (rhoBreadthStructuralBoundaryATree.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
          .fvar "a"
      unfold rhoBreadthStructuralBoundaryATree
      rw [CostRegionTree.reindexType_normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)]
      simp [rhoCutOrderAStructuralTree, CostRegionTree.normalize])

/-- Positive canary: different boundary spellings with aligned child trees
become exactly one semantic atom at the parent boundary. -/
theorem rhoBreadth_alignedBoundaryAtoms_eq :
    TypedCostStaticAtom.ofBoundaryValue rhoBreadthBoundaryWitnessA.typed
        (rhoBreadthBoundaryChildA.normalizedBoundaryValue
          rhoHereditaryNormalizationKernel) =
      TypedCostStaticAtom.ofBoundaryValue rhoBreadthStructuralBoundaryA
        (rhoBreadthStructuralBoundaryATree.normalizedBoundaryValue
          rhoHereditaryNormalizationKernel) :=
  CostRegionTree.alignedBoundaryAtom_eq
    rhoBreadthBoundaryA_sameFiber_structural
    rhoBreadthBoundaryChildA_structuralAlignment

/-- Changing only the authored source type changes semantic identity even
when the target value, support, and target type are unchanged. -/
def rhoBreadthWrongSourceTypeBoundaryA :
    TypedCostRegionBoundary rhoCIGSLT .wrapped rhoCutOrderFree where
  boundary :=
    { type := .base "Proc"
      support := []
      targetType := mapTypeExpr
        (CostStaticColor.wrapped.symbols rhoCIGSLT) (.base "Name")
      targetSupport := []
      content := .fvar "a" }
  contentTyped := rhoBreadthStructuralBoundaryA.contentTyped
  contentCanonicalBinderMetadata := rfl
  contentObjectPattern := rfl
  contentReflectiveScopeSafe := rhoBreadthStructuralBoundaryA.contentReflectiveScopeSafe

/-- The same deliberately wrong source fibre, packaged with only the target
indices carried by `CertifiedCostRegionBoundary`.  This value demonstrates
why a stopped traversal must retain the executable certification equation in
addition to the decoded boundary record. -/
def rhoBreadthWrongSourceTypeCertifiedBoundaryA :
    CertifiedCostRegionBoundary rhoCIGSLT .wrapped rhoCutOrderFree []
      (mapTypeExpr (CostStaticColor.wrapped.symbols rhoCIGSLT)
        (.base "Name")) (.fvar "a") where
  typed := rhoBreadthWrongSourceTypeBoundaryA
  content_eq := rfl
  targetSupport_eq := rfl
  targetType_eq := rfl

/-- Negative receipt canary: the executable boundary certifier cannot
produce the forged source fibre, even though its target type, target support,
and content are all well formed. -/
theorem rhoBreadth_wrongSourceType_not_certified :
    certifyCostRegionBoundary? rhoCIGSLT .wrapped rhoCutOrderFree []
        (mapTypeExpr (CostStaticColor.wrapped.symbols rhoCIGSLT)
          (.base "Name")) (.fvar "a") ≠
      some rhoBreadthWrongSourceTypeCertifiedBoundaryA := by
  intro certified
  have sourceType := certifyCostRegionBoundary?_sourceType_eq certified
  change (.base "Proc" : TypeExpr) = .base "Name" at sourceType
  exact (show "Proc" ≠ "Name" by decide) (TypeExpr.base.inj sourceType)

/-- Negative canary: equality of restored compact values alone cannot
replace the same-fibre premise of `alignedBoundaryAtom_eq`. -/
theorem rhoBreadth_sameNormal_wrongSourceType_atoms_ne :
    TypedCostStaticAtom.ofBoundaryValue rhoBreadthStructuralBoundaryA
        (rhoBreadthStructuralBoundaryATree.normalizedBoundaryValue
          rhoHereditaryNormalizationKernel) ≠
      TypedCostStaticAtom.ofBoundaryValue rhoBreadthWrongSourceTypeBoundaryA
        (rhoBreadthStructuralBoundaryATree.normalizedBoundaryValue
          rhoHereditaryNormalizationKernel) := by
  intro equality
  have sourceTypeEquality := congrArg
    (fun atom => atom.key.sourceType) equality
  have nameEqProc : "Name" = "Proc" := TypeExpr.base.inj sourceTypeEquality
  exact (show "Name" ≠ "Proc" by decide) nameEqProc

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostSemanticAtomTreeAlignmentCanary
