import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryStaticRootClassification
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryRouteBreadthCanary

/-!
# Static-to-neutral collapse canary for rho Cost

A bare parallel singleton is a genuine static root at a base process type,
while its sole element may be a neutral interaction-principal application.
Reflective canonicalization identifies the two compact patterns.  This
canary records that a complete static-pair closure must therefore handle a
static-to-structural atom case; static/static frame comparison alone is not
exhaustive.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostGeneratorInvariantCounterexample
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryRouteBreadthCanary

/-- The singleton parallel shell around the neutral breadth process. -/
def rhoStaticNeutralSingletonPattern : Pattern :=
  .collection .hashBag [rhoBreadthLeftPattern] none

private theorem rhoRuleThree_mem : rhoCalc.terms[3] ∈ rhoCalc.terms :=
  List.getElem_mem _

theorem rhoStaticNeutralSingleton_typed :
    HasType rhoCIGSLT.costWholeLanguage rhoCutOrderFree []
      rhoStaticNeutralSingletonPattern (.base (costBaseSortName "Proc")) := by
  apply HasType.collectionConstructor
      (rule := costBaseConstructor rhoInteractionCut rhoCalc.terms[3])
      (parameterName := "ps")
      (elementType := .base (costBaseSortName "Proc"))
  · exact rhoCIGSLT.costBaseConstructor_mem_costWhole _ rhoRuleThree_mem
  · exact rho_costBaseParallelConstructor_params
  · exact .cons rhoBreadthLeft_typed (.nil [] _)

/-- Checked singleton shell used by the executable region-tree compiler. -/
def rhoStaticNeutralSingleton :
    OpenTerm rhoCIGSLT.costWholeLanguage rhoCutOrderFree []
      rhoBreadthBaseProcSort := by
  refine ⟨rhoStaticNeutralSingletonPattern,
    rhoStaticNeutralSingleton_typed, rfl, rfl, ?_⟩
  intro declaration membership
  simp [rhoStaticNeutralSingletonPattern, rhoBreadthLeftPattern,
    rhoBreadthLeftProcess, rhoBreadthOutputName, rhoCutOrderRedex,
    rhoCutOrderBaseQuote, rhoCutOrderBaseDrop, rhoCutOrderWrappedDrop,
    binderSafeAt, binderSafeListAt]

/-- The deterministic compiler retains the bare base collection as a static
root. -/
theorem rhoStaticNeutralSingleton_rootIsStatic :
    (CostRegionTree.buildOpenTerm
      (source := rhoCIGSLT) rhoStaticNeutralSingleton).rootIsStatic = true := by
  exact CostStaticRootShape.baseCollection.rootIsStatic _

/-- The singleton's element is the explicitly retained neutral output tree. -/
theorem rhoBreadthLeftTree_rootIsStatic_false :
    rhoBreadthLeftTree.rootIsStatic = false := rfl

/-- Reflective canonicalization collapses the static singleton shell to its
neutral element. -/
theorem rhoStaticNeutralSingleton_canonical_eq_neutral :
    canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT .base
          rhoReflectivePresentation.toReflectivePresentationDecl)
        rhoStaticNeutralSingletonPattern =
      canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT .base
          rhoReflectivePresentation.toReflectivePresentationDecl)
        rhoBreadthLeftPattern := by
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT .base
    rhoReflectivePresentation.toReflectivePresentationDecl
  change canonicalize declaration rhoStaticNeutralSingletonPattern =
    canonicalize declaration rhoBreadthLeftPattern
  have parallelType : declaration.parallelCollection = .hashBag := by
    rfl
  rw [show rhoStaticNeutralSingletonPattern =
      .collection declaration.parallelCollection [rhoBreadthLeftPattern]
        none by
    simp [rhoStaticNeutralSingletonPattern, parallelType]]
  exact canonicalize_parallel_singleton declaration rhoBreadthLeftPattern

/-- A canonical pair at the base process fibre can have one static endpoint
and one neutral endpoint. -/
theorem rho_exists_static_neutral_canonical_pair :
    ∃ (left : CostRegionTree rhoCIGSLT rhoCutOrderFree [] []
          rhoStaticNeutralSingletonPattern (.base (costBaseSortName "Proc")))
      (right : CostRegionTree rhoCIGSLT rhoCutOrderFree [] []
          rhoBreadthLeftPattern (.base (costBaseSortName "Proc"))),
      left.rootIsStatic = true ∧ right.rootIsStatic = false ∧
        canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT .base
              rhoReflectivePresentation.toReflectivePresentationDecl)
            rhoStaticNeutralSingletonPattern =
          canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT .base
              rhoReflectivePresentation.toReflectivePresentationDecl)
            rhoBreadthLeftPattern := by
  exact ⟨CostRegionTree.buildOpenTerm
      (source := rhoCIGSLT) rhoStaticNeutralSingleton,
    rhoBreadthLeftTree, rhoStaticNeutralSingleton_rootIsStatic,
    rhoBreadthLeftTree_rootIsStatic_false,
    rhoStaticNeutralSingleton_canonical_eq_neutral⟩

/-- The general asymmetric-root classifier orients the singleton witness at
the static endpoint; the structural child is not misclassified as a second
static region. -/
theorem rhoStaticNeutralSingleton_collapsingRoot :
    CollapsingRoot
      (costStaticReflectivePresentationDecl rhoCIGSLT .base
        rhoReflectivePresentation.toReflectivePresentationDecl)
      rhoStaticNeutralSingletonPattern := by
  exact rhoCollapsingRoot_of_static_structural_canonical_eq .base
    (CostRegionTree.buildOpenTerm
      (source := rhoCIGSLT) rhoStaticNeutralSingleton)
    rhoBreadthLeftTree rhoStaticNeutralSingleton_rootIsStatic
    rhoBreadthLeftTree_rootIsStatic_false
    rhoStaticNeutralSingleton_canonical_eq_neutral

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
