import ForeignSupportMismatchOrderCanary
import DualBoundaryKeyCanary

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus
namespace A1TelescopeProbe

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open ForeignSupportMismatchOrderCanary

noncomputable def leftEnvironment :=
  CostStaticAtomEnvironment.ofInventory
    (leftView.node.semanticAtomEnvironment
      (leftView.children.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))).1

noncomputable def rightEnvironment :=
  CostStaticAtomEnvironment.ofInventory
    (rightView.node.semanticAtomEnvironment
      (rightView.children.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))).1

theorem roots_aligned : CanonicalRootAligned declaration leftPattern
    rightPattern := by
  apply CanonicalRootAligned.apply (by decide)
  exact .cons
    CostTypedMixedColorApexCounterexample.typedApexMixedColor_canonical_eq .nil

theorem quoteRoot_atomTargetSupport_eq_nil
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound sourceAvailable : List TypeExpr}
    {thinning : CostStaticBinderThinning
      LanguageDefContinuedInteraction.rhoCIGSLT color sourceBound targetBound}
    {outer : Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext}
    {pattern : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan
      LanguageDefContinuedInteraction.rhoCIGSLT color targetFree sourceBound
        targetBound thinning sourceAvailable outer pattern sourceType)
    (frameFree : WellSorted.ReflectiveSubstitutionBinderFree
      plan.abstractPattern = true)
    (quoteRoot : plan.rootClass =
      CostStaticPlanRootClass.application
        rhoReflectivePresentation.quoteConstructor)
    {values : TypedCostRegionBoundaryTable.Values
      LanguageDefContinuedInteraction.rhoCIGSLT color targetFree
        plan.boundaryTable}
    (inventory : CostStaticParameterInventory
      LanguageDefContinuedInteraction.rhoCIGSLT color targetFree
        plan.boundaryTable values plan.abstractPattern)
    (slot : Fin (CostStaticAtomEnvironment.ofInventory inventory).atomCount) :
    ((CostStaticAtomEnvironment.ofInventory inventory).atomValue slot).key.targetSupport =
      [] := by
  apply
    CostStaticAtomEnvironment.ofInventory_atomValue_targetSupport_eq_nil_of_boundaryEntries
      inventory
  intro boundary membership
  exact
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticRegionPlan.boundaryTargetSupport_eq_nil_of_quoteRoot
      plan frameFree boundary membership quoteRoot

end A1TelescopeProbe
end Mettapedia.Languages.ProcessCalculi.RhoCalculus
