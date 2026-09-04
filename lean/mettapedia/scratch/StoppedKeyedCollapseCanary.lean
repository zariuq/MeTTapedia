import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryBoundarySideCell

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical

/-- Canary for the depth-polymorphic stopped-context collapse needed by the
foreign boundary-side cell. -/
theorem CostStaticPlanStopped.canonicalizeByDepths_environmentReify_root_eq_fvar_canary
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable}
    {inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1}
    (environment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      inventory)
    {payload : Pattern}
    (state : CostStaticPlanStopped rhoCIGSLT color targetFree payload
      node.skeleton.1)
    (slot : Fin environment.atomCount)
    (selected : environment.slotOfName? state.boundaryOccurrence.name =
      some slot)
    (collapse : canonicalize
        rhoReflectivePresentation.toReflectivePresentationDecl
        (state.skeletonContext.fill (.fvar state.boundaryOccurrence.name)) =
      .fvar state.boundaryOccurrence.name)
    {Key : Type} [LinearOrder Key]
    (key : Nat → Nat → Pattern → Key)
    (availableDepth scopeDepth : Nat) :
    canonicalizeByDepths key rhoReflectivePresentation availableDepth scopeDepth
        (environment.reify node.skeleton.1) =
      .fvar (environment.atomName slot) := by
  let declaration := rhoReflectivePresentation.toReflectivePresentationDecl
  have frameFree : contextFrameFreeFvarNames state.skeletonContext = [] :=
    contextFrameFreeFvarNames_eq_nil_of_collapse declaration collapse
  have reifiedContext :
      environment.reifyContext state.skeletonContext = state.skeletonContext :=
    CostStaticAtomEnvironment.reifyContext_eq_self_of_frameFreeFvarNames_eq_nil
      environment state.skeletonContext frameFree
  have reifiedFrame : environment.reify node.skeleton.1 =
      state.skeletonContext.fill (.fvar (environment.atomName slot)) := by
    calc
      environment.reify node.skeleton.1 =
          environment.reify
            (state.skeletonContext.fill
              (.fvar state.boundaryOccurrence.name)) :=
        congrArg environment.reify state.abstract_eq
      _ = (environment.reifyContext state.skeletonContext).fill
          (environment.reify (.fvar state.boundaryOccurrence.name)) :=
        (environment.reifyContext_fill state.skeletonContext _).symm
      _ = state.skeletonContext.fill
          (.fvar (environment.atomName slot)) := by
        rw [reifiedContext]
        simp only [CostStaticAtomEnvironment.reify]
        unfold CostStaticAtomEnvironment.reifyName
        rw [selected]
  have ordinaryCollapse : canonicalize declaration
        (state.skeletonContext.fill (.fvar (environment.atomName slot))) =
      .fvar (environment.atomName slot) := by
    simpa [declaration, canonicalize] using
      canonicalize_fill_eq_of_collapse declaration (by decide) collapse
        (.fvar (environment.atomName slot))
  rw [reifiedFrame]
  exact canonicalizeByDepths_eq_fvar_of_canonicalize_eq key declaration
    availableDepth scopeDepth ordinaryCollapse

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
