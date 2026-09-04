import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryBoundarySideCell

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

theorem CostStaticPlanReached.parentAtomTargetSupport_eq_nil_of_quoteRoot
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {payload : Pattern}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (reached : CostStaticPlanReached rhoCIGSLT color targetFree payload
      node.plan.abstractPattern)
    (admission : reached.plan.RawAdmission)
    (frameFree : WellSorted.ReflectiveSubstitutionBinderFree
      reached.plan.abstractPattern = true)
    (quoteRoot : reached.plan.rootClass =
      CostStaticPlanRootClass.application
        rhoReflectivePresentation.quoteConstructor)
    (embedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      reached.plan.boundaryTable.entries node.plan.boundaryTable.entries)
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable}
    {inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1}
    (environment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      inventory)
    {name : String}
    (membership : name ∈
      (environment.reify reached.plan.abstractPattern).freeFvarNames)
    (slot : Fin environment.atomCount)
    (selected : environment.lookupAtom? name = some slot) :
    (environment.atomValue slot).key.targetSupport = [] := by
  have abstractObject :
      WellSorted.isObjectPattern reached.plan.abstractPattern = true :=
    reached.plan.abstractPattern_object admission.object
  obtain ⟨originalName, originalMembership, reifiedName⟩ :=
    environment.exists_originalName_of_mem_freeFvarNames_reify_of_object
      reached.plan.abstractPattern abstractObject membership
  obtain ⟨localOccurrence, localName⟩ :=
    CostStaticFVarOccurrence.exists_of_mem_freeFvarNames_of_object
      originalMembership abstractObject
  let parentOccurrence : CostStaticFVarOccurrence node.skeleton.1 :=
    CostStaticFVarOccurrence.castRoot
      (reached.abstract_eq.symm.trans node.skeleton_pattern.symm)
      (localOccurrence.inContext reached.skeletonContext)
  have parentName : parentOccurrence.name = originalName := by
    simp [parentOccurrence, localName]
  obtain ⟨parentSlot, parentSelected⟩ := Option.isSome_iff_exists.mp
    (environment.slotOfName?_isSome_of_occurrence parentOccurrence)
  have originalSelected : environment.slotOfName? originalName =
      some parentSlot := by
    simpa [parentName] using parentSelected
  have reifiedNameAtSlot : environment.reifyName originalName =
      environment.atomName parentSlot := by
    simp [CostStaticAtomEnvironment.reifyName, originalSelected]
  have selectedAtSlot : environment.lookupAtom?
      (environment.atomName parentSlot) = some slot := by
    rw [← reifiedNameAtSlot, reifiedName]
    exact selected
  have slotEq : parentSlot = slot := by
    rw [environment.lookupAtom?_atomName] at selectedAtSlot
    exact Option.some.inj selectedAtSlot
  subst slot
  have localSubset : reached.plan.boundaryTable.entries ⊆
      reached.plan.boundaryTable.entries := fun _ membership => membership
  obtain ⟨typed, _safe⟩ :=
    reached.plan.abstractPattern_supportedSafe reached.plan.boundaryTable
      localSubset
  obtain ⟨freeType, typedName⟩ :=
    typed.toHasType.freeType_of_mem_freeFvarNames_of_isObjectPattern
      abstractObject originalMembership
  have parentSupport : node.plan.boundaryTable.restorationSupport
      originalName = [] := by
    apply reached.plan.boundaryTable.restorationSupport_eq_nil_of_entries_subset
      node.plan.boundaryTable embedding.subset
    · intro boundary boundaryMembership
      exact
        Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticRegionPlan.boundaryTargetSupport_eq_nil_of_quoteRoot
          reached.plan frameFree boundary boundaryMembership quoteRoot
    · exact typedName
  rw [environment.atomValue_targetSupport_eq_of_slotOfName?_eq_some
    parentOccurrence parentSlot parentSelected]
  simpa only [CostStaticRegionNode.boundaryTable, parentName] using
    parentSupport

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
