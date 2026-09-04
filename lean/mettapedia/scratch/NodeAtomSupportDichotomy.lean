import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryBoundarySideCell

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

/-- Every semantic atom of a rho static node retains either the node's full
target binder support or the empty support introduced below quotation. -/
theorem CostStaticRegionNode.ofInventory_atomValue_targetSupport_eq_targetBound_or_nil
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable}
    (inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1)
    (slot : Fin (CostStaticAtomEnvironment.ofInventory inventory).atomCount) :
    ((CostStaticAtomEnvironment.ofInventory inventory).atomValue slot).key.targetSupport =
        node.targetBound ∨
      ((CostStaticAtomEnvironment.ofInventory inventory).atomValue slot).key.targetSupport =
        [] := by
  let environment := CostStaticAtomEnvironment.ofInventory inventory
  obtain ⟨position, rfl⟩ :=
    CostStaticAtomEnvironment.ofInventory_occurrenceSlot_surjective inventory
      slot
  rw [environment.occurrenceValue]
  change (inventory.occurrenceAt position).atom.key.targetSupport =
      node.targetBound ∨
    (inventory.occurrenceAt position).atom.key.targetSupport = []
  generalize parameterEquality : inventory.occurrenceAt position = parameter
  cases parameter with
  | sourceFVar occurrence decodedName targetLookup decodedType =>
      exact Or.inr rfl
  | boundary occurrence notSource resolved resolution =>
      have tableResolution :
          node.boundaryTable.resolve occurrence.name = some resolved.1 := by
        have agrees := values.resolve_boundary node.boundaryTable
          occurrence.name
        rw [resolution] at agrees
        simpa using agrees.symm
      have membership : resolved.1 ∈ node.boundaryTable.entries :=
        node.boundaryTable.mem_entries_of_resolve_eq_some tableResolution
      simpa [CostStaticParameterOccurrence.atom,
        TypedCostStaticAtom.ofBoundaryValue] using
          (CostStaticRegionNode.boundaryTargetSupport_eq_targetBound_or_nil
            node resolved.1 membership)

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
