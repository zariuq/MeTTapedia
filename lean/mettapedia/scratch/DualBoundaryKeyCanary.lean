import ClaudeDualBoundary
import Mettapedia.GSLT.LanguageDef.CostRestorationBoundaryVariable

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus
namespace ClaudeDualBoundary

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryProviderCrossColorReachedCanary
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryCrossColorQuadrantCanary

noncomputable def deepEntryIndex :
    Fin deepViewPair.2.node.finiteBoundaryTable.entries.length :=
  ⟨0, by rw [deepEntries_length]; decide⟩

noncomputable def deepKernelTable :
    TypedCostRegionBoundaryTable rhoCIGSLT deepViewPair.1
      FreeTypeContext.empty deepViewPair.2.node.plan.occurrences :=
  deepViewPair.2.node.finiteBoundaryTable

noncomputable def deepKernelValues :
    TypedCostRegionBoundaryTable.Values rhoCIGSLT deepViewPair.1
      FreeTypeContext.empty deepKernelTable :=
  deepViewPair.2.children.normalizeValues
    (normalizeStatic := rhoHereditaryNormalizationKernel.normalize)

noncomputable def deepKernelEntryName : String :=
  costRegionBoundaryVariableName
    ((deepViewPair.2.children.getEntry deepEntryIndex).boundary.boundary)

theorem deepResolved_obtain :
    ∃ resolved : TypedCostRegionBoundaryTable.Values.Resolved rhoCIGSLT
        deepViewPair.1 FreeTypeContext.empty,
      deepKernelValues.resolve deepKernelTable deepKernelEntryName =
        some resolved ∧
      resolved.2.1 =
        (((deepViewPair.2.children.getEntry deepEntryIndex)
          ).tree.normalizedBoundaryValue rhoHereditaryNormalizationKernel).1 := by
  obtain ⟨resolved, resolution, _resolvedBoundary, resolvedNormal⟩ :=
    deepViewPair.2.children.exists_resolve_normalizedValue_eq_getEntry
      (kernel := rhoHereditaryNormalizationKernel)
      CostCanonicalLaws.rho_unambiguousStaticDecomposition deepEntryIndex
  exact ⟨resolved, resolution, resolvedNormal⟩

theorem deepEntryTree_normalize_eq :
    ((deepViewPair.2.children.getEntry deepEntryIndex).tree.normalize
        (normalizeStatic := rhoHereditaryNormalizationKernel.normalize)).pattern =
      (rightTree.normalize
        (normalizeStatic := rhoHereditaryNormalizationKernel.normalize)).pattern := by
  have object : WellSorted.isObjectPattern rightPattern = true := by
    decide
  exact CostRegionTree.normalize_pattern_eq_of_unambiguous
    CostCanonicalLaws.rho_unambiguousStaticDecomposition
    rhoHereditaryNormalizationKernel
    (deepViewPair.2.children.getEntry deepEntryIndex).tree rightTree object

theorem deepStoredEntry_eq_deepBoundaryEntry :
    (deepViewPair.2.children.getEntry deepEntryIndex).boundary =
      deepBoundaryEntry := by
  rfl

theorem deepAtom_assignment_resolved :
    deepKernelValues.assignment deepKernelTable deepOccurrence.name =
      (((deepViewPair.2.children.getEntry deepEntryIndex)
        ).tree.normalizedBoundaryValue rhoHereditaryNormalizationKernel).1 := by
  obtain ⟨resolved, resolution, resolvedNormal⟩ := deepResolved_obtain
  rw [← resolvedNormal]
  rw [TypedCostRegionBoundaryTable.Values.assignment.eq_unfold]
  dsimp only []
  rw [show deepOccurrence.name =
      costRegionBoundaryVariableName deepBoundaryEntry.boundary from rfl]
  rw [decodeCostRegionSourceVariableName_boundary]
  rw [show costRegionBoundaryVariableName deepBoundaryEntry.boundary =
      deepKernelEntryName from by
    rw [deepKernelEntryName,
      congrArg costRegionBoundaryVariableName
        (congrArg (·.boundary) deepStoredEntry_eq_deepBoundaryEntry)]]
  rw [resolution]

theorem deepAtom_normal :
    (deepEnv.atomValue deepSlot).key.normal = rightPattern := by
  have viaAssignment := deepEnv.atomValue_normal_eq_of_slotOfName?_eq_some
    (values := deepKernelValues) deepOccurrence deepSlot deepSlot_selected
  rw [viaAssignment]
  rw [deepAtom_assignment_resolved]
  rw [CostRegionTree.normalizedBoundaryValue_pattern]
  rw [deepEntryTree_normalize_eq]
  rw [rightTree_normalizeK]

noncomputable def leftAtomKey : CostStaticAtomKey :=
  (leftEnv.atomValue leftSlot).key

noncomputable def deepAtomKey : CostStaticAtomKey :=
  (deepEnv.atomValue deepSlot).key

theorem leftResolvedForKey_exists :
    ∃ resolved : TypedCostRegionBoundaryTable.Values.Resolved rhoCIGSLT
        leftViewPair.1 FreeTypeContext.empty,
      leftKernelValues.resolve leftKernelTable leftOccurrence.name =
          some resolved ∧
        resolved.1 =
          (leftViewPair.2.children.getEntry leftEntryIndex).boundary ∧
        resolved.2.1 =
          (((leftViewPair.2.children.getEntry leftEntryIndex)
            ).tree.normalizedBoundaryValue
              rhoHereditaryNormalizationKernel).1 := by
  obtain ⟨resolved, resolutionAtEntry, resolvedBoundary, resolvedNormal⟩ :=
    leftViewPair.2.children.exists_resolve_normalizedValue_eq_getEntry
      (kernel := rhoHereditaryNormalizationKernel)
      CostCanonicalLaws.rho_unambiguousStaticDecomposition leftEntryIndex
  refine ⟨resolved, ?_, resolvedBoundary, resolvedNormal⟩
  rw [show leftOccurrence.name =
    costRegionBoundaryVariableName
      ((leftViewPair.2.children.getEntry leftEntryIndex).boundary.boundary) from by
    rw [show leftOccurrence.name =
        costRegionBoundaryVariableName leftBoundaryEntry.boundary from rfl,
      ← congrArg costRegionBoundaryVariableName
        (congrArg (·.boundary) leftStoredEntry_eq_leftBoundaryEntry)]]
  exact resolutionAtEntry

noncomputable def leftResolvedForKey :=
  Classical.choose leftResolvedForKey_exists

theorem leftResolvedForKey_resolution :
    leftKernelValues.resolve leftKernelTable leftOccurrence.name =
      some leftResolvedForKey :=
  (Classical.choose_spec leftResolvedForKey_exists).1

theorem leftResolvedForKey_boundary :
    leftResolvedForKey.1 =
      (leftViewPair.2.children.getEntry leftEntryIndex).boundary :=
  (Classical.choose_spec leftResolvedForKey_exists).2.1

theorem leftResolvedForKey_normal :
    leftResolvedForKey.2.1 =
      (((leftViewPair.2.children.getEntry leftEntryIndex)
        ).tree.normalizedBoundaryValue rhoHereditaryNormalizationKernel).1 :=
  (Classical.choose_spec leftResolvedForKey_exists).2.2

theorem deepResolvedForKey_exists :
    ∃ resolved : TypedCostRegionBoundaryTable.Values.Resolved rhoCIGSLT
        deepViewPair.1 FreeTypeContext.empty,
      deepKernelValues.resolve deepKernelTable deepOccurrence.name =
          some resolved ∧
        resolved.1 =
          (deepViewPair.2.children.getEntry deepEntryIndex).boundary ∧
        resolved.2.1 =
          (((deepViewPair.2.children.getEntry deepEntryIndex)
            ).tree.normalizedBoundaryValue
              rhoHereditaryNormalizationKernel).1 := by
  obtain ⟨resolved, resolutionAtEntry, resolvedBoundary, resolvedNormal⟩ :=
    deepViewPair.2.children.exists_resolve_normalizedValue_eq_getEntry
      (kernel := rhoHereditaryNormalizationKernel)
      CostCanonicalLaws.rho_unambiguousStaticDecomposition deepEntryIndex
  refine ⟨resolved, ?_, resolvedBoundary, resolvedNormal⟩
  rw [show deepOccurrence.name =
    costRegionBoundaryVariableName
      ((deepViewPair.2.children.getEntry deepEntryIndex).boundary.boundary) from by
    rw [show deepOccurrence.name =
        costRegionBoundaryVariableName deepBoundaryEntry.boundary from rfl,
      ← congrArg costRegionBoundaryVariableName
        (congrArg (·.boundary) deepStoredEntry_eq_deepBoundaryEntry)]]
  exact resolutionAtEntry

noncomputable def deepResolvedForKey :=
  Classical.choose deepResolvedForKey_exists

theorem deepResolvedForKey_resolution :
    deepKernelValues.resolve deepKernelTable deepOccurrence.name =
      some deepResolvedForKey :=
  (Classical.choose_spec deepResolvedForKey_exists).1

theorem deepResolvedForKey_boundary :
    deepResolvedForKey.1 =
      (deepViewPair.2.children.getEntry deepEntryIndex).boundary :=
  (Classical.choose_spec deepResolvedForKey_exists).2.1

theorem deepResolvedForKey_normal :
    deepResolvedForKey.2.1 =
      (((deepViewPair.2.children.getEntry deepEntryIndex)
        ).tree.normalizedBoundaryValue rhoHereditaryNormalizationKernel).1 :=
  (Classical.choose_spec deepResolvedForKey_exists).2.2

theorem leftOccurrence_notSource :
    decodeCostRegionSourceVariableName leftOccurrence.name = none := by
  simpa only [leftOccurrence, leftBoundaryVarName] using
    decodeCostRegionSourceVariableName_boundary leftBoundaryEntry.boundary

theorem deepOccurrence_notSource :
    decodeCostRegionSourceVariableName deepOccurrence.name = none := by
  simpa only [deepOccurrence, deepBoundaryVarName] using
    decodeCostRegionSourceVariableName_boundary deepBoundaryEntry.boundary

theorem dualResolved_sameFiber : CostRegionBoundary.SameFiber
    leftResolvedForKey.1.boundary deepResolvedForKey.1.boundary := by
  rw [leftResolvedForKey_boundary, deepResolvedForKey_boundary]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem dualResolved_normalEq :
    leftResolvedForKey.2.1 = deepResolvedForKey.2.1 := by
  rw [leftResolvedForKey_normal, deepResolvedForKey_normal,
      CostRegionTree.normalizedBoundaryValue_pattern,
      CostRegionTree.normalizedBoundaryValue_pattern]
  exact leftEntryTree_normalize_eq.trans deepEntryTree_normalize_eq.symm

theorem leftAtomValue_eq_resolved :
    leftEnv.atomValue leftSlot =
      TypedCostStaticAtom.ofBoundaryValue leftResolvedForKey.1
        leftResolvedForKey.2 :=
  leftEnv.atomValue_eq_ofBoundaryValue_of_slotOfName?_eq_some
    leftOccurrence leftSlot leftSlot_selected leftOccurrence_notSource
      leftResolvedForKey leftResolvedForKey_resolution

theorem deepAtomValue_eq_resolved :
    deepEnv.atomValue deepSlot =
      TypedCostStaticAtom.ofBoundaryValue deepResolvedForKey.1
        deepResolvedForKey.2 :=
  deepEnv.atomValue_eq_ofBoundaryValue_of_slotOfName?_eq_some
    deepOccurrence deepSlot deepSlot_selected deepOccurrence_notSource
      deepResolvedForKey deepResolvedForKey_resolution

theorem dualResolved_key_eq :
    (TypedCostStaticAtom.ofBoundaryValue leftResolvedForKey.1
        leftResolvedForKey.2).key =
      (TypedCostStaticAtom.ofBoundaryValue deepResolvedForKey.1
        deepResolvedForKey.2).key := by
  exact CostStaticAtomKey.ext_components dualResolved_sameFiber.type_eq
    dualResolved_sameFiber.support_eq dualResolved_sameFiber.targetType_eq
      dualResolved_sameFiber.targetSupport_eq dualResolved_normalEq

theorem dualAtomKey_screen
    (keyEq : (leftEnv.atomValue leftSlot).key =
      (deepEnv.atomValue deepSlot).key) :
    leftAtomKey = deepAtomKey := by
  simpa only [leftAtomKey, deepAtomKey] using keyEq

theorem dual_atom_keys_eq : leftAtomKey = deepAtomKey := by
  apply dualAtomKey_screen
  rw [congrArg TypedCostStaticAtom.key leftAtomValue_eq_resolved,
    congrArg TypedCostStaticAtom.key deepAtomValue_eq_resolved]
  exact dualResolved_key_eq

theorem dual_atom_keys_eq_raw :
    (leftEnv.atomValue leftSlot).key =
      (deepEnv.atomValue deepSlot).key := by
  simpa only [leftAtomKey, deepAtomKey] using dual_atom_keys_eq

end ClaudeDualBoundary
end Mettapedia.Languages.ProcessCalculi.RhoCalculus
