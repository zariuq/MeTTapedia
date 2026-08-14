import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryOccurrenceSupport
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostFillDeterminism

/-!
# Total occurrence-support profiles for hereditary rho Cost frames

This module derives the occurrence-indexed support profile of one static rho
Cost frame from the frame's real plan, caller-relative input safety, and the
recursive safety certificates of its boundary values.  The construction
retains positional occurrences until each semantic atom class receives its
greatest common reflective suffix.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

namespace CostStaticRegionNode

/-- Every classified inventory occurrence has a caller-relative support-safe
semantic value.  The availability is extracted from the exact occurrence in
the node's plan; source leaves use the input certificate and boundary leaves
use the corresponding recursive child certificate. -/
theorem exists_occurrenceAtomSafe
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable)
    (inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1)
    (support : ContextSupport.Support) (available : List TypeExpr)
    (binderImage : TypeExpr → TypeExpr)
    (childrenPreserve : CostStaticBoundaryChildReflectiveSupportPreserving
      node.boundaryTable values support binderImage)
    (inputSafe : node.term.2.1.ReflectiveSupportSafeAt
      rhoCIGSLT.costWholeReflectionProfile support available binderImage)
    (position : inventory.Occurrence) :
    ∃ occurrenceAvailable,
      (inventory.occurrenceAtom position).normalTyped.ReflectiveSupportSafeAt
        rhoCIGSLT.costWholeReflectionProfile support occurrenceAvailable
          binderImage := by
  let positional := planDecorationOccurrenceAt node inventory position
  obtain ⟨packed⟩ := nonempty_planOccurrenceAt node inventory position
  rcases packed with ⟨planAvailable, planOccurrence⟩
  let parameter := inventory.occurrenceAt position
  have nameEquality : parameter.fvarOccurrence.name = positional.name := by
    exact (planDecorationOccurrenceAt_name node inventory position).symm
  have semanticWitness := CostStaticRegionPlan.semanticLeafWitness node.plan
    rho_costWholeLanguage_collectionChoiceDeterministic node.boundaryTable
      values (fun _ membership => membership) inputSafe parameter
        planOccurrence.1 nameEquality childrenPreserve
  obtain ⟨_parameterName, occurrenceAvailable, semanticSafe⟩ :=
    semanticWitness
  exact ⟨occurrenceAvailable, semanticSafe.atomSafe⟩

/-- Assemble the total caller-relative occurrence support profile for an
explicit inventory and its executable semantic quotient. -/
noncomputable def occurrenceSupportProfile
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable)
    (inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1)
    (support : ContextSupport.Support) (available : List TypeExpr)
    (binderImage : TypeExpr → TypeExpr)
    (childrenPreserve : CostStaticBoundaryChildReflectiveSupportPreserving
      node.boundaryTable values support binderImage)
    (inputSafe : node.term.2.1.ReflectiveSupportSafeAt
      rhoCIGSLT.costWholeReflectionProfile support available binderImage) :
    CostStaticOccurrenceSupportProfile
      (CostStaticAtomEnvironment.ofInventory inventory) support binderImage := by
  classical
  let occurrenceSafe : ∀ position : inventory.Occurrence,
      ∃ occurrenceAvailable,
        (inventory.occurrenceAtom position).normalTyped.ReflectiveSupportSafeAt
          rhoCIGSLT.costWholeReflectionProfile support occurrenceAvailable
            binderImage :=
    fun position => exists_occurrenceAtomSafe node values inventory support
      available binderImage childrenPreserve inputSafe position
  let occurrenceAvailable : inventory.Occurrence → List TypeExpr :=
    fun position => Classical.choose (occurrenceSafe position)
  let classSupport : OccurrenceClassSupport
      (CostStaticAtomEnvironment.ofInventory inventory).occurrenceSlot :=
    OccurrenceClassSupport.ofSurjective occurrenceAvailable
      (CostStaticAtomEnvironment.ofInventory_occurrenceSlot_surjective
        inventory)
  exact
    { classSupport := classSupport
      occurrenceSafe := by
        intro position
        exact Classical.choose_spec (occurrenceSafe position) }

/-- Total occurrence support for the exact finite inventory and quotient
selected by hereditary normalization. -/
noncomputable def semanticOccurrenceSupportProfile
    {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable)
    (support : ContextSupport.Support) (available : List TypeExpr)
    (binderImage : TypeExpr → TypeExpr)
    (childrenPreserve : CostStaticBoundaryChildReflectiveSupportPreserving
      node.boundaryTable values support binderImage)
    (inputSafe : node.term.2.1.ReflectiveSupportSafeAt
      rhoCIGSLT.costWholeReflectionProfile support available binderImage) :
    let packed := node.semanticAtomEnvironment values
    CostStaticOccurrenceSupportProfile packed.2 support binderImage := by
  let packed := node.semanticAtomEnvironment values
  change CostStaticOccurrenceSupportProfile packed.2 support binderImage
  have environmentEquality : packed.2 =
      CostStaticAtomEnvironment.ofInventory packed.1 :=
    node.semanticAtomEnvironment_snd_eq_ofInventory_fst values
  rw [environmentEquality]
  exact occurrenceSupportProfile node values packed.1 support available
    binderImage childrenPreserve inputSafe

end CostStaticRegionNode

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
