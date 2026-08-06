import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryStaticStructuralClosure
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryRouteBreadthCanary

/-!
# Canary for the rho static-to-structural atom terminal

The established base Quote/Drop fixture is reclosed through the general
canonical-atom terminal.  This checks that the terminal consumes the actual
finite environment selected by a compiled static node rather than a hand-
written equality of final normal forms.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostGeneratorInvariantCounterexample
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryRouteBreadthCanary

/-- The breadth Quote/Drop node's reified frame selects one source-variable
atom for any complete value assignment. -/
noncomputable def rhoBreadthBaseRedexA_canonicalAtomWitness
    (values : TypedCostRegionBoundaryTable.Values rhoCIGSLT .base
      rhoCutOrderFree rhoBreadthBaseRedexANode.finiteBoundaryTable) :
    let environment := CostStaticAtomEnvironment.ofInventory
      (rhoBreadthBaseRedexANode.semanticAtomEnvironment values).1
    Σ slot : Fin environment.atomCount,
      PLift ((rhoBreadthBaseRedexANode.reifiedSourceFrame environment).1 =
        .apply rhoReflectivePresentation.quoteConstructor
          [.apply rhoReflectivePresentation.dropConstructor
            [.fvar (environment.atomName slot)]]) ×
      PLift ((.fvar "a" : Pattern) = environment.restore
        rhoBreadthBaseRedexANode.targetBound
          (.fvar (environment.atomName slot))) := by
  let inventory := (rhoBreadthBaseRedexANode.semanticAtomEnvironment values).1
  let environment := CostStaticAtomEnvironment.ofInventory inventory
  have sourceMembership : costRegionSourceVariableName "a" ∈
      rhoBreadthBaseRedexANode.skeleton.1.freeFvarNames := by
    rw [rhoBreadthBaseRedexANode_skeleton_pattern]
    simp [Pattern.freeFvarNames]
  let occurrenceExists := rhoBreadthBaseRedexANode.skeleton_fvar_covered
    (costRegionSourceVariableName "a") sourceMembership
  let occurrence := Classical.choose occurrenceExists
  have occurrenceName := Classical.choose_spec occurrenceExists
  have slotExists := environment.slotOfName?_isSome_of_occurrence occurrence
  let slot := (environment.slotOfName? occurrence.name).get slotExists
  have selectedAtOccurrence : environment.slotOfName? occurrence.name =
      some slot := (Option.some_get slotExists).symm
  have selected : environment.slotOfName? (costRegionSourceVariableName "a") =
      some slot := by
    rw [← occurrenceName]
    exact selectedAtOccurrence
  have reifiedSource :
      (rhoBreadthBaseRedexANode.reifiedSourceFrame environment).1 =
        .apply rhoReflectivePresentation.quoteConstructor
          [.apply rhoReflectivePresentation.dropConstructor
            [.fvar (environment.atomName slot)]] := by
    rw [rhoBreadthBaseRedexANode.reifiedSourceFrame_pattern]
    change environment.reify
      (.apply "NQuote"
        [.apply "PDrop" [.fvar (costRegionSourceVariableName "a")]]) = _
    simp [CostStaticAtomEnvironment.reify,
      CostStaticAtomEnvironment.reifyName, selected,
      rhoReflectivePresentation]
  refine ⟨slot, ⟨reifiedSource⟩, ⟨?_⟩⟩
  · exact
      ((Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticRegionNode.quoteDropSourceVariableSemanticAtomJoinWithInventory
        rhoBreadthBaseRedexANode values inventory occurrence "a"
          occurrenceName slot selectedAtOccurrence reifiedSource).rightFactors :
        (.fvar "a" : Pattern) = environment.restore
          rhoBreadthBaseRedexANode.targetBound
            (.fvar (environment.atomName slot)))

/-- The generic static-to-structural terminal reconstructs the exact
Quote/Drop atom join used by the hereditary executor. -/
noncomputable def rhoBreadthBaseRedexAJoin_viaCanonicalAtom :
    PackedCostSemanticAtomJoin rhoCIGSLT
      (Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticRegionNode.normalizeHereditary
        rhoBreadthBaseRedexANode
        (TypedCostRegionBoundaryTable.Values.original
          rhoBreadthBaseRedexANode.finiteBoundaryTable)).1
      (.fvar "a") := by
  obtain ⟨slot, canonicalFrame, rightFactors⟩ :=
    rhoBreadthBaseRedexA_canonicalAtomWitness
      (TypedCostRegionBoundaryTable.Values.original
        rhoBreadthBaseRedexANode.finiteBoundaryTable)
  rcases canonicalFrame with ⟨reifiedFrame⟩
  rcases rightFactors with ⟨rightFactors⟩
  have canonicalFrame :=
    CostStaticRegionNode.canonicalizeReifiedTargetFrame_quoteDrop_atom
      rhoBreadthBaseRedexANode _ slot reifiedFrame
  exact rhoCanonicalAtomSemanticJoin rhoBreadthBaseRedexANode
    (TypedCostRegionBoundaryTable.Values.original
      rhoBreadthBaseRedexANode.finiteBoundaryTable)
    slot canonicalFrame rightFactors

theorem rhoBreadthBaseRedexA_normalize_viaCanonicalAtom :
    (Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticRegionNode.normalizeHereditary
      rhoBreadthBaseRedexANode
      (TypedCostRegionBoundaryTable.Values.original
        rhoBreadthBaseRedexANode.finiteBoundaryTable)).1 = .fvar "a" :=
  rhoBreadthBaseRedexAJoin_viaCanonicalAtom.results_eq

/-- Structural free-variable endpoint exposed by the base Quote/Drop frame. -/
def rhoBreadthATree :
    CostRegionTree rhoCIGSLT rhoCutOrderFree [] [] (.fvar "a")
      (.base (costBaseSortName "Name")) :=
  .fvar (by simp [rhoCutOrderFree, FreeTypeContext.ofList])

/-- The full root bridge for the established Quote/Drop fixture is obtained
from the specialized asymmetric terminal, not from a final equality. -/
noncomputable def rhoBreadthBaseRedexABridge_viaQuoteDropAtom :
    CostRegionRootNormalizationBridge rhoCIGSLT
      rhoHereditaryNormalizationKernel rhoCutOrderFree
      rhoBreadthBaseRedexAStaticTree rhoBreadthATree := by
  let values := rhoBreadthBaseRedexAChildren.normalizeValues
    (normalizeStatic := rhoHereditaryStaticNormalizer)
  obtain ⟨slot, reifiedFrame, rightFactors⟩ :=
    rhoBreadthBaseRedexA_canonicalAtomWitness values
  rcases reifiedFrame with ⟨reifiedFrame⟩
  rcases rightFactors with ⟨rightFactors⟩
  apply rhoStaticRootBridgeOfQuoteDropAtom rhoBreadthBaseRedexANode
    rhoBreadthBaseRedexAChildren rhoBreadthATree slot reifiedFrame
  simpa [rhoBreadthATree, CostRegionTree.normalize] using rightFactors

theorem rhoBreadthBaseRedexABridge_viaQuoteDropAtom_results_eq :
    (rhoBreadthBaseRedexAStaticTree.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
      (rhoBreadthATree.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern :=
  rhoBreadthBaseRedexABridge_viaQuoteDropAtom.toTreeAlignment.normalize_pattern_eq

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
