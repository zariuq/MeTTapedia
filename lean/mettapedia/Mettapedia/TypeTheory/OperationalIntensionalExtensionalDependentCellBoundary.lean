import Mettapedia.TypeTheory.CategoryIndexedFamilyTwoCellAction
import Mettapedia.TypeTheory.OperationalIntensionalExtensionalCellThinness
import Mettapedia.TypeTheory.OperationalIntensionalExtensionalSemanticThinness
import Mettapedia.TypeTheory.ProofRelevantRouteFamilyBridge

/-!
# Dependent-family detection of operational, intensional, and extensional cells

The selected operational/intensional/extensional semantics lands in `Cat`.
Its natural transformations therefore act on covariant dependent families by
right whiskering.  Covariant representables prove that this action is jointly
faithful: two semantic cells agree exactly when they act identically on every
dependent family.

For the selected semantic image every parallel natural-transformation fibre
is already a subsingleton, so no dependent family separates the raw
factorization round trip from the reflexive cell after interpretation.  This
is contrasted with genuine proof-relevant context cells: revision-distinct rho
paths and work-distinct graph paths induce parallel point transformations that
their native dependent families do separate.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory
namespace OperationalIntensionalExtensionalDependentCellBoundary

open CategoryTheory CategoryTheory.Bicategory
open CategoryIndexedFamilyTwoCellAction
open OperationalIntensionalExtensionalTwoComputad
open OperationalIntensionalExtensionalCellThinness
open OperationalIntensionalExtensionalSemanticThinness
open ProofRelevantRouteFamilyBridge

universe u

/-! ## The exact dependent action of semantic cells -/

/-- Covariant dependent families over one selected semantic mode. -/
abbrev SemanticFamily (mode : Mode) :=
  CategoryTheory.Functor
    (semanticPseudofunctor.{u}.obj mode : Type (u + 1)) (Type u)

/-- A semantic cell acts on every family over its target mode. -/
def semanticFamilyAction
    {source target : Mode} {first second : ModePath source target}
    (cell : SemanticCell.{u} first second)
    (family : SemanticFamily.{u} target) :=
  whiskeredFamilyAction cell.toNatTrans family

@[simp] theorem semanticFamilyAction_app
    {source target : Mode} {first second : ModePath source target}
    (cell : SemanticCell.{u} first second)
    (family : SemanticFamily.{u} target)
    (object : semanticPseudofunctor.{u}.obj source) :
    (semanticFamilyAction cell family).app object =
      family.map (cell.toNatTrans.app object) :=
  rfl

/-- The action on all covariant families detects semantic-cell equality
exactly. -/
theorem semanticCell_eq_iff_all_family_actions_eq
    {source target : Mode} {first second : ModePath source target}
    (left right : SemanticCell.{u} first second) :
    left = right ↔
      ∀ family : SemanticFamily.{u} target,
        semanticFamilyAction left family =
          semanticFamilyAction right family := by
  constructor
  · intro equality family
    cases equality
    rfl
  · intro equalActions
    apply CategoryTheory.Cat.Hom₂.ext
    apply whiskeredDependentAction_injective
    funext family
    exact equalActions family

/-- In the selected `Cat` image every parallel semantic cell has the same
dependent action. -/
theorem selected_semantic_family_actions_equal
    {source target : Mode} {first second : ModePath source target}
    (left right : SemanticCell.{u} first second)
    (family : SemanticFamily.{u} target) :
    semanticFamilyAction left family =
      semanticFamilyAction right family := by
  exact congrArg (fun cell => semanticFamilyAction cell family)
    (Subsingleton.elim left right)

/-! ## Raw factorization history versus selected semantics -/

/-- Interpret a raw authored mode cell and then act on one dependent family. -/
def interpretedFamilyAction
    {source target : Mode} {first second : ModePath source target}
    (cell : ModeCell first second)
    (family : SemanticFamily.{u} target) :=
  semanticFamilyAction (interpretCell.{u} cell) family

/-- Although their raw construction histories differ, the factorization round
trip and the reflexive cell act identically on every family after the selected
semantic interpretation. -/
theorem factor_history_family_actions_equal
    (family : SemanticFamily.{u} Mode.extensional) :
    interpretedFamilyAction factorRoundTrip family =
      interpretedFamilyAction factorIdentityCell family := by
  exact congrArg (fun cell => semanticFamilyAction cell family)
    semantic_factor_history_identified

/-- Exact positive/negative boundary for the factorization history. -/
theorem factor_history_raw_distinct_semantically_family_equal
    (family : SemanticFamily.{u} Mode.extensional) :
    factorRoundTrip ≠ factorIdentityCell ∧
      interpretedFamilyAction factorRoundTrip family =
        interpretedFamilyAction factorIdentityCell family := by
  constructor
  · simpa [factorIdentityCell] using factorRoundTrip_not_reflexive
  · exact factor_history_family_actions_equal family

/-! ## Authentic rho and graph context-cell discriminators -/

/-- The revision-zero communication route as a context-level point cell. -/
noncomputable def rhoZeroPointCell :=
  @pointCell ProofRelevantRouteFamilyBridge.Rho.communicationContext _ _
    ProofRelevantRouteFamilyBridge.Rho.zeroRevisionPath

/-- The revision-one communication route as a context-level point cell. -/
noncomputable def rhoOnePointCell :=
  @pointCell ProofRelevantRouteFamilyBridge.Rho.communicationContext _ _
    ProofRelevantRouteFamilyBridge.Rho.oneRevisionPath

/-- Revision-distinct rho paths induce distinct natural transformations
between point substitutions. -/
theorem rho_revision_point_cells_distinct :
    rhoZeroPointCell ≠ rhoOnePointCell := by
  apply pointCell_injective.ne
  exact ProofRelevantRouteFamilyBridge.Rho.zeroRevisionPath_ne_oneRevisionPath

/-- The rho communication-history family distinguishes the actions of those
parallel point transformations. -/
theorem rho_revision_family_actions_distinct :
    familyAction
        rhoZeroPointCell
        ProofRelevantRouteFamilyBridge.Rho.communicationHistoryFamily ≠
      familyAction
        rhoOnePointCell
        ProofRelevantRouteFamilyBridge.Rho.communicationHistoryFamily := by
  exact pointCell_familyActions_ne_of_map_ne
    ProofRelevantRouteFamilyBridge.Rho.communicationHistoryFamily
    ProofRelevantRouteFamilyBridge.Rho.zeroRevisionPath
    ProofRelevantRouteFamilyBridge.Rho.oneRevisionPath _
    ProofRelevantRouteFamilyBridge.Rho.communicationHistoryFamily_distinguishes_revisions

/-- The direct native graph proof as a context-level point cell. -/
def graphDirectPointCell :=
  @pointCell
    (ProofRelevantRouteFamilyBridge.Graph.nativeProofContext
      Mettapedia.GraphTheory.Walk.Examples.pathGraph) _ _
    Mettapedia.GraphTheory.Walk.ModeCellProofThinnessBoundary.directProof

/-- The detour native graph proof as a context-level point cell. -/
def graphDetourPointCell :=
  @pointCell
    (ProofRelevantRouteFamilyBridge.Graph.nativeProofContext
      Mettapedia.GraphTheory.Walk.Examples.pathGraph) _ _
    Mettapedia.GraphTheory.Walk.ModeCellProofThinnessBoundary.detourProof

/-- Direct and detour graph proofs induce distinct natural transformations
between point substitutions. -/
theorem graph_work_point_cells_distinct :
    graphDirectPointCell ≠ graphDetourPointCell := by
  apply pointCell_injective.ne
  exact Mettapedia.GraphTheory.Walk.ModeCellProofThinnessBoundary.directProof_ne_detourProof

/-- The native graph-proof family distinguishes the actions of those parallel
point transformations. -/
theorem graph_work_family_actions_distinct :
    familyAction
        graphDirectPointCell
        ProofRelevantRouteFamilyBridge.Graph.pathGraphProofFamily ≠
      familyAction
        graphDetourPointCell
        ProofRelevantRouteFamilyBridge.Graph.pathGraphProofFamily := by
  exact pointCell_familyActions_ne_of_map_ne
    ProofRelevantRouteFamilyBridge.Graph.pathGraphProofFamily
    Mettapedia.GraphTheory.Walk.ModeCellProofThinnessBoundary.directProof
    Mettapedia.GraphTheory.Walk.ModeCellProofThinnessBoundary.detourProof _
    ProofRelevantRouteFamilyBridge.Graph.pathGraphProofFamily_distinguishes_work

/-! ## Connected level boundary -/

/-- The selected mode semantics erases the administrative factor history,
while the rho and graph context categories retain genuinely observable
parallel two-cells.  These are two different categorical levels. -/
theorem selected_mode_and_proof_relevant_context_cell_boundary :
    (∀ family : SemanticFamily.{u} Mode.extensional,
      interpretedFamilyAction factorRoundTrip family =
        interpretedFamilyAction factorIdentityCell family) ∧
      familyAction
          rhoZeroPointCell
          ProofRelevantRouteFamilyBridge.Rho.communicationHistoryFamily ≠
        familyAction
          rhoOnePointCell
          ProofRelevantRouteFamilyBridge.Rho.communicationHistoryFamily ∧
      familyAction
          graphDirectPointCell
          ProofRelevantRouteFamilyBridge.Graph.pathGraphProofFamily ≠
        familyAction
          graphDetourPointCell
          ProofRelevantRouteFamilyBridge.Graph.pathGraphProofFamily :=
  ⟨factor_history_family_actions_equal,
    rho_revision_family_actions_distinct,
    graph_work_family_actions_distinct⟩

/-! ## Axiom audit -/

#print axioms semanticCell_eq_iff_all_family_actions_eq
#print axioms factor_history_raw_distinct_semantically_family_equal
#print axioms rho_revision_family_actions_distinct
#print axioms graph_work_family_actions_distinct
#print axioms selected_mode_and_proof_relevant_context_cell_boundary

end OperationalIntensionalExtensionalDependentCellBoundary
end Mettapedia.TypeTheory
