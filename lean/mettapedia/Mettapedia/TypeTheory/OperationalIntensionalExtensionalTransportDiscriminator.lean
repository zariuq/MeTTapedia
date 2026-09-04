import Mettapedia.TypeTheory.OperationalIntensionalExtensionalDependentCellBoundary
import Mettapedia.TypeTheory.RouteTransportDiscriminator

/-!
# Transport discriminators at the operational--intensional--extensional boundary

This module applies the exact dependent-consumer criterion to the existing
operational/intensional/extensional specimen.

The selected mode semantics is locally thin: parallel semantic mode cells
cannot be distinguished by any covariant dependent family.  Raw authored
factorization histories may still differ, but their interpreted family actions
agree.  In contrast, revision-distinct rho routes and work-distinct graph
proofs induce genuine context 2-cells with explicit dependent-family
discriminators.

This is a level-separation theorem.  It neither promotes rho or graph proof
routes into mode cells nor collapses their proof relevance merely because the
selected mode-comparison layer is thin.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory
namespace OperationalIntensionalExtensionalTransportDiscriminator

open CategoryTheory
open CategoryIndexedFamilyTwoCellAction
open OperationalIntensionalExtensionalTwoComputad
open OperationalIntensionalExtensionalCellThinness
open OperationalIntensionalExtensionalSemanticThinness
open OperationalIntensionalExtensionalDependentCellBoundary
open ProofRelevantRouteFamilyBridge
open RouteTransportDiscriminator

universe u

/-! ## Selected semantic mode cells -/

/-- No covariant dependent family distinguishes parallel cells in the
selected locally thin semantic mode image. -/
theorem selected_semantic_cells_have_no_dependent_discriminator
    {source target : Mode} {first second : ModePath source target}
    (left right : SemanticCell.{u} first second) :
    ¬ HasWhiskeredFamilyDiscriminator left.toNatTrans right.toNatTrans := by
  rintro ⟨family, different⟩
  exact different
    (selected_semantic_family_actions_equal left right family)

/-- The raw factor round trip differs from reflexivity, but after semantic
interpretation there is no dependent-family consumer which can tell the two
cells apart. -/
theorem raw_factor_history_distinct_without_semantic_discriminator :
    factorRoundTrip ≠ factorIdentityCell ∧
      ¬ HasWhiskeredFamilyDiscriminator
        (interpretCell.{u} factorRoundTrip).toNatTrans
        (interpretCell.{u} factorIdentityCell).toNatTrans := by
  constructor
  · simpa [factorIdentityCell] using factorRoundTrip_not_reflexive
  · exact selected_semantic_cells_have_no_dependent_discriminator _ _

/-! ## Proof-relevant context cells -/

/-- The rho revision routes satisfy the exact required-consumer gate, with
the communication-history family as the explicit consumer. -/
theorem rho_revision_has_dependent_discriminator :
    HasDependentFamilyDiscriminator rhoZeroPointCell rhoOnePointCell :=
  ⟨ProofRelevantRouteFamilyBridge.Rho.communicationHistoryFamily,
    rho_revision_family_actions_distinct⟩

/-- The direct and detour graph proofs satisfy the same gate, with the native
graph-proof family as the explicit consumer. -/
theorem graph_work_has_dependent_discriminator :
    HasDependentFamilyDiscriminator graphDirectPointCell graphDetourPointCell :=
  ⟨ProofRelevantRouteFamilyBridge.Graph.pathGraphProofFamily,
    graph_work_family_actions_distinct⟩

/-- The explicit discriminators recover the already-proved inequality of the
underlying context cells via the generic exact criterion. -/
theorem proof_relevant_discriminators_recover_cell_distinctions :
    rhoZeroPointCell ≠ rhoOnePointCell ∧
      graphDirectPointCell ≠ graphDetourPointCell :=
  ⟨(hasDependentFamilyDiscriminator_iff_ne _ _).1
      rho_revision_has_dependent_discriminator,
    (hasDependentFamilyDiscriminator_iff_ne _ _).1
      graph_work_has_dependent_discriminator⟩

/-! ## Connected boundary -/

/-- Exact three-way boundary:

* raw construction history may be retained syntactically;
* the selected mode-comparison semantics has no dependent discriminator; and
* proof-relevant context routes may have required dependent consumers.

Thus local semantic thinness is an observer-certified implementation profile,
not a global proof-irrelevance principle. -/
theorem local_thinness_and_context_proof_relevance_coexist :
    (factorRoundTrip ≠ factorIdentityCell ∧
      ¬ HasWhiskeredFamilyDiscriminator
        (interpretCell.{u} factorRoundTrip).toNatTrans
        (interpretCell.{u} factorIdentityCell).toNatTrans) ∧
      HasDependentFamilyDiscriminator rhoZeroPointCell rhoOnePointCell ∧
      HasDependentFamilyDiscriminator graphDirectPointCell graphDetourPointCell :=
  ⟨raw_factor_history_distinct_without_semantic_discriminator,
    rho_revision_has_dependent_discriminator,
    graph_work_has_dependent_discriminator⟩

/-! ## Axiom audit -/

#print axioms selected_semantic_cells_have_no_dependent_discriminator
#print axioms raw_factor_history_distinct_without_semantic_discriminator
#print axioms rho_revision_has_dependent_discriminator
#print axioms graph_work_has_dependent_discriminator
#print axioms proof_relevant_discriminators_recover_cell_distinctions
#print axioms local_thinness_and_context_proof_relevance_coexist

end OperationalIntensionalExtensionalTransportDiscriminator
end Mettapedia.TypeTheory
