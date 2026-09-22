import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentRetainedSemanticRequirements
import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentQuotientRetainedIdentity
import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentQuotientProducts
import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentQuotientProductCodes
import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentQuotientDeclarations
import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentQuotientServices
import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentQuotientMotiveAbstraction

/-!
# A jointly qualified retained-input native semantic profile

All 33 semantic clauses use one actual formed quotient interpretation, its
native universe/product/identity operations, the exact retained-input J run,
and one supplied registry. The actual declaration table uses that very same
interpretation. Source qualification, caller-required services and installed
declaration instances remain independent of the semantic construction.

The existing common assembly and original four-face service contract give
a concrete jointly qualified instance with nonempty wire/HOL declaration
requirements. A changed but admitted service payload still satisfies all
33 semantic clauses and fails the unchanged caller contract. A requested
missing declaration is rejected despite its independently formed type.

This is the retained-input comparison profile, not the original family-only
profile, a full six-family model, an external host model or a language-policy
selection. The original exact family-only J obstruction remains in force.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentQuotientRetainedSemantics

open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
open Presentation FormationSensitive SharedJudgmentFragment FormationSensitiveContextual
open Mettapedia.GSLT.LanguageDef KernelAuthority NIKMetalogic
open SharedJudgmentRetainedSemanticRequirements

universe uIndex uArtifact uEvidence

variable {Index : Type uIndex} {targets : Index → AdmissionObject.{uArtifact}}

/-- Raw data only. The supplied registry already has the same interpretation
as its index; no law about it is assumed or stored in this construction. -/
noncomputable def candidate (assembly : Assembly)
    (registry : SharedJudgmentServiceRegistry.Data.{uIndex, uArtifact, uEvidence}
      targets (SharedJudgmentQuotientInterpretation.data assembly)) :
    Data assembly (QuotientCwf.cwf assembly.rules) targets where
  interpretation := SharedJudgmentQuotientInterpretation.data assembly
  universes := SharedJudgmentQuotientUniverses.operations assembly
  products := QuotientProducts.products assembly.declarations
  sums := QuotientProducts.sums assembly.declarations
  frames := SharedJudgmentQuotientMotiveCoverage.frames assembly
  scope := QuotientRetainedIdentityInterface.Scope
  run := QuotientRetainedIdentityInterface.run
  reindexing := QuotientRetainedIdentityInterface.reindexing
  registry := registry
  declarations := SharedJudgmentQuotientDeclarations.declarations assembly

variable {assembly : Assembly}

/-- These are the unchanged predicate bodies, with their complete native
quantifiers, on the constructed record rather than unrelated inhabitants. -/
theorem shared_qualified
    (registry : SharedJudgmentServiceRegistry.Data.{uIndex, uArtifact, uEvidence}
      targets (SharedJudgmentQuotientInterpretation.data assembly)) :
    ∀ requirement, sharedHolds requirement (candidate assembly registry) := by
  intro requirement
  cases requirement with
  | admittedTotal => exact SharedJudgmentQuotientInterpretation.admitted_total
  | substitutionsTotal => exact SharedJudgmentQuotientInterpretation.substitutions_total
  | substitutionConstructors => exact SharedJudgmentQuotientInterpretation.substitution_constructors
  | typeSubstitution => exact SharedJudgmentQuotientInterpretation.substitution_stable.1
  | termSubstitution => exact SharedJudgmentQuotientInterpretation.substitution_stable.2
  | conversion => exact SharedJudgmentQuotientInterpretation.conversion_invariant
  | annotation => exact SharedJudgmentQuotientInterpretation.annotation_transport
  | comprehension => exact SharedJudgmentQuotientInterpretation.comprehension_coverage
  | families => exact SharedJudgmentQuotientInterpretation.family_coverage
  | piFormation => exact SharedJudgmentQuotientProducts.pi_formation_meaning
  | piIntroduction => exact SharedJudgmentQuotientProducts.pi_introduction_meaning
  | piElimination => exact SharedJudgmentQuotientProducts.pi_elimination_meaning
  | piBeta => exact SharedJudgmentQuotientProducts.pi_beta
  | sigmaFormation => exact SharedJudgmentQuotientProducts.sigma_formation_meaning
  | sigmaIntroduction => exact SharedJudgmentQuotientProducts.sigma_introduction_meaning
  | sigmaElimination => exact SharedJudgmentQuotientProducts.sigma_elimination_meaning
  | sigmaBeta => exact SharedJudgmentQuotientProducts.sigma_beta
  | identityFormation => exact SharedJudgmentQuotientIdentity.identity_formation_meaning
  | reflexivity => exact SharedJudgmentQuotientIdentity.reflexivity_meaning
  | motives => exact SharedJudgmentQuotientMotiveCoverage.based_motive_coverage
  | basedBoundary => exact SharedJudgmentQuotientMotiveCoverage.based_boundary
  | sortMeaning => exact SharedJudgmentQuotientUniverses.sort_meaning
  | codeTotal => exact SharedJudgmentQuotientUniverses.code_total
  | codesDecode => exact SharedJudgmentQuotientUniverses.codes_decode
  | cumulativeMeaning => exact SharedJudgmentQuotientUniverses.cumulative_meaning
  | universeSubstitution => exact SharedJudgmentQuotientUniverses.universe_substitution
  | piCodeMeaning => exact SharedJudgmentQuotientProductCodes.pi_code_meaning
  | sigmaCodeMeaning => exact SharedJudgmentQuotientProductCodes.sigma_code_meaning

theorem retained_qualified
    (registry : SharedJudgmentServiceRegistry.Data.{uIndex, uArtifact, uEvidence}
      targets (SharedJudgmentQuotientInterpretation.data assembly)) :
    ∀ requirement, retainedHolds requirement (candidate assembly registry) := by
  intro requirement
  cases requirement with
  | frameCoverage => exact SharedJudgmentQuotientRetainedIdentity.frame_coverage
  | scopeCoverage => exact SharedJudgmentQuotientRetainedIdentity.scope_coverage
  | constructorMeaning => exact SharedJudgmentQuotientRetainedIdentity.constructor_meaning
  | admittedBeta => exact SharedJudgmentQuotientRetainedIdentity.admitted_beta
  | admittedSubstitution => exact SharedJudgmentQuotientRetainedIdentity.admitted_substitution

theorem semantic_qualified
    (registry : SharedJudgmentServiceRegistry.Data.{uIndex, uArtifact, uEvidence}
      targets (SharedJudgmentQuotientInterpretation.data assembly)) :
    semanticSpecification.Satisfies (candidate assembly registry) := by
  intro requirement _
  cases requirement with
  | shared requirement => exact shared_qualified registry requirement
  | retained requirement => exact retained_qualified registry requirement

/-- Required entries must really be installed and formed. This hypothesis
supplies only presence; the other three table laws are constructed. -/
theorem declarations_qualified
    (registry : SharedJudgmentServiceRegistry.Data.{uIndex, uArtifact, uEvidence}
      targets (SharedJudgmentQuotientInterpretation.data assembly))
    (required : SharedJudgmentDeclarationInterpretation.Instance → Prop)
    (present : ∀ slot, required slot → slot.Admitted assembly) :
    ∀ requirement, declarationHolds required requirement (candidate assembly registry) := by
  intro requirement
  cases requirement with
  | present => exact present
  | coverage => exact SharedJudgmentQuotientDeclarations.coverage required
  | typeMeaning => exact SharedJudgmentQuotientDeclarations.closed_type_agreement
  | headMeaning => exact SharedJudgmentQuotientDeclarations.closed_head_agreement

/-- The remaining conditions are exactly the independent source assembly,
the caller's original service contract and actual required-entry presence.
All semantic and declaration-meaning clauses have already been constructed. -/
theorem qualified_iff
    (registry : SharedJudgmentServiceRegistry.Data.{uIndex, uArtifact, uEvidence}
      targets (SharedJudgmentQuotientInterpretation.data assembly))
    (contract : SharedJudgmentServiceRegistry.Contract.{uIndex, uArtifact, uEvidence} targets)
    (required : SharedJudgmentDeclarationInterpretation.Instance → Prop) :
    (SharedJudgmentRetainedSemanticRequirements.specification contract required).Satisfies
        (candidate assembly registry) ↔
      SharedJudgmentFragment.specification.Satisfies assembly ∧
      (SharedJudgmentServiceRegistry.requiredSpecification contract
        (SharedJudgmentQuotientInterpretation.data assembly)).Satisfies registry ∧
      (∀ slot, required slot → slot.Admitted assembly) := by
  rw [SharedJudgmentRetainedSemanticRequirements.satisfies_iff]
  constructor
  · rintro ⟨source, _, services, declarations⟩
    exact ⟨source, services, declarations .present⟩
  · rintro ⟨source, services, present⟩
    exact ⟨source, fun requirement => semantic_qualified registry requirement (requirement_mem requirement),
      services, declarations_qualified registry required present⟩

namespace Controls

open SharedJudgmentDeclarationInterpretation.Controls (naturalInstance natural_admitted)
open SharedJudgmentQuotientDeclarations.Controls (holUniversalInstance hol_universal_admitted missingInstance)
open SharedJudgmentServiceRegistry.Controls (targets contract)

/-- The caller names two actual declarations; their admission is proved
afterwards, not used as the definition of what the caller requires. -/
def requiredDeclarations (slot : SharedJudgmentDeclarationInterpretation.Instance) : Prop :=
  slot = naturalInstance 7 LevelExpr.param ∨ slot = holUniversalInstance

theorem required_declarations_present :
    ∀ slot, requiredDeclarations slot → slot.Admitted common := by
  intro slot required
  rcases required with rfl | rfl
  · exact natural_admitted 7 LevelExpr.param
  · exact hol_universal_admitted

theorem required_declarations_nonempty : ∃ slot, requiredDeclarations slot :=
  ⟨naturalInstance 7 LevelExpr.param, Or.inl rfl⟩

noncomputable def commonCandidate := candidate common SharedJudgmentQuotientServices.registry

/-- One actual record meets the 33 semantic clauses, seven source clauses,
all six original service/binding clauses, and four declaration clauses. -/
theorem common_qualified :
    (SharedJudgmentRetainedSemanticRequirements.specification contract requiredDeclarations).Satisfies
      commonCandidate :=
  (qualified_iff SharedJudgmentQuotientServices.registry contract requiredDeclarations).mpr
    ⟨SharedJudgmentFragment.common_qualified, SharedJudgmentQuotientServices.required_registry_qualified,
      required_declarations_present⟩

theorem retained_scope_nonempty : ∃ input, commonCandidate.scope input :=
  qualified_scope_nonempty commonCandidate (semantic_qualified SharedJudgmentQuotientServices.registry)

/-- Correct independent native meanings of a changed output do not meet
the caller's requested surface, despite all 33 semantic laws remaining true. -/
theorem changed_payload_semantics_without_contract :
    semanticSpecification.Satisfies (candidate common SharedJudgmentQuotientServices.Controls.wrongPayload) ∧
      ¬ (SharedJudgmentRetainedSemanticRequirements.specification contract requiredDeclarations).Satisfies
        (candidate common SharedJudgmentQuotientServices.Controls.wrongPayload) := by
  refine ⟨semantic_qualified _, ?_⟩
  intro qualified
  exact SharedJudgmentQuotientServices.Controls.changed_payload_rejected
    (((qualified_iff _ contract requiredDeclarations).mp qualified).2.1)

/-- A requested absent head does not pass by table-coverage vacuity. Its
type remains independently formed under these very same native rules. -/
theorem missing_required_declaration_rejected :
    Judgment common.rules .nil missingInstance.entry.type (sortTm Tower.zero) ∧
      ¬ (SharedJudgmentRetainedSemanticRequirements.specification contract
        (fun slot => requiredDeclarations slot ∨ slot = missingInstance)).Satisfies commonCandidate := by
  refine ⟨SharedJudgmentQuotientDeclarations.Controls.formed_annotation_missing_name.1, ?_⟩
  intro qualified
  have present := ((qualified_iff SharedJudgmentQuotientServices.registry contract
    (fun slot => requiredDeclarations slot ∨ slot = missingInstance)).mp qualified).2.2
  have admitted := present missingInstance (Or.inr rfl)
  have absent := SharedJudgmentQuotientDeclarations.Controls.formed_annotation_missing_name.2
  have selected := SharedJudgmentQuotientDeclarations.selected_of_admitted missingInstance admitted
  rw [absent] at selected
  cases selected

/-- The newly qualified profile does not turn the old exact family-only
J condition into a theorem. The established native collision still refutes
that condition for every total operation retaining the canonical frames. -/
theorem original_family_only_conflict
    (operations : SharedJudgmentTypeInterpretation.Operations (QuotientCwf.cwf common.rules))
    (sameFrames : operations.frames = commonCandidate.frames) :
    ¬ SharedJudgmentTypeInterpretation.BasedJMeaning commonCandidate.interpretation operations :=
  SharedJudgmentQuotientMotiveAbstraction.Controls.no_total_exact_constructor operations sameFrames

end Controls

#print axioms semantic_qualified
#print axioms declarations_qualified
#print axioms qualified_iff
#print axioms Controls.common_qualified
#print axioms Controls.changed_payload_semantics_without_contract
#print axioms Controls.missing_required_declaration_rejected
#print axioms Controls.original_family_only_conflict

end Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentQuotientRetainedSemantics
