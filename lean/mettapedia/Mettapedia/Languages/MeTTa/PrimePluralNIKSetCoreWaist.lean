import Mettapedia.GSLT.LanguageDef.CertifiedTheoryCategory
import Mettapedia.Languages.MeTTa.PrimePluralNIKWaist
import Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority

/-!
# External set semantics in the plural Prime NIK waist

This module extends the existing three-authority Prime waist with a fourth,
independently meaningful Megalodon set-core authority.  The original selected
Mathdata profile remains present as its own native-theoremhood node.  The new
node instead accepts only a structurally covered fragment and interprets its
claims in every extensional membership model of that fragment.

The extension is a conservative coproduct.  It adds no conversion between the
native selected profile and the external semantic profile.  In particular,
semantic host irrelevance preserves the meaning of set-core claims when they
enter the larger waist, while authority tags still prevent certificates from
crossing between the two Megalodon-facing nodes.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimePluralNIKSetCoreWaist

open Mettapedia.GSLT.LanguageDef.CheckerAuthorityFamily
open Mettapedia.GSLT.LanguageDef.CertifiedTheoryCategory
open Mettapedia.GSLT.LanguageDef.NIKHeterogeneousTheory

private abbrev primeTheory :=
  Mettapedia.Languages.MeTTa.PrimePluralNIKWaist.theory
private abbrev primeContract :=
  Mettapedia.Languages.MeTTa.PrimePluralNIKWaist.contract
private abbrev setCoreTheory :=
  Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority.theory
private abbrev setCoreContract :=
  Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority.contract

abbrev Kind :=
  Sum Mettapedia.Languages.MeTTa.PrimePluralNIKWaist.Kind Unit

/-- The original plural waist and the external set-core authority coexist
without identifying their signatures, claims, certificates, or meanings. -/
def theory := Coproduct.theory primeTheory setCoreTheory

/-- The outer tag selects either the established Prime waist or the external
set-core checker. -/
def contract :=
  Coproduct.contract primeTheory setCoreTheory primeContract setCoreContract

/-- The established three-authority waist enters the extension exactly. -/
def primeInclusion :=
  Coproduct.leftInclusion primeTheory setCoreTheory primeContract setCoreContract

/-- The external set-core authority enters the extension exactly. -/
def setCoreInclusion :=
  Coproduct.rightInclusion primeTheory setCoreTheory primeContract setCoreContract

theorem primeInclusion_conservative :
    primeInclusion.toTheoryTranslation.Conservative :=
  Coproduct.leftInclusion_conservative primeTheory setCoreTheory
    primeContract setCoreContract

theorem setCoreInclusion_conservative :
    setCoreInclusion.toTheoryTranslation.Conservative :=
  Coproduct.rightInclusion_conservative primeTheory setCoreTheory
    primeContract setCoreContract

private theorem setCoreIdentity_conservative :
    (TheoryTranslation.identity setCoreTheory).Conservative where
  scope_reflecting := by intro kind claim inScope; exact inScope
  meaning_reflecting := by intro kind claim meaningful; exact meaningful

/-! ## Concrete semantic host irrelevance -/

/-- Adding the larger Prime host changes neither the covered set-core scope
nor its independently stated model-theoretic meaning. -/
theorem setCore_scope_is_host_irrelevant
    (formula : Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority.ClosedFormula) :
    setCoreTheory.Scope () formula <->
      theory.Scope (.inr ()) formula :=
  HostIrrelevance.scope_iff
    (TheoryTranslation.identity setCoreTheory)
    setCoreInclusion.toTheoryTranslation
    setCoreIdentity_conservative
    setCoreInclusion_conservative
    () formula

theorem setCore_meaning_is_host_irrelevant
    (formula : Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority.ClosedFormula) :
    setCoreTheory.Meaning () formula <->
      theory.Meaning (.inr ()) formula :=
  HostIrrelevance.meaning_iff
    (TheoryTranslation.identity setCoreTheory)
    setCoreInclusion.toTheoryTranslation
    setCoreIdentity_conservative
    setCoreInclusion_conservative
    () formula

/-! ## Positive and negative controls -/

/-- The independently meaningful set-core identity theorem replays through
the extended dispatcher. -/
theorem setCore_identity_replays :
    (contract.checker (.inr ())).check
        Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority.identityFormula
        (Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority.reflexiveProof
          Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority.predicateFormula) =
      true :=
  Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority.identity_replays

/-- Its meaning remains external validity rather than accepted replay. -/
theorem setCore_identity_has_external_meaning :
    theory.Meaning (.inr ())
      Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority.identityFormula :=
  Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority.identity_has_external_meaning

/-- The concrete empty-membership countermodel survives entry into the plural
waist. -/
theorem setCore_universalMembership_not_meaning :
    Not (theory.Meaning (.inr ())
      Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority.universalMembership) :=
  Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority.universalMembership_not_valid

/-- The same counterexample is outside the covered semantic fragment and is
rejected for every certificate. -/
theorem setCore_universalMembership_rejected
    (proof : Mettapedia.Languages.Megalodon.MathdataKernel.Pf) :
    (contract.checker (.inr ())).check
      Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority.universalMembership
      proof = false :=
  Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority.universalMembership_rejected
    proof

/-- The original selected Mathdata authority remains live at its old inner
tag after the conservative extension. -/
theorem selected_megalodon_definition_replays :
    (contract.checker (.inl (.inr (.inr
      Mettapedia.Languages.Megalodon.MathdataKernel.definitionConversionEnvironment)))).check
        Mettapedia.Languages.Megalodon.SelectedTheoryProfile.definitionClaim
        Mettapedia.Languages.Megalodon.MathdataKernel.definitionConversionProof =
      true :=
  Mettapedia.Languages.MeTTa.PrimePluralNIKWaist.megalodon_definition_replays

/-- Even though both Megalodon-facing nodes use `Pf`, their authority tags are
not interchangeable. -/
theorem selected_certificate_rejected_at_setCore_kind :
    contract.toAuthorityFamily.packedChecker.check
      ⟨.inr (),
        Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority.identityFormula⟩
      ⟨.inl (.inr (.inr
          Mettapedia.Languages.Megalodon.MathdataKernel.definitionConversionEnvironment)),
        Mettapedia.Languages.Megalodon.MathdataKernel.definitionConversionProof⟩ =
      false := by
  exact AuthorityFamily.packedChecker_rejects_wrongKind
    (family := contract.toAuthorityFamily)
    (claimKind := Sum.inr ())
    (certificateKind := Sum.inl (Sum.inr (Sum.inr
      Mettapedia.Languages.Megalodon.MathdataKernel.definitionConversionEnvironment)))
    (by simp)
    Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority.identityFormula
    Mettapedia.Languages.Megalodon.MathdataKernel.definitionConversionProof

/-- An exact authority translation cannot preserve replay while mapping the
accepted set-core identity certificate to a rejected selected-profile replay.
Coexistence therefore does not synthesize a semantic bridge. -/
theorem no_replay_breaking_setCore_to_selected :
    Not (Exists fun translation : CertifiedTranslation setCoreContract
        Mettapedia.Languages.Megalodon.SelectedTheoryProfile.contract =>
      (Mettapedia.Languages.Megalodon.SelectedTheoryProfile.contract.checker
          (translation.mapKind ())).check
        (translation.mapClaim ()
          Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority.identityFormula)
        (translation.mapCertificate ()
          (Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority.reflexiveProof
            Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority.predicateFormula)) =
        false) := by
  rintro ⟨translation, targetRejects⟩
  have commutes := translation.check_commutes ()
    Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority.identityFormula
    (Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority.reflexiveProof
      Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority.predicateFormula)
  rw [Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority.identity_replays]
    at commutes
  rw [targetRejects] at commutes
  cases commutes

#print axioms primeInclusion_conservative
#print axioms setCoreInclusion_conservative
#print axioms setCore_scope_is_host_irrelevant
#print axioms setCore_meaning_is_host_irrelevant
#print axioms setCore_identity_replays
#print axioms setCore_identity_has_external_meaning
#print axioms setCore_universalMembership_not_meaning
#print axioms setCore_universalMembership_rejected
#print axioms selected_megalodon_definition_replays
#print axioms selected_certificate_rejected_at_setCore_kind
#print axioms no_replay_breaking_setCore_to_selected

end Mettapedia.Languages.MeTTa.PrimePluralNIKSetCoreWaist
