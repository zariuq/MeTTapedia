import Mettapedia.GSLT.LanguageDef.NIKHeterogeneousTheory
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DeclarationAwareNIKAuthority
import Mettapedia.Languages.Megalodon.ImplicationalSemanticAuthority
import Mettapedia.Languages.Megalodon.SelectedTheoryProfile

/-!
# A plural NIK waist for Prime

This module places three independently exact native authorities behind one
tagged dispatcher:

* the declaration-aware formed structural fragment of the Prime DTT; and
* a Megalodon implicational fragment with independent valuation semantics;
* Megalodon's selected-environment Mathdata kernel.

The coproduct is deliberately conservative.  It does not identify their
claims, proof objects, signatures, or meanings, and it supplies no automatic
translation between them.  Such a translation must be authored separately
and prove exact replay and semantic preservation.

The Megalodon component currently means native Mathdata theoremhood.  A HOTG
model-validity profile remains a distinct future authority rather than an
unproved reinterpretation of this node.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimePluralNIKWaist

open Mettapedia.GSLT.LanguageDef.CheckerAuthorityFamily
open Mettapedia.GSLT.LanguageDef.NIKHeterogeneousTheory
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DeclarationAwareFormedTyping.Examples

private abbrev dttTheory :=
  Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DeclarationAwareNIKAuthority.theory
private abbrev dttContract :=
  Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DeclarationAwareNIKAuthority.contract
private abbrev implicationTheory :=
  Mettapedia.Languages.Megalodon.ImplicationalSemanticAuthority.theory
private abbrev implicationContract :=
  Mettapedia.Languages.Megalodon.ImplicationalSemanticAuthority.contract
private abbrev megalodonTheory :=
  Mettapedia.Languages.Megalodon.SelectedTheoryProfile.theory
private abbrev megalodonContract :=
  Mettapedia.Languages.Megalodon.SelectedTheoryProfile.contract

/-! ## The conservative three-kernel authority -/

abbrev Kind :=
  Sum Unit
    (Sum Unit Mettapedia.Languages.Megalodon.MathdataKernel.Environment)

/-- The two higher-order-facing authorities form an inner conservative pair. -/
private def higherOrderTheory :=
  Coproduct.theory implicationTheory megalodonTheory

private def higherOrderContract :=
  Coproduct.contract implicationTheory megalodonTheory implicationContract
    megalodonContract

/-- All three theory families coexist without a common claim encoding. -/
def theory := Coproduct.theory dttTheory higherOrderTheory

/-- The tagged checker chooses the native authority named by the kind. -/
def contract :=
  Coproduct.contract dttTheory higherOrderTheory dttContract
    higherOrderContract

/-- The DTT authority enters exactly and conservatively. -/
def dttInclusion :=
  Coproduct.leftInclusion dttTheory higherOrderTheory dttContract
    higherOrderContract

/-- The inner higher-order pair enters the outer plural waist. -/
private def higherOrderInclusion :=
  Coproduct.rightInclusion dttTheory higherOrderTheory dttContract
    higherOrderContract

/-- The independently meaningful implication authority reaches the plural
waist by a retained two-stage composition. -/
def implicationInclusion :=
  CertifiedTranslation.comp
    (Coproduct.leftInclusion implicationTheory megalodonTheory
      implicationContract megalodonContract)
    higherOrderInclusion

/-- The selected Megalodon authority reaches the plural waist through the
other inner coproduct injection. -/
def megalodonInclusion :=
  CertifiedTranslation.comp
    (Coproduct.rightInclusion implicationTheory megalodonTheory
      implicationContract megalodonContract)
    higherOrderInclusion

theorem dttInclusion_conservative :
  dttInclusion.toTheoryTranslation.Conservative :=
  Coproduct.leftInclusion_conservative dttTheory higherOrderTheory
    dttContract higherOrderContract

theorem implicationInclusion_conservative :
    implicationInclusion.toTheoryTranslation.Conservative := by
  exact TheoryTranslation.Conservative.comp
    (Coproduct.leftInclusion implicationTheory megalodonTheory
      implicationContract megalodonContract).toTheoryTranslation
    higherOrderInclusion.toTheoryTranslation
    (Coproduct.leftInclusion_conservative implicationTheory megalodonTheory
      implicationContract megalodonContract)
    (Coproduct.rightInclusion_conservative dttTheory higherOrderTheory
      dttContract higherOrderContract)

theorem megalodonInclusion_conservative :
    megalodonInclusion.toTheoryTranslation.Conservative := by
  exact TheoryTranslation.Conservative.comp
    (Coproduct.rightInclusion implicationTheory megalodonTheory
      implicationContract megalodonContract).toTheoryTranslation
    higherOrderInclusion.toTheoryTranslation
    (Coproduct.rightInclusion_conservative implicationTheory megalodonTheory
      implicationContract megalodonContract)
    (Coproduct.rightInclusion_conservative dttTheory higherOrderTheory
      dttContract higherOrderContract)

/-! ## Concrete replay controls -/

/-- The nontrivial dependent-function example replays through the plural
dispatcher in the DTT fibre. -/
theorem dtt_simplePi_replays :
    (contract.checker (.inl ())).check simplePiQuery simplePiIntrinsic.raw =
      true :=
  Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DeclarationAwareNIKAuthority.simplePi_replays

/-- The implication identity proof replays in the semantic higher-order
fragment. -/
theorem implication_identity_replays :
    (contract.checker (.inr (.inl ()))).check
        Mettapedia.Languages.Megalodon.ImplicationalSemanticAuthority.identityClaim
        Mettapedia.Languages.Megalodon.ImplicationalSemanticAuthority.identityProof =
      true :=
  Mettapedia.Languages.Megalodon.ImplicationalSemanticAuthority.identity_accepted

/-- This middle node already has an independently stated model-theoretic
meaning, rather than identifying accepted replay with truth. -/
theorem implication_identity_has_external_meaning :
    theory.Meaning (.inr (.inl ()))
      Mettapedia.Languages.Megalodon.ImplicationalSemanticAuthority.identityClaim :=
  Mettapedia.Languages.Megalodon.ImplicationalSemanticAuthority.identity_meaning

/-- Countermodel control: the plural waist does not make a bare atom valid. -/
theorem implication_bare_atom_not_meaning :
    ¬ theory.Meaning (.inr (.inl ()))
      Mettapedia.Languages.Megalodon.ImplicationalSemanticAuthority.bareAtomClaim :=
  Mettapedia.Languages.Megalodon.ImplicationalSemanticAuthority.bareAtom_not_meaning

/-- Megalodon's definition-sensitive native example independently replays in
its selected environment. -/
theorem megalodon_definition_replays :
    (contract.checker (.inr (.inr
      Mettapedia.Languages.Megalodon.MathdataKernel.definitionConversionEnvironment))).check
        Mettapedia.Languages.Megalodon.SelectedTheoryProfile.definitionClaim
        Mettapedia.Languages.Megalodon.MathdataKernel.definitionConversionProof =
      true :=
  Mettapedia.Languages.Megalodon.SelectedTheoryProfile.definition_profile_accepts

/-- Even though both kernels are live, a Megalodon proof cannot be submitted
as a DTT certificate through the packed dispatcher. -/
theorem megalodon_certificate_rejected_at_dtt_kind :
    contract.toAuthorityFamily.packedChecker.check
        ⟨.inl (), simplePiQuery⟩
        ⟨.inr (.inr
            Mettapedia.Languages.Megalodon.MathdataKernel.definitionConversionEnvironment),
          Mettapedia.Languages.Megalodon.MathdataKernel.definitionConversionProof⟩ =
      false := by
  exact AuthorityFamily.packedChecker_rejects_wrongKind
    (family := contract.toAuthorityFamily)
    (claimKind := Sum.inl ())
    (certificateKind :=
      Sum.inr (Sum.inr
        Mettapedia.Languages.Megalodon.MathdataKernel.definitionConversionEnvironment))
    (by simp) simplePiQuery
      Mettapedia.Languages.Megalodon.MathdataKernel.definitionConversionProof

/-- No exact authority translation may turn this accepted DTT proof into a
rejected Megalodon replay.  Coexistence alone therefore cannot justify an
invented cross-kernel adapter. -/
theorem no_replay_breaking_dtt_to_megalodon :
    ¬ (exists translation :
        CertifiedTranslation dttContract megalodonContract,
      (megalodonContract.checker (translation.mapKind ())).check
          (translation.mapClaim () simplePiQuery)
          (translation.mapCertificate () simplePiIntrinsic.raw) = false) := by
  rintro ⟨translation, targetRejects⟩
  have commutes :=
    translation.check_commutes () simplePiQuery simplePiIntrinsic.raw
  rw [Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DeclarationAwareNIKAuthority.simplePi_replays]
    at commutes
  rw [targetRejects] at commutes
  cases commutes

/-- All three component theorem scopes are unchanged by entering the plural
waist. -/
theorem component_scopes_are_exact :
    (theory.Scope (.inl ()) simplePiQuery <->
      dttTheory.Scope () simplePiQuery) /\
    (theory.Scope (.inr (.inl ()))
        Mettapedia.Languages.Megalodon.ImplicationalSemanticAuthority.identityClaim <->
      implicationTheory.Scope ()
        Mettapedia.Languages.Megalodon.ImplicationalSemanticAuthority.identityClaim) /\
    (theory.Scope (.inr (.inr
        Mettapedia.Languages.Megalodon.MathdataKernel.definitionConversionEnvironment))
        Mettapedia.Languages.Megalodon.SelectedTheoryProfile.definitionClaim <->
      megalodonTheory.Scope
        Mettapedia.Languages.Megalodon.MathdataKernel.definitionConversionEnvironment
        Mettapedia.Languages.Megalodon.SelectedTheoryProfile.definitionClaim) := by
  exact ⟨Iff.rfl, Iff.rfl, Iff.rfl⟩

#print axioms dttInclusion_conservative
#print axioms implicationInclusion_conservative
#print axioms megalodonInclusion_conservative
#print axioms dtt_simplePi_replays
#print axioms implication_identity_replays
#print axioms implication_identity_has_external_meaning
#print axioms implication_bare_atom_not_meaning
#print axioms megalodon_definition_replays
#print axioms megalodon_certificate_rejected_at_dtt_kind
#print axioms no_replay_breaking_dtt_to_megalodon
#print axioms component_scopes_are_exact

end Mettapedia.Languages.MeTTa.PrimePluralNIKWaist
