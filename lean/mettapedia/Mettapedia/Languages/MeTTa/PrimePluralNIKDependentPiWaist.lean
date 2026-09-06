import Mettapedia.GSLT.LanguageDef.CertifiedTheoryCategory
import Mettapedia.Languages.MeTTa.PrimePluralNIKSetCoreWaist
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.FourFaceDependentPiExperiment

/-!
# A selected dependent-computation node in the plural Prime NIK waist

The established Prime waist contains a broad declaration-aware DTT authority
for formed structural typing.  The calibrated dependent-Pi experiment proves
something different: one genuine dependent beta cell whose contractum and
opened codomain have separate authored certificates and whose meaning is
validated in independent dependent-function and set-graph semantics.

This module adds that computational cell as a separately tagged authority.  It
does not reinterpret the structural DTT authority, identify formation with
conversion, or present one selected cell as a complete DTT kernel.  The outer
coproduct preserves the existing Prime waist exactly while making the stronger
computational evidence available at its honest scope.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimePluralNIKDependentPiWaist

open Mettapedia.GSLT.LanguageDef.CheckerAuthorityFamily
open Mettapedia.GSLT.LanguageDef.CertifiedTheoryCategory
open Mettapedia.GSLT.LanguageDef.NIKHeterogeneousTheory
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.FourFaceDependentPiExperiment

universe u v

private abbrev primeTheory :=
  Mettapedia.Languages.MeTTa.PrimePluralNIKSetCoreWaist.theory

private abbrev primeContract :=
  Mettapedia.Languages.MeTTa.PrimePluralNIKSetCoreWaist.contract

private abbrev dependentPiTheory :=
  NIKProfile.theory.{u, v}

private abbrev dependentPiContract :=
  NIKProfile.contract.{u, v}

/-- The old four-node Prime waist or the selected dependent computation. -/
abbrev Kind :=
  Sum Mettapedia.Languages.MeTTa.PrimePluralNIKSetCoreWaist.Kind Unit

/-- The established declaration-aware structural DTT node. -/
def structuralDTTKind : Kind := .inl (.inl (.inl ()))

/-- The separately selected dependent-Pi computational node. -/
def selectedDependentPiKind : Kind := .inr ()

/-- Conservative coexistence of the established Prime waist and the selected
dependent-Pi computational authority. -/
def theory :=
  Coproduct.theory primeTheory dependentPiTheory.{u, v}

/-- The outer tag selects the established authority or the dependent
computation checker. -/
def contract :=
  Coproduct.contract primeTheory dependentPiTheory.{u, v} primeContract
    dependentPiContract.{u, v}

/-- The established Prime waist enters without reinterpretation. -/
def primeInclusion :=
  Coproduct.leftInclusion primeTheory dependentPiTheory.{u, v} primeContract
    dependentPiContract.{u, v}

/-- The selected dependent computation enters without weakening its scope or
external meaning. -/
def dependentPiInclusion :=
  Coproduct.rightInclusion primeTheory dependentPiTheory.{u, v} primeContract
    dependentPiContract.{u, v}

theorem primeInclusion_conservative :
    primeInclusion.{u, v}.toTheoryTranslation.Conservative :=
  Coproduct.leftInclusion_conservative primeTheory dependentPiTheory.{u, v}
    primeContract dependentPiContract.{u, v}

theorem dependentPiInclusion_conservative :
    dependentPiInclusion.{u, v}.toTheoryTranslation.Conservative :=
  Coproduct.rightInclusion_conservative primeTheory dependentPiTheory.{u, v}
    primeContract dependentPiContract.{u, v}

private theorem dependentPiIdentity_conservative :
    (TheoryTranslation.identity dependentPiTheory.{u, v}).Conservative where
  scope_reflecting := by
    intro kind candidate inScope
    exact inScope
  meaning_reflecting := by
    intro kind candidate meaningful
    exact meaningful

/-! ## Exact semantic host irrelevance -/

/-- Entering the larger Prime host changes no selected computational scope. -/
theorem dependentPi_scope_is_host_irrelevant
    (candidate : NIKProfile.Candidate) :
    dependentPiTheory.{u, v}.Scope () candidate <->
      theory.{u, v}.Scope selectedDependentPiKind candidate :=
  HostIrrelevance.scope_iff
    (TheoryTranslation.identity dependentPiTheory.{u, v})
    dependentPiInclusion.{u, v}.toTheoryTranslation
    dependentPiIdentity_conservative.{u, v}
    dependentPiInclusion_conservative.{u, v}
    () candidate

/-- Entering the larger Prime host changes no dependent-function or set-graph
meaning. -/
theorem dependentPi_meaning_is_host_irrelevant
    (candidate : NIKProfile.Candidate) :
    dependentPiTheory.{u, v}.Meaning () candidate <->
      theory.{u, v}.Meaning selectedDependentPiKind candidate :=
  HostIrrelevance.meaning_iff
    (TheoryTranslation.identity dependentPiTheory.{u, v})
    dependentPiInclusion.{u, v}.toTheoryTranslation
    dependentPiIdentity_conservative.{u, v}
    dependentPiInclusion_conservative.{u, v}
    () candidate

/-! ## Positive and negative controls -/

/-- The original declaration-aware DTT formation example still replays at its
old nested tag. -/
theorem structural_simplePi_replays :
    (contract.{u, v}.checker structuralDTTKind).check
        DeclarationAwareFormedTyping.Examples.simplePiQuery
        DeclarationAwareFormedTyping.Examples.simplePiIntrinsic.raw = true :=
  DeclarationAwareNIKAuthority.simplePi_replays

/-- The dependent beta cell replays both its term and opened-type certificate
through the new computational tag. -/
theorem dependentPi_beta_replays :
    (contract.{u, v}.checker selectedDependentPiKind).check
        NIKProfile.canonicalCandidate
        NIKProfile.canonicalCertificate = true :=
  NIKProfile.canonical_certificate_replays

/-- Accepted replay projects to the independent dependent-function and
set-graph semantics. -/
theorem dependentPi_beta_has_external_meaning :
    theory.{u, v}.Meaning selectedDependentPiKind
      NIKProfile.canonicalCandidate :=
  NIKProfile.accepted_has_dependent_meaning
    NIKProfile.canonicalCandidate
    NIKProfile.canonicalCertificate
    NIKProfile.canonical_certificate_replays

/-- The external semantics includes a genuinely varying dependent family. -/
theorem dependentPi_varying_family_is_not_constant :
    Subsingleton (ExtensionalFaces.varyingModel.Fiber false) /\
      ¬ Subsingleton
        (ExtensionalFaces.varyingModel.Fiber true) :=
  ExtensionalFaces.varying_fibres_have_distinct_subsingleton_status

/-- Extensional beta validity does not collapse the distinct native redex and
contractum syntax trees. -/
theorem dependentPi_external_validity_does_not_reflect_raw_syntax :
    ExtensionalFaces.ShallowValid.{u, v} /\
      ScopedDTT.source ≠ ScopedDTT.target :=
  ExtensionalFaces.extensional_validity_not_raw_reflection

/-- A changed contractum remains semantically false after entering Prime. -/
theorem wrongTermCandidate_not_meaning :
    ¬ theory.{u, v}.Meaning selectedDependentPiKind
      NIKProfile.wrongTermCandidate :=
  NIKProfile.wrongTermCandidate_not_meaning

/-- A changed opened codomain remains semantically false after entering
Prime. -/
theorem wrongTypeCandidate_not_meaning :
    ¬ theory.{u, v}.Meaning selectedDependentPiKind
      NIKProfile.wrongTypeCandidate :=
  NIKProfile.wrongTypeCandidate_not_meaning

/-- No replacement proof can make the wrong contractum pass. -/
theorem wrongTermCandidate_rejected
    (certificate : NIKProfile.Certificate) :
    (contract.{u, v}.checker selectedDependentPiKind).check
      NIKProfile.wrongTermCandidate certificate = false :=
  NIKProfile.wrong_term_rejected certificate

/-- No replacement proof can make the wrong opened codomain pass. -/
theorem wrongTypeCandidate_rejected
    (certificate : NIKProfile.Certificate) :
    (contract.{u, v}.checker selectedDependentPiKind).check
      NIKProfile.wrongTypeCandidate certificate = false :=
  NIKProfile.wrong_type_rejected certificate

/-- A valid dependent-computation certificate cannot be submitted to the
structural DTT checker merely because both authorities inhabit one waist. -/
theorem dependentPi_certificate_rejected_at_structural_kind :
    contract.{u, v}.toAuthorityFamily.packedChecker.check
      ⟨structuralDTTKind,
        DeclarationAwareFormedTyping.Examples.simplePiQuery⟩
      ⟨selectedDependentPiKind, NIKProfile.canonicalCertificate⟩ = false := by
  exact AuthorityFamily.packedChecker_rejects_wrongKind
    (family := contract.{u, v}.toAuthorityFamily)
    (claimKind := structuralDTTKind)
    (certificateKind := selectedDependentPiKind)
    (by simp [structuralDTTKind, selectedDependentPiKind])
    DeclarationAwareFormedTyping.Examples.simplePiQuery
    NIKProfile.canonicalCertificate

/-- Coexistence cannot provide an exact adapter that turns the accepted
dependent computation into a rejected replay in the established Prime waist. -/
theorem no_replay_breaking_dependentPi_to_prime :
    ¬ Exists fun translation :
        CertifiedTranslation dependentPiContract.{u, v} primeContract =>
      (primeContract.checker (translation.mapKind ())).check
        (translation.mapClaim () NIKProfile.canonicalCandidate)
        (translation.mapCertificate ()
          NIKProfile.canonicalCertificate) = false := by
  rintro ⟨translation, targetRejects⟩
  have commutes := translation.check_commutes ()
    NIKProfile.canonicalCandidate
    NIKProfile.canonicalCertificate
  have sourceAccepts :
      (dependentPiContract.{u, v}.checker ()).check
        NIKProfile.canonicalCandidate
        NIKProfile.canonicalCertificate = true :=
    NIKProfile.canonical_certificate_replays
  rw [targetRejects] at commutes
  rw [sourceAccepts] at commutes
  cases commutes

#print axioms primeInclusion_conservative
#print axioms dependentPiInclusion_conservative
#print axioms dependentPi_scope_is_host_irrelevant
#print axioms dependentPi_meaning_is_host_irrelevant
#print axioms structural_simplePi_replays
#print axioms dependentPi_beta_replays
#print axioms dependentPi_beta_has_external_meaning
#print axioms dependentPi_varying_family_is_not_constant
#print axioms dependentPi_external_validity_does_not_reflect_raw_syntax
#print axioms wrongTermCandidate_not_meaning
#print axioms wrongTypeCandidate_not_meaning
#print axioms wrongTermCandidate_rejected
#print axioms wrongTypeCandidate_rejected
#print axioms dependentPi_certificate_rejected_at_structural_kind
#print axioms no_replay_breaking_dependentPi_to_prime

end Mettapedia.Languages.MeTTa.PrimePluralNIKDependentPiWaist
