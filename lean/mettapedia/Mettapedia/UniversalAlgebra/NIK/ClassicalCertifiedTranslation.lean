import Mettapedia.UniversalAlgebra.NIK.RejectedCertificate
import Mettapedia.UniversalAlgebra.NIK.TheoryEquivalence

/-!
# Classical authority translations between equivalent equation systems

Consequence equivalence determines the existence of accepted target
certificates, but an exact authority translation needs a total map on every
certificate, including rejected inputs.  Equational replay has a canonical
rejected certificate for every proposed conclusion.  Classical selection of
an accepted target certificate, paired with that rejected sentinel, therefore
lifts consequence equivalence to an all-input checker-commuting authority
translation.

The construction is deliberately named `classical`: it establishes the exact
extensional boundary, but it is not an executable proof compiler.  A
constructive translation must replace certificate selection with an explicit
structural transformation.
-/

set_option autoImplicit false

namespace Mettapedia.UniversalAlgebra.NIK

open Mettapedia.Logic
open Mettapedia.OSLF.Framework.InitialModalSchema
open Mettapedia.GSLT.LanguageDef.NIKHeterogeneousTheory

universe u

variable {S : Signature.{u}} [DecidableEq S.Operation]

/-- A successfully replayed source certificate has an accepted target
certificate with the same conclusion whenever consequence is preserved. -/
theorem exists_target_certificate_of_valid
    {source target : EquationSystem S}
    (preserves : ∀ equation,
      EquationalConsequence source equation →
        EquationalConsequence target equation)
    (certificate : Derivation (Equation S)
      (EquationalRuleWitness source))
    (valid : certificate.valid (equationalRuleInterface source) = true) :
    ∃ targetCertificate : Derivation (Equation S)
        (EquationalRuleWitness target),
      targetCertificate.valid (equationalRuleInterface target) = true ∧
        targetCertificate.concl = certificate.concl := by
  apply Derives.exists_derivation (equationalRuleInterface target)
  exact preserves certificate.concl
    (Derivation.valid_sound (equationalRuleInterface source) certificate valid)

/-- Classically select one accepted target certificate for a valid source
certificate. -/
noncomputable def selectedTargetCertificate
    {source target : EquationSystem S}
    (preserves : ∀ equation,
      EquationalConsequence source equation →
        EquationalConsequence target equation)
    (certificate : Derivation (Equation S)
      (EquationalRuleWitness source))
    (valid : certificate.valid (equationalRuleInterface source) = true) :
    Derivation (Equation S) (EquationalRuleWitness target) :=
  Classical.choose
    (exists_target_certificate_of_valid preserves certificate valid)

theorem selectedTargetCertificate_valid
    {source target : EquationSystem S}
    (preserves : ∀ equation,
      EquationalConsequence source equation →
        EquationalConsequence target equation)
    (certificate : Derivation (Equation S)
      (EquationalRuleWitness source))
    (valid : certificate.valid (equationalRuleInterface source) = true) :
    (selectedTargetCertificate preserves certificate valid).valid
      (equationalRuleInterface target) = true :=
  (Classical.choose_spec
    (exists_target_certificate_of_valid preserves certificate valid)).1

theorem selectedTargetCertificate_concl
    {source target : EquationSystem S}
    (preserves : ∀ equation,
      EquationalConsequence source equation →
        EquationalConsequence target equation)
    (certificate : Derivation (Equation S)
      (EquationalRuleWitness source))
    (valid : certificate.valid (equationalRuleInterface source) = true) :
    (selectedTargetCertificate preserves certificate valid).concl =
      certificate.concl :=
  (Classical.choose_spec
    (exists_target_certificate_of_valid preserves certificate valid)).2

/-- Totalize classical accepted-certificate selection by mapping every
rejected source certificate to the canonical rejected target sentinel. -/
noncomputable def classicalCompileCertificate
    {source target : EquationSystem S}
    (preserves : ∀ equation,
      EquationalConsequence source equation →
        EquationalConsequence target equation)
    (certificate : Derivation (Equation S)
      (EquationalRuleWitness source)) :
    Derivation (Equation S) (EquationalRuleWitness target) :=
  if valid : certificate.valid (equationalRuleInterface source) = true then
    selectedTargetCertificate preserves certificate valid
  else
    rejectedCertificate target certificate.concl

/-- Classical compilation preserves the physical root conclusion on all
inputs, accepted or rejected. -/
theorem classicalCompileCertificate_concl
    {source target : EquationSystem S}
    (preserves : ∀ equation,
      EquationalConsequence source equation →
        EquationalConsequence target equation)
    (certificate : Derivation (Equation S)
      (EquationalRuleWitness source)) :
    (classicalCompileCertificate preserves certificate).concl =
      certificate.concl := by
  by_cases valid :
      certificate.valid (equationalRuleInterface source) = true
  · simp only [classicalCompileCertificate, dif_pos valid]
    exact selectedTargetCertificate_concl preserves certificate valid
  · simp [classicalCompileCertificate, valid]

/-- Classical compilation preserves the replay-validity bit exactly, not
merely in the accepted direction. -/
theorem classicalCompileCertificate_valid
    {source target : EquationSystem S}
    (preserves : ∀ equation,
      EquationalConsequence source equation →
        EquationalConsequence target equation)
    (certificate : Derivation (Equation S)
      (EquationalRuleWitness source)) :
    (classicalCompileCertificate preserves certificate).valid
        (equationalRuleInterface target) =
      certificate.valid (equationalRuleInterface source) := by
  by_cases valid :
      certificate.valid (equationalRuleInterface source) = true
  · rw [valid]
    simp only [classicalCompileCertificate, dif_pos valid]
    exact selectedTargetCertificate_valid preserves certificate valid
  · have invalid :
        certificate.valid (equationalRuleInterface source) = false :=
      Bool.eq_false_of_not_eq_true valid
    rw [invalid]
    simp [classicalCompileCertificate, valid]

/-- The totalized certificate map makes profile-blind equational replay
commute for every claim and every source certificate. -/
theorem classicalCompileCertificate_check_commutes
    {source target : EquationSystem S}
    (preserves : ∀ equation,
      EquationalConsequence source equation →
        EquationalConsequence target equation)
    (claim : Equation S)
    (certificate : Derivation (Equation S)
      (EquationalRuleWitness source)) :
    ((classicalCompileCertificate preserves certificate).valid
          (equationalRuleInterface target) &&
        decide ((classicalCompileCertificate preserves certificate).concl =
          claim)) =
      (
      certificate.valid (equationalRuleInterface source) &&
        decide (certificate.concl = claim)) := by
  rw [classicalCompileCertificate_valid]
  simp only [classicalCompileCertificate_concl]

/-- Consequence equivalence lifts classically to an exact translation between
the native equational replay authorities. -/
noncomputable def classicalCertifiedTranslation
    {source target : EquationSystem S}
    (equivalent : EquationSystem.SameConsequences source target) :
    CertifiedTranslation (contract source) (contract target) where
  mapKind := id
  mapSignature := id
  signature_commutes := by intro _kind; rfl
  mapClaim := fun _kind equation => equation
  mapCertificate := fun _kind certificate =>
    classicalCompileCertificate (fun equation => (equivalent equation).mp)
      certificate
  check_commutes := by
    intro _kind claim certificate
    change
      ((classicalCompileCertificate
          (fun equation => (equivalent equation).mp) certificate).valid
            (equationalRuleInterface target) &&
          decide ((classicalCompileCertificate
            (fun equation => (equivalent equation).mp) certificate).concl =
              claim)) =
        (
        certificate.valid (equationalRuleInterface source) &&
          decide (certificate.concl = claim))
    exact classicalCompileCertificate_check_commutes
      (fun equation => (equivalent equation).mp) claim certificate
  meaning_preserved := by
    intro _kind equation meaningful
    exact (entails_iff_of_sameConsequences equivalent equation).mp meaningful

/-- Forgetting the classically selected certificate map recovers the canonical
identity-on-equations semantic translation. -/
theorem classicalCertifiedTranslation_toTheoryTranslation
    {source target : EquationSystem S}
    (equivalent : EquationSystem.SameConsequences source target) :
    (classicalCertifiedTranslation equivalent).toTheoryTranslation =
      identityOnEquationsTranslation equivalent := by
  apply Mettapedia.GSLT.LanguageDef.CertifiedTheoryCategory.TheoryTranslation.ext_data
  · intro kind
    rfl
  · intro signature
    rfl
  · intro kind equation
    rfl

/-- The classical exact authority route is conservative after certificates
are forgotten. -/
theorem classicalCertifiedTranslation_conservative
    {source target : EquationSystem S}
    (equivalent : EquationSystem.SameConsequences source target) :
    (classicalCertifiedTranslation equivalent).toTheoryTranslation.Conservative := by
  rw [classicalCertifiedTranslation_toTheoryTranslation]
  exact identityOnEquationsTranslation_conservative equivalent

namespace Monoid

open Mettapedia.UniversalAlgebra.Monoid

/-- Positive control: the redundant monoid extension has an exact native
authority route back to the original monoid checker. -/
noncomputable def derivedExtensionCertifiedTranslation :
    CertifiedTranslation (contract derivedExtension) (contract equationSystem) :=
  classicalCertifiedTranslation derivedExtension_sameConsequences

/-- The added equation has an accepted source certificate whose transported
certificate is accepted by the original monoid checker. -/
theorem derived_equation_certificate_transports :
    ∃ sourceCertificate,
      ((contract derivedExtension).checker ()).check
          (mul (mul one x) one, x) sourceCertificate = true ∧
        ((contract equationSystem).checker
          (derivedExtensionCertifiedTranslation.mapKind ())).check
          (derivedExtensionCertifiedTranslation.mapClaim ()
            (mul (mul one x) one, x))
          (derivedExtensionCertifiedTranslation.mapCertificate ()
            sourceCertificate) = true := by
  have sourceScope : EquationalConsequence derivedExtension
      (mul (mul one x) one, x) :=
    (derivedExtension_sameConsequences _).mpr one_mul_mul_one
  obtain ⟨sourceCertificate, accepted⟩ :=
    ((contract derivedExtension).scopeAuthority ()).complete _ sourceScope
  refine ⟨sourceCertificate, accepted, ?_⟩
  rw [derivedExtensionCertifiedTranslation.check_commutes]
  exact accepted

/-- Negative control: the collapsing extension has no exact identity-on-claim
authority route whose forgotten semantic map is conservative. -/
theorem no_identity_conservative_authorityTranslation_from_collapsingExtension :
    ¬ ∃ translation :
        CertifiedTranslation (contract collapsingExtension)
          (contract equationSystem),
      (∀ equation, translation.mapClaim () equation = equation) ∧
        translation.toTheoryTranslation.Conservative := by
  rintro ⟨translation, claimFixed, conservative⟩
  apply no_identity_conservative_translation_from_collapsingExtension
  exact ⟨translation.toTheoryTranslation, claimFixed, conservative⟩

end Monoid

end Mettapedia.UniversalAlgebra.NIK
