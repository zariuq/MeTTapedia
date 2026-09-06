import Mettapedia.GSLT.LanguageDef.NIKCertificateGSLTPhysicalShield
import Mettapedia.GSLT.LanguageDef.InferenceSharedCettaWireCompilation

/-!
# Shared-pattern physical authority for CertificateGSLT shields

The ordinary physical shield encodes complete `WireArticle` patterns inline.
The version-two carrier instead places pattern constructors in one
chronological table and lets rule arguments and the target cite table roots.

`InferenceSharedCettaWireCompilation` supplies a total structural producer
and proves that materialization recovers every canonical closed-derivation
article exactly.  This module turns that result into a fourth NIK authority:
intrinsic proofs compile into shared physical CeTTa terms, and replay commutes
for every submitted claim.

The structural producer intentionally does not deduplicate equal occurrences.
Hash-consing remains an untrusted optimization whose output is accepted only
after the same shared decoder, materializer, and logical checker succeed.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NIKCertificateGSLTSharedPhysicalShield

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.NIKHeterogeneousTheory
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.GSLT.LanguageDef.CertificateGSLTAuthorityFunctor
open Mettapedia.GSLT.LanguageDef.InferenceCettaWire
open Mettapedia.GSLT.LanguageDef.InferenceSharedCettaWire
open Mettapedia.GSLT.LanguageDef.InferenceSharedCettaWireCompilation
open Mettapedia.GSLT.LanguageDef.NIKCertificateGSLTOperationalShield
open Mettapedia.GSLT.LanguageDef.NIKCertificateGSLTPhysicalShield

variable {Meaning : Pattern -> Prop}

/-! ## Exact compiled shared replay -/

/-- Compile a typed closed derivation into the shared physical ABI. -/
def sharedCertificateOfDerivation
    {definition : ValidatedCalculusLanguageDef} {claim : Pattern}
    (derivation : Derivation definition claim) : CettaTerm :=
  encodeSharedWireArticle
    (buildSharedWireArticle (articleOfDerivation derivation))

/-- Shared physical replay of a compiled typed derivation accepts exactly
when the independently submitted claim equals the derivation's indexed
conclusion. -/
theorem checkSharedPacket_compiled_eq_decide
    {definition : ValidatedCalculusLanguageDef} {actual : Pattern}
    (derivation : Derivation definition actual) (submitted : Pattern) :
    checkSharedPacket definition submitted
        (sharedCertificateOfDerivation derivation) =
      decide (actual = submitted) := by
  simp only [sharedCertificateOfDerivation, checkSharedPacket,
    decodeSharedWireArticle_encodeSharedWireArticle]
  rw [materialize_buildSharedWireArticle_of_derivation derivation]
  change
    (if (articleOfDerivation derivation).target = submitted then
        checkWireArticle definition (articleOfDerivation derivation)
      else false) = decide (actual = submitted)
  rw [checkWireArticle_articleOfDerivation derivation]
  simp [articleOfDerivation]

/-! ## Exact shared physical authority -/

/-- Decode, materialize, and replay a version-two shared physical article.
Neither the semantic predicate nor intrinsic proof objects are inputs. -/
def sharedPhysicalChecker (presentation : SoundPresentation Meaning) :
    Checker Pattern CettaTerm where
  check := checkSharedPacket presentation.object.definition

/-- Shared physical CeTTa articles have exact authority for the intrinsic NIK
scope. -/
def sharedPhysicalContract (presentation : SoundPresentation Meaning) :
    AuthorityContract (theory presentation) where
  Certificate := fun _kind => CettaTerm
  checker := fun _kind => sharedPhysicalChecker presentation
  scopeAuthority := fun _kind =>
    { sound := by
        intro claim certificate accepted
        exact (scope_iff_closed_derivation presentation claim).2
          (checkSharedPacket_sound presentation.object.definition claim
            certificate accepted)
      complete := by
        intro claim inScope
        rcases (scope_iff_closed_derivation presentation claim).1 inScope with
          ⟨derivation⟩
        exact ⟨sharedCertificateOfDerivation derivation,
          by simpa [sharedPhysicalChecker] using
            checkSharedPacket_compiled_eq_decide derivation claim⟩ }

/-- Compile an intrinsic CertificateGSLT proof object into the shared physical
ABI. -/
def toSharedPhysicalCertificate (presentation : SoundPresentation Meaning) :
    (contract presentation).Certificate () -> CettaTerm
  | ⟨_claim, proof⟩ => sharedCertificateOfDerivation proof.close

/-- Intrinsic proof objects lower exactly to shared physical replay. -/
def nativeToSharedPhysical (presentation : SoundPresentation Meaning) :
    CertifiedTranslation (contract presentation)
      (sharedPhysicalContract presentation) where
  mapKind := id
  mapSignature := id
  signature_commutes := by intro kind; cases kind; rfl
  mapClaim := fun _kind claim => claim
  mapCertificate := fun _kind certificate =>
    toSharedPhysicalCertificate presentation certificate
  check_commutes := by
    intro kind claim certificate
    cases kind
    rcases certificate with ⟨actual, proof⟩
    exact checkSharedPacket_compiled_eq_decide proof.close claim
  meaning_preserved := by
    intro _kind _claim meaningful
    exact meaningful

/-! ## The four-discipline shield tower -/

/-- Retain intrinsic, raw, logical-wire, ordinary-physical, and
shared-physical routes as separate authority edges. -/
structure SharedPhysicalShieldTower
    (presentation : SoundPresentation Meaning) where
  ordinary : PhysicalShieldTower presentation
  sharedPhysical : AuthorityContract (theory presentation)
  lowerSharedPhysical :
    CertifiedTranslation (contract presentation) sharedPhysical

def sharedPhysicalShieldTower (presentation : SoundPresentation Meaning) :
    SharedPhysicalShieldTower presentation where
  ordinary := physicalShieldTower presentation
  sharedPhysical := sharedPhysicalContract presentation
  lowerSharedPhysical := nativeToSharedPhysical presentation

/-! ## Positive, negative, and host-irrelevance theorems -/

/-- Positive control: every intrinsic proof compiles to an accepted shared
physical article at its exact conclusion. -/
theorem compiled_shared_physical_accepts
    (presentation : SoundPresentation Meaning) {claim : Pattern}
    (proof : (derivationClone presentation.object).Hom [] claim) :
    ((sharedPhysicalContract presentation).checker ()).check claim
        (toSharedPhysicalCertificate presentation ⟨claim, proof⟩) = true := by
  simpa [sharedPhysicalContract, sharedPhysicalChecker,
    toSharedPhysicalCertificate] using
    checkSharedPacket_compiled_eq_decide proof.close claim

/-- Negative control: changing only the submitted claim makes the same
compiled physical article reject. -/
theorem compiled_shared_physical_rejects_wrong_claim
    (presentation : SoundPresentation Meaning)
    {actual submitted : Pattern} (different : actual ≠ submitted)
    (proof : (derivationClone presentation.object).Hom [] actual) :
    ((sharedPhysicalContract presentation).checker ()).check submitted
        (toSharedPhysicalCertificate presentation ⟨actual, proof⟩) = false := by
  simpa [sharedPhysicalContract, sharedPhysicalChecker,
    toSharedPhysicalCertificate, different] using
    checkSharedPacket_compiled_eq_decide proof.close submitted

/-- Ordinary physical and shared physical replay have exactly the same
theorem image.  The theorem does not identify certificate sizes or costs. -/
theorem physical_exists_iff_shared_physical_exists
    (presentation : SoundPresentation Meaning) (claim : Pattern) :
    (∃ certificate : CettaTerm,
        ((physicalContract presentation).checker ()).check claim certificate =
          true) <->
      ∃ certificate : CettaTerm,
        ((sharedPhysicalContract presentation).checker ()).check claim
          certificate = true := by
  constructor
  · rintro ⟨certificate, accepted⟩
    have inScope :=
      (physicalContract presentation).scopeAuthority () |>.sound
        claim certificate accepted
    exact (sharedPhysicalContract presentation).scopeAuthority () |>.complete
      claim inScope
  · rintro ⟨certificate, accepted⟩
    have inScope :=
      (sharedPhysicalContract presentation).scopeAuthority () |>.sound
        claim certificate accepted
    exact (physicalContract presentation).scopeAuthority () |>.complete
      claim inScope

/-- A physical term outside the shared article grammar fails closed. -/
theorem malformed_shared_physical_certificate_rejected
    (presentation : SoundPresentation Meaning) (claim : Pattern) :
    ((sharedPhysicalContract presentation).checker ()).check claim
        (.symbol "not-a-shared-proof-dag") = false := by
  rfl

/-- A shared article with an unknown version remains rejected after canonical
physical encoding. -/
theorem wrong_shared_version_rejected
    (presentation : SoundPresentation Meaning) (claim : Pattern)
    (article : SharedWireArticle)
    (wrongVersion : article.version ≠ sharedArticleVersion) :
    ((sharedPhysicalContract presentation).checker ()).check claim
        (encodeSharedWireArticle article) = false := by
  simp [sharedPhysicalContract, sharedPhysicalChecker, checkSharedPacket,
    materializeSharedArticle?, wrongVersion]

#print axioms checkSharedPacket_compiled_eq_decide
#print axioms sharedPhysicalContract
#print axioms nativeToSharedPhysical
#print axioms compiled_shared_physical_accepts
#print axioms compiled_shared_physical_rejects_wrong_claim
#print axioms physical_exists_iff_shared_physical_exists
#print axioms malformed_shared_physical_certificate_rejected
#print axioms wrong_shared_version_rejected

end Mettapedia.GSLT.LanguageDef.NIKCertificateGSLTSharedPhysicalShield
