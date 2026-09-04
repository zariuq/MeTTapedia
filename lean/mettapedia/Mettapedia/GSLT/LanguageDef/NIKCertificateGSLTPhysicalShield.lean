import Mettapedia.GSLT.LanguageDef.NIKCertificateGSLTOperationalShield
import Mettapedia.GSLT.LanguageDef.InferenceCettaWireFormat

/-!
# A physical CeTTa ABI authority for CertificateGSLT shields

The operational shield has an intrinsic proof-object authority and two logical
replay formats: recursive `RawProof` trees and chronological `WireArticle`
DAGs.  This module adds a third, physically distinct certificate carrier:
CeTTa-shaped S-expressions.

The physical checker first decodes a `CettaTerm`, then replays the decoded
chronological article.  Canonical encoding is an exact authority translation:
decoding an encoded article is lossless, and acceptance commutes for every
submitted claim, including wrong claims.  Thus serialization changes neither
the theorem image nor the rejection behavior.

This module specifies and qualifies the physical ABI.  It does not claim that
an external CeTTa or C implementation realizes the checker; that requires a
separate implementation-correspondence theorem.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NIKCertificateGSLTPhysicalShield

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.NIKHeterogeneousTheory
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.GSLT.LanguageDef.CertificateGSLTAuthorityFunctor
open Mettapedia.GSLT.LanguageDef.InferenceCettaWire
open Mettapedia.GSLT.LanguageDef.NIKCertificateGSLTOperationalShield

variable {Meaning : Pattern -> Prop}

/-! ## Fail-closed physical replay -/

/-- Decode a physical CeTTa certificate and replay its chronological article.
The submitted claim remains an independent checker input, so the redundant
article target cannot select the claim it is checked against. -/
def physicalChecker (presentation : SoundPresentation Meaning) :
    Checker Pattern CettaTerm where
  check := fun claim encodedArticle =>
    match decodeWireArticle encodedArticle with
    | some article =>
        decide (article.target = claim) &&
          checkWireArticle presentation.object.definition article
    | none => false

/-- Physical CeTTa articles have exact authority for the same independently
qualified NIK scope as intrinsic, raw-tree, and logical wire certificates. -/
def physicalContract (presentation : SoundPresentation Meaning) :
    AuthorityContract (theory presentation) where
  Certificate := fun _kind => CettaTerm
  checker := fun _kind => physicalChecker presentation
  scopeAuthority := fun _kind =>
    { sound := by
        intro claim encodedArticle accepted
        cases decoded : decodeWireArticle encodedArticle with
        | none =>
          simp [physicalChecker, decoded] at accepted
        | some article =>
          simp only [physicalChecker, decoded, Bool.and_eq_true,
            decide_eq_true_eq] at accepted
          rw [← accepted.1]
          exact (scope_iff_closed_derivation presentation article.target).2
            (checkWireArticle_sound accepted.2)
      complete := by
        intro claim inScope
        rcases (scope_iff_closed_derivation presentation claim).1 inScope with
          ⟨derivation⟩
        refine ⟨encodeWireArticle (articleOfDerivation derivation), ?_⟩
        simp only [physicalChecker, decodeWireArticle_encodeWireArticle,
          Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨rfl, checkWireArticle_articleOfDerivation derivation⟩ }

/-! ## Exact logical-wire to physical-wire translation -/

/-- Canonical physical encoding preserves the exact decision made by logical
chronological replay for every article and submitted claim. -/
@[simp] theorem physical_checker_encode
    (presentation : SoundPresentation Meaning) (claim : Pattern)
    (article : WireArticle) :
    ((physicalContract presentation).checker ()).check claim
        (encodeWireArticle article) =
      ((wireContract presentation).checker ()).check claim article := by
  simp [physicalContract, physicalChecker, wireContract, wireChecker]

/-- Lossless encoding of logical wire articles into the physical CeTTa ABI. -/
def wireToPhysical (presentation : SoundPresentation Meaning) :
    AuthorityTranslation (wireContract presentation)
      (physicalContract presentation) where
  mapKind := id
  mapSignature := id
  signature_commutes := by intro kind; cases kind; rfl
  mapClaim := fun _kind claim => claim
  mapCertificate := fun _kind article => encodeWireArticle article
  check_commutes := by
    intro kind claim article
    cases kind
    exact physical_checker_encode presentation claim article
  meaning_preserved := by
    intro _kind _claim meaningful
    exact meaningful

/-- The intrinsic proof-object authority lowers to the physical ABI by
chronological linearization followed by exact CeTTa encoding. -/
def nativeToPhysical (presentation : SoundPresentation Meaning) :
    AuthorityTranslation (contract presentation)
      (physicalContract presentation) :=
  AuthorityTranslation.comp (nativeToWire presentation)
    (wireToPhysical presentation)

/-- The physical certificate produced directly from an intrinsic certificate. -/
def toPhysicalCertificate (presentation : SoundPresentation Meaning) :
    (contract presentation).Certificate () -> CettaTerm :=
  fun certificate =>
    encodeWireArticle (toWireCertificate presentation certificate)

@[simp] theorem nativeToPhysical_mapCertificate
    (presentation : SoundPresentation Meaning)
    (certificate : (contract presentation).Certificate ()) :
    (nativeToPhysical presentation).mapCertificate () certificate =
      toPhysicalCertificate presentation certificate :=
  rfl

/-! ## The physical shield tower -/

/-- Package the logical plural shield with its exact physical ABI endpoint.
The two lowerings into the physical endpoint are retained separately: one
from intrinsic proofs and one from already-linearized wire articles. -/
structure PhysicalShieldTower (presentation : SoundPresentation Meaning) where
  logical : ShieldSpan presentation
  physical : AuthorityContract (theory presentation)
  lowerPhysical : AuthorityTranslation (contract presentation) physical
  encodeWire : AuthorityTranslation logical.wire physical

/-- The canonical intrinsic/raw/wire/physical shield tower. -/
def physicalShieldTower (presentation : SoundPresentation Meaning) :
    PhysicalShieldTower presentation where
  logical := shieldSpan presentation
  physical := physicalContract presentation
  lowerPhysical := nativeToPhysical presentation
  encodeWire := wireToPhysical presentation

/-! ## Positive, negative, and host-irrelevance theorems -/

/-- Raw-tree, logical-wire, and physical-wire replay agree on every submitted
claim compiled from one intrinsic certificate. -/
theorem compiled_replays_agree_physical
    (presentation : SoundPresentation Meaning) (submitted : Pattern)
    (certificate : (contract presentation).Certificate ()) :
    ((rawContract presentation).checker ()).check submitted
        (toRawCertificate presentation certificate) =
      ((physicalContract presentation).checker ()).check submitted
        (toPhysicalCertificate presentation certificate) := by
  rw [compiled_replays_agree presentation submitted certificate]
  exact (physical_checker_encode presentation submitted
    (toWireCertificate presentation certificate)).symm

/-- Positive control: an intrinsic proof compiles to accepted evidence in all
three executable certificate disciplines. -/
theorem compiled_triplet_accepts
    (presentation : SoundPresentation Meaning) {claim : Pattern}
    (proof : (derivationClone presentation.object).Hom [] claim) :
    ((rawContract presentation).checker ()).check claim
        (toRawCertificate presentation ⟨claim, proof⟩) = true ∧
      ((wireContract presentation).checker ()).check claim
          (toWireCertificate presentation ⟨claim, proof⟩) = true ∧
        ((physicalContract presentation).checker ()).check claim
          (toPhysicalCertificate presentation ⟨claim, proof⟩) = true := by
  rcases compiled_pair_accepts presentation proof with
    ⟨rawAccepted, wireAccepted⟩
  exact ⟨rawAccepted, wireAccepted,
    (physical_checker_encode presentation claim
      (toWireCertificate presentation ⟨claim, proof⟩)).trans wireAccepted⟩

/-- Negative control: all three compiled certificates reject the same wrong
submitted claim. -/
theorem compiled_triplet_rejects_wrong_claim
    (presentation : SoundPresentation Meaning)
    {actual submitted : Pattern} (different : actual ≠ submitted)
    (proof : (derivationClone presentation.object).Hom [] actual) :
    ((rawContract presentation).checker ()).check submitted
        (toRawCertificate presentation ⟨actual, proof⟩) = false ∧
      ((wireContract presentation).checker ()).check submitted
          (toWireCertificate presentation ⟨actual, proof⟩) = false ∧
        ((physicalContract presentation).checker ()).check submitted
          (toPhysicalCertificate presentation ⟨actual, proof⟩) = false := by
  rcases compiled_pair_rejects_wrong_claim presentation different proof with
    ⟨rawRejected, wireRejected⟩
  exact ⟨rawRejected, wireRejected,
    (physical_checker_encode presentation submitted
      (toWireCertificate presentation ⟨actual, proof⟩)).trans wireRejected⟩

/-- Logical and physical chronological replay accept some certificate at
exactly the same claims.  The theorem does not identify checking cost or make
an external implementation claim. -/
theorem wire_exists_iff_physical_exists
    (presentation : SoundPresentation Meaning) (claim : Pattern) :
    (∃ article : WireArticle,
        ((wireContract presentation).checker ()).check claim article = true) <->
      ∃ encodedArticle : CettaTerm,
        ((physicalContract presentation).checker ()).check claim
          encodedArticle = true := by
  constructor
  · rintro ⟨article, accepted⟩
    exact ⟨encodeWireArticle article,
      (physical_checker_encode presentation claim article).trans accepted⟩
  · rintro ⟨encodedArticle, accepted⟩
    have inScope :=
      (physicalContract presentation).scopeAuthority () |>.sound
        claim encodedArticle accepted
    exact (wireContract presentation).scopeAuthority () |>.complete
      claim inScope

/-- A term outside the physical proof-DAG grammar fails closed. -/
theorem malformed_physical_certificate_rejected
    (presentation : SoundPresentation Meaning) (claim : Pattern) :
    ((physicalContract presentation).checker ()).check claim
      (.symbol "not-a-proof-dag") = false := by
  rfl

/-- A logical article carrying the wrong ABI version remains rejected after
physical encoding. -/
theorem encoded_wrong_wire_version_rejected
    (presentation : SoundPresentation Meaning) (claim : Pattern)
    (article : WireArticle)
    (wrongVersion : article.version ≠ wireArticleVersion) :
    ((physicalContract presentation).checker ()).check claim
        (encodeWireArticle article) = false := by
  rw [physical_checker_encode]
  exact wrong_wire_version_rejected presentation claim article wrongVersion

/-- Canonical physical encoding does not collapse distinct logical articles. -/
theorem physical_encoding_injective : Function.Injective encodeWireArticle :=
  encodeWireArticle_injective

#print axioms physicalContract
#print axioms physical_checker_encode
#print axioms wireToPhysical
#print axioms nativeToPhysical
#print axioms compiled_replays_agree_physical
#print axioms compiled_triplet_accepts
#print axioms compiled_triplet_rejects_wrong_claim
#print axioms wire_exists_iff_physical_exists
#print axioms malformed_physical_certificate_rejected
#print axioms encoded_wrong_wire_version_rejected
#print axioms physical_encoding_injective

end Mettapedia.GSLT.LanguageDef.NIKCertificateGSLTPhysicalShield
