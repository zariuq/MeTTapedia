import Mettapedia.GSLT.LanguageDef.CertificateGSLTAuthorityFunctor
import Mettapedia.GSLT.LanguageDef.CertificateGSLTWireFormat

/-!
# Plural operational shields for semantic CertificateGSLTs

A semantically qualified CertificateGSLT already has an intrinsic authority:
its certificates are closed, type-indexed derivations, and its native checker
compares the retained conclusion with the submitted claim.  This module lowers
the same intrinsic proof object into two executable audit disciplines:

* `RawProof`, replayed recursively as a proof tree by `checkRaw`;
* `WireArticle`, replayed chronologically as a versioned proof DAG by
  `checkWireArticle`.

Both checkers have exact authority for the same independently defined NIK
scope.  Erasure and linearization give two exact authority translations from
the intrinsic proof-object tier.  Their checker squares commute for accepting
and rejecting submissions, and their accepted certificate images coincide
exactly at theorem-existence level.

This is representational and control-flow diversity inside one Lean
formalization.  The two replay algorithms still share rule instantiation and
the ambient Lean trust base; no implementation-independence claim is made.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NIKCertificateGSLTOperationalShield

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.NIKHeterogeneousTheory
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.GSLT.LanguageDef.CertificateGSLTAuthorityFunctor

variable {Meaning : Pattern -> Prop}

/-! ## One scope, three certificate disciplines -/

/-- The intrinsic proof scope is equivalently inhabited by an ordinary
closed derivation.  This is the common theorem image against which both
executable replay disciplines are qualified. -/
theorem scope_iff_closed_derivation
    (presentation : SoundPresentation Meaning) (claim : Pattern) :
    (theory presentation).Scope () claim <->
      Nonempty (Derivation presentation.object.definition claim) := by
  constructor
  · rintro ⟨judgedProof⟩
    let openProof :=
      (closedProofFibreEquiv (derivationClone presentation.object) claim).symm
        judgedProof
    exact ⟨openProof.close⟩
  · rintro ⟨derivation⟩
    let openProof :
        (derivationClone presentation.object).Hom [] claim :=
      OpenDerivation.ofClosed (context := []) derivation
    exact ⟨closedProofFibreEquiv
      (derivationClone presentation.object) claim openProof⟩

/-- Recursive proof-tree replay.  The semantic predicate is deliberately not
an input to this checker. -/
def rawChecker (presentation : SoundPresentation Meaning) :
    Checker Pattern RawProof where
  check := checkRaw presentation.object.definition

/-- Recursive raw-tree replay has exact authority for the intrinsic proof
scope. -/
def rawContract (presentation : SoundPresentation Meaning) :
    AuthorityContract (theory presentation) where
  Certificate := fun _kind => RawProof
  checker := fun _kind => rawChecker presentation
  scopeAuthority := fun _kind =>
    { sound := by
        intro claim proof accepted
        exact (scope_iff_closed_derivation presentation claim).2
          (checkRaw_soundness accepted)
      complete := by
        intro claim inScope
        rcases (scope_iff_closed_derivation presentation claim).1 inScope with
          ⟨derivation⟩
        exact ⟨derivation.erase, checkRaw_erase derivation⟩ }

/-- Versioned chronological DAG replay, including target redundancy and the
wire-version gate. -/
def wireChecker (presentation : SoundPresentation Meaning) :
    Checker Pattern WireArticle where
  check := fun claim article =>
    decide (article.target = claim) &&
      checkWireArticle presentation.object.definition article

/-- Chronological wire-DAG replay has exact authority for the same intrinsic
proof scope. -/
def wireContract (presentation : SoundPresentation Meaning) :
    AuthorityContract (theory presentation) where
  Certificate := fun _kind => WireArticle
  checker := fun _kind => wireChecker presentation
  scopeAuthority := fun _kind =>
    { sound := by
        intro claim article accepted
        simp only [wireChecker, Bool.and_eq_true, decide_eq_true_eq] at accepted
        rw [← accepted.1]
        exact (scope_iff_closed_derivation presentation article.target).2
          (checkWireArticle_sound accepted.2)
      complete := by
        intro claim inScope
        rcases (scope_iff_closed_derivation presentation claim).1 inScope with
          ⟨derivation⟩
        refine ⟨articleOfDerivation derivation, ?_⟩
        simp only [wireChecker, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨rfl, checkWireArticle_articleOfDerivation derivation⟩ }

/-! ## Two exact lowerings from intrinsic proofs -/

/-- Erase an intrinsic closed proof to the recursive raw proof-tree format. -/
def toRawCertificate (presentation : SoundPresentation Meaning) :
    (contract presentation).Certificate () -> RawProof
  | ⟨_claim, proof⟩ => proof.close.erase

/-- Linearize an intrinsic closed proof to a versioned chronological article. -/
def toWireCertificate (presentation : SoundPresentation Meaning) :
    (contract presentation).Certificate () -> WireArticle
  | ⟨_claim, proof⟩ => articleOfDerivation proof.close

/-- A typed derivation erased to a raw tree is accepted exactly at its indexed
conclusion.  In particular, erasure preserves rejection at every other
submitted claim. -/
theorem checkRaw_erase_eq_decide
    {definition : ValidatedCalculusLanguageDef}
    {actual : Pattern} (derivation : Derivation definition actual)
    (submitted : Pattern) :
    checkRaw definition submitted derivation.erase =
      decide (actual = submitted) := by
  by_cases equal : actual = submitted
  · subst submitted
    simp [checkRaw_erase]
  · cases checked : checkRaw definition submitted derivation.erase with
    | false => simp [equal]
    | true =>
        have collision : actual = submitted :=
          checkRaw_goal_unique (checkRaw_erase derivation) checked
        exact (equal collision).elim

/-- Intrinsic proof objects lower exactly to recursive raw-tree replay. -/
def nativeToRaw (presentation : SoundPresentation Meaning) :
    AuthorityTranslation (contract presentation) (rawContract presentation) where
  mapKind := id
  mapSignature := id
  signature_commutes := by intro kind; cases kind; rfl
  mapClaim := fun _kind claim => claim
  mapCertificate := fun _kind certificate =>
    toRawCertificate presentation certificate
  check_commutes := by
    intro kind claim certificate
    cases kind
    rcases certificate with ⟨actual, proof⟩
    change checkRaw presentation.object.definition claim proof.close.erase =
      decide (actual = claim)
    exact checkRaw_erase_eq_decide proof.close claim
  meaning_preserved := by
    intro _kind _claim meaningful
    exact meaningful

/-- Intrinsic proof objects lower exactly to chronological wire-DAG replay. -/
def nativeToWire (presentation : SoundPresentation Meaning) :
    AuthorityTranslation (contract presentation) (wireContract presentation) where
  mapKind := id
  mapSignature := id
  signature_commutes := by intro kind; cases kind; rfl
  mapClaim := fun _kind claim => claim
  mapCertificate := fun _kind certificate =>
    toWireCertificate presentation certificate
  check_commutes := by
    intro kind claim certificate
    cases kind
    rcases certificate with ⟨actual, proof⟩
    change
      (decide ((articleOfDerivation proof.close).target = claim) &&
          checkWireArticle presentation.object.definition
            (articleOfDerivation proof.close)) =
        decide (actual = claim)
    rw [checkWireArticle_articleOfDerivation]
    simp [articleOfDerivation]
  meaning_preserved := by
    intro _kind _claim meaningful
    exact meaningful

/-! ## The commuting shield span -/

/-- The intrinsic proof-object authority and its two executable lowerings,
packaged without postulating a certificate conversion between the two target
formats. -/
structure ShieldSpan (presentation : SoundPresentation Meaning) where
  raw : AuthorityContract (theory presentation)
  wire : AuthorityContract (theory presentation)
  lowerRaw : AuthorityTranslation (contract presentation) raw
  lowerWire : AuthorityTranslation (contract presentation) wire

/-- The canonical plural shield span for a semantic presentation. -/
def shieldSpan (presentation : SoundPresentation Meaning) :
    ShieldSpan presentation where
  raw := rawContract presentation
  wire := wireContract presentation
  lowerRaw := nativeToRaw presentation
  lowerWire := nativeToWire presentation

/-- Both executable lowerings make exactly the same acceptance decision on
every submitted claim derived from one intrinsic certificate. -/
theorem compiled_replays_agree
    (presentation : SoundPresentation Meaning) (submitted : Pattern)
    (certificate : (contract presentation).Certificate ()) :
    ((rawContract presentation).checker ()).check submitted
        (toRawCertificate presentation certificate) =
      ((wireContract presentation).checker ()).check submitted
        (toWireCertificate presentation certificate) := by
  rcases certificate with ⟨actual, proof⟩
  change checkRaw presentation.object.definition submitted proof.close.erase =
    (decide ((articleOfDerivation proof.close).target = submitted) &&
      checkWireArticle presentation.object.definition
        (articleOfDerivation proof.close))
  rw [checkRaw_erase_eq_decide, checkWireArticle_articleOfDerivation]
  simp [articleOfDerivation]

/-- Every intrinsic closed derivation compiles to accepted raw-tree and
wire-DAG evidence at its exact conclusion. -/
theorem compiled_pair_accepts
    (presentation : SoundPresentation Meaning) {claim : Pattern}
    (proof : (derivationClone presentation.object).Hom [] claim) :
    ((rawContract presentation).checker ()).check claim
        (toRawCertificate presentation ⟨claim, proof⟩) = true ∧
      ((wireContract presentation).checker ()).check claim
        (toWireCertificate presentation ⟨claim, proof⟩) = true := by
  constructor
  · change checkRaw presentation.object.definition claim proof.close.erase = true
    exact checkRaw_erase proof.close
  · change
      (decide ((articleOfDerivation proof.close).target = claim) &&
        checkWireArticle presentation.object.definition
          (articleOfDerivation proof.close)) = true
    rw [checkWireArticle_articleOfDerivation]
    simp [articleOfDerivation]

/-- Negative control: both lowered certificates reject the same wrong claim. -/
theorem compiled_pair_rejects_wrong_claim
    (presentation : SoundPresentation Meaning)
    {actual submitted : Pattern} (different : actual ≠ submitted)
    (proof : (derivationClone presentation.object).Hom [] actual) :
    ((rawContract presentation).checker ()).check submitted
        (toRawCertificate presentation ⟨actual, proof⟩) = false ∧
      ((wireContract presentation).checker ()).check submitted
        (toWireCertificate presentation ⟨actual, proof⟩) = false := by
  constructor
  · change
      checkRaw presentation.object.definition submitted proof.close.erase = false
    rw [checkRaw_erase_eq_decide]
    simp [different]
  · change
      (decide ((articleOfDerivation proof.close).target = submitted) &&
        checkWireArticle presentation.object.definition
          (articleOfDerivation proof.close)) = false
    rw [checkWireArticle_articleOfDerivation]
    simp [articleOfDerivation, different]

/-- The two replay disciplines accept some certificate at exactly the same
claims.  This is semantic host irrelevance at theorem-existence level; it does
not identify individual certificates or their checking costs. -/
theorem raw_exists_iff_wire_exists
    (presentation : SoundPresentation Meaning) (claim : Pattern) :
    (∃ proof : RawProof,
        ((rawContract presentation).checker ()).check claim proof = true) <->
      ∃ article : WireArticle,
        ((wireContract presentation).checker ()).check claim article = true := by
  constructor
  · rintro ⟨proof, accepted⟩
    have inScope :=
      (rawContract presentation).scopeAuthority () |>.sound
        claim proof accepted
    exact (wireContract presentation).scopeAuthority () |>.complete
      claim inScope
  · rintro ⟨article, accepted⟩
    have inScope :=
      (wireContract presentation).scopeAuthority () |>.sound
        claim article accepted
    exact (rawContract presentation).scopeAuthority () |>.complete
      claim inScope

/-- A wire article with an unknown ABI version is rejected independently of
its nodes, root, and target. -/
theorem wrong_wire_version_rejected
    (presentation : SoundPresentation Meaning) (claim : Pattern)
    (article : WireArticle)
    (wrongVersion : article.version ≠ wireArticleVersion) :
    ((wireContract presentation).checker ()).check claim article = false := by
  simp [wireContract, wireChecker,
    checkWireArticle_version_gate wrongVersion]

#print axioms scope_iff_closed_derivation
#print axioms rawContract
#print axioms wireContract
#print axioms checkRaw_erase_eq_decide
#print axioms nativeToRaw
#print axioms nativeToWire
#print axioms compiled_replays_agree
#print axioms compiled_pair_accepts
#print axioms compiled_pair_rejects_wrong_claim
#print axioms raw_exists_iff_wire_exists
#print axioms wrong_wire_version_rejected

end Mettapedia.GSLT.LanguageDef.NIKCertificateGSLTOperationalShield
