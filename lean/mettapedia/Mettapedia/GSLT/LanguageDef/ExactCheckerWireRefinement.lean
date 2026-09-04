import Mettapedia.GSLT.LanguageDef.KernelAuthority

/-!
# Exact refinement of encoded certificate checkers

This module states the representation-independent correctness obligation for a
checker implementation whose public inputs are encoded claims and encoded
certificates.  Exactness covers the complete physical input space:

* decodable inputs replay the abstract checker;
* undecodable claims or certificates are rejected.

Agreement only on encoder-produced inputs is deliberately weaker.  The
negative control exhibits an implementation that agrees on every canonical
input while accepting malformed input.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ExactCheckerWireRefinement

open KernelAuthority

universe uClaim uCertificate uClaimWire uCertificateWire uLevel

/-- The semantic predicate on a claim wire is the source meaning of its
decoded claim; malformed claim wires have no meaning. -/
def DecodedMeaning
    {Claim : Type uClaim} {ClaimWire : Type uClaimWire}
    (claimCodec : Checker.PartialCodec Claim ClaimWire)
    (meaning : Claim → Prop) (wire : ClaimWire) : Prop :=
  match claimCodec.decode wire with
  | none => False
  | some claim => meaning claim

/-- The canonical fail-closed checker induced by claim and certificate
decoders.  This is a specification, not a generated implementation. -/
def decodedChecker
    {Claim : Type uClaim} {Certificate : Type uCertificate}
    {ClaimWire : Type uClaimWire} {CertificateWire : Type uCertificateWire}
    (source : Checker Claim Certificate)
    (claimCodec : Checker.PartialCodec Claim ClaimWire)
    (certificateCodec : Checker.PartialCodec Certificate CertificateWire) :
    Checker ClaimWire CertificateWire where
  check wireClaim wireCertificate :=
    match claimCodec.decode wireClaim,
        certificateCodec.decode wireCertificate with
    | some claim, some certificate => source.check claim certificate
    | _, _ => false

/-- A physical checker exactly implements the decoded abstract checker on all
wire inputs, not only on canonical encodings. -/
structure ExactWireRefinement
    {Claim : Type uClaim} {Certificate : Type uCertificate}
    {ClaimWire : Type uClaimWire} {CertificateWire : Type uCertificateWire}
    (source : Checker Claim Certificate)
    (claimCodec : Checker.PartialCodec Claim ClaimWire)
    (certificateCodec : Checker.PartialCodec Certificate CertificateWire)
    (target : Checker ClaimWire CertificateWire) : Prop where
  check_eq_decoded : ∀ wireClaim wireCertificate,
    target.check wireClaim wireCertificate =
      (decodedChecker source claimCodec certificateCodec).check
        wireClaim wireCertificate

namespace ExactWireRefinement

variable
    {Claim : Type uClaim} {Certificate : Type uCertificate}
    {ClaimWire : Type uClaimWire} {CertificateWire : Type uCertificateWire}
    {source : Checker Claim Certificate}
    {claimCodec : Checker.PartialCodec Claim ClaimWire}
    {certificateCodec : Checker.PartialCodec Certificate CertificateWire}
    {target : Checker ClaimWire CertificateWire}

/-- The reference decoded checker satisfies its own exact implementation
contract. -/
def reference : ExactWireRefinement source claimCodec certificateCodec
    (decodedChecker source claimCodec certificateCodec) where
  check_eq_decoded _ _ := rfl

/-- Exact total-wire refinement implies the expected commuting equation on
canonical inputs. -/
theorem canonical_check_commutes
    (refinement : ExactWireRefinement source claimCodec certificateCodec target)
    (claim : Claim) (certificate : Certificate) :
    target.check (claimCodec.encode claim)
        (certificateCodec.encode certificate) =
      source.check claim certificate := by
  rw [refinement.check_eq_decoded]
  simp [decodedChecker, claimCodec.decode_encode,
    certificateCodec.decode_encode]

/-- A malformed claim wire is rejected independently of its certificate. -/
theorem rejects_undecodable_claim
    (refinement : ExactWireRefinement source claimCodec certificateCodec target)
    {wireClaim : ClaimWire} (malformed : claimCodec.decode wireClaim = none)
    (wireCertificate : CertificateWire) :
    target.check wireClaim wireCertificate = false := by
  rw [refinement.check_eq_decoded]
  simp [decodedChecker, malformed]

/-- A malformed certificate wire is rejected independently of a decodable
claim. -/
theorem rejects_undecodable_certificate
    (refinement : ExactWireRefinement source claimCodec certificateCodec target)
    {wireCertificate : CertificateWire}
    (malformed : certificateCodec.decode wireCertificate = none)
    (wireClaim : ClaimWire) :
    target.check wireClaim wireCertificate = false := by
  rw [refinement.check_eq_decoded]
  simp [decodedChecker, malformed]

/-- Exact fail-closed decoding transports source soundness to the complete
wire carrier. -/
theorem sound
    (refinement : ExactWireRefinement source claimCodec certificateCodec target)
    {meaning : Claim → Prop} (sourceSound : source.Sound meaning) :
    target.Sound (DecodedMeaning claimCodec meaning) := by
  intro wireClaim wireCertificate accepted
  have decodedAccepted :
      (decodedChecker source claimCodec certificateCodec).check
          wireClaim wireCertificate = true := by
    rw [← refinement.check_eq_decoded]
    exact accepted
  cases claimResult : claimCodec.decode wireClaim with
  | none =>
      simp [decodedChecker, claimResult] at decodedAccepted
  | some claim =>
      cases certificateResult : certificateCodec.decode wireCertificate with
      | none =>
          simp [decodedChecker, claimResult, certificateResult] at decodedAccepted
      | some certificate =>
          have sourceAccepted : source.check claim certificate = true := by
            simpa [decodedChecker, claimResult, certificateResult] using
              decodedAccepted
          simpa [DecodedMeaning, claimResult] using
            sourceSound claim certificate sourceAccepted

/-- Exact fail-closed decoding transports certificate completeness to the
complete wire carrier. -/
theorem certificateComplete
    (refinement : ExactWireRefinement source claimCodec certificateCodec target)
    {meaning : Claim → Prop}
    (sourceComplete : source.CertificateComplete meaning) :
    target.CertificateComplete (DecodedMeaning claimCodec meaning) := by
  intro wireClaim meaningful
  cases claimResult : claimCodec.decode wireClaim with
  | none =>
      simp [DecodedMeaning, claimResult] at meaningful
  | some claim =>
      have sourceMeaning : meaning claim := by
        simpa [DecodedMeaning, claimResult] using meaningful
      obtain ⟨certificate, sourceAccepted⟩ :=
        sourceComplete claim sourceMeaning
      refine ⟨certificateCodec.encode certificate, ?_⟩
      rw [refinement.check_eq_decoded]
      simp [decodedChecker, claimResult, certificateCodec.decode_encode,
        sourceAccepted]

/-- Exact fail-closed decoding transports source authority to the complete
wire carrier. -/
theorem authority
    (refinement : ExactWireRefinement source claimCodec certificateCodec target)
    {meaning : Claim → Prop} (sourceAuthority : source.Authority meaning) :
    target.Authority (DecodedMeaning claimCodec meaning) where
  sound := refinement.sound sourceAuthority.sound
  complete := refinement.certificateComplete sourceAuthority.complete

/-- If source soundness separates a claim from meaning, every physical
certificate wire is rejected for the canonical encoding of that claim. -/
theorem rejects_encoded_claim_outside_meaning
    (refinement : ExactWireRefinement source claimCodec certificateCodec target)
    {meaning : Claim → Prop} (sourceSound : source.Sound meaning)
    {claim : Claim} (outsideMeaning : ¬ meaning claim)
    (wireCertificate : CertificateWire) :
    target.check (claimCodec.encode claim) wireCertificate = false := by
  cases accepted : target.check (claimCodec.encode claim) wireCertificate with
  | false => rfl
  | true =>
      have wireMeaning :
          DecodedMeaning claimCodec meaning (claimCodec.encode claim) :=
        refinement.sound sourceSound _ _ accepted
      have claimMeaning : meaning claim := by
        simpa [DecodedMeaning, claimCodec.decode_encode] using wireMeaning
      exact (outsideMeaning claimMeaning).elim

end ExactWireRefinement

/-- Exact checker implementation at a strictly lower trust level.  The level
order and the wire-correctness theorem remain orthogonal fields. -/
structure StrictlyLowerExactWireRefinement
    {Level : Type uLevel} [Preorder Level]
    (hostLevel targetLevel : Level)
    {Claim : Type uClaim} {Certificate : Type uCertificate}
    {ClaimWire : Type uClaimWire} {CertificateWire : Type uCertificateWire}
    (source : Checker Claim Certificate)
    (claimCodec : Checker.PartialCodec Claim ClaimWire)
    (certificateCodec : Checker.PartialCodec Certificate CertificateWire)
    (target : Checker ClaimWire CertificateWire) : Prop where
  below : targetLevel < hostLevel
  wireRefinement : ExactWireRefinement source claimCodec certificateCodec target

/-- Strict stratification forbids a checker-refinement claim at its own host
level. -/
theorem no_sameLevel_refinement
    {Level : Type uLevel} [Preorder Level] (level : Level)
    {Claim : Type uClaim} {Certificate : Type uCertificate}
    {ClaimWire : Type uClaimWire} {CertificateWire : Type uCertificateWire}
    (source : Checker Claim Certificate)
    (claimCodec : Checker.PartialCodec Claim ClaimWire)
    (certificateCodec : Checker.PartialCodec Certificate CertificateWire)
    (target : Checker ClaimWire CertificateWire) :
    ¬ Nonempty (StrictlyLowerExactWireRefinement level level
      source claimCodec certificateCodec target) := by
  rintro ⟨refinement⟩
  exact lt_irrefl level refinement.below

/-! ## Controls -/

namespace Canary

def source : Checker Bool Unit where
  check claim _certificate := claim

def sourceMeaning (claim : Bool) : Prop := claim = true

theorem source_authority : source.Authority sourceMeaning where
  sound := by
    intro claim certificate accepted
    simpa [source, sourceMeaning] using accepted
  complete := by
    intro claim meaningful
    exact ⟨(), by simpa [source, sourceMeaning] using meaningful⟩

def claimCodec : Checker.PartialCodec Bool (Option Bool) where
  encode := some
  decode := id
  decode_encode _ := rfl

def certificateCodec : Checker.PartialCodec Unit (Option Unit) where
  encode := some
  decode := id
  decode_encode _ := rfl

abbrev referenceChecker : Checker (Option Bool) (Option Unit) :=
  decodedChecker source claimCodec certificateCodec

def exactReference : ExactWireRefinement
    source claimCodec certificateCodec referenceChecker :=
  ExactWireRefinement.reference

/-- Positive control: exact decoding transports authority to the wire
checker. -/
theorem reference_authority :
    referenceChecker.Authority (DecodedMeaning claimCodec sourceMeaning) :=
  exactReference.authority source_authority

/-- Positive malformed-input control. -/
theorem reference_rejects_missing_claim :
    referenceChecker.check none (some ()) = false := rfl

/-- This implementation agrees with the source on every canonical input but
accepts all malformed inputs. -/
def canonicalOnlyChecker : Checker (Option Bool) (Option Unit) where
  check wireClaim wireCertificate :=
    match wireClaim, wireCertificate with
    | some claim, some _certificate => claim
    | _, _ => true

theorem canonicalOnlyChecker_commutes
    (claim : Bool) (certificate : Unit) :
    canonicalOnlyChecker.check (claimCodec.encode claim)
        (certificateCodec.encode certificate) =
      source.check claim certificate := by
  cases claim <;> rfl

/-- Negative control: canonical agreement does not imply exact total-wire
refinement because malformed claims are accepted. -/
theorem canonicalOnlyChecker_not_exact :
    ¬ ExactWireRefinement source claimCodec certificateCodec
      canonicalOnlyChecker := by
  intro refinement
  have malformed := refinement.check_eq_decoded
    (none : Option Bool) (some ())
  simp [canonicalOnlyChecker, decodedChecker, claimCodec] at malformed

def levelOneReference : StrictlyLowerExactWireRefinement
    (hostLevel := (1 : Nat)) (targetLevel := 0)
    source claimCodec certificateCodec referenceChecker where
  below := by decide
  wireRefinement := exactReference

end Canary

/-! ## Axiom audit -/

#print axioms ExactWireRefinement.canonical_check_commutes
#print axioms ExactWireRefinement.rejects_undecodable_claim
#print axioms ExactWireRefinement.rejects_encoded_claim_outside_meaning
#print axioms ExactWireRefinement.authority
#print axioms no_sameLevel_refinement
#print axioms Canary.reference_authority
#print axioms Canary.canonicalOnlyChecker_not_exact

end Mettapedia.GSLT.LanguageDef.ExactCheckerWireRefinement
