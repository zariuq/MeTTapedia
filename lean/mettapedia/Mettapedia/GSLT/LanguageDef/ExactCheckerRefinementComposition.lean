import Mettapedia.GSLT.LanguageDef.ExactCheckerWireRefinement

/-!
# Composing exact checker refinements down to C

A generated native checker normally crosses more than one representation
boundary.  In the intended direct route, an abstract certificate checker is
lowered to a StructuredC-shaped checker and then to a C-shaped checker.  Each
boundary must agree on its complete input carrier, including malformed inputs;
agreement only on compiler-produced examples is insufficient.

This module proves that fail-closed partial codecs and exact checker
refinements compose.  Consequently source soundness reaches the final C
checker, and malformed inputs at either decoding layer remain rejected.  The
record deliberately contains no callback or scripting layer.  An external
qualification must still establish that emitted C implements the modeled
final checker; a Lean record cannot infer the implementation language of an
arbitrary executable.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ExactCheckerRefinementComposition

open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.ExactCheckerWireRefinement

universe uSource uMiddle uTarget
universe uClaim uCertificate uMiddleClaim uMiddleCertificate
universe uTargetClaim uTargetCertificate

/-! ## Partial codecs compose without weakening fail-closed decoding -/

/-- Compose an abstract-to-middle codec with a middle-to-target codec. -/
def composeCodec
    {Source : Type uSource} {Middle : Type uMiddle} {Target : Type uTarget}
    (first : Checker.PartialCodec Source Middle)
    (second : Checker.PartialCodec Middle Target) :
    Checker.PartialCodec Source Target where
  encode source := second.encode (first.encode source)
  decode target := (second.decode target).bind first.decode
  decode_encode source := by
    simp [second.decode_encode, first.decode_encode]

@[simp] theorem composeCodec_encode
    {Source : Type uSource} {Middle : Type uMiddle} {Target : Type uTarget}
    (first : Checker.PartialCodec Source Middle)
    (second : Checker.PartialCodec Middle Target) (source : Source) :
    (composeCodec first second).encode source =
      second.encode (first.encode source) :=
  rfl

@[simp] theorem composeCodec_decode
    {Source : Type uSource} {Middle : Type uMiddle} {Target : Type uTarget}
    (first : Checker.PartialCodec Source Middle)
    (second : Checker.PartialCodec Middle Target) (target : Target) :
    (composeCodec first second).decode target =
      (second.decode target).bind first.decode :=
  rfl

/-! ## Exact total-input refinement is transitive -/

/-- Compose two exact fail-closed checker refinements.  The intermediate
checker is used as an independently specified seam; it is not erased from the
proof merely because the resulting codec can be written directly. -/
def composeExactRefinement
    {Claim : Type uClaim} {Certificate : Type uCertificate}
    {MiddleClaim : Type uMiddleClaim}
    {MiddleCertificate : Type uMiddleCertificate}
    {TargetClaim : Type uTargetClaim}
    {TargetCertificate : Type uTargetCertificate}
    {source : Checker Claim Certificate}
    {sourceClaimCodec : Checker.PartialCodec Claim MiddleClaim}
    {sourceCertificateCodec :
      Checker.PartialCodec Certificate MiddleCertificate}
    {middle : Checker MiddleClaim MiddleCertificate}
    {targetClaimCodec : Checker.PartialCodec MiddleClaim TargetClaim}
    {targetCertificateCodec :
      Checker.PartialCodec MiddleCertificate TargetCertificate}
    {target : Checker TargetClaim TargetCertificate}
    (first : ExactWireRefinement source sourceClaimCodec
      sourceCertificateCodec middle)
    (second : ExactWireRefinement middle targetClaimCodec
      targetCertificateCodec target) :
    ExactWireRefinement source
      (composeCodec sourceClaimCodec targetClaimCodec)
      (composeCodec sourceCertificateCodec targetCertificateCodec) target where
  check_eq_decoded targetClaim targetCertificate := by
    rw [second.check_eq_decoded]
    cases claimDecoded : targetClaimCodec.decode targetClaim with
    | none =>
        simp [decodedChecker, composeCodec, claimDecoded]
    | some middleClaim =>
        cases certificateDecoded :
            targetCertificateCodec.decode targetCertificate with
        | none =>
            simp [decodedChecker, composeCodec, claimDecoded,
              certificateDecoded]
        | some middleCertificate =>
            simp [decodedChecker, composeCodec, claimDecoded,
              certificateDecoded,
              first.check_eq_decoded middleClaim middleCertificate]

/-! ## The direct StructuredC-to-C contract -/

/-- A two-stage native checker route.  The middle carrier is intended to be
the exact StructuredC ABI and the final carrier the exact C ABI.  Both
refinements quantify over all inputs, so neither stage can hide permissive
malformed-input behavior behind canonical examples. -/
structure DirectNativeCheckerPipeline
    {Claim : Type uClaim} {Certificate : Type uCertificate}
    {StructuredClaim : Type uMiddleClaim}
    {StructuredCertificate : Type uMiddleCertificate}
    {CClaim : Type uTargetClaim} {CCertificate : Type uTargetCertificate}
    (source : Checker Claim Certificate)
    (sourceClaimCodec : Checker.PartialCodec Claim StructuredClaim)
    (sourceCertificateCodec :
      Checker.PartialCodec Certificate StructuredCertificate)
    (structuredChecker : Checker StructuredClaim StructuredCertificate)
    (structuredClaimCodec : Checker.PartialCodec StructuredClaim CClaim)
    (structuredCertificateCodec :
      Checker.PartialCodec StructuredCertificate CCertificate)
    (cChecker : Checker CClaim CCertificate) : Prop where
  structuredExact : ExactWireRefinement source sourceClaimCodec
    sourceCertificateCodec structuredChecker
  cExact : ExactWireRefinement structuredChecker structuredClaimCodec
    structuredCertificateCodec cChecker

namespace DirectNativeCheckerPipeline

variable
    {Claim : Type uClaim} {Certificate : Type uCertificate}
    {StructuredClaim : Type uMiddleClaim}
    {StructuredCertificate : Type uMiddleCertificate}
    {CClaim : Type uTargetClaim} {CCertificate : Type uTargetCertificate}
    {source : Checker Claim Certificate}
    {sourceClaimCodec : Checker.PartialCodec Claim StructuredClaim}
    {sourceCertificateCodec :
      Checker.PartialCodec Certificate StructuredCertificate}
    {structuredChecker : Checker StructuredClaim StructuredCertificate}
    {structuredClaimCodec : Checker.PartialCodec StructuredClaim CClaim}
    {structuredCertificateCodec :
      Checker.PartialCodec StructuredCertificate CCertificate}
    {cChecker : Checker CClaim CCertificate}

/-- The two explicit stages induce one exact source-to-C refinement. -/
def exactToC
    (pipeline : DirectNativeCheckerPipeline source sourceClaimCodec
      sourceCertificateCodec structuredChecker structuredClaimCodec
      structuredCertificateCodec cChecker) :
    ExactWireRefinement source
      (composeCodec sourceClaimCodec structuredClaimCodec)
      (composeCodec sourceCertificateCodec structuredCertificateCodec)
      cChecker :=
  composeExactRefinement pipeline.structuredExact pipeline.cExact

/-- Source checker soundness reaches every accepted final C input. -/
theorem cSound
    (pipeline : DirectNativeCheckerPipeline source sourceClaimCodec
      sourceCertificateCodec structuredChecker structuredClaimCodec
      structuredCertificateCodec cChecker)
    {Meaning : Claim → Prop} (sourceSound : source.Sound Meaning) :
    cChecker.Sound
      (DecodedMeaning
        (composeCodec sourceClaimCodec structuredClaimCodec) Meaning) :=
  pipeline.exactToC.sound sourceSound

/-- Failure of either claim decoder forces rejection at the final C layer. -/
theorem rejectsMalformedClaim
    (pipeline : DirectNativeCheckerPipeline source sourceClaimCodec
      sourceCertificateCodec structuredChecker structuredClaimCodec
      structuredCertificateCodec cChecker)
    {cClaim : CClaim}
    (malformed :
      (composeCodec sourceClaimCodec structuredClaimCodec).decode cClaim =
        none)
    (cCertificate : CCertificate) :
    cChecker.check cClaim cCertificate = false :=
  pipeline.exactToC.rejects_undecodable_claim malformed cCertificate

/-- Failure of either certificate decoder forces rejection at the final C
layer. -/
theorem rejectsMalformedCertificate
    (pipeline : DirectNativeCheckerPipeline source sourceClaimCodec
      sourceCertificateCodec structuredChecker structuredClaimCodec
      structuredCertificateCodec cChecker)
    {cCertificate : CCertificate}
    (malformed :
      (composeCodec sourceCertificateCodec structuredCertificateCodec).decode
        cCertificate = none)
    (cClaim : CClaim) :
    cChecker.check cClaim cCertificate = false :=
  pipeline.exactToC.rejects_undecodable_certificate malformed cClaim

end DirectNativeCheckerPipeline

/-! ## Positive and negative controls -/

namespace Canary

open Mettapedia.GSLT.LanguageDef.ExactCheckerWireRefinement.Canary

/-- A second physical wrapper around the first option-valued wire. -/
def outerClaimCodec :
    Checker.PartialCodec (Option Bool) (Option (Option Bool)) where
  encode := some
  decode := id
  decode_encode _ := rfl

def outerCertificateCodec :
    Checker.PartialCodec (Option Unit) (Option (Option Unit)) where
  encode := some
  decode := id
  decode_encode _ := rfl

abbrev cReference :
    Checker (Option (Option Bool)) (Option (Option Unit)) :=
  decodedChecker referenceChecker outerClaimCodec outerCertificateCodec

def directReference : DirectNativeCheckerPipeline source claimCodec
    certificateCodec referenceChecker outerClaimCodec outerCertificateCodec
    cReference where
  structuredExact := exactReference
  cExact := ExactWireRefinement.reference

theorem canonical_true_accepts :
    cReference.check (some (some true)) (some (some ())) = true :=
  rfl

theorem malformed_outer_claim_rejected :
    cReference.check none (some (some ())) = false :=
  rfl

theorem malformed_inner_claim_rejected :
    cReference.check (some none) (some (some ())) = false :=
  rfl

/-- This final checker agrees on every doubly canonical input but accepts all
malformed inputs. -/
def canonicalOnlyC :
    Checker (Option (Option Bool)) (Option (Option Unit)) where
  check wireClaim wireCertificate :=
    match wireClaim, wireCertificate with
    | some (some claim), some (some _certificate) => claim
    | _, _ => true

theorem canonicalOnlyC_commutes (claim : Bool) (certificate : Unit) :
    canonicalOnlyC.check
        ((composeCodec claimCodec outerClaimCodec).encode claim)
        ((composeCodec certificateCodec outerCertificateCodec).encode
          certificate) =
      source.check claim certificate := by
  cases claim <;> rfl

/-- Canonical-example agreement cannot inhabit the direct native contract:
the malformed outer input exposes the missing fail-closed refinement. -/
theorem canonicalOnlyC_not_direct :
    ¬ DirectNativeCheckerPipeline source claimCodec certificateCodec
      referenceChecker outerClaimCodec outerCertificateCodec
      canonicalOnlyC := by
  intro pipeline
  have rejected := pipeline.rejectsMalformedClaim
    (cClaim := (none : Option (Option Bool))) (by rfl)
    (some (some ()))
  exact Bool.noConfusion rejected

end Canary

/-! ## Audited theorem crowns -/

#print axioms composeCodec
#print axioms composeExactRefinement
#print axioms DirectNativeCheckerPipeline.exactToC
#print axioms DirectNativeCheckerPipeline.cSound
#print axioms DirectNativeCheckerPipeline.rejectsMalformedClaim
#print axioms DirectNativeCheckerPipeline.rejectsMalformedCertificate
#print axioms Canary.canonical_true_accepts
#print axioms Canary.malformed_outer_claim_rejected
#print axioms Canary.malformed_inner_claim_rejected
#print axioms Canary.canonicalOnlyC_not_direct

end Mettapedia.GSLT.LanguageDef.ExactCheckerRefinementComposition
