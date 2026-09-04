import Mettapedia.GSLT.LanguageDef.ExactCheckerWireRefinement
import Mettapedia.GSLT.LanguageDef.M0GCLogicalReplay
import Mettapedia.GSLT.LanguageDef.M0GCLogicalReplayCanary

/-!
# Exact M0GC byte-checker refinement

This module connects the existing M0GC byte decoder and logical replay
checker to the representation-independent exact-wire refinement contract.
The key physical fact is that every successfully decoded certificate obeys
the bounds required by the canonical encoder.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.M0GCExactWireRefinement

open Mettapedia.GSLT.LanguageDef.CompiledPlanWireFormat
open Mettapedia.GSLT.LanguageDef.ExactCheckerWireRefinement
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.M0GCLogicalReplay
open Mettapedia.GSLT.LanguageDef.M0GCWireFormat
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- A successful fixed-count reader returns exactly the requested number of
values. -/
theorem readMany_output_length
    {Value : Type} (read : Reader Value) :
    ∀ {count : Nat} {input : List UInt8} {values : List Value}
      {rest : List UInt8},
      readMany read count input = some (values, rest) →
        values.length = count
  | 0, input, values, rest, decoded => by
      simp only [readMany] at decoded
      exact congrArg (fun result => result.1.length)
        (Option.some.inj decoded).symm
  | count + 1, input, values, rest, decoded => by
      simp only [readMany] at decoded
      rcases Option.bind_eq_some_iff.mp decoded with
        ⟨⟨head, afterHead⟩, _headDecoded, tailDecoded⟩
      rcases Option.bind_eq_some_iff.mp tailDecoded with
        ⟨⟨tail, suffix⟩, tailRead, finished⟩
      have tailLength : tail.length = count :=
        readMany_output_length read tailRead
      have pairEqual := Option.some.inj finished
      have valuesEqual : head :: tail = values := congrArg Prod.fst pairEqual
      rw [← valuesEqual, List.length_cons, tailLength]

/-- A successful fixed-width byte read returns exactly the requested number
of bytes. -/
theorem readBytes_output_length {count : Nat} {input bytes rest : List UInt8}
    (decoded : readBytes count input = some (bytes, rest)) :
    bytes.length = count := by
  unfold readBytes at decoded
  split at decoded
  next fits =>
    have pairEqual := Option.some.inj decoded
    have bytesEqual : input.take count = bytes := congrArg Prod.fst pairEqual
    rw [← bytesEqual, List.length_take, min_eq_left fits]
  next doesNotFit => simp at decoded

/-- Successful header decoding establishes both fixed-width digest
invariants carried by the decoded header. -/
theorem readHeader_digest_lengths
    {input : List UInt8} {header : Header} {rest : List UInt8}
    (decoded : readHeader input = some (header, rest)) :
    header.profileDigest.length = digestWidth ∧
      header.sourceDigest.length = digestWidth := by
  unfold readHeader at decoded
  rcases Option.bind_eq_some_iff.mp decoded with
    ⟨⟨_, rest0⟩, _magicRead, afterMagic⟩
  rcases Option.bind_eq_some_iff.mp afterMagic with
    ⟨⟨decodedVersion, rest1⟩, _versionRead, afterVersion⟩
  by_cases wrongVersion : decodedVersion != version
  · simp [wrongVersion] at afterVersion
  · simp only [wrongVersion] at afterVersion
    rcases Option.bind_eq_some_iff.mp afterVersion with
      ⟨⟨flags, rest2⟩, _flagsRead, afterFlags⟩
    rcases Option.bind_eq_some_iff.mp afterFlags with
      ⟨⟨termCount, rest3⟩, _termCountRead, afterTermCount⟩
    rcases Option.bind_eq_some_iff.mp afterTermCount with
      ⟨⟨childCount, rest4⟩, _childCountRead, afterChildCount⟩
    rcases Option.bind_eq_some_iff.mp afterChildCount with
      ⟨⟨proofCount, rest5⟩, _proofCountRead, afterProofCount⟩
    rcases Option.bind_eq_some_iff.mp afterProofCount with
      ⟨⟨argumentCount, rest6⟩, _argumentCountRead, afterArgumentCount⟩
    rcases Option.bind_eq_some_iff.mp afterArgumentCount with
      ⟨⟨premiseReferenceCount, rest7⟩, _premiseCountRead,
        afterPremiseCount⟩
    rcases Option.bind_eq_some_iff.mp afterPremiseCount with
      ⟨⟨goalTerm, rest8⟩, _goalRead, afterGoal⟩
    rcases Option.bind_eq_some_iff.mp afterGoal with
      ⟨⟨profileDigest, rest9⟩, profileRead, afterProfile⟩
    rcases Option.bind_eq_some_iff.mp afterProfile with
      ⟨⟨sourceDigest, rest10⟩, sourceRead, afterSource⟩
    rcases Option.bind_eq_some_iff.mp afterSource with
      ⟨⟨bodyChecksum, suffix⟩, _checksumRead, finished⟩
    have pairEqual := Option.some.inj finished
    have headerEqual :
        ({ flags, termCount, childCount, proofCount, argumentCount,
           premiseReferenceCount, goalTerm, profileDigest, sourceDigest,
           bodyChecksum } : Header) = header := congrArg Prod.fst pairEqual
    subst header
    exact ⟨readBytes_output_length profileRead,
      readBytes_output_length sourceRead⟩

/-- The canonical decoder cannot produce an out-of-range certificate: table
lengths come from `UInt32` header counts and digest widths come from the two
fixed-width header reads. -/
theorem readCertificate_encodable
    {input : List UInt8} {certificate : Certificate} {rest : List UInt8}
    (decoded : readCertificate input = some (certificate, rest)) :
    certificate.Encodable := by
  unfold readCertificate at decoded
  rcases Option.bind_eq_some_iff.mp decoded with
    ⟨⟨header, rest0⟩, headerRead, afterHeader⟩
  rcases Option.bind_eq_some_iff.mp afterHeader with
    ⟨⟨terms, rest1⟩, termsRead, afterTerms⟩
  rcases Option.bind_eq_some_iff.mp afterTerms with
    ⟨⟨children, rest2⟩, childrenRead, afterChildren⟩
  rcases Option.bind_eq_some_iff.mp afterChildren with
    ⟨⟨proofs, rest3⟩, proofsRead, afterProofs⟩
  rcases Option.bind_eq_some_iff.mp afterProofs with
    ⟨⟨arguments, rest4⟩, argumentsRead, afterArguments⟩
  rcases Option.bind_eq_some_iff.mp afterArguments with
    ⟨⟨premises, suffix⟩, premisesRead, finished⟩
  dsimp only at finished
  split at finished
  next checksumExact =>
    have pairEqual := Option.some.inj finished
    have certificateEqual :
        ({ flags := header.flags
           terms
           children
           proofs
           arguments
           premises
           goalTerm := header.goalTerm
           profileDigest := header.profileDigest
           sourceDigest := header.sourceDigest } : Certificate) =
          certificate := congrArg Prod.fst pairEqual
    subst certificate
    have termLength : terms.length = header.termCount.toNat :=
      readMany_output_length readTermNode termsRead
    have childLength : children.length = header.childCount.toNat :=
      readMany_output_length readUInt32LE childrenRead
    have proofLength : proofs.length = header.proofCount.toNat :=
      readMany_output_length readProofNode proofsRead
    have argumentLength : arguments.length = header.argumentCount.toNat :=
      readMany_output_length readUInt32LE argumentsRead
    have premiseLength :
        premises.length = header.premiseReferenceCount.toNat :=
      readMany_output_length readUInt32LE premisesRead
    have digestLengths := readHeader_digest_lengths headerRead
    exact
      ⟨by simpa [termLength] using header.termCount.toNat_lt_size,
       by simpa [childLength] using header.childCount.toNat_lt_size,
       by simpa [proofLength] using header.proofCount.toNat_lt_size,
       by simpa [argumentLength] using header.argumentCount.toNat_lt_size,
       by simpa [premiseLength] using
         header.premiseReferenceCount.toNat_lt_size,
       digestLengths.1,
       digestLengths.2⟩
  next checksumMismatch => simp at finished

/-- Every certificate returned by the public exact-file decoder belongs to
the encoder's canonical domain. -/
theorem decodeCertificate?_encodable
    {bytes : List UInt8} {certificate : Certificate}
    (decoded : decodeCertificate? bytes = some certificate) :
    certificate.Encodable := by
  unfold decodeCertificate? at decoded
  cases readResult : readCertificate bytes with
  | none => simp [readResult] at decoded
  | some pair =>
      rcases pair with ⟨parsed, rest⟩
      cases rest with
      | nil =>
          simp only [readResult, Option.some.injEq] at decoded
          subst certificate
          exact readCertificate_encodable readResult
      | cons byte tail => simp [readResult] at decoded

/-! ## Exact checker refinement -/

/-- The precise abstract certificate carrier represented by canonical M0GC
bytes.  This is a domain restriction justified by decoding, not an extra
runtime validation assumption. -/
abbrev EncodableCertificate :=
  { certificate : Certificate // certificate.Encodable }

def certificateEncodableDecidable (certificate : Certificate) :
    Decidable certificate.Encodable := by
  unfold Certificate.Encodable
  infer_instance

/-- Identity wire discipline for submitted claims.  M0GC's physical boundary
encodes certificates; its current replay API receives the submitted pattern
as an already parsed value. -/
def patternCodec : Checker.PartialCodec Pattern Pattern where
  encode := id
  decode := some
  decode_encode _ := rfl

/-- Canonical M0GC encoding with fail-closed decoding into the exact
encodable-certificate domain. -/
def certificateCodec :
    Checker.PartialCodec EncodableCertificate (List UInt8) where
  encode certificate := encodeCertificate certificate.1
  decode bytes :=
    match decodeCertificate? bytes with
    | none => none
    | some certificate =>
        letI : Decidable certificate.Encodable :=
          certificateEncodableDecidable certificate
        if encodable : certificate.Encodable then
          some ⟨certificate, encodable⟩
        else
          none
  decode_encode certificate := by
    simp [decodeCertificate?_encodeCertificate certificate.1 certificate.2,
      certificate.2]

/-- Logical replay over decoded, canonically encodable certificates. -/
def certificateChecker (definition : ValidatedCalculusLanguageDef)
    (profile : RuntimeProfile) : Checker Pattern EncodableCertificate where
  check submitted certificate :=
    checkCertificate definition profile submitted certificate.1

/-- The already implemented public M0GC byte checker. -/
def byteChecker (definition : ValidatedCalculusLanguageDef)
    (profile : RuntimeProfile) : Checker Pattern (List UInt8) where
  check := checkBytes definition profile

@[simp] theorem certificateCodec_encode
    (certificate : EncodableCertificate) :
    certificateCodec.encode certificate =
      encodeCertificate certificate.1 := rfl

@[simp] theorem byteChecker_check
    (definition : ValidatedCalculusLanguageDef) (profile : RuntimeProfile)
    (submitted : Pattern) (bytes : List UInt8) :
    (byteChecker definition profile).check submitted bytes =
      checkBytes definition profile submitted bytes := rfl

/-- The actual M0GC byte checker is exactly the fail-closed decoding of the
logical certificate checker on every byte string. -/
def exactWireRefinement (definition : ValidatedCalculusLanguageDef)
    (profile : RuntimeProfile) :
    ExactWireRefinement (certificateChecker definition profile)
      patternCodec certificateCodec (byteChecker definition profile) where
  check_eq_decoded submitted bytes := by
    unfold byteChecker decodedChecker patternCodec certificateCodec
      certificateChecker checkBytes
    cases decoded : decodeCertificate? bytes with
    | none => simp [decoded]
    | some certificate =>
        simp [decoded, decodeCertificate?_encodable decoded]

/-- Canonical inputs commute through the concrete byte checker. -/
theorem canonical_check_commutes (definition : ValidatedCalculusLanguageDef)
    (profile : RuntimeProfile) (submitted : Pattern)
    (certificate : EncodableCertificate) :
    checkBytes definition profile submitted
        (encodeCertificate certificate.1) =
      checkCertificate definition profile submitted certificate.1 := by
  exact ExactWireRefinement.canonical_check_commutes
    (exactWireRefinement definition profile) submitted certificate

/-- Every byte string rejected by the M0GC decoder is rejected by the
concrete byte checker for every submitted claim. -/
theorem malformed_bytes_rejected (definition : ValidatedCalculusLanguageDef)
    (profile : RuntimeProfile) (submitted : Pattern) (bytes : List UInt8)
    (malformed : decodeCertificate? bytes = none) :
    checkBytes definition profile submitted bytes = false := by
  simp [checkBytes, malformed]

theorem leading_zero_bytes_rejected (tail : List UInt8) :
    decodeCertificate? (0 :: tail) = none := rfl

/-- Logical soundness of decoded replay, stated on the exact abstract
certificate carrier used by the refinement theorem. -/
theorem certificateChecker_sound (definition : ValidatedCalculusLanguageDef)
    (profile : RuntimeProfile) :
    (certificateChecker definition profile).Sound
      (fun submitted => Nonempty (Derivation definition submitted)) := by
  intro submitted certificate accepted
  exact checkCertificate_sound accepted

/-- Exact wire refinement transports logical soundness to the implemented
byte checker. -/
theorem byteChecker_sound (definition : ValidatedCalculusLanguageDef)
    (profile : RuntimeProfile) :
    (byteChecker definition profile).Sound
      (fun submitted => Nonempty (Derivation definition submitted)) := by
  have transported := ExactWireRefinement.sound
    (exactWireRefinement definition profile)
    (certificateChecker_sound definition profile)
  intro submitted bytes accepted
  have decodedMeaning := transported submitted bytes accepted
  simpa [DecodedMeaning, patternCodec] using decodedMeaning

/-! ## Concrete discriminators -/

namespace Canary

open Mettapedia.GSLT.LanguageDef.M0GCLogicalReplayCanary

/-- Positive control crossing the concrete source calculus, canonical codec,
byte decoder, materializer, and logical replay checker. -/
theorem encoded_pair_accepts :
    (byteChecker definition profile).check pair
        (certificateCodec.encode ⟨certificate, certificate_encodable⟩) =
      true := by
  rw [byteChecker_check, certificateCodec_encode]
  exact encoded_bytes_accept

/-- Negative physical control: corrupt magic is rejected through the exact
all-input refinement boundary. -/
theorem corrupt_magic_rejected :
    (byteChecker definition profile).check pair
        (0 :: (encodeCertificate certificate).tail) = false := by
  rw [byteChecker_check]
  apply malformed_bytes_rejected definition profile pair
  exact leading_zero_bytes_rejected _

/-- Negative semantic control: valid bytes cannot substitute the certificate's
own target for a different submitted claim. -/
theorem unrelated_claim_rejected :
    (byteChecker definition profile).check unrelatedClaim
        (certificateCodec.encode ⟨certificate, certificate_encodable⟩) =
      false := by
  rw [byteChecker_check, certificateCodec_encode]
  rw [canonical_check_commutes]
  exact wrong_submitted_claim_rejected

end Canary

#print axioms readCertificate_encodable
#print axioms exactWireRefinement
#print axioms byteChecker_sound
#print axioms Canary.encoded_pair_accepts
#print axioms Canary.corrupt_magic_rejected
#print axioms Canary.unrelated_claim_rejected

end Mettapedia.GSLT.LanguageDef.M0GCExactWireRefinement
