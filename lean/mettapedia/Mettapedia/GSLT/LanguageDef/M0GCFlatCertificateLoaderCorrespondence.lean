import Mettapedia.GSLT.LanguageDef.M0GCCanonicalBodyBytes

/-!
# Complete flat-loader refinement for M0GC

This module composes the fixed-offset header reader, flat body-table loader,
and original-body checksum gate used by the bounded M0GC proof-certificate
checker.  Its main theorem is a no-extra-acceptance result: every certificate
accepted by the flat loader is accepted, with no trailing bytes, by the
canonical sequential M0GC reader.

Maturity boundary: this is a fully connected proof of concept for the
byte-list algorithm represented by the current C loader.  It is not a C
semantics theorem and does not qualify packed structure casts, pointer
arithmetic, integer overflow, allocation, file I/O, compiler output, object
code, an operating system, or hardware.  M0GC is an experimental bounded
certificate format, not the official MM0/MMB format.
-/

namespace Mettapedia.GSLT.LanguageDef.M0GCFlatCertificateLoaderCorrespondence

open Mettapedia.GSLT.LanguageDef.CompiledPlanWireFormat
open Mettapedia.GSLT.LanguageDef.M0GCWireFormat
open Mettapedia.GSLT.LanguageDef.M0GCFlatBodyLoaderCorrespondence
open Mettapedia.GSLT.LanguageDef.M0GCFlatHeaderLoaderCorrespondence
open Mettapedia.GSLT.LanguageDef.M0GCCanonicalBodyBytes

/-- Executable flat certificate loader corresponding to the bounded C proof
of concept at the byte-list abstraction boundary. -/
def readCertificateFlat? (bytes : List UInt8) : Option Certificate := do
  let header ← readHeaderFlat? bytes
  let body := bytes.drop 104
  let tables ← readBodyFlat? (BodyCounts.ofHeader header) body
  if header.bodyChecksum = fnv1a64 body then
    some (certificateOfTables header tables)
  else
    none

/-- Factored canonical reading theorem.  A sequential header read and a
sequential body read, together with the canonical-body checksum, determine a
successful canonical certificate read. -/
theorem readCertificate_of_sequential_components
    (bytes : List UInt8) (header : Header) (tables : BodyTables)
    (headerRead : readHeader bytes = some (header, bytes.drop 104))
    (bodyRead :
      readBodySequential (BodyCounts.ofHeader header) (bytes.drop 104) =
        some (tables, []))
    (checksumExact :
      header.bodyChecksum =
        fnv1a64 (encodeBody (certificateOfTables header tables))) :
    readCertificate bytes =
      some (certificateOfTables header tables, []) := by
  cases termsResult :
      CompiledPlanWireFormat.readMany readTermNode header.termCount.toNat
        (bytes.drop 104) with
  | none =>
      simp [readBodySequential, BodyCounts.ofHeader, termsResult] at bodyRead
  | some termsPair =>
      rcases termsPair with ⟨terms, rest1⟩
      cases childrenResult :
          CompiledPlanWireFormat.readMany readUInt32LE
            header.childCount.toNat rest1 with
      | none =>
          simp [readBodySequential, BodyCounts.ofHeader, termsResult,
            childrenResult] at bodyRead
      | some childrenPair =>
          rcases childrenPair with ⟨children, rest2⟩
          cases proofsResult :
              CompiledPlanWireFormat.readMany readProofNode
                header.proofCount.toNat rest2 with
          | none =>
              simp [readBodySequential, BodyCounts.ofHeader, termsResult,
                childrenResult, proofsResult] at bodyRead
          | some proofsPair =>
              rcases proofsPair with ⟨proofs, rest3⟩
              cases argumentsResult :
                  CompiledPlanWireFormat.readMany readUInt32LE
                    header.argumentCount.toNat rest3 with
              | none =>
                  simp [readBodySequential, BodyCounts.ofHeader, termsResult,
                    childrenResult, proofsResult, argumentsResult]
                    at bodyRead
              | some argumentsPair =>
                  rcases argumentsPair with ⟨arguments, rest4⟩
                  cases premisesResult :
                      CompiledPlanWireFormat.readMany readUInt32LE
                        header.premiseReferenceCount.toNat rest4 with
                  | none =>
                      simp [readBodySequential, BodyCounts.ofHeader,
                        termsResult, childrenResult, proofsResult,
                        argumentsResult, premisesResult] at bodyRead
                  | some premisesPair =>
                      rcases premisesPair with ⟨premises, finalRest⟩
                      simp [readBodySequential, BodyCounts.ofHeader,
                        termsResult, childrenResult, proofsResult,
                        argumentsResult, premisesResult, Option.bind]
                        at bodyRead
                      rcases bodyRead with ⟨rfl, rfl⟩
                      unfold readCertificate
                      rw [headerRead]
                      simp [termsResult, childrenResult, proofsResult,
                        argumentsResult, premisesResult, Option.bind,
                        certificateOfTables, checksumExact]

/-- Main no-extra-acceptance theorem.  Successful flat loading refines the
canonical sequential proof-certificate reader exactly. -/
theorem readCertificateFlat?_refines_canonical
    (bytes : List UInt8) (certificate : Certificate)
    (accepted : readCertificateFlat? bytes = some certificate) :
    readCertificate bytes = some (certificate, []) := by
  cases headerResult : readHeaderFlat? bytes with
  | none =>
      simp [readCertificateFlat?, headerResult] at accepted
  | some header =>
      let body := bytes.drop 104
      cases tablesResult :
          readBodyFlat? (BodyCounts.ofHeader header) body with
      | none =>
          simp [readCertificateFlat?, headerResult, body, tablesResult]
            at accepted
      | some tables =>
          by_cases rawChecksumExact : header.bodyChecksum = fnv1a64 body
          · simp [readCertificateFlat?, headerResult, body, tablesResult,
              rawChecksumExact] at accepted
            subst certificate
            have headerSequential :=
              readHeaderFlat?_refines_sequential bytes header headerResult
            have bodySequential :=
              readBodyFlat?_refines_sequential
                (BodyCounts.ofHeader header) body tables tablesResult
            have bodyCanonical :=
              readBodyFlat?_canonical_bytes
                (BodyCounts.ofHeader header) body tables tablesResult
            have canonicalChecksum :
                header.bodyChecksum =
                  fnv1a64
                    (encodeBody (certificateOfTables header tables)) := by
              rw [encodeBody_certificateOfTables, ← bodyCanonical]
              exact rawChecksumExact
            exact readCertificate_of_sequential_components
              bytes header tables headerSequential bodySequential
              canonicalChecksum
          · simp [readCertificateFlat?, headerResult, body, tablesResult,
              rawChecksumExact] at accepted

/-- The flat loader therefore also refines the public exact-file decoder. -/
theorem readCertificateFlat?_refines_decodeCertificate?
    (bytes : List UInt8) (certificate : Certificate)
    (accepted : readCertificateFlat? bytes = some certificate) :
    decodeCertificate? bytes = some certificate := by
  have canonical :=
    readCertificateFlat?_refines_canonical bytes certificate accepted
  simp [decodeCertificate?, canonical]

/-! ## Positive and negative executable discriminators -/

theorem canonical_canary_flat_accepts :
    readCertificateFlat? (encodeCertificate canaryCertificate) =
      some canaryCertificate := by
  set_option maxRecDepth 10000 in
    decide

theorem corrupt_magic_flat_rejected :
    readCertificateFlat?
        (0 :: (encodeCertificate canaryCertificate).tail) = none := by
  decide

theorem wrong_version_flat_rejected :
    readCertificateFlat? wrongVersionCanary = none := by
  decide

theorem wrong_checksum_flat_rejected :
    readCertificateFlat? wrongChecksumCanary = none := by
  set_option maxRecDepth 10000 in
    decide

theorem trailing_byte_flat_rejected :
    readCertificateFlat? (encodeCertificate canaryCertificate ++ [0]) =
      none := by
  set_option maxRecDepth 10000 in
    decide

#print axioms readCertificate_of_sequential_components
#print axioms readCertificateFlat?_refines_canonical
#print axioms readCertificateFlat?_refines_decodeCertificate?
#print axioms canonical_canary_flat_accepts
#print axioms corrupt_magic_flat_rejected
#print axioms wrong_version_flat_rejected
#print axioms wrong_checksum_flat_rejected
#print axioms trailing_byte_flat_rejected

end Mettapedia.GSLT.LanguageDef.M0GCFlatCertificateLoaderCorrespondence
