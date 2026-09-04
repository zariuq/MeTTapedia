import Mettapedia.GSLT.LanguageDef.M0GCFlatBodyLoaderCorrespondence

/-!
# Fixed-offset header-parser refinement for M0GC

The bounded M0GC proof-certificate checker treats the first 104 bytes as a
packed header.  The canonical Lean wire decoder consumes those same fields
sequentially.  This module gives the header analogue of the flat-body theorem:
successful reads at the specified offsets reconstruct the canonical header
and leave the body beginning at byte 104.

Maturity boundary: this is a fully connected proof of concept for the binary
header layout.  It proves offset-parser refinement over lists of bytes.  It
does not yet prove that a C packed-structure cast is defined, that C scalar
loads implement these readers, or that a compiler preserves those operations.
It also does not yet connect the original-body checksum to re-encoding of the
decoded tables.
-/

namespace Mettapedia.GSLT.LanguageDef.M0GCFlatHeaderLoaderCorrespondence

open Mettapedia.GSLT.LanguageDef.CompiledPlanWireFormat
open Mettapedia.GSLT.LanguageDef.M0GCWireFormat
open Mettapedia.GSLT.LanguageDef.M0GCFlatBodyLoaderCorrespondence

/-! ## Offset reads -/

/-- Read a value at a fixed byte offset, intentionally discarding the local
reader suffix. -/
def readAt? (read : Reader alpha) (bytes : List UInt8)
    (offset : Nat) : Option alpha := do
  let (value, _) ← read (bytes.drop offset)
  some value

theorem readBytes_consumesExactly (count : Nat) :
    ConsumesExactly (readBytes count) count := by
  intro input value rest accepted
  unfold readBytes at accepted
  split at accepted
  next enough =>
    simp only [Option.some.injEq, Prod.mk.injEq] at accepted
    exact accepted.2.symm
  next short =>
    contradiction

/-- Any successful offset read by a fixed-width reader is the corresponding
successful cursor read with the exact calculated suffix. -/
theorem readAt?_refines_cursor
    {read : Reader alpha} {width : Nat}
    (fixedWidth : ConsumesExactly read width)
    (bytes : List UInt8) (offset : Nat) (value : alpha)
    (accepted : readAt? read bytes offset = some value) :
    read (bytes.drop offset) =
      some (value, bytes.drop (offset + width)) := by
  unfold readAt? at accepted
  cases readResult : read (bytes.drop offset) with
  | none =>
      simp [readResult] at accepted
  | some pair =>
      rcases pair with ⟨actual, suffix⟩
      simp [readResult, Option.bind] at accepted
      subst actual
      have suffixExact :=
        fixedWidth (bytes.drop offset) value suffix readResult
      rw [suffixExact, List.drop_drop]

/-- A four-byte `M0GC` prefix is exactly the canonical magic reader. -/
theorem readMagic_of_take_eq_magic
    (bytes : List UInt8)
    (magicExact : bytes.take 4 = M0GCWireFormat.magic) :
    M0GCWireFormat.readMagic bytes = some ((), bytes.drop 4) := by
  have decomposition := List.take_append_drop 4 bytes
  rw [magicExact] at decomposition
  rw [← decomposition]
  rfl

/-! ## Header layout evidence -/

/-- Successful fixed-offset reads for every M0GC header field. -/
structure FlatHeaderReads (bytes : List UInt8) (header : Header) : Prop where
  magicExact : bytes.take 4 = M0GCWireFormat.magic
  versionRead : readAt? readUInt16LE bytes 4 = some version
  flagsRead : readAt? readUInt16LE bytes 6 = some header.flags
  termCountRead : readAt? readUInt32LE bytes 8 = some header.termCount
  childCountRead : readAt? readUInt32LE bytes 12 = some header.childCount
  proofCountRead : readAt? readUInt32LE bytes 16 = some header.proofCount
  argumentCountRead :
    readAt? readUInt32LE bytes 20 = some header.argumentCount
  premiseCountRead :
    readAt? readUInt32LE bytes 24 = some header.premiseReferenceCount
  goalTermRead : readAt? readUInt32LE bytes 28 = some header.goalTerm
  profileDigestRead :
    readAt? (readBytes digestWidth) bytes 32 = some header.profileDigest
  sourceDigestRead :
    readAt? (readBytes digestWidth) bytes 64 = some header.sourceDigest
  bodyChecksumRead :
    readAt? readUInt64LE bytes 96 = some header.bodyChecksum

/-- Fixed-offset header reads refine the canonical sequential header decoder. -/
theorem FlatHeaderReads.refines_sequential
    {bytes : List UInt8} {header : Header}
    (reads : FlatHeaderReads bytes header) :
    readHeader bytes = some (header, bytes.drop 104) := by
  have magicSequential :=
    readMagic_of_take_eq_magic bytes reads.magicExact
  have versionSequential :
      readUInt16LE (bytes.drop 4) = some (version, bytes.drop 6) := by
    simpa using readAt?_refines_cursor readUInt16LE_consumesExactly
      bytes 4 version reads.versionRead
  have flagsSequential :
      readUInt16LE (bytes.drop 6) = some (header.flags, bytes.drop 8) := by
    simpa using readAt?_refines_cursor readUInt16LE_consumesExactly
      bytes 6 header.flags reads.flagsRead
  have termCountSequential :
      readUInt32LE (bytes.drop 8) =
        some (header.termCount, bytes.drop 12) := by
    simpa using readAt?_refines_cursor readUInt32LE_consumesExactly
      bytes 8 header.termCount reads.termCountRead
  have childCountSequential :
      readUInt32LE (bytes.drop 12) =
        some (header.childCount, bytes.drop 16) := by
    simpa using readAt?_refines_cursor readUInt32LE_consumesExactly
      bytes 12 header.childCount reads.childCountRead
  have proofCountSequential :
      readUInt32LE (bytes.drop 16) =
        some (header.proofCount, bytes.drop 20) := by
    simpa using readAt?_refines_cursor readUInt32LE_consumesExactly
      bytes 16 header.proofCount reads.proofCountRead
  have argumentCountSequential :
      readUInt32LE (bytes.drop 20) =
        some (header.argumentCount, bytes.drop 24) := by
    simpa using readAt?_refines_cursor readUInt32LE_consumesExactly
      bytes 20 header.argumentCount reads.argumentCountRead
  have premiseCountSequential :
      readUInt32LE (bytes.drop 24) =
        some (header.premiseReferenceCount, bytes.drop 28) := by
    simpa using readAt?_refines_cursor readUInt32LE_consumesExactly
      bytes 24 header.premiseReferenceCount reads.premiseCountRead
  have goalTermSequential :
      readUInt32LE (bytes.drop 28) =
        some (header.goalTerm, bytes.drop 32) := by
    simpa using readAt?_refines_cursor readUInt32LE_consumesExactly
      bytes 28 header.goalTerm reads.goalTermRead
  have profileDigestSequential :
      readBytes digestWidth (bytes.drop 32) =
        some (header.profileDigest, bytes.drop 64) := by
    simpa [digestWidth] using
      readAt?_refines_cursor (readBytes_consumesExactly digestWidth)
        bytes 32 header.profileDigest reads.profileDigestRead
  have sourceDigestSequential :
      readBytes digestWidth (bytes.drop 64) =
        some (header.sourceDigest, bytes.drop 96) := by
    simpa [digestWidth] using
      readAt?_refines_cursor (readBytes_consumesExactly digestWidth)
        bytes 64 header.sourceDigest reads.sourceDigestRead
  have bodyChecksumSequential :
      readUInt64LE (bytes.drop 96) =
        some (header.bodyChecksum, bytes.drop 104) := by
    simpa using readAt?_refines_cursor readUInt64LE_consumesExactly
      bytes 96 header.bodyChecksum reads.bodyChecksumRead
  simp [readHeader, magicSequential, versionSequential, flagsSequential,
    termCountSequential, childCountSequential, proofCountSequential,
    argumentCountSequential, premiseCountSequential, goalTermSequential,
    profileDigestSequential, sourceDigestSequential, bodyChecksumSequential,
    Option.bind]

/-! ## Executable fixed-offset header loading -/

/-- Executable fixed-offset header loader corresponding to the packed header
portion of the bounded C proof of concept. -/
def readHeaderFlat? (bytes : List UInt8) : Option Header :=
  if bytes.take 4 = M0GCWireFormat.magic then do
    let decodedVersion ← readAt? readUInt16LE bytes 4
    if decodedVersion = version then do
      let flags ← readAt? readUInt16LE bytes 6
      let termCount ← readAt? readUInt32LE bytes 8
      let childCount ← readAt? readUInt32LE bytes 12
      let proofCount ← readAt? readUInt32LE bytes 16
      let argumentCount ← readAt? readUInt32LE bytes 20
      let premiseReferenceCount ← readAt? readUInt32LE bytes 24
      let goalTerm ← readAt? readUInt32LE bytes 28
      let profileDigest ← readAt? (readBytes digestWidth) bytes 32
      let sourceDigest ← readAt? (readBytes digestWidth) bytes 64
      let bodyChecksum ← readAt? readUInt64LE bytes 96
      some
        { flags, termCount, childCount, proofCount, argumentCount,
          premiseReferenceCount, goalTerm, profileDigest, sourceDigest,
          bodyChecksum }
    else
      none
  else
    none

theorem readHeaderFlat?_eq_some_iff
    (bytes : List UInt8) (header : Header) :
    readHeaderFlat? bytes = some header ↔ FlatHeaderReads bytes header := by
  constructor
  · intro accepted
    unfold readHeaderFlat? at accepted
    by_cases magicExact : bytes.take 4 = M0GCWireFormat.magic
    · rw [if_pos magicExact] at accepted
      cases versionResult : readAt? readUInt16LE bytes 4 with
      | none =>
          rw [versionResult] at accepted
          simp at accepted
      | some decodedVersion =>
          rw [versionResult] at accepted
          by_cases versionExact : decodedVersion = version
          · simp [versionExact] at accepted
            subst decodedVersion
            cases flagsResult : readAt? readUInt16LE bytes 6 with
            | none =>
                rw [flagsResult] at accepted
                simp at accepted
            | some flags =>
                rw [flagsResult] at accepted
                cases termCountResult : readAt? readUInt32LE bytes 8 with
                | none =>
                    rw [termCountResult] at accepted
                    simp at accepted
                | some termCount =>
                    rw [termCountResult] at accepted
                    cases childCountResult :
                        readAt? readUInt32LE bytes 12 with
                    | none =>
                        rw [childCountResult] at accepted
                        simp at accepted
                    | some childCount =>
                        rw [childCountResult] at accepted
                        cases proofCountResult :
                            readAt? readUInt32LE bytes 16 with
                        | none =>
                            rw [proofCountResult] at accepted
                            simp at accepted
                        | some proofCount =>
                            rw [proofCountResult] at accepted
                            cases argumentCountResult :
                                readAt? readUInt32LE bytes 20 with
                            | none =>
                                rw [argumentCountResult] at accepted
                                simp at accepted
                            | some argumentCount =>
                                rw [argumentCountResult] at accepted
                                cases premiseCountResult :
                                    readAt? readUInt32LE bytes 24 with
                                | none =>
                                    rw [premiseCountResult] at accepted
                                    simp at accepted
                                | some premiseCount =>
                                    rw [premiseCountResult] at accepted
                                    cases goalTermResult :
                                        readAt? readUInt32LE bytes 28 with
                                    | none =>
                                        rw [goalTermResult] at accepted
                                        simp at accepted
                                    | some goalTerm =>
                                        rw [goalTermResult] at accepted
                                        cases profileDigestResult :
                                            readAt? (readBytes digestWidth)
                                              bytes 32 with
                                        | none =>
                                            rw [profileDigestResult] at accepted
                                            simp at accepted
                                        | some profileDigest =>
                                            rw [profileDigestResult] at accepted
                                            cases sourceDigestResult :
                                                readAt?
                                                  (readBytes digestWidth)
                                                  bytes 64 with
                                            | none =>
                                                rw [sourceDigestResult]
                                                  at accepted
                                                simp at accepted
                                            | some sourceDigest =>
                                                rw [sourceDigestResult]
                                                  at accepted
                                                cases bodyChecksumResult :
                                                    readAt? readUInt64LE bytes
                                                      96 with
                                                | none =>
                                                    rw [bodyChecksumResult]
                                                      at accepted
                                                    simp at accepted
                                                | some bodyChecksum =>
                                                    rw [bodyChecksumResult]
                                                      at accepted
                                                    simp at accepted
                                                    subst header
                                                    exact
                                                      { magicExact
                                                        versionRead :=
                                                          versionResult
                                                        flagsRead := flagsResult
                                                        termCountRead :=
                                                          termCountResult
                                                        childCountRead :=
                                                          childCountResult
                                                        proofCountRead :=
                                                          proofCountResult
                                                        argumentCountRead :=
                                                          argumentCountResult
                                                        premiseCountRead :=
                                                          premiseCountResult
                                                        goalTermRead :=
                                                          goalTermResult
                                                        profileDigestRead :=
                                                          profileDigestResult
                                                        sourceDigestRead :=
                                                          sourceDigestResult
                                                        bodyChecksumRead :=
                                                          bodyChecksumResult }
          · simp [versionExact] at accepted
    · rw [if_neg magicExact] at accepted
      simp at accepted
  · intro reads
    simp [readHeaderFlat?, reads.magicExact, reads.versionRead,
      reads.flagsRead, reads.termCountRead, reads.childCountRead,
      reads.proofCountRead, reads.argumentCountRead, reads.premiseCountRead,
      reads.goalTermRead, reads.profileDigestRead, reads.sourceDigestRead,
      reads.bodyChecksumRead, Option.bind]

/-- Successful executable fixed-offset loading refines canonical sequential
header decoding and identifies the exact body suffix. -/
theorem readHeaderFlat?_refines_sequential
    (bytes : List UInt8) (header : Header)
    (accepted : readHeaderFlat? bytes = some header) :
    readHeader bytes = some (header, bytes.drop 104) :=
  (readHeaderFlat?_eq_some_iff bytes header).mp accepted |>.refines_sequential

/-! ## Executable discriminators -/

def canaryHeader : Header :=
  headerOf canaryCertificate (fnv1a64 (encodeBody canaryCertificate))

/-- Positive discriminator: fixed-offset loading reconstructs the canonical
header of an encoded certificate. -/
theorem canary_flat_header_accepts :
    readHeaderFlat? (encodeCertificate canaryCertificate) =
      some canaryHeader := by
  set_option maxRecDepth 10000 in
    decide

/-- Negative discriminator: fixed-offset loading rejects a corrupted magic
prefix. -/
theorem corrupt_magic_flat_header_rejected :
    readHeaderFlat?
        (0 :: (encodeCertificate canaryCertificate).tail) = none := by
  decide

/-- Negative discriminator: fixed-offset loading rejects an unsupported
version. -/
theorem wrong_version_flat_header_rejected :
    readHeaderFlat? wrongVersionCanary = none := by
  decide

#print axioms readBytes_consumesExactly
#print axioms readAt?_refines_cursor
#print axioms FlatHeaderReads.refines_sequential
#print axioms readHeaderFlat?_eq_some_iff
#print axioms readHeaderFlat?_refines_sequential
#print axioms canary_flat_header_accepts
#print axioms corrupt_magic_flat_header_rejected
#print axioms wrong_version_flat_header_rejected

end Mettapedia.GSLT.LanguageDef.M0GCFlatHeaderLoaderCorrespondence
