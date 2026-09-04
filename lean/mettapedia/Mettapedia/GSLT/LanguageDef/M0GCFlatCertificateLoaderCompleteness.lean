import Mettapedia.GSLT.LanguageDef.M0GCFlatCertificateLoaderCorrespondence

/-!
# Producer completeness of the M0GC flat loader

The forward flat-loader refinement proves that flat acceptance cannot add a
certificate rejected by the canonical decoder.  This module proves the
complementary producer-facing direction: every encodable certificate emitted
by the canonical M0GC producer is accepted by the flat loader.

Together, the two results give exact agreement on the supported producer image.
They do not claim equivalence on arbitrary malformed byte strings.

Maturity boundary: this remains a fully connected proof of concept for a
byte-list loader algorithm.  It is not C source semantics, verified C,
compiler correctness, object-code correctness, or official MM0/MMB.
-/

namespace Mettapedia.GSLT.LanguageDef.M0GCFlatCertificateLoaderCompleteness

open Mettapedia.GSLT.LanguageDef.CompiledPlanWireFormat
open Mettapedia.GSLT.LanguageDef.M0GCWireFormat
open Mettapedia.GSLT.LanguageDef.M0GCFlatBodyLoaderCorrespondence
open Mettapedia.GSLT.LanguageDef.M0GCFlatHeaderLoaderCorrespondence
open Mettapedia.GSLT.LanguageDef.M0GCCanonicalBodyBytes
open Mettapedia.GSLT.LanguageDef.M0GCFlatCertificateLoaderCorrespondence

/-! ## Canonical encoded lists at aligned flat offsets -/

/-- A canonical list of fixed-width records can be read at the offset given by
an arbitrary preceding byte prefix. -/
theorem readManyAt_encodeList
    {read : Reader alpha} {encode : alpha → List UInt8} {width : Nat}
    (roundTrip : ∀ value rest,
      read (encode value ++ rest) = some (value, rest))
    (widthExact : ∀ value, (encode value).length = width) :
    ∀ (leadingBytes : List UInt8) (values : List alpha) (suffix : List UInt8),
      readManyAt read width
          (leadingBytes ++ values.flatMap encode ++ suffix)
          leadingBytes.length values.length =
        some values := by
  intro leadingBytes values
  induction values generalizing leadingBytes with
  | nil =>
      intro suffix
      simp [readManyAt]
  | cons value values inductionHypothesis =>
      intro suffix
      have headRead :
          read
              ((leadingBytes ++ encode value ++ values.flatMap encode ++ suffix).drop
                leadingBytes.length) =
            some (value, values.flatMap encode ++ suffix) := by
        simpa [List.append_assoc] using
          roundTrip value (values.flatMap encode ++ suffix)
      have tailRead :=
        inductionHypothesis (leadingBytes ++ encode value) suffix
      simp only [List.flatMap_cons]
      rw [readManyAt.eq_def]
      simp only [List.length_cons]
      simp only [List.append_assoc] at headRead ⊢
      rw [headRead]
      change
        (readManyAt read width
          (leadingBytes ++ (encode value ++ (values.flatMap encode ++ suffix)))
          (leadingBytes.length + width) values.length).bind
            (fun tail => some (value :: tail)) = some (value :: values)
      have leadingLength :
          (leadingBytes ++ encode value).length = leadingBytes.length + width := by
        simp [widthExact]
      have tailRead' :
          readManyAt read width
              (leadingBytes ++ (encode value ++ (values.flatMap encode ++ suffix)))
              (leadingBytes.length + width) values.length =
            some values := by
        simpa [List.append_assoc, leadingLength] using tailRead
      rw [tailRead']
      rfl

/-! ## Complete canonical bodies -/

/-- The decoded table lengths agree exactly with the counts governing their
physical layout. -/
structure MatchesCounts
    (tables : BodyTables) (counts : BodyCounts) : Prop where
  terms : tables.terms.length = counts.termCount
  children : tables.children.length = counts.childCount
  proofs : tables.proofs.length = counts.proofCount
  arguments : tables.arguments.length = counts.argumentCount
  premises : tables.premises.length = counts.premiseCount

theorem encodeUInt32LE_length (value : UInt32) :
    (encodeUInt32LE value).length = 4 := by
  rfl

theorem encodeUInt16LE_length (value : UInt16) :
    (encodeUInt16LE value).length = 2 := by
  rfl

theorem encodeUInt64LE_length (value : UInt64) :
    (encodeUInt64LE value).length = 8 := by
  rfl

theorem flatMap_encodeTermNode_length (values : List TermNode) :
    (values.flatMap encodeTermNode).length = 20 * values.length := by
  simp [encodeTermNode_length]
  omega

theorem flatMap_encodeUInt32LE_length (values : List UInt32) :
    (values.flatMap encodeUInt32LE).length = 4 * values.length := by
  simp [encodeUInt32LE_length]
  omega

theorem flatMap_encodeProofNode_length (values : List ProofNode) :
    (values.flatMap encodeProofNode).length = 32 * values.length := by
  simp [encodeProofNode_length]
  omega

/-- Counts matching all five decoded tables determine the exact packed body
length expected by the flat loader. -/
theorem encodeBodyTables_length_of_matches
    (tables : BodyTables) (counts : BodyCounts)
    (agreement : MatchesCounts tables counts) :
    (encodeBodyTables tables).length = bodyByteLength counts := by
  simp [encodeBodyTables, bodyByteLength, premiseTableOffset,
    argumentTableOffset, proofTableOffset, childTableOffset,
    encodeTermNode_length, encodeProofNode_length, encodeUInt32LE_length,
    agreement.terms, agreement.children, agreement.proofs,
    agreement.arguments, agreement.premises]
  omega

/-- Every canonical body whose table lengths agree with its governing counts
is accepted by the executable flat-table loader. -/
theorem readBodyFlat?_encodeBodyTables
    (tables : BodyTables) (counts : BodyCounts)
    (agreement : MatchesCounts tables counts) :
    readBodyFlat? counts (encodeBodyTables tables) = some tables := by
  let termBytes := tables.terms.flatMap encodeTermNode
  let childBytes := tables.children.flatMap encodeUInt32LE
  let proofBytes := tables.proofs.flatMap encodeProofNode
  let argumentBytes := tables.arguments.flatMap encodeUInt32LE
  let premiseBytes := tables.premises.flatMap encodeUInt32LE
  have bodyShape :
      encodeBodyTables tables =
        termBytes ++ childBytes ++ proofBytes ++ argumentBytes ++
          premiseBytes := by
    rfl
  have termBytesLength : termBytes.length = 20 * counts.termCount := by
    dsimp only [termBytes]
    rw [flatMap_encodeTermNode_length, agreement.terms]
  have childBytesLength : childBytes.length = 4 * counts.childCount := by
    dsimp only [childBytes]
    rw [flatMap_encodeUInt32LE_length, agreement.children]
  have proofBytesLength : proofBytes.length = 32 * counts.proofCount := by
    dsimp only [proofBytes]
    rw [flatMap_encodeProofNode_length, agreement.proofs]
  have argumentBytesLength :
      argumentBytes.length = 4 * counts.argumentCount := by
    dsimp only [argumentBytes]
    rw [flatMap_encodeUInt32LE_length, agreement.arguments]
  have termPrefixLength : termBytes.length = childTableOffset counts := by
    simpa only [childTableOffset] using termBytesLength
  have childPrefixLength :
      (termBytes ++ childBytes).length = proofTableOffset counts := by
    simp only [List.length_append, termBytesLength, childBytesLength,
      proofTableOffset, childTableOffset]
  have proofPrefixLength :
      (termBytes ++ childBytes ++ proofBytes).length =
        argumentTableOffset counts := by
    simp only [List.length_append, termBytesLength, childBytesLength,
      proofBytesLength, argumentTableOffset, proofTableOffset,
      childTableOffset]
  have argumentPrefixLength :
      (termBytes ++ childBytes ++ proofBytes ++ argumentBytes).length =
        premiseTableOffset counts := by
    simp only [List.length_append, termBytesLength, childBytesLength,
      proofBytesLength, argumentBytesLength, premiseTableOffset,
      argumentTableOffset, proofTableOffset, childTableOffset]
  have termsRead :
      readManyAt readTermNode 20 (encodeBodyTables tables)
          (termTableOffset counts) counts.termCount =
        some tables.terms := by
    have canonicalRead :=
      readManyAt_encodeList
        (alpha := TermNode) (read := readTermNode) (encode := encodeTermNode)
        readTermNode_encodeTermNode encodeTermNode_length
        [] tables.terms
        (childBytes ++ proofBytes ++ argumentBytes ++ premiseBytes)
    simpa [bodyShape, termTableOffset, agreement.terms, termBytes,
      List.append_assoc] using canonicalRead
  have childrenRead :
      readManyAt readUInt32LE 4 (encodeBodyTables tables)
          (childTableOffset counts) counts.childCount =
        some tables.children := by
    have canonicalRead :=
      readManyAt_encodeList
        (alpha := UInt32) (read := readUInt32LE) (encode := encodeUInt32LE)
        readUInt32LE_encodeUInt32LE encodeUInt32LE_length
        termBytes tables.children
        (proofBytes ++ argumentBytes ++ premiseBytes)
    simpa [bodyShape, termPrefixLength, agreement.children, childBytes,
      List.append_assoc] using canonicalRead
  have proofsRead :
      readManyAt readProofNode 32 (encodeBodyTables tables)
          (proofTableOffset counts) counts.proofCount =
        some tables.proofs := by
    have canonicalRead :=
      readManyAt_encodeList
        (alpha := ProofNode) (read := readProofNode) (encode := encodeProofNode)
        readProofNode_encodeProofNode encodeProofNode_length
        (termBytes ++ childBytes) tables.proofs
        (argumentBytes ++ premiseBytes)
    simpa [bodyShape, childPrefixLength, agreement.proofs, proofBytes,
      List.append_assoc] using canonicalRead
  have argumentsRead :
      readManyAt readUInt32LE 4 (encodeBodyTables tables)
          (argumentTableOffset counts) counts.argumentCount =
        some tables.arguments := by
    have canonicalRead :=
      readManyAt_encodeList
        (alpha := UInt32) (read := readUInt32LE) (encode := encodeUInt32LE)
        readUInt32LE_encodeUInt32LE encodeUInt32LE_length
        (termBytes ++ childBytes ++ proofBytes) tables.arguments
        premiseBytes
    rw [← proofPrefixLength]
    simpa [bodyShape, agreement.arguments, argumentBytes,
      List.append_assoc] using canonicalRead
  have premisesRead :
      readManyAt readUInt32LE 4 (encodeBodyTables tables)
          (premiseTableOffset counts) counts.premiseCount =
        some tables.premises := by
    have canonicalRead :=
      readManyAt_encodeList
        (alpha := UInt32) (read := readUInt32LE) (encode := encodeUInt32LE)
        readUInt32LE_encodeUInt32LE encodeUInt32LE_length
        (termBytes ++ childBytes ++ proofBytes ++ argumentBytes)
        tables.premises []
    rw [← argumentPrefixLength]
    simpa [bodyShape, agreement.premises, premiseBytes,
      List.append_assoc] using canonicalRead
  have bodyLength := encodeBodyTables_length_of_matches tables counts agreement
  simp [readBodyFlat?, bodyLength, termsRead, childrenRead, proofsRead,
    argumentsRead, premisesRead]

/-! ## Complete canonical headers and certificates -/

/-- A successful cursor read after an exact-length leading segment yields the
corresponding fixed-offset read. -/
theorem readAt?_of_split
    {read : Reader alpha} {bytes leadingBytes remainingBytes : List UInt8}
    {offset : Nat} {value : alpha} {rest : List UInt8}
    (decomposition : bytes = leadingBytes ++ remainingBytes)
    (leadingLength : leadingBytes.length = offset)
    (fieldRead : read remainingBytes = some (value, rest)) :
    readAt? read bytes offset = some value := by
  rw [decomposition, ← leadingLength]
  simp [readAt?, fieldRead]

/-- Fixed-offset header loading accepts every canonical header encoding and
ignores only the body bytes following the exact 104-byte header. -/
theorem readHeaderFlat?_encodeHeader_append
    (header : Header) (body : List UInt8)
    (profileWidth : header.profileDigest.length = digestWidth)
    (sourceWidth : header.sourceDigest.length = digestWidth) :
    readHeaderFlat? (encodeHeader header ++ body) = some header := by
  let p4 := M0GCWireFormat.magic
  let p6 := p4 ++ encodeUInt16LE version
  let p8 := p6 ++ encodeUInt16LE header.flags
  let p12 := p8 ++ encodeUInt32LE header.termCount
  let p16 := p12 ++ encodeUInt32LE header.childCount
  let p20 := p16 ++ encodeUInt32LE header.proofCount
  let p24 := p20 ++ encodeUInt32LE header.argumentCount
  let p28 := p24 ++ encodeUInt32LE header.premiseReferenceCount
  let p32 := p28 ++ encodeUInt32LE header.goalTerm
  let p64 := p32 ++ header.profileDigest
  let p96 := p64 ++ header.sourceDigest
  let s96 := encodeUInt64LE header.bodyChecksum ++ body
  let s64 := header.sourceDigest ++ s96
  let s32 := header.profileDigest ++ s64
  let s28 := encodeUInt32LE header.goalTerm ++ s32
  let s24 := encodeUInt32LE header.premiseReferenceCount ++ s28
  let s20 := encodeUInt32LE header.argumentCount ++ s24
  let s16 := encodeUInt32LE header.proofCount ++ s20
  let s12 := encodeUInt32LE header.childCount ++ s16
  let s8 := encodeUInt32LE header.termCount ++ s12
  let s6 := encodeUInt16LE header.flags ++ s8
  let s4 := encodeUInt16LE version ++ s6
  have split4 : encodeHeader header ++ body = p4 ++ s4 := by
    simp only [encodeHeader, p4, s4, s6, s8, s12, s16, s20, s24, s28,
      s32, s64, s96, List.append_assoc]
  have split6 : encodeHeader header ++ body = p6 ++ s6 := by
    calc
      encodeHeader header ++ body = p4 ++ s4 := split4
      _ = p6 ++ s6 := by simp [p6, s4, List.append_assoc]
  have split8 : encodeHeader header ++ body = p8 ++ s8 := by
    calc
      encodeHeader header ++ body = p6 ++ s6 := split6
      _ = p8 ++ s8 := by simp [p8, s6, List.append_assoc]
  have split12 : encodeHeader header ++ body = p12 ++ s12 := by
    calc
      encodeHeader header ++ body = p8 ++ s8 := split8
      _ = p12 ++ s12 := by simp [p12, s8, List.append_assoc]
  have split16 : encodeHeader header ++ body = p16 ++ s16 := by
    calc
      encodeHeader header ++ body = p12 ++ s12 := split12
      _ = p16 ++ s16 := by simp [p16, s12, List.append_assoc]
  have split20 : encodeHeader header ++ body = p20 ++ s20 := by
    calc
      encodeHeader header ++ body = p16 ++ s16 := split16
      _ = p20 ++ s20 := by simp [p20, s16, List.append_assoc]
  have split24 : encodeHeader header ++ body = p24 ++ s24 := by
    calc
      encodeHeader header ++ body = p20 ++ s20 := split20
      _ = p24 ++ s24 := by simp [p24, s20, List.append_assoc]
  have split28 : encodeHeader header ++ body = p28 ++ s28 := by
    calc
      encodeHeader header ++ body = p24 ++ s24 := split24
      _ = p28 ++ s28 := by simp [p28, s24, List.append_assoc]
  have split32 : encodeHeader header ++ body = p32 ++ s32 := by
    calc
      encodeHeader header ++ body = p28 ++ s28 := split28
      _ = p32 ++ s32 := by simp [p32, s28, List.append_assoc]
  have split64 : encodeHeader header ++ body = p64 ++ s64 := by
    calc
      encodeHeader header ++ body = p32 ++ s32 := split32
      _ = p64 ++ s64 := by simp [p64, s32, List.append_assoc]
  have split96 : encodeHeader header ++ body = p96 ++ s96 := by
    calc
      encodeHeader header ++ body = p64 ++ s64 := split64
      _ = p96 ++ s96 := by simp [p96, s64, List.append_assoc]
  have p4Length : p4.length = 4 := by
    simp [p4, M0GCWireFormat.magic]
  have p6Length : p6.length = 6 := by
    simp [p6, p4Length, encodeUInt16LE_length]
  have p8Length : p8.length = 8 := by
    simp [p8, p6Length, encodeUInt16LE_length]
  have p12Length : p12.length = 12 := by
    simp [p12, p8Length, encodeUInt32LE_length]
  have p16Length : p16.length = 16 := by
    simp [p16, p12Length, encodeUInt32LE_length]
  have p20Length : p20.length = 20 := by
    simp [p20, p16Length, encodeUInt32LE_length]
  have p24Length : p24.length = 24 := by
    simp [p24, p20Length, encodeUInt32LE_length]
  have p28Length : p28.length = 28 := by
    simp [p28, p24Length, encodeUInt32LE_length]
  have p32Length : p32.length = 32 := by
    simp [p32, p28Length, encodeUInt32LE_length]
  have p64Length : p64.length = 64 := by
    simp [p64, p32Length, profileWidth, digestWidth]
  have p96Length : p96.length = 96 := by
    simp [p96, p64Length, sourceWidth, digestWidth]
  have versionRead : readUInt16LE s4 = some (version, s6) := by
    simp [s4]
  have flagsRead : readUInt16LE s6 = some (header.flags, s8) := by
    simp [s6]
  have termCountRead :
      readUInt32LE s8 = some (header.termCount, s12) := by
    simp [s8]
  have childCountRead :
      readUInt32LE s12 = some (header.childCount, s16) := by
    simp [s12]
  have proofCountRead :
      readUInt32LE s16 = some (header.proofCount, s20) := by
    simp [s16]
  have argumentCountRead :
      readUInt32LE s20 = some (header.argumentCount, s24) := by
    simp [s20]
  have premiseCountRead :
      readUInt32LE s24 = some (header.premiseReferenceCount, s28) := by
    simp [s24]
  have goalTermRead :
      readUInt32LE s28 = some (header.goalTerm, s32) := by
    simp [s28]
  have profileDigestRead :
      readBytes digestWidth s32 = some (header.profileDigest, s64) := by
    simpa [s32] using
      readBytes_append header.profileDigest s64 profileWidth
  have sourceDigestRead :
      readBytes digestWidth s64 = some (header.sourceDigest, s96) := by
    simpa [s64] using
      readBytes_append header.sourceDigest s96 sourceWidth
  have bodyChecksumRead :
      readUInt64LE s96 = some (header.bodyChecksum, body) := by
    simp [s96]
  apply (readHeaderFlat?_eq_some_iff _ _).2
  exact
    { magicExact := by
        rw [split4]
        simp [p4, M0GCWireFormat.magic]
      versionRead := readAt?_of_split split4 p4Length versionRead
      flagsRead := readAt?_of_split split6 p6Length flagsRead
      termCountRead := readAt?_of_split split8 p8Length termCountRead
      childCountRead := readAt?_of_split split12 p12Length childCountRead
      proofCountRead := readAt?_of_split split16 p16Length proofCountRead
      argumentCountRead :=
        readAt?_of_split split20 p20Length argumentCountRead
      premiseCountRead :=
        readAt?_of_split split24 p24Length premiseCountRead
      goalTermRead := readAt?_of_split split28 p28Length goalTermRead
      profileDigestRead :=
        readAt?_of_split split32 p32Length profileDigestRead
      sourceDigestRead :=
        readAt?_of_split split64 p64Length sourceDigestRead
      bodyChecksumRead :=
        readAt?_of_split split96 p96Length bodyChecksumRead }

/-- Forget the header fields of a certificate and expose its five physical
body tables. -/
def bodyTablesOfCertificate (certificate : Certificate) : BodyTables :=
  { terms := certificate.terms
    children := certificate.children
    proofs := certificate.proofs
    arguments := certificate.arguments
    premises := certificate.premises }

@[simp] theorem encodeBodyTables_bodyTablesOfCertificate
    (certificate : Certificate) :
    encodeBodyTables (bodyTablesOfCertificate certificate) =
      encodeBody certificate :=
  rfl

@[simp] theorem certificateOfTables_headerOf_bodyTables
    (certificate : Certificate) (checksum : UInt64) :
    certificateOfTables (headerOf certificate checksum)
        (bodyTablesOfCertificate certificate) =
      certificate :=
  rfl

/-- Encodability makes each modular `UInt32.ofNat` count in the header exact,
so the canonical body tables match the physical offsets selected by that
header. -/
theorem bodyTablesOfCertificate_matches_header
    (certificate : Certificate) (checksum : UInt64)
    (encodable : certificate.Encodable) :
    MatchesCounts (bodyTablesOfCertificate certificate)
      (BodyCounts.ofHeader (headerOf certificate checksum)) := by
  rcases encodable with
    ⟨termsFit, childrenFit, proofsFit, argumentsFit, premisesFit,
      _profileWidth, _sourceWidth⟩
  exact
    { terms := by
        simp [bodyTablesOfCertificate, BodyCounts.ofHeader, headerOf,
          Nat.mod_eq_of_lt termsFit]
      children := by
        simp [bodyTablesOfCertificate, BodyCounts.ofHeader, headerOf,
          Nat.mod_eq_of_lt childrenFit]
      proofs := by
        simp [bodyTablesOfCertificate, BodyCounts.ofHeader, headerOf,
          Nat.mod_eq_of_lt proofsFit]
      arguments := by
        simp [bodyTablesOfCertificate, BodyCounts.ofHeader, headerOf,
          Nat.mod_eq_of_lt argumentsFit]
      premises := by
        simp [bodyTablesOfCertificate, BodyCounts.ofHeader, headerOf,
          Nat.mod_eq_of_lt premisesFit] }

/-- Producer completeness: every certificate satisfying the canonical M0GC
encoding bounds is accepted by the flat loader after canonical encoding. -/
theorem readCertificateFlat?_encodeCertificate
    (certificate : Certificate) (encodable : certificate.Encodable) :
    readCertificateFlat? (encodeCertificate certificate) =
      some certificate := by
  rcases encodable with
    ⟨termsFit, childrenFit, proofsFit, argumentsFit, premisesFit,
      profileWidth, sourceWidth⟩
  have encodable' : certificate.Encodable :=
    ⟨termsFit, childrenFit, proofsFit, argumentsFit, premisesFit,
      profileWidth, sourceWidth⟩
  let checksum := fnv1a64 (encodeBody certificate)
  let header := headerOf certificate checksum
  let tables := bodyTablesOfCertificate certificate
  have headerRead :
      readHeaderFlat? (encodeCertificate certificate) = some header := by
    have canonicalHeaderRead :=
      readHeaderFlat?_encodeHeader_append header (encodeBody certificate)
        profileWidth sourceWidth
    simpa [encodeCertificate, header, checksum] using canonicalHeaderRead
  have headerLength : (encodeHeader header).length = 104 := by
    exact encodeHeader_length header profileWidth sourceWidth
  have bodyDrop :
      (encodeCertificate certificate).drop 104 = encodeBody certificate := by
    simp only [encodeCertificate]
    change
      (encodeHeader header ++ encodeBody certificate).drop 104 =
        encodeBody certificate
    rw [← headerLength]
    simp
  have countAgreement :
      MatchesCounts tables (BodyCounts.ofHeader header) := by
    exact bodyTablesOfCertificate_matches_header certificate checksum encodable'
  have bodyRead :
      readBodyFlat? (BodyCounts.ofHeader header) (encodeBody certificate) =
        some tables := by
    have canonicalBodyRead :=
      readBodyFlat?_encodeBodyTables tables (BodyCounts.ofHeader header)
        countAgreement
    simpa [tables] using canonicalBodyRead
  unfold readCertificateFlat?
  rw [headerRead, bodyDrop]
  change
    (readBodyFlat? (BodyCounts.ofHeader header)
      (encodeBody certificate)).bind
        (fun loadedTables =>
          if header.bodyChecksum = fnv1a64 (encodeBody certificate) then
            some (certificateOfTables header loadedTables)
          else none) =
      some certificate
  rw [bodyRead]
  simp [header, checksum, tables, headerOf, bodyTablesOfCertificate,
    certificateOfTables]

/-- On the canonical producer image, the flat loader and public canonical
decoder return exactly the same certificate. -/
theorem flat_eq_canonical_on_encodeCertificate
    (certificate : Certificate) (encodable : certificate.Encodable) :
    readCertificateFlat? (encodeCertificate certificate) =
      decodeCertificate? (encodeCertificate certificate) := by
  rw [readCertificateFlat?_encodeCertificate certificate encodable,
    decodeCertificate?_encodeCertificate certificate encodable]

/-! ## Positive and negative boundary discriminators -/

theorem canary_flat_accepts_from_producer_completeness :
    readCertificateFlat? (encodeCertificate canaryCertificate) =
      some canaryCertificate :=
  readCertificateFlat?_encodeCertificate canaryCertificate
    canaryCertificate_encodable

/-- A producer value with a short profile identity violates the exact-width
boundary required by both canonical and flat framing. -/
def shortProfileDigestCertificate : Certificate :=
  { canaryCertificate with profileDigest := [] }

theorem shortProfileDigestCertificate_not_encodable :
    ¬ shortProfileDigestCertificate.Encodable := by
  simp [shortProfileDigestCertificate, Certificate.Encodable,
    canaryCertificate, digestWidth]

theorem short_profile_digest_flat_rejected :
    readCertificateFlat?
        (encodeCertificate shortProfileDigestCertificate) = none := by
  set_option maxRecDepth 10000 in
    decide

#print axioms readManyAt_encodeList
#print axioms encodeBodyTables_length_of_matches
#print axioms readBodyFlat?_encodeBodyTables
#print axioms readAt?_of_split
#print axioms readHeaderFlat?_encodeHeader_append
#print axioms bodyTablesOfCertificate_matches_header
#print axioms readCertificateFlat?_encodeCertificate
#print axioms flat_eq_canonical_on_encodeCertificate
#print axioms short_profile_digest_flat_rejected

end Mettapedia.GSLT.LanguageDef.M0GCFlatCertificateLoaderCompleteness
