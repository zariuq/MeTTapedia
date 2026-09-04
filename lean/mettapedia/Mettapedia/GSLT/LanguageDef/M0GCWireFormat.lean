import Mettapedia.GSLT.LanguageDef.CompiledPlanWireFormat

/-!
# Exact M0GC version-one wire format

M0GC is the compact proof-certificate carrier used by the bounded MM0/GSLT
experiment.  It is inspired by MMB's flat replay discipline, but it is not the
official MMB format.  This module specifies only its physical framing:

* packed little-endian scalar fields;
* chronological term, child, proof, argument, and premise-reference tables;
* two exact 32-byte profile/source identities;
* FNV-1a-64 authentication of the complete body; and
* rejection of wrong magic, version, checksum, truncation, or trailing bytes.

Semantic admission is deliberately separate.  In particular, decoding does
not yet establish term topology, symbol arities, proof chronology, rule
identity, substitution correctness, or goal replay.  Those are obligations of
the M0GC structural replay layer, just as `CompiledPlanAdmission` is separate
from `CompiledPlanWireFormat`.
-/

namespace Mettapedia.GSLT.LanguageDef.M0GCWireFormat

open Mettapedia.GSLT.LanguageDef.CompiledPlanWireFormat

/-! ## Missing fixed-width primitives -/

def encodeUInt16LE (value : UInt16) : List UInt8 :=
  let bits := value.toBitVec
  [ UInt8.ofBitVec (bits.extractLsb' 0 8)
  , UInt8.ofBitVec (bits.extractLsb' 8 8) ]

def readUInt16LE : Reader UInt16
  | byte0 :: byte1 :: rest =>
      some (UInt16.ofBitVec (byte1.toBitVec ++ byte0.toBitVec), rest)
  | _ => none

@[simp] theorem readUInt16LE_encodeUInt16LE
    (value : UInt16) (rest : List UInt8) :
    readUInt16LE (encodeUInt16LE value ++ rest) = some (value, rest) := by
  simp only [encodeUInt16LE, List.cons_append, List.nil_append, readUInt16LE]
  congr 2
  apply UInt16.eq_iff_toBitVec_eq.mpr
  simp only
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb'
        (by decide : 8 = 0 + 8)]
  exact BitVec.extractLsb'_eq_self

def encodeUInt64LE (value : UInt64) : List UInt8 :=
  let bits := value.toBitVec
  [ UInt8.ofBitVec (bits.extractLsb' 0 8)
  , UInt8.ofBitVec (bits.extractLsb' 8 8)
  , UInt8.ofBitVec (bits.extractLsb' 16 8)
  , UInt8.ofBitVec (bits.extractLsb' 24 8)
  , UInt8.ofBitVec (bits.extractLsb' 32 8)
  , UInt8.ofBitVec (bits.extractLsb' 40 8)
  , UInt8.ofBitVec (bits.extractLsb' 48 8)
  , UInt8.ofBitVec (bits.extractLsb' 56 8) ]

def readUInt64LE : Reader UInt64
  | byte0 :: byte1 :: byte2 :: byte3 ::
      byte4 :: byte5 :: byte6 :: byte7 :: rest =>
      some
        (UInt64.ofBitVec
          (byte7.toBitVec ++ byte6.toBitVec ++
            byte5.toBitVec ++ byte4.toBitVec ++
            byte3.toBitVec ++ byte2.toBitVec ++
            byte1.toBitVec ++ byte0.toBitVec), rest)
  | _ => none

@[simp] theorem readUInt64LE_encodeUInt64LE
    (value : UInt64) (rest : List UInt8) :
    readUInt64LE (encodeUInt64LE value ++ rest) = some (value, rest) := by
  simp only [encodeUInt64LE, List.cons_append, List.nil_append, readUInt64LE]
  congr 2
  apply UInt64.eq_iff_toBitVec_eq.mpr
  simp only
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb'
        (by decide : 56 = 48 + 8)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb'
        (by decide : 48 = 40 + 8)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb'
        (by decide : 40 = 32 + 8)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb'
        (by decide : 32 = 24 + 8)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb'
        (by decide : 24 = 16 + 8)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb'
        (by decide : 16 = 8 + 8)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb'
        (by decide : 8 = 0 + 8)]
  exact BitVec.extractLsb'_eq_self

/-! ## Fixed byte blocks and FNV-1a -/

def readBytes (count : Nat) : Reader (List UInt8) := fun input =>
  if count <= input.length then
    some (input.take count, input.drop count)
  else
    none

theorem readBytes_append
    (bytes rest : List UInt8) (lengthExact : bytes.length = count) :
    readBytes count (bytes ++ rest) = some (bytes, rest) := by
  subst count
  simp [readBytes]

def fnv64Offset : UInt64 := 14695981039346656037

def fnv64Prime : UInt64 := 1099511628211

def fnv1a64 (bytes : List UInt8) : UInt64 :=
  bytes.foldl
    (fun hash byte => (hash ^^^ UInt64.ofNat byte.toNat) * fnv64Prime)
    fnv64Offset

/-! ## Packed records -/

/-- One 20-byte M0GC ground-term heap record. -/
structure TermNode where
  symbol : UInt16
  arity : UInt16
  childStart : UInt32
  reserved : UInt32
  termHash : UInt64
deriving DecidableEq, Repr

/-- One 32-byte chronological M0GC proof record. -/
structure ProofNode where
  opcode : UInt16
  rule : UInt16
  argumentCount : UInt16
  premiseCount : UInt16
  argumentStart : UInt32
  premiseStart : UInt32
  resultTerm : UInt32
  reserved : UInt32
  ruleFingerprint : UInt64
deriving DecidableEq, Repr

def encodeTermNode (node : TermNode) : List UInt8 :=
  encodeUInt16LE node.symbol ++
    encodeUInt16LE node.arity ++
    encodeUInt32LE node.childStart ++
    encodeUInt32LE node.reserved ++
    encodeUInt64LE node.termHash

def readTermNode : Reader TermNode := fun input => do
  let (symbol, rest1) <- readUInt16LE input
  let (arity, rest2) <- readUInt16LE rest1
  let (childStart, rest3) <- readUInt32LE rest2
  let (reserved, rest4) <- readUInt32LE rest3
  let (termHash, rest) <- readUInt64LE rest4
  some ({ symbol, arity, childStart, reserved, termHash }, rest)

@[simp] theorem readTermNode_encodeTermNode
    (node : TermNode) (rest : List UInt8) :
    readTermNode (encodeTermNode node ++ rest) = some (node, rest) := by
  simp [encodeTermNode, readTermNode]

def encodeProofNode (node : ProofNode) : List UInt8 :=
  encodeUInt16LE node.opcode ++
    encodeUInt16LE node.rule ++
    encodeUInt16LE node.argumentCount ++
    encodeUInt16LE node.premiseCount ++
    encodeUInt32LE node.argumentStart ++
    encodeUInt32LE node.premiseStart ++
    encodeUInt32LE node.resultTerm ++
    encodeUInt32LE node.reserved ++
    encodeUInt64LE node.ruleFingerprint

def readProofNode : Reader ProofNode := fun input => do
  let (opcode, rest1) <- readUInt16LE input
  let (rule, rest2) <- readUInt16LE rest1
  let (argumentCount, rest3) <- readUInt16LE rest2
  let (premiseCount, rest4) <- readUInt16LE rest3
  let (argumentStart, rest5) <- readUInt32LE rest4
  let (premiseStart, rest6) <- readUInt32LE rest5
  let (resultTerm, rest7) <- readUInt32LE rest6
  let (reserved, rest8) <- readUInt32LE rest7
  let (ruleFingerprint, rest) <- readUInt64LE rest8
  some
    ({ opcode, rule, argumentCount, premiseCount, argumentStart,
       premiseStart, resultTerm, reserved, ruleFingerprint }, rest)

@[simp] theorem readProofNode_encodeProofNode
    (node : ProofNode) (rest : List UInt8) :
    readProofNode (encodeProofNode node ++ rest) = some (node, rest) := by
  simp [encodeProofNode, readProofNode]

theorem encodeTermNode_length (node : TermNode) :
    (encodeTermNode node).length = 20 := by
  simp [encodeTermNode, encodeUInt16LE, encodeUInt32LE, encodeUInt64LE]

theorem encodeProofNode_length (node : ProofNode) :
    (encodeProofNode node).length = 32 := by
  simp [encodeProofNode, encodeUInt16LE, encodeUInt32LE, encodeUInt64LE]

/-! ## Complete version-one certificates -/

def magic : List UInt8 := [77, 48, 71, 67]

def version : UInt16 := 1

def digestWidth : Nat := 32

def readMagic : Reader Unit
  | 77 :: 48 :: 71 :: 67 :: rest => some ((), rest)
  | _ => none

structure Header where
  flags : UInt16
  termCount : UInt32
  childCount : UInt32
  proofCount : UInt32
  argumentCount : UInt32
  premiseReferenceCount : UInt32
  goalTerm : UInt32
  profileDigest : List UInt8
  sourceDigest : List UInt8
  bodyChecksum : UInt64
deriving DecidableEq, Repr

structure Certificate where
  flags : UInt16
  terms : List TermNode
  children : List UInt32
  proofs : List ProofNode
  arguments : List UInt32
  premises : List UInt32
  goalTerm : UInt32
  profileDigest : List UInt8
  sourceDigest : List UInt8
deriving DecidableEq, Repr

def Certificate.Encodable (certificate : Certificate) : Prop :=
  certificate.terms.length < UInt32.size ∧
    certificate.children.length < UInt32.size ∧
    certificate.proofs.length < UInt32.size ∧
    certificate.arguments.length < UInt32.size ∧
    certificate.premises.length < UInt32.size ∧
    certificate.profileDigest.length = digestWidth ∧
    certificate.sourceDigest.length = digestWidth

def encodeBody (certificate : Certificate) : List UInt8 :=
  certificate.terms.flatMap encodeTermNode ++
    certificate.children.flatMap encodeUInt32LE ++
    certificate.proofs.flatMap encodeProofNode ++
    certificate.arguments.flatMap encodeUInt32LE ++
    certificate.premises.flatMap encodeUInt32LE

def headerOf (certificate : Certificate) (checksum : UInt64) : Header :=
  { flags := certificate.flags
    termCount := UInt32.ofNat certificate.terms.length
    childCount := UInt32.ofNat certificate.children.length
    proofCount := UInt32.ofNat certificate.proofs.length
    argumentCount := UInt32.ofNat certificate.arguments.length
    premiseReferenceCount := UInt32.ofNat certificate.premises.length
    goalTerm := certificate.goalTerm
    profileDigest := certificate.profileDigest
    sourceDigest := certificate.sourceDigest
    bodyChecksum := checksum }

def encodeHeader (header : Header) : List UInt8 :=
  magic ++ encodeUInt16LE version ++ encodeUInt16LE header.flags ++
    encodeUInt32LE header.termCount ++
    encodeUInt32LE header.childCount ++
    encodeUInt32LE header.proofCount ++
    encodeUInt32LE header.argumentCount ++
    encodeUInt32LE header.premiseReferenceCount ++
    encodeUInt32LE header.goalTerm ++
    header.profileDigest ++ header.sourceDigest ++
    encodeUInt64LE header.bodyChecksum

def encodeFramedCertificate
    (certificate : Certificate) (checksum : UInt64) : List UInt8 :=
  encodeHeader (headerOf certificate checksum) ++ encodeBody certificate

def encodeCertificate (certificate : Certificate) : List UInt8 :=
  let body := encodeBody certificate
  encodeHeader (headerOf certificate (fnv1a64 body)) ++ body

def readHeader : Reader Header := fun input => do
  let (_, rest0) <- readMagic input
  let (decodedVersion, rest1) <- readUInt16LE rest0
  if decodedVersion != version then none else
  let (flags, rest2) <- readUInt16LE rest1
  let (termCount, rest3) <- readUInt32LE rest2
  let (childCount, rest4) <- readUInt32LE rest3
  let (proofCount, rest5) <- readUInt32LE rest4
  let (argumentCount, rest6) <- readUInt32LE rest5
  let (premiseReferenceCount, rest7) <- readUInt32LE rest6
  let (goalTerm, rest8) <- readUInt32LE rest7
  let (profileDigest, rest9) <- readBytes digestWidth rest8
  let (sourceDigest, rest10) <- readBytes digestWidth rest9
  let (bodyChecksum, rest) <- readUInt64LE rest10
  some
    ({ flags, termCount, childCount, proofCount, argumentCount,
       premiseReferenceCount, goalTerm, profileDigest, sourceDigest,
       bodyChecksum }, rest)

def readCertificate : Reader Certificate := fun input => do
  let (header, rest0) <- readHeader input
  let (terms, rest1) <- readMany readTermNode header.termCount.toNat rest0
  let (children, rest2) <- readMany readUInt32LE header.childCount.toNat rest1
  let (proofs, rest3) <- readMany readProofNode header.proofCount.toNat rest2
  let (arguments, rest4) <-
    readMany readUInt32LE header.argumentCount.toNat rest3
  let (premises, rest) <-
    readMany readUInt32LE header.premiseReferenceCount.toNat rest4
  let certificate : Certificate :=
    { flags := header.flags
      terms
      children
      proofs
      arguments
      premises
      goalTerm := header.goalTerm
      profileDigest := header.profileDigest
      sourceDigest := header.sourceDigest }
  if header.bodyChecksum = fnv1a64 (encodeBody certificate) then
    some (certificate, rest)
  else
    none

def decodeCertificate? (bytes : List UInt8) : Option Certificate :=
  match readCertificate bytes with
  | some (certificate, []) => some certificate
  | _ => none

/-! ## Exact producer/consumer round trip -/

theorem readHeader_encodeHeader
    (header : Header) (rest : List UInt8)
    (profileWidth : header.profileDigest.length = digestWidth)
    (sourceWidth : header.sourceDigest.length = digestWidth) :
    readHeader (encodeHeader header ++ rest) = some (header, rest) := by
  simp [encodeHeader, readHeader, magic, readMagic, version,
    readBytes_append, profileWidth, sourceWidth]

theorem readCertificate_encodeFramedCertificate
    (certificate : Certificate) (rest : List UInt8)
    (encodable : certificate.Encodable) :
    readCertificate
        (encodeFramedCertificate certificate
          (fnv1a64 (encodeBody certificate)) ++ rest) =
      some (certificate, rest) := by
  rcases encodable with
    ⟨termsFit, childrenFit, proofsFit, argumentsFit, premisesFit,
      profileWidth, sourceWidth⟩
  have termsExact :
      (UInt32.ofNat certificate.terms.length).toNat =
        certificate.terms.length := by
    simp [Nat.mod_eq_of_lt termsFit]
  have childrenExact :
      (UInt32.ofNat certificate.children.length).toNat =
        certificate.children.length := by
    simp [Nat.mod_eq_of_lt childrenFit]
  have proofsExact :
      (UInt32.ofNat certificate.proofs.length).toNat =
        certificate.proofs.length := by
    simp [Nat.mod_eq_of_lt proofsFit]
  have argumentsExact :
      (UInt32.ofNat certificate.arguments.length).toNat =
        certificate.arguments.length := by
    simp [Nat.mod_eq_of_lt argumentsFit]
  have premisesExact :
      (UInt32.ofNat certificate.premises.length).toNat =
        certificate.premises.length := by
    simp [Nat.mod_eq_of_lt premisesFit]
  have readTerms := readMany_encodeList
    readTermNode encodeTermNode readTermNode_encodeTermNode
    certificate.terms
    (certificate.children.flatMap encodeUInt32LE ++
      (certificate.proofs.flatMap encodeProofNode ++
        (certificate.arguments.flatMap encodeUInt32LE ++
          (certificate.premises.flatMap encodeUInt32LE ++ rest))))
  have readChildren := readMany_encodeList
    readUInt32LE encodeUInt32LE readUInt32LE_encodeUInt32LE
    certificate.children
    (certificate.proofs.flatMap encodeProofNode ++
      (certificate.arguments.flatMap encodeUInt32LE ++
        (certificate.premises.flatMap encodeUInt32LE ++ rest)))
  have readProofs := readMany_encodeList
    readProofNode encodeProofNode readProofNode_encodeProofNode
    certificate.proofs
    (certificate.arguments.flatMap encodeUInt32LE ++
      (certificate.premises.flatMap encodeUInt32LE ++ rest))
  have readArguments := readMany_encodeList
    readUInt32LE encodeUInt32LE readUInt32LE_encodeUInt32LE
    certificate.arguments
    (certificate.premises.flatMap encodeUInt32LE ++ rest)
  have readPremises := readMany_encodeList
    readUInt32LE encodeUInt32LE readUInt32LE_encodeUInt32LE
    certificate.premises rest
  have headerRead := readHeader_encodeHeader
    (headerOf certificate (fnv1a64 (encodeBody certificate)))
    (encodeBody certificate ++ rest) profileWidth sourceWidth
  simp only [encodeFramedCertificate, List.append_assoc]
  unfold readCertificate
  rw [headerRead]
  simp [headerOf, termsExact, childrenExact, proofsExact, argumentsExact,
    premisesExact, encodeBody, readTerms, readChildren, readProofs,
    readArguments, readPremises]

@[simp] theorem decodeCertificate?_encodeCertificate
    (certificate : Certificate) (encodable : certificate.Encodable) :
    decodeCertificate? (encodeCertificate certificate) = some certificate := by
  have readExact :
      readCertificate (encodeCertificate certificate) =
        some (certificate, []) := by
    simpa [encodeCertificate, encodeFramedCertificate] using
      readCertificate_encodeFramedCertificate certificate [] encodable
  unfold decodeCertificate?
  rw [readExact]

theorem encodeHeader_length
    (header : Header)
    (profileWidth : header.profileDigest.length = digestWidth)
    (sourceWidth : header.sourceDigest.length = digestWidth) :
    (encodeHeader header).length = 104 := by
  simp [encodeHeader, magic, encodeUInt16LE, encodeUInt32LE,
    encodeUInt64LE, profileWidth, sourceWidth, digestWidth]

/-! ## Positive and negative framing canaries -/

def canaryTerm : TermNode :=
  { symbol := 0
    arity := 0
    childStart := 0
    reserved := 0
    termHash := 0 }

def canaryProof : ProofNode :=
  { opcode := 1
    rule := 0
    argumentCount := 0
    premiseCount := 0
    argumentStart := 0
    premiseStart := 0
    resultTerm := 0
    reserved := 0
    ruleFingerprint := 0 }

def canaryCertificate : Certificate :=
  { flags := 0
    terms := [canaryTerm]
    children := []
    proofs := [canaryProof]
    arguments := []
    premises := []
    goalTerm := 0
    profileDigest := List.replicate digestWidth 0
    sourceDigest := List.replicate digestWidth 0 }

theorem canaryCertificate_encodable : canaryCertificate.Encodable := by
  simp [Certificate.Encodable, canaryCertificate, digestWidth]
  decide

theorem canary_round_trip :
    decodeCertificate? (encodeCertificate canaryCertificate) =
      some canaryCertificate :=
  decodeCertificate?_encodeCertificate canaryCertificate
    canaryCertificate_encodable

theorem corrupt_magic_rejected :
    decodeCertificate? (0 :: (encodeCertificate canaryCertificate).tail) =
      none := by
  decide

def wrongVersionCanary : List UInt8 :=
  magic ++ encodeUInt16LE 2 ++ (encodeCertificate canaryCertificate).drop 6

theorem wrong_version_rejected :
    decodeCertificate? wrongVersionCanary = none := by
  decide

def wrongChecksumCanary : List UInt8 :=
  encodeFramedCertificate canaryCertificate
    (fnv1a64 (encodeBody canaryCertificate) + 1)

theorem wrong_checksum_rejected :
    decodeCertificate? wrongChecksumCanary = none := by
  set_option maxRecDepth 10000 in
    decide

theorem trailing_byte_rejected :
    decodeCertificate? (encodeCertificate canaryCertificate ++ [0]) = none := by
  set_option maxRecDepth 10000 in
    decide

#print axioms readUInt16LE_encodeUInt16LE
#print axioms readUInt64LE_encodeUInt64LE
#print axioms readCertificate_encodeFramedCertificate
#print axioms decodeCertificate?_encodeCertificate
#print axioms corrupt_magic_rejected
#print axioms wrong_version_rejected
#print axioms wrong_checksum_rejected
#print axioms trailing_byte_rejected

end Mettapedia.GSLT.LanguageDef.M0GCWireFormat
