import Batteries.Data.Array.Lemmas
import Mettapedia.GSLT.LanguageDef.M0GCFlatCertificateLoaderCompleteness

/-!
# Bounded byte-memory representation for the M0GC checker

This module introduces the target-neutral memory seam between the proved
list-of-bytes M0GC loader and future low-level realizations.  A `ByteRegion`
is an immutable array together with an intrinsically valid base and extent.
Reads use array extraction and explicit bounds checks rather than packed
structure casts.

In standard proof-engineering terminology, this is an abstract byte-addressed
machine refinement for an executable proof-certificate checker.  It is one
prospective component of a proof-checking root of trust; it is not itself a
trusted inference kernel or a verified machine-code checker.

The main representation theorem says that compiling a list of bytes to a
full byte region and reading an in-bounds range returns exactly the
corresponding list slice.  A separate theorem rejects every out-of-bounds
range, so bounds failure cannot silently become an empty or truncated field.

Maturity boundary: this is a fully connected intermediate proof of concept.
It is not yet a mutable memory model, machine-word address arithmetic,
Pancake or Clight semantics, compiler correctness, object-code correctness,
or the official MM0/MMB format.
-/

namespace Mettapedia.GSLT.LanguageDef.M0GCBoundedByteMemory

open Mettapedia.GSLT.LanguageDef.CompiledPlanWireFormat
open Mettapedia.GSLT.LanguageDef.M0GCWireFormat
open Mettapedia.GSLT.LanguageDef.M0GCCanonicalBodyBytes
open Mettapedia.GSLT.LanguageDef.M0GCFlatBodyLoaderCorrespondence
open Mettapedia.GSLT.LanguageDef.M0GCFlatHeaderLoaderCorrespondence
open Mettapedia.GSLT.LanguageDef.M0GCFlatCertificateLoaderCorrespondence
open Mettapedia.GSLT.LanguageDef.M0GCFlatCertificateLoaderCompleteness

/-! ## Intrinsically bounded byte regions -/

/-- One immutable region of byte-addressed memory.  `base` and `extent`
select a valid subregion of the backing array. -/
structure ByteRegion where
  cells : Array UInt8
  base : Nat
  extent : Nat
  inBounds : base + extent ≤ cells.size

namespace ByteRegion

/-- Compile a source byte list to one full, zero-based memory region. -/
def ofList (bytes : List UInt8) : ByteRegion where
  cells := bytes.toArray
  base := 0
  extent := bytes.length
  inBounds := by simp

/-- Read one byte at a region-relative address.  The explicit region check is
part of the target semantics; it is not delegated to a source-list reader. -/
def loadByte? (region : ByteRegion) (offset : Nat) : Option UInt8 :=
  if offset < region.extent then
    region.cells[region.base + offset]?
  else
    none

/-- Read a range only when the complete half-open interval lies within the
selected region.  The extraction is performed over the backing `Array`.
No partial prefix is returned on failure. -/
def loadBytes? (region : ByteRegion) (offset width : Nat) :
    Option (List UInt8) :=
  if offset + width ≤ region.extent then
    some
      ((region.cells.extract
        (region.base + offset)
        (region.base + offset + width)).toList)
  else
    none

@[simp] theorem ofList_extent (bytes : List UInt8) :
    (ofList bytes).extent = bytes.length := rfl

/-- A compiled byte region implements source-list indexing exactly. -/
@[simp] theorem loadByte?_ofList (bytes : List UInt8) (offset : Nat) :
    (ofList bytes).loadByte? offset = bytes[offset]? := by
  simp [loadByte?, ofList, List.getElem?_toArray]

/-- Array-backed reads of a compiled source are exactly the corresponding
source-list slices whenever the complete range is in bounds. -/
theorem loadBytes?_ofList_of_inBounds
    (bytes : List UInt8) (offset width : Nat)
    (inBounds : offset + width ≤ bytes.length) :
    (ofList bytes).loadBytes? offset width =
      some ((bytes.drop offset).take width) := by
  simp [loadBytes?, ofList, inBounds, List.extract_eq_take_drop]

/-- A range crossing the declared boundary is rejected rather than silently
truncated. -/
theorem loadBytes?_ofList_of_outOfBounds
    (bytes : List UInt8) (offset width : Nat)
    (outOfBounds : bytes.length < offset + width) :
    (ofList bytes).loadBytes? offset width = none := by
  simp [loadBytes?, ofList, Nat.not_le.mpr outOfBounds]

/-- Exact two-branch characterization of reads from a compiled source. -/
theorem loadBytes?_ofList (bytes : List UInt8) (offset width : Nat) :
    (ofList bytes).loadBytes? offset width =
      if offset + width ≤ bytes.length then
        some ((bytes.drop offset).take width)
      else
        none := by
  split
  next inBounds => exact loadBytes?_ofList_of_inBounds bytes offset width inBounds
  next outOfBounds =>
    exact loadBytes?_ofList_of_outOfBounds bytes offset width
      (Nat.lt_of_not_ge outOfBounds)

/-! ## Fixed-width field reads -/

/-- Discard the suffix of a successful sequential reader. -/
def readerValue? (read : Reader α) (input : List UInt8) : Option α := do
  let (value, _) ← read input
  some value

/-- Accept a field decoder only when it consumes the complete bounded field. -/
def readerExhaustive? (read : Reader α) (input : List UInt8) : Option α := do
  let (value, rest) ← read input
  if rest.isEmpty then some value else none

/-- A field decoder has exact bounded-width behavior when decoding its exact
prefix agrees with decoding the same prefix inside an arbitrary suffix, and
short inputs are rejected.  This is the reusable contract required by a
bounded-memory implementation. -/
def BoundedFieldAgreement (read : Reader α) (width : Nat) : Prop :=
  ∀ input,
    (if width ≤ input.length then
      readerExhaustive? read (input.take width)
    else
      none) = readerValue? read input

/-- Canonical re-encoding plus exact encoder width is sufficient to qualify a
sequential reader for bounded-memory use.  The proof covers both directions:
a complete prefix accepted locally must also be accepted with any suffix, and
a short input cannot be accepted because it cannot contain a full canonical
encoding. -/
theorem boundedFieldAgreement_of_reencodesPrefix
    {read : Reader α} {encode : α → List UInt8} {width : Nat}
    (roundTrip : ∀ value rest,
      read (encode value ++ rest) = some (value, rest))
    (widthExact : ∀ value, (encode value).length = width)
    (canonical : ReencodesPrefix read encode) :
    BoundedFieldAgreement read width := by
  intro input
  by_cases enough : width ≤ input.length
  · rw [if_pos enough]
    cases sourceResult : read input with
    | none =>
        unfold readerValue?
        rw [sourceResult]
        unfold readerExhaustive?
        cases prefixResult : read (input.take width) with
        | none => rfl
        | some pair =>
            rcases pair with ⟨value, rest⟩
            cases rest with
            | nil =>
                have prefixCanonical :=
                  canonical (input.take width) value [] prefixResult
                have inputSplit := List.take_append_drop width input
                have inputCanonical :
                    input = encode value ++ input.drop width := by
                  calc
                    input = input.take width ++ input.drop width :=
                      inputSplit.symm
                    _ = encode value ++ input.drop width := by
                      rw [prefixCanonical]
                      simp
                have acceptedWithSuffix := roundTrip value (input.drop width)
                rw [inputCanonical] at sourceResult
                rw [acceptedWithSuffix] at sourceResult
                contradiction
            | cons head tail => rfl
    | some pair =>
        rcases pair with ⟨value, rest⟩
        have inputCanonical := canonical input value rest sourceResult
        have prefixCanonical : input.take width = encode value := by
          rw [inputCanonical]
          simp [widthExact]
        have roundTripEmpty : read (encode value) = some (value, []) := by
          simpa using roundTrip value []
        unfold readerExhaustive? readerValue?
        rw [prefixCanonical, roundTripEmpty, sourceResult]
        rfl
  · rw [if_neg enough]
    unfold readerValue?
    cases sourceResult : read input with
    | none => rfl
    | some pair =>
        rcases pair with ⟨value, rest⟩
        have inputCanonical := canonical input value rest sourceResult
        have enough' : width ≤ input.length := by
          rw [inputCanonical]
          simp [widthExact]
        exact (enough enough').elim

/-- Apply a canonical field decoder to an exactly bounded memory range.
Requiring the local decoder to exhaust the extracted field prevents a
shorter decoder from accepting only a prefix of the declared field. -/
def readField? (read : Reader α) (width : Nat) (region : ByteRegion)
    (offset : Nat) : Option α := do
  let field ← region.loadBytes? offset width
  readerExhaustive? read field

/-- Any decoder satisfying the exact bounded-width contract has identical
behavior through compiled byte memory and through the original list-offset
reader. -/
theorem readField?_ofList
    (read : Reader α) (width : Nat)
    (positive : 0 < width)
    (agreement : BoundedFieldAgreement read width)
    (bytes : List UInt8) (offset : Nat) :
    readField? read width (ofList bytes) offset =
      M0GCFlatHeaderLoaderCorrespondence.readAt? read bytes offset := by
  unfold readField? M0GCFlatHeaderLoaderCorrespondence.readAt?
  rw [loadBytes?_ofList]
  change _ = readerValue? read (bytes.drop offset)
  by_cases complete : offset + width ≤ bytes.length
  · have enough : width ≤ (bytes.drop offset).length := by
      simp only [List.length_drop]
      omega
    have exact := agreement (bytes.drop offset)
    rw [if_pos enough] at exact
    simpa [complete] using exact
  · have short : ¬width ≤ (bytes.drop offset).length := by
      simp only [List.length_drop]
      omega
    have exact := agreement (bytes.drop offset)
    rw [if_neg short] at exact
    simpa [complete] using exact

/-- A bounded field read depends only on the prefix ending at that field.
Truncating a compiled byte list at any later boundary leaves the read
unchanged.  This is the reusable locality law for proving that a partial
physical allocation executes successfully up to its first missing field. -/
theorem readField?_ofList_take_eq
    (read : Reader α) (width : Nat) (bytes : List UInt8)
    (limit offset : Nat)
    (fieldCovered : offset + width ≤ limit)
    (limitCovered : limit ≤ bytes.length) :
    readField? read width (ofList (bytes.take limit)) offset =
      readField? read width (ofList bytes) offset := by
  have truncatedLength : (bytes.take limit).length = limit := by
    simp [List.length_take, Nat.min_eq_left limitCovered]
  unfold readField?
  rw [loadBytes?_ofList_of_inBounds (bytes.take limit) offset width (by
        rw [truncatedLength]
        exact fieldCovered)]
  rw [loadBytes?_ofList_of_inBounds bytes offset width
        (fieldCovered.trans limitCovered)]
  congr 1
  rw [List.drop_take, List.take_take]
  have widthFits : width ≤ limit - offset := by omega
  rw [Nat.min_eq_left widthFits]

def loadUInt16LE? (region : ByteRegion) (offset : Nat) : Option UInt16 :=
  readField? readUInt16LE 2 region offset

theorem readUInt16LE_boundedFieldAgreement :
    BoundedFieldAgreement readUInt16LE 2 := by
  exact boundedFieldAgreement_of_reencodesPrefix
    readUInt16LE_encodeUInt16LE
    (fun _ => rfl)
    readUInt16LE_reencodesPrefix

/-- The bounded-memory 16-bit load agrees with the existing fixed-offset list
reader for every input, including short-input rejection. -/
theorem loadUInt16LE?_ofList (bytes : List UInt8) (offset : Nat) :
    loadUInt16LE? (ofList bytes) offset =
      M0GCFlatHeaderLoaderCorrespondence.readAt? readUInt16LE bytes offset := by
  exact readField?_ofList readUInt16LE 2 (by decide)
    readUInt16LE_boundedFieldAgreement bytes offset

def loadUInt32LE? (region : ByteRegion) (offset : Nat) : Option UInt32 :=
  readField? readUInt32LE 4 region offset

theorem readUInt32LE_boundedFieldAgreement :
    BoundedFieldAgreement readUInt32LE 4 := by
  exact boundedFieldAgreement_of_reencodesPrefix
    readUInt32LE_encodeUInt32LE
    (fun _ => rfl)
    readUInt32LE_reencodesPrefix

theorem loadUInt32LE?_ofList (bytes : List UInt8) (offset : Nat) :
    loadUInt32LE? (ofList bytes) offset =
      M0GCFlatHeaderLoaderCorrespondence.readAt? readUInt32LE bytes offset := by
  exact readField?_ofList readUInt32LE 4 (by decide)
    readUInt32LE_boundedFieldAgreement bytes offset

def loadUInt64LE? (region : ByteRegion) (offset : Nat) : Option UInt64 :=
  readField? readUInt64LE 8 region offset

theorem readUInt64LE_boundedFieldAgreement :
    BoundedFieldAgreement readUInt64LE 8 := by
  exact boundedFieldAgreement_of_reencodesPrefix
    readUInt64LE_encodeUInt64LE
    (fun _ => rfl)
    readUInt64LE_reencodesPrefix

theorem loadUInt64LE?_ofList (bytes : List UInt8) (offset : Nat) :
    loadUInt64LE? (ofList bytes) offset =
      M0GCFlatHeaderLoaderCorrespondence.readAt? readUInt64LE bytes offset := by
  exact readField?_ofList readUInt64LE 8 (by decide)
    readUInt64LE_boundedFieldAgreement bytes offset

/-- Decode one physical term record through the bounded field interface. -/
def loadTermNode? (region : ByteRegion) (offset : Nat) : Option TermNode :=
  readField? readTermNode 20 region offset

theorem readTermNode_boundedFieldAgreement :
    BoundedFieldAgreement readTermNode 20 := by
  exact boundedFieldAgreement_of_reencodesPrefix
    readTermNode_encodeTermNode
    encodeTermNode_length
    readTermNode_reencodesPrefix

theorem loadTermNode?_ofList (bytes : List UInt8) (offset : Nat) :
    loadTermNode? (ofList bytes) offset =
      M0GCFlatHeaderLoaderCorrespondence.readAt? readTermNode bytes offset := by
  exact readField?_ofList readTermNode 20 (by decide)
    readTermNode_boundedFieldAgreement bytes offset

/-- Decode one physical proof record through the bounded field interface. -/
def loadProofNode? (region : ByteRegion) (offset : Nat) : Option ProofNode :=
  readField? readProofNode 32 region offset

theorem readProofNode_boundedFieldAgreement :
    BoundedFieldAgreement readProofNode 32 := by
  exact boundedFieldAgreement_of_reencodesPrefix
    readProofNode_encodeProofNode
    encodeProofNode_length
    readProofNode_reencodesPrefix

theorem loadProofNode?_ofList (bytes : List UInt8) (offset : Nat) :
    loadProofNode? (ofList bytes) offset =
      M0GCFlatHeaderLoaderCorrespondence.readAt? readProofNode bytes offset := by
  exact readField?_ofList readProofNode 32 (by decide)
    readProofNode_boundedFieldAgreement bytes offset

/-! ## Fixed-stride table loading -/

/-- Read `count` records through one bounded-memory field loader at a fixed
stride.  Unlike the source reader, this target operation has no exposed
suffix: each iteration receives an explicit byte address. -/
def loadMany? (load : ByteRegion → Nat → Option α) (width : Nat)
    (region : ByteRegion) : Nat → Nat → Option (List α)
  | _, 0 => some []
  | offset, count + 1 => do
      let head ← load region offset
      let tail ← loadMany? load width region (offset + width) count
      some (head :: tail)

/-- Pointwise agreement of one field loader lifts to exact agreement of the
complete fixed-stride table loop. -/
theorem loadMany?_ofList
    (load : ByteRegion → Nat → Option α) (read : Reader α) (width : Nat)
    (single : ∀ bytes offset,
      load (ofList bytes) offset =
        M0GCFlatHeaderLoaderCorrespondence.readAt? read bytes offset)
    (bytes : List UInt8) :
    ∀ offset count,
      loadMany? load width (ofList bytes) offset count =
        readManyAt read width bytes offset count := by
  intro offset count
  induction count generalizing offset with
  | zero => rfl
  | succ count inductionHypothesis =>
      simp only [loadMany?, readManyAt]
      rw [single bytes offset]
      unfold M0GCFlatHeaderLoaderCorrespondence.readAt?
      cases firstResult : read (bytes.drop offset) with
      | none => simp
      | some pair =>
          rcases pair with ⟨head, suffix⟩
          simp [inductionHypothesis]

/-- Dropping a source prefix and starting at `offset` is observationally the
same table read as starting at `base + offset` in the undropped source. -/
theorem readManyAt_drop (read : Reader α) (width : Nat)
    (bytes : List UInt8) (base : Nat) :
    ∀ offset count,
      readManyAt read width bytes (base + offset) count =
        readManyAt read width (bytes.drop base) offset count := by
  intro offset count
  induction count generalizing offset with
  | zero => rfl
  | succ count inductionHypothesis =>
      simp only [readManyAt]
      rw [show bytes.drop (base + offset) =
          (bytes.drop base).drop offset by simp [List.drop_drop]]
      simp only [Nat.add_assoc]
      rw [inductionHypothesis (offset + width)]

/-- Combined representation theorem for a fixed-stride loop over a body
beginning at a nonzero memory base. -/
theorem loadMany?_ofList_drop
    (load : ByteRegion → Nat → Option α) (read : Reader α) (width : Nat)
    (single : ∀ bytes offset,
      load (ofList bytes) offset =
        M0GCFlatHeaderLoaderCorrespondence.readAt? read bytes offset)
    (bytes : List UInt8) (base offset count : Nat) :
    loadMany? load width (ofList bytes) (base + offset) count =
      readManyAt read width (bytes.drop base) offset count := by
  calc
    loadMany? load width (ofList bytes) (base + offset) count =
        readManyAt read width bytes (base + offset) count :=
      loadMany?_ofList load read width single bytes (base + offset) count
    _ = readManyAt read width (bytes.drop base) offset count :=
      readManyAt_drop read width bytes base offset count

/-- Fixed-size raw blocks use the same bounded field interface as scalars. -/
def loadBlock? (region : ByteRegion) (offset width : Nat) :
    Option (List UInt8) :=
  readField? (readBytes width) width region offset

theorem readBytes_boundedFieldAgreement (width : Nat) :
    BoundedFieldAgreement (readBytes width) width := by
  intro input
  by_cases enough : width ≤ input.length
  · simp [readerExhaustive?, readerValue?, readBytes, enough]
  · simp [readerValue?, readBytes, enough]

theorem loadBlock?_ofList (bytes : List UInt8) (offset width : Nat)
    (positive : 0 < width) :
    loadBlock? (ofList bytes) offset width =
      M0GCFlatHeaderLoaderCorrespondence.readAt?
        (readBytes width) bytes offset := by
  exact readField?_ofList (readBytes width) width positive
    (readBytes_boundedFieldAgreement width) bytes offset

/-! ## Body-table loading over bounded memory -/

/-- Load all five physical M0GC body tables from an explicit base address.
The gate requires that the selected body exactly exhaust the region; a base
outside the region cannot be accepted even for an empty body. -/
def readBodyAtMemory? (counts : BodyCounts) (region : ByteRegion)
    (base : Nat) : Option BodyTables :=
  if base ≤ region.extent ∧
      region.extent - base = bodyByteLength counts then do
    let terms ←
      loadMany? loadTermNode? 20 region
        (base + termTableOffset counts) counts.termCount
    let children ←
      loadMany? loadUInt32LE? 4 region
        (base + childTableOffset counts) counts.childCount
    let proofs ←
      loadMany? loadProofNode? 32 region
        (base + proofTableOffset counts) counts.proofCount
    let arguments ←
      loadMany? loadUInt32LE? 4 region
        (base + argumentTableOffset counts) counts.argumentCount
    let premises ←
      loadMany? loadUInt32LE? 4 region
        (base + premiseTableOffset counts) counts.premiseCount
    some { terms, children, proofs, arguments, premises }
  else
    none

/-- Zero-based body loading is the specialization used for standalone body
tests. -/
def readBodyMemory? (counts : BodyCounts) (region : ByteRegion) :
    Option BodyTables :=
  readBodyAtMemory? counts region 0

/-- Exact correspondence for a body at an arbitrary valid source offset. -/
theorem readBodyAtMemory?_ofList (counts : BodyCounts)
    (bytes : List UInt8) (base : Nat) :
    readBodyAtMemory? counts (ofList bytes) base =
      if base ≤ bytes.length then
        readBodyFlat? counts (bytes.drop base)
      else
        none := by
  unfold readBodyAtMemory?
  simp only [ofList_extent]
  rw [loadMany?_ofList_drop loadTermNode? readTermNode 20
    loadTermNode?_ofList bytes base]
  rw [loadMany?_ofList_drop loadUInt32LE? readUInt32LE 4
    loadUInt32LE?_ofList bytes base]
  rw [loadMany?_ofList_drop loadProofNode? readProofNode 32
    loadProofNode?_ofList bytes base]
  rw [loadMany?_ofList_drop loadUInt32LE? readUInt32LE 4
    loadUInt32LE?_ofList bytes base]
  rw [loadMany?_ofList_drop loadUInt32LE? readUInt32LE 4
    loadUInt32LE?_ofList bytes base]
  by_cases baseInBounds : base ≤ bytes.length
  · have dropLength : (bytes.drop base).length = bytes.length - base := by
      simp
    simp [baseInBounds, readBodyFlat?, dropLength]
  · simp [baseInBounds]

/-- Compiling a source body to bounded byte memory preserves the complete
five-table loader exactly, including its exact-length rejection behavior. -/
theorem readBodyMemory?_ofList (counts : BodyCounts) (bytes : List UInt8) :
    readBodyMemory? counts (ofList bytes) = readBodyFlat? counts bytes := by
  unfold readBodyMemory?
  rw [readBodyAtMemory?_ofList]
  simp

/-- Positive body discriminator inherited through the proved memory
representation. -/
theorem canary_memory_body_accepts :
    readBodyMemory? canaryCounts (ofList (encodeBody canaryCertificate)) =
      some canaryTables := by
  rw [readBodyMemory?_ofList]
  exact canary_flat_body_accepts

/-- Negative body discriminator: truncation at the memory boundary is
rejected before a partial table collection can be returned. -/
theorem truncated_memory_body_rejected :
    readBodyMemory? canaryCounts
        (ofList (encodeBody canaryCertificate).dropLast) = none := by
  rw [readBodyMemory?_ofList]
  exact truncated_canary_body_rejected

/-- Negative body discriminator: trailing memory outside the declared tables
is rejected rather than ignored. -/
theorem trailing_memory_body_rejected :
    readBodyMemory? canaryCounts
        (ofList (encodeBody canaryCertificate ++ [0])) = none := by
  rw [readBodyMemory?_ofList]
  exact trailing_canary_body_rejected

/-! ## Header loading over bounded memory -/

/-- The fixed-offset M0GC header algorithm expressed solely through bounded
byte-region loads. -/
def readHeaderMemory? (region : ByteRegion) : Option Header := do
  let decodedMagic ← region.loadBlock? 0 4
  if decodedMagic = M0GCWireFormat.magic then do
    let decodedVersion ← region.loadUInt16LE? 4
    if decodedVersion = version then do
      let flags ← region.loadUInt16LE? 6
      let termCount ← region.loadUInt32LE? 8
      let childCount ← region.loadUInt32LE? 12
      let proofCount ← region.loadUInt32LE? 16
      let argumentCount ← region.loadUInt32LE? 20
      let premiseReferenceCount ← region.loadUInt32LE? 24
      let goalTerm ← region.loadUInt32LE? 28
      let profileDigest ← region.loadBlock? 32 digestWidth
      let sourceDigest ← region.loadBlock? 64 digestWidth
      let bodyChecksum ← region.loadUInt64LE? 96
      some
        { flags, termCount, childCount, proofCount, argumentCount,
          premiseReferenceCount, goalTerm, profileDigest, sourceDigest,
          bodyChecksum }
    else
      none
  else
    none

/-- The bounded-memory header algorithm is exactly the proved list-level flat
header loader on every source byte list. -/
theorem readHeaderMemory?_ofList (bytes : List UInt8) :
    readHeaderMemory? (ofList bytes) =
      M0GCFlatHeaderLoaderCorrespondence.readHeaderFlat? bytes := by
  by_cases enoughMagic : 4 ≤ bytes.length
  · have magicLoad :
        loadBlock? (ofList bytes) 0 4 = some (bytes.take 4) := by
      simp [loadBlock?, readField?, loadBytes?_ofList, enoughMagic,
        readerExhaustive?, readBytes]
    unfold readHeaderMemory?
      M0GCFlatHeaderLoaderCorrespondence.readHeaderFlat?
    rw [magicLoad]
    rw [loadUInt16LE?_ofList bytes 4]
    rw [loadUInt16LE?_ofList bytes 6]
    rw [loadUInt32LE?_ofList bytes 8]
    rw [loadUInt32LE?_ofList bytes 12]
    rw [loadUInt32LE?_ofList bytes 16]
    rw [loadUInt32LE?_ofList bytes 20]
    rw [loadUInt32LE?_ofList bytes 24]
    rw [loadUInt32LE?_ofList bytes 28]
    rw [loadBlock?_ofList bytes 32 digestWidth (by decide)]
    rw [loadBlock?_ofList bytes 64 digestWidth (by decide)]
    rw [loadUInt64LE?_ofList bytes 96]
    rfl
  · have magicLoad : loadBlock? (ofList bytes) 0 4 = none := by
      simp [loadBlock?, readField?, loadBytes?_ofList, enoughMagic]
    have magicMismatch : bytes.take 4 ≠ M0GCWireFormat.magic := by
      intro equal
      have lengths := congrArg List.length equal
      simp [M0GCWireFormat.magic] at lengths
      omega
    simp [readHeaderMemory?, magicLoad,
      M0GCFlatHeaderLoaderCorrespondence.readHeaderFlat?, magicMismatch]

/-- Successful flat header decoding entails that the complete 104-byte header
is present.  This connects the parser fact to the memory safety boundary used
by the body-at-offset theorem. -/
theorem readHeaderFlat?_some_implies_length
    (bytes : List UInt8) (header : Header)
    (accepted : readHeaderFlat? bytes = some header) :
    104 ≤ bytes.length := by
  have reads := (readHeaderFlat?_eq_some_iff bytes header).mp accepted
  have boundedRead :
      loadUInt64LE? (ofList bytes) 96 = some header.bodyChecksum := by
    rw [loadUInt64LE?_ofList]
    exact reads.bodyChecksumRead
  unfold loadUInt64LE? readField? at boundedRead
  rw [loadBytes?_ofList] at boundedRead
  by_cases complete : 96 + 8 ≤ bytes.length
  · omega
  · simp [complete] at boundedRead

/-! ## Complete certificate loading over bounded memory -/

/-- Header, body tables, and original-byte checksum composed over one bounded
byte region.  The table loader enforces that the body beginning at byte 104
exactly exhausts the region. -/
def readCertificateMemory? (region : ByteRegion) : Option Certificate := do
  let header ← readHeaderMemory? region
  let counts := BodyCounts.ofHeader header
  let bodyWidth := bodyByteLength counts
  let bodyBytes ← region.loadBytes? 104 bodyWidth
  let tables ← readBodyAtMemory? counts region 104
  if header.bodyChecksum = fnv1a64 bodyBytes then
    some (certificateOfTables header tables)
  else
    none

/-- The complete bounded-memory loader has exactly the behavior of the proved
flat byte-list loader on every source input—not merely on valid encodings. -/
theorem readCertificateMemory?_ofList (bytes : List UInt8) :
    readCertificateMemory? (ofList bytes) = readCertificateFlat? bytes := by
  unfold readCertificateMemory?
  rw [readHeaderMemory?_ofList]
  cases headerResult : readHeaderFlat? bytes with
  | none =>
      simp [readCertificateFlat?, headerResult]
  | some header =>
      have headerFits : 104 ≤ bytes.length :=
        readHeaderFlat?_some_implies_length bytes header headerResult
      unfold readCertificateFlat?
      rw [headerResult]
      dsimp only [Bind.bind, instMonadOption, Option.bind]
      rw [readBodyAtMemory?_ofList]
      simp only [headerFits, if_true]
      by_cases bodyExact :
          (bytes.drop 104).length =
            bodyByteLength (BodyCounts.ofHeader header)
      · have rangeComplete :
            104 + bodyByteLength (BodyCounts.ofHeader header) ≤
              bytes.length := by
          simp only [List.length_drop] at bodyExact
          omega
        rw [loadBytes?_ofList_of_inBounds bytes 104
          (bodyByteLength (BodyCounts.ofHeader header)) rangeComplete]
        have takeAll :
            (bytes.drop 104).take
                (bodyByteLength (BodyCounts.ofHeader header)) =
              bytes.drop 104 := by
          rw [← bodyExact]
          simp
        rw [takeAll]
      · have bodyRejected :
            readBodyFlat? (BodyCounts.ofHeader header) (bytes.drop 104) =
              none := by
          unfold readBodyFlat?
          rw [if_neg bodyExact]
        rw [bodyRejected]
        cases (ofList bytes).loadBytes? 104
            (bodyByteLength (BodyCounts.ofHeader header)) <;> rfl

/-- Standard sound-refinement statement: acceptance through compiled bounded
memory implies acceptance by the canonical sequential certificate reader with
no trailing bytes. -/
theorem readCertificateMemory?_ofList_refines_canonical
    (bytes : List UInt8) (certificate : Certificate)
    (accepted : readCertificateMemory? (ofList bytes) = some certificate) :
    readCertificate bytes = some (certificate, []) := by
  rw [readCertificateMemory?_ofList] at accepted
  exact readCertificateFlat?_refines_canonical bytes certificate accepted

/-- The same result at the public exact-file decoding boundary. -/
theorem readCertificateMemory?_ofList_refines_decodeCertificate?
    (bytes : List UInt8) (certificate : Certificate)
    (accepted : readCertificateMemory? (ofList bytes) = some certificate) :
    decodeCertificate? bytes = some certificate := by
  rw [readCertificateMemory?_ofList] at accepted
  exact readCertificateFlat?_refines_decodeCertificate?
    bytes certificate accepted

/-- Standard producer-completeness statement: every encodable certificate
emitted by the canonical producer is accepted through bounded byte memory. -/
theorem readCertificateMemory?_encodeCertificate
    (certificate : Certificate) (encodable : certificate.Encodable) :
    readCertificateMemory? (ofList (encodeCertificate certificate)) =
      some certificate := by
  rw [readCertificateMemory?_ofList]
  exact readCertificateFlat?_encodeCertificate certificate encodable

/-- Positive end-to-end header discriminator inherited through the proved
representation theorem. -/
theorem canary_memory_header_accepts :
    readHeaderMemory? (ofList (encodeCertificate canaryCertificate)) =
      some M0GCFlatHeaderLoaderCorrespondence.canaryHeader := by
  rw [readHeaderMemory?_ofList]
  exact M0GCFlatHeaderLoaderCorrespondence.canary_flat_header_accepts

/-- Negative discriminator: corrupt magic is still rejected after the array
representation change. -/
theorem corrupt_magic_memory_header_rejected :
    readHeaderMemory?
        (ofList (0 :: (encodeCertificate canaryCertificate).tail)) = none := by
  rw [readHeaderMemory?_ofList]
  exact M0GCFlatHeaderLoaderCorrespondence.corrupt_magic_flat_header_rejected

/-- Negative discriminator: a three-byte input cannot be mistaken for a
complete header. -/
theorem truncated_memory_header_rejected :
    readHeaderMemory? (ofList [77, 48, 71]) = none := by
  decide

/-- Positive full-certificate discriminator through bounded byte memory. -/
theorem canary_memory_certificate_accepts :
    readCertificateMemory? (ofList (encodeCertificate canaryCertificate)) =
      some canaryCertificate := by
  rw [readCertificateMemory?_ofList]
  exact canonical_canary_flat_accepts

/-- Negative full-certificate discriminator: a checksum mutation remains
rejected after the representation change. -/
theorem wrong_checksum_memory_certificate_rejected :
    readCertificateMemory? (ofList wrongChecksumCanary) = none := by
  rw [readCertificateMemory?_ofList]
  exact wrong_checksum_flat_rejected

/-- Negative full-certificate discriminator: trailing memory cannot be
silently ignored. -/
theorem trailing_memory_certificate_rejected :
    readCertificateMemory?
        (ofList (encodeCertificate canaryCertificate ++ [0])) = none := by
  rw [readCertificateMemory?_ofList]
  exact trailing_byte_flat_rejected

/-! ## Discriminating examples -/

/-- Positive canary: a nonzero-offset range is selected exactly. -/
example :
    (ofList [10, 20, 30, 40, 50]).loadBytes? 1 3 =
      some [20, 30, 40] := by
  decide

/-- Positive scalar canary: relative addressing selects the expected byte. -/
example : (ofList [10, 20, 30]).loadByte? 1 = some 20 := by
  decide

/-- Negative canary: the same memory rejects a range extending one byte past
its boundary. -/
example :
    (ofList [10, 20, 30, 40, 50]).loadBytes? 3 3 = none := by
  decide

/-- Negative scalar canary: an address at the extent is outside the region. -/
example : (ofList [10, 20, 30]).loadByte? 3 = none := by
  decide

end ByteRegion

#print axioms ByteRegion.loadBytes?_ofList
#print axioms ByteRegion.boundedFieldAgreement_of_reencodesPrefix
#print axioms ByteRegion.readField?_ofList
#print axioms ByteRegion.loadMany?_ofList_drop
#print axioms ByteRegion.readBodyAtMemory?_ofList
#print axioms ByteRegion.readHeaderMemory?_ofList
#print axioms ByteRegion.readCertificateMemory?_ofList
#print axioms ByteRegion.readCertificateMemory?_ofList_refines_canonical
#print axioms ByteRegion.readCertificateMemory?_encodeCertificate
#print axioms ByteRegion.canary_memory_body_accepts
#print axioms ByteRegion.canary_memory_header_accepts
#print axioms ByteRegion.canary_memory_certificate_accepts
#print axioms ByteRegion.corrupt_magic_memory_header_rejected
#print axioms ByteRegion.wrong_checksum_memory_certificate_rejected

end Mettapedia.GSLT.LanguageDef.M0GCBoundedByteMemory
