import MeTTailCore.Crypto.SHA256
import Mettapedia.Languages.Megalodon.PublicationHashRoot

/-!
# Executable SHA-256 leg of Megalodon publication identity

This module instantiates the abstract publication hash-root algebra with the
byte framing used by Megalodon: domain words 1, 7, and 8, big-endian 32-bit
integers, and the bit-level type serializer used by `Mathdata`.

The imported SHA-256 function is an executable implementation and artifact
oracle.  This file does not assert that it refines an independently defined
FIPS SHA-256 specification.  The structural hash-root theorems remain valid
for every `HashOps`, while a future cryptographic refinement theorem can
replace this implementation leg without changing those theorems.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.PublicationSHA256

open Mettapedia.Languages.Megalodon.MathdataKernel
open Mettapedia.Languages.Megalodon.PublicationHashRoot

abbrev Digest := ByteArray

/-- Four-byte big-endian representation used by Megalodon's hash framing. -/
def uint32BE (value : UInt32) : ByteArray :=
  ByteArray.empty
    |>.push (value >>> 24).toUInt8
    |>.push (value >>> 16).toUInt8
    |>.push (value >>> 8).toUInt8
    |>.push value.toUInt8

def hashBytes (bytes : ByteArray) : Digest :=
  MeTTailCore.Crypto.SHA256.sha256Bytes bytes

/-- `SHA256(be32(1) || be32(value))`. -/
def hashInt32 (value : UInt32) : Digest :=
  hashBytes ((uint32BE 1).append (uint32BE value))

/-- `SHA256(be32(7) || left || right)`. -/
def hashPair (left right : Digest) : Digest :=
  hashBytes (((uint32BE 7).append left).append right)

/-- `SHA256(be32(8) || be32(tag) || root)`. -/
def hashTag (root : Digest) (tag : UInt32) : Digest :=
  hashBytes (((uint32BE 8).append (uint32BE tag)).append root)

/-! ## Exact bit-level type serialization -/

/-- State of Megalodon's least-significant-bit-first bit packer. -/
private structure BitWriter where
  bytes : ByteArray := ByteArray.empty
  pending : UInt8 := 0
  used : Nat := 0

private def BitWriter.writeBit (writer : BitWriter) (bit : Nat) : BitWriter :=
  let mask : UInt8 := (1 : UInt8) <<< UInt8.ofNat writer.used
  let pending := if bit % 2 = 0 then writer.pending else writer.pending ||| mask
  if writer.used + 1 = 8 then
    { bytes := writer.bytes.push pending }
  else
    { writer with pending := pending, used := writer.used + 1 }

/-- Write the low `count` bits of `value`, low bit first. -/
private def BitWriter.writeBits : Nat → Nat → BitWriter → BitWriter
  | 0, _, writer => writer
  | count + 1, value, writer =>
      writeBits count (value / 2) (writer.writeBit (value % 2))

private def BitWriter.finish (writer : BitWriter) : ByteArray :=
  if writer.used = 0 then writer.bytes else writer.bytes.push writer.pending

/-- Megalodon's compact nonnegative integer encoding for values below 65536. -/
private def writeVarIntB? (index : Nat) (writer : BitWriter) :
    Option BitWriter :=
  if index < 4 then
    some ((writer.writeBits 2 0).writeBits 2 index)
  else if index < 20 then
    some ((writer.writeBits 2 1).writeBits 4 (index - 4))
  else if index < 276 then
    some ((writer.writeBits 2 2).writeBits 8 (index - 20))
  else if index < 65536 then
    some ((writer.writeBits 2 3).writeBits 16 index)
  else
    none

/-- Megalodon's exact `seo_tp` equations over the bit writer. -/
private def writeType? : Tp → BitWriter → Option BitWriter
  | .arr domain codomain, writer => do
      let writer ← writeType? domain (writer.writeBits 2 0)
      writeType? codomain writer
  | .prop, writer => some (writer.writeBits 2 1)
  | .base index, writer =>
      writeVarIntB? index (writer.writeBits 2 2)
  | .var index, writer =>
      writeVarIntB? index (writer.writeBits 3 3)
  | .all body, writer =>
      writeType? body (writer.writeBits 3 7)

/-- Canonical bytes hashed by Megalodon's `hashtp`. -/
def typeBytes? (type : Tp) : Option ByteArray := do
  let writer ← writeType? type {}
  pure writer.finish

/-- `hashtag (SHA256(typeBytes)) 64`, when type serialization succeeds. -/
def typeRoot? (type : Tp) : Option Digest := do
  let bytes ← typeBytes? type
  pure (hashTag (hashBytes bytes) 64)

/-! ## Exact 256-bit name decoding -/

private def hexNibble? (character : Char) : Option UInt8 :=
  let value := character.toNat
  if 48 ≤ value ∧ value ≤ 57 then
    some (UInt8.ofNat (value - 48))
  else if 97 ≤ value ∧ value ≤ 102 then
    some (UInt8.ofNat (value - 87))
  else if 65 ≤ value ∧ value ≤ 70 then
    some (UInt8.ofNat (value - 55))
  else
    none

private def decodeHexCharacters? (characters : List Char)
    (bytes : ByteArray) : Option ByteArray :=
  match characters with
  | [] => some bytes
  | high :: low :: rest => do
      let highNibble ← hexNibble? high
      let lowNibble ← hexNibble? low
      let byte := (highNibble <<< 4) ||| lowNibble
      decodeHexCharacters? rest (bytes.push byte)
  | [_] => none
termination_by characters.length

/-- Decode one canonical 64-hex-character publication identifier. -/
def decodeDigest? (name : Name) : Option Digest :=
  if name.length = 64 then
    decodeHexCharacters? name.toList ByteArray.empty
  else
    none

/-- Executable Megalodon publication operations.  Logical checking does not
depend on the collision-freedom of this instance. -/
def operations : HashOps Digest where
  hashInt32 := hashInt32
  hashPair := hashPair
  hashTag := hashTag
  typeRoot? := typeRoot?
  namedRoot? := decodeDigest?

/-! ## Framing and serialization canaries -/

#guard MeTTailCore.Crypto.SHA256.toHexString (hashInt32 0) =
  "cbbc48750debb8535093b3deaf88ac7f4cff87425576a58de2bac754acdb4616"

#guard MeTTailCore.Crypto.SHA256.toHexString
    (hashTag (hashInt32 0) 96) =
  "d58762d200971dcc7f1850726d9f2328403127deeba124fc3ba2d2d9f7c3cb8c"

#guard typeBytes? .prop = some (ByteArray.mk #[1])
#guard typeBytes? (.arr .prop .prop) = some (ByteArray.mk #[20])
#guard typeBytes? (.base 0) = some (ByteArray.mk #[2])
#guard typeBytes? (.var 0) = some (ByteArray.mk #[3])
#guard typeBytes? (.all .prop) = some (ByteArray.mk #[15])

/-- Malformed or non-hash symbolic names fail closed at the publication
boundary while remaining ordinary logical names in the proof kernel. -/
example : decodeDigest? "ordinary-logical-name" = none := by
  rfl

/- The exact empty-document publication root under the executable SHA leg. -/
#guard (documentRoot? operations []).map
    MeTTailCore.Crypto.SHA256.toHexString =
  some "ae6d58be55f2432a9f7bf9bc9439d9a4166b6edf166c6af7e642bb63e5c92b7a"

end Mettapedia.Languages.Megalodon.PublicationSHA256
