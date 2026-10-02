import Mettapedia.GSLT.LanguageDef.NativeRecordWordCodec
import Mettapedia.GSLT.LanguageDef.NativeRecordWordPublication
import Mettapedia.GSLT.LanguageDef.NativeRecordOperand
import Mettapedia.GSLT.Parsing.NativeBinaryMemoryBounds

/-!
The record word iterator after its ordered operand selection. Null output
pointers and positions beyond the byte length poison the reader before
decoding. Decoding failure retains caller slots; success publishes the word
before the new position, including aliases. The declared codec is read from
the Words record, and no word-count guard or ownership guard is introduced.
This profile requires that codec's fields to have their declared realization;
the physical union, pointer and size_t layouts remain separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeRecordWordIteration

open NativeOps (Address SourceState TargetState StateRelated SourceMemory TargetMemory
  MemoryRelated)
open NativeRecordAccess
open NativeWord64 (Word encode bounded)
open Parsing.BinaryRecordCodec (WordCodec)
open Parsing.NativeBinaryMemoryWord (Failure)

def payloadAddress (operand : Address) : Address := field operand 2

def sourceFinish {World : Type} (state : SourceState World) (view word position : Address)
    (decoded : Except Failure (Nat × Nat)) : Option (Bool × SourceState World) :=
  match decoded with
  | .error _ => (sourceSetFault state view).map (fun post => (false, post))
  | .ok (value, next) => do
    let memory ← NativeRecordWordPublication.sourcePublish state.memory word position
      (bounded 64 value) (bounded 64 next)
    some (true, {state with memory := memory})

def targetFinish {World : Type} (state : TargetState World) (view word position : Address)
    (decoded : Except Failure (BitVec 64 × Nat)) : Option (Bool × TargetState World) :=
  match decoded with
  | .error _ =>
    match targetSetFault state view with
    | none => none
    | some post => some (false, post)
  | .ok (value, next) =>
    match NativeRecordWordPublication.targetPublish state.memory word position value
        (BitVec.ofNat 64 next) with
    | none => none
    | some memory => some (true, {state with memory := memory})

inductive SourceBody (codec : WordCodec) {World : Type} : SourceState World → Address →
    Address → Option Address → Option Address → Bool → SourceState World → Prop where
  | nullPosition {state post : SourceState World} {view operand : Address} (word : Option Address)
      (poisoned : sourceSetFault state view = some post) :
      SourceBody codec state view operand none word false post
  | nullWord {state post : SourceState World} {view operand position : Address}
      (poisoned : sourceSetFault state view = some post) :
      SourceBody codec state view operand (some position) none false post
  | outside {state post : SourceState World} {view operand position word : Address}
      {offset length : Word}
      (positionRead : sourceReadWord state.memory position = some offset)
      (lengthRead : sourceReadWord state.memory (field (payloadAddress operand) 1) = some length)
      (outside : length.val < offset.val) (poisoned : sourceSetFault state view = some post) :
      SourceBody codec state view operand (some position) (some word) false post
  | invalidData {state post : SourceState World} {view operand position word : Address}
      {offset length : Word}
      (positionRead : sourceReadWord state.memory position = some offset)
      (lengthRead : sourceReadWord state.memory (field (payloadAddress operand) 1) = some length)
      (inside : offset.val ≤ length.val)
      (dataRead : sourceReadPointer state.memory (field (payloadAddress operand) 0) = some none)
      (nonempty : length.val ≠ 0) (poisoned : sourceSetFault state view = some post) :
      SourceBody codec state view operand (some position) (some word) false post
  | decoded {state post : SourceState World} {view operand position word : Address}
      {offset length : Word} {data : Option Address} {result : Except Failure (Nat × Nat)}
      {returned : Bool}
      (positionRead : sourceReadWord state.memory position = some offset)
      (lengthRead : sourceReadWord state.memory (field (payloadAddress operand) 1) = some length)
      (inside : offset.val ≤ length.val)
      (dataRead : sourceReadPointer state.memory (field (payloadAddress operand) 0) = some data)
      (validData : data ≠ none ∨ length.val = 0)
      (codecRead : NativeRecordWordCodec.sourceCodec state.memory operand = some codec)
      (decoded : Parsing.NativeBinaryMemoryWord.sourceRun codec state.memory data length.val
        offset.val = some result)
      (finished : sourceFinish state view word position result = some (returned, post)) :
      SourceBody codec state view operand (some position) (some word) returned post

inductive TargetBody (codec : WordCodec) {World : Type} : TargetState World → Address →
    Address → Option Address → Option Address → Bool → TargetState World → Prop where
  | nullPosition {state post : TargetState World} {view operand : Address} (word : Option Address)
      (poisoned : targetSetFault state view = some post) :
      TargetBody codec state view operand none word false post
  | nullWord {state post : TargetState World} {view operand position : Address}
      (poisoned : targetSetFault state view = some post) :
      TargetBody codec state view operand (some position) none false post
  | outside {state post : TargetState World} {view operand position word : Address}
      {offset length : BitVec 64}
      (positionRead : targetReadWord state.memory position = some offset)
      (lengthRead : targetReadWord state.memory (field (payloadAddress operand) 1) = some length)
      (outside : length.toNat < offset.toNat) (poisoned : targetSetFault state view = some post) :
      TargetBody codec state view operand (some position) (some word) false post
  | invalidData {state post : TargetState World} {view operand position word : Address}
      {offset length : BitVec 64}
      (positionRead : targetReadWord state.memory position = some offset)
      (lengthRead : targetReadWord state.memory (field (payloadAddress operand) 1) = some length)
      (inside : offset.toNat ≤ length.toNat)
      (dataRead : targetReadPointer state.memory (field (payloadAddress operand) 0) = some none)
      (nonempty : length.toNat ≠ 0) (poisoned : targetSetFault state view = some post) :
      TargetBody codec state view operand (some position) (some word) false post
  | decoded {state post : TargetState World} {view operand position word : Address}
      {offset length : BitVec 64} {data : Option Address}
      {result : Except Failure (BitVec 64 × Nat)} {returned : Bool}
      (positionRead : targetReadWord state.memory position = some offset)
      (lengthRead : targetReadWord state.memory (field (payloadAddress operand) 1) = some length)
      (inside : offset.toNat ≤ length.toNat)
      (dataRead : targetReadPointer state.memory (field (payloadAddress operand) 0) = some data)
      (validData : data ≠ none ∨ length.toNat = 0)
      (codecRead : NativeRecordWordCodec.targetCodec state.memory operand = some codec)
      (decoded : Parsing.NativeBinaryMemoryWord.targetRun codec state.memory data length.toNat
        offset.toNat = some result)
      (finished : targetFinish state view word position result = some (returned, post)) :
      TargetBody codec state view operand (some position) (some word) returned post

end Mettapedia.GSLT.LanguageDef.NativeRecordWordIteration
