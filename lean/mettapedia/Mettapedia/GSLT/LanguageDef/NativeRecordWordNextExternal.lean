import Mettapedia.GSLT.LanguageDef.NativeRecordWordBodyBackward
import Mettapedia.GSLT.LanguageDef.NativeRecordSelectorsExternal

/-!
The complete four-argument record-next-word interface at its declared codec
and memory profile. Operand selection precedes the iterator body. A missing
operand returns false in the guard's post-state; a selected operand uses the
proved body, including reader poisoning and caller publication. Preservation
and reflection retain every state component. The non-shortest policy used by
the pinned guest is a codec condition, not a theorem or consistency premise.
Concrete record/union/pointer and size_t realization remain ABI obligations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeRecordWordIteration

open NativeOps (Address SourceState TargetState StateRelated SourceExternalSemantics
  TargetExternalSemantics ExternalCorrespondence encodeValues)
open NativeWord64 (Word encode)
open Parsing.BinaryRecordCodec (WordCodec)

inductive SourceCall (codec : WordCodec) {World : Type} : SourceState World → Option Address →
    Word → Option Address → Option Address → Bool → SourceState World → Prop where
  | missing {state post : SourceState World} {view position word : Option Address} {index : Word}
      (selected : NativeRecordOperand.SourceOperand state view index .words none post) :
      SourceCall codec state view index position word false post
  | present {state intermediate post : SourceState World} {view operand : Address}
      {position word : Option Address} {index : Word} {returned : Bool}
      (selected : NativeRecordOperand.SourceOperand state (some view) index .words
        (some operand) intermediate)
      (called : SourceBody codec intermediate view operand position word returned post) :
      SourceCall codec state (some view) index position word returned post

inductive TargetCall (codec : WordCodec) {World : Type} : TargetState World → Option Address →
    BitVec 64 → Option Address → Option Address → Bool → TargetState World → Prop where
  | missing {state post : TargetState World} {view position word : Option Address} {index : BitVec 64}
      (selected : NativeRecordOperand.TargetOperand state view index .words none post) :
      TargetCall codec state view index position word false post
  | present {state intermediate post : TargetState World} {view operand : Address}
      {position word : Option Address} {index : BitVec 64} {returned : Bool}
      (selected : NativeRecordOperand.TargetOperand state (some view) index .words
        (some operand) intermediate)
      (called : TargetBody codec intermediate view operand position word returned post) :
      TargetCall codec state (some view) index position word returned post

theorem call_forward {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop}
    (codec : WordCodec) (nonShortest : codec.requireShortest = false)
    (source : SourceState SourceWorld) (target : TargetState TargetWorld)
    (related : StateRelated worldRelated source target) (view : Option Address) (index : Word)
    (position word : Option Address) (returned : Bool) (post : SourceState SourceWorld)
    (called : SourceCall codec source view index position word returned post) :
    ∃ native, TargetCall codec target view (encode index) position word returned native ∧
      StateRelated worldRelated post native := by
  cases called with
  | missing selected =>
    obtain ⟨native, nativeSelected, postRelated⟩ := NativeRecordOperand.operand_forward
      source target related view index .words none post selected
    exact ⟨native, .missing nativeSelected, postRelated⟩
  | @present intermediate _ view operand _ _ _ _ selected body =>
    obtain ⟨nativeIntermediate, nativeSelected, intermediateRelated⟩ :=
      NativeRecordOperand.operand_forward source target related (some view) index .words
        (some operand) intermediate selected
    obtain ⟨native, nativeBody, postRelated⟩ := body_forward codec nonShortest intermediate
      nativeIntermediate intermediateRelated view operand position word returned post body
    exact ⟨native, .present nativeSelected nativeBody, postRelated⟩

theorem call_backward {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop}
    (codec : WordCodec) (nonShortest : codec.requireShortest = false)
    (source : SourceState SourceWorld) (target : TargetState TargetWorld)
    (related : StateRelated worldRelated source target) (view : Option Address) (index : Word)
    (position word : Option Address) (returned : Bool) (native : TargetState TargetWorld)
    (called : TargetCall codec target view (encode index) position word returned native) :
    ∃ post, SourceCall codec source view index position word returned post ∧
      StateRelated worldRelated post native := by
  cases called with
  | missing selected =>
    obtain ⟨post, sourceSelected, postRelated⟩ := NativeRecordOperand.operand_backward
      source target related view index .words none native selected
    exact ⟨post, .missing sourceSelected, postRelated⟩
  | @present intermediate _ view operand _ _ _ _ selected body =>
    obtain ⟨sourceIntermediate, sourceSelected, intermediateRelated⟩ :=
      NativeRecordOperand.operand_backward source target related (some view) index .words
        (some operand) intermediate selected
    obtain ⟨post, sourceBody, postRelated⟩ := body_backward codec nonShortest sourceIntermediate
      intermediate intermediateRelated view operand position word returned native body
    exact ⟨post, .present sourceSelected sourceBody, postRelated⟩

def sourceExternal (codec : WordCodec) (World : Type) : SourceExternalSemantics World :=
  ⟨fun name arguments pre raw post =>
    ∃ view index position word returned, name = "record-next-word" ∧
      arguments = [.reference view, .word index, .reference position, .reference word] ∧
      raw = .bool returned ∧ SourceCall codec pre view index position word returned post⟩

def targetExternal (codec : WordCodec) (World : Type) : TargetExternalSemantics World :=
  ⟨fun name arguments pre raw post =>
    ∃ view index position word returned, name = "record-next-word" ∧
      arguments = [.reference view, .word index, .reference position, .reference word] ∧
      raw = .bool returned ∧ TargetCall codec pre view index position word returned post⟩

theorem external_correspondence {SourceWorld TargetWorld : Type}
    (codec : WordCodec) (nonShortest : codec.requireShortest = false)
    (worldRelated : SourceWorld → TargetWorld → Prop) :
    ExternalCorrespondence (sourceExternal codec SourceWorld)
      (targetExternal codec TargetWorld) worldRelated := by
  constructor
  · intro name arguments source target raw post related called
    obtain ⟨view, index, position, word, returned, named, args, rawEqual, call⟩ := called
    subst arguments
    subst raw
    obtain ⟨native, nativeCalled, postRelated⟩ := call_forward codec nonShortest source target
      related view index position word returned post call
    exact ⟨native, ⟨view, encode index, position, word, returned, named, rfl, rfl, nativeCalled⟩,
      postRelated⟩
  · intro name arguments source target raw native related called
    obtain ⟨view, index, position, word, returned, named, args, rawEqual, call⟩ := called
    have decodedArguments := congrArg NativeOps.decodeValues args
    have sourceArguments : arguments =
        [.reference view, .word index.toFin, .reference position, .reference word] := by
      simpa only [NativeOps.decode_encode_values, NativeOps.decodeValues, NativeOps.decodeValue]
        using decodedArguments
    have normalized : encode index.toFin = index := BitVec.ofFin_toFin index
    rw [← normalized] at call
    obtain ⟨post, sourceCalled, postRelated⟩ := call_backward codec nonShortest source target
      related view index.toFin position word returned native call
    exact ⟨.bool returned, post,
      ⟨view, index.toFin, position, word, returned, named, sourceArguments, rfl, sourceCalled⟩,
      rawEqual, postRelated⟩

theorem pinned_external_correspondence {SourceWorld TargetWorld : Type}
    (worldRelated : SourceWorld → TargetWorld → Prop) :
    ExternalCorrespondence (sourceExternal ⟨247, 8, false⟩ SourceWorld)
      (targetExternal ⟨247, 8, false⟩ TargetWorld) worldRelated :=
  external_correspondence ⟨247, 8, false⟩ rfl worldRelated

end Mettapedia.GSLT.LanguageDef.NativeRecordWordIteration
