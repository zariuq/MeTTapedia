import Mettapedia.GSLT.LanguageDef.InferenceCettaWireFormat

/-!
# Native NIK presentation wire

The native authority catalog uses `GPresentationV1` as its package constructor.
The inference-language interchange carrier uses `GInferenceLanguageV1`.
This boundary gives the native tag its own encoder and decoder, reusing all
field codecs. It preserves the complete checker-facing definition, including
ordered rules, side conditions and conversion declarations.

The round trip concerns the symbolic wire carrier. It does not establish
correctness of the C text parser or generic C inference implementation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.InferencePresentationWire

open Mettapedia.GSLT.LanguageDef.InferenceCettaWire
open Mettapedia.GSLT.LanguageDef.InferenceLanguageWire

def encode (definition : RuntimeInferenceLanguage) : CettaTerm :=
  .application "GPresentationV1"
    [.natural inferenceLanguageWireVersion,
      encodeList encodeConstructor definition.constructors,
      encodeList encodeJudgment definition.judgments,
      encodeList encodeRule definition.rules,
      encodeConversion definition.conversion]

def decode : CettaTerm → Option RuntimeInferenceLanguage
  | .application "GPresentationV1" fields =>
      decodeRuntimeInferenceLanguage (.application "GInferenceLanguageV1" fields)
  | _ => none

def encodeDefinition (definition : CalculusLanguageDef) : CettaTerm :=
  encode (RuntimeInferenceLanguage.ofDefinition definition)

def renderDefinition (definition : CalculusLanguageDef) : String :=
  CettaTerm.render (encodeDefinition definition)

@[simp] theorem decode_encode (definition : RuntimeInferenceLanguage) :
    decode (encode definition) = some definition := by
  exact decodeRuntimeInferenceLanguage_encodeRuntimeInferenceLanguage definition

@[simp] theorem decode_encodeDefinition (definition : CalculusLanguageDef) :
    decode (encodeDefinition definition) =
      some (RuntimeInferenceLanguage.ofDefinition definition) :=
  decode_encode _

theorem encode_injective : Function.Injective encode := by
  intro first second equality
  have decoded := congrArg decode equality
  simpa only [decode_encode, Option.some.injEq] using decoded

/-- Foreign outer tags are rejected rather than interpreted as native packages. -/
theorem foreign_tag_rejected (tag : String) (fields : List CettaTerm)
    (different : tag ≠ "GPresentationV1") :
    decode (.application tag fields) = none := by
  simp [decode, different]

theorem version_two_rejected (constructors judgments rules conversion : CettaTerm) :
    decode (.application "GPresentationV1"
      [.natural 2, constructors, judgments, rules, conversion]) = none := by
  simp [decode, InferenceCettaWire.decodeRuntimeInferenceLanguage, inferenceLanguageWireVersion]

end Mettapedia.GSLT.LanguageDef.InferencePresentationWire
