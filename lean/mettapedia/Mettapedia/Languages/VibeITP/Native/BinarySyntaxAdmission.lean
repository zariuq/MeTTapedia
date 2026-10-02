import Mettapedia.GSLT.Parsing.BinaryRecordSource
import Mettapedia.Languages.VibeITP.Native.GeneratedBinarySource

/-! Admission of the exported binary syntax through the existing canonical
GSLT source decoder, closed signature validation and binary descriptor decoder.
The source-text parser boundary is proved separately. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option Elab.async false

namespace Mettapedia.Languages.VibeITP.Native.BinarySyntaxAdmission

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.Parsing
open BinaryRecordCodec
open BinaryRecordSource

theorem canonical_encoding : GeneratedBinarySource.binarySyntax =
    CanonicalSourceGSLT.encode GeneratedBinarySource.canonicalSource := by rfl

theorem canonical_decoded : CanonicalSourceGSLT.decode GeneratedBinarySource.binarySyntax =
    some GeneratedBinarySource.canonicalSource := by
  rw [canonical_encoding, CanonicalSourceGSLT.decode_encode]

theorem canonical_closed : CanonicalSourceGSLT.compositionValid
    [GeneratedBinarySource.canonicalSource] = true := by cbv

def opcodePairs : List (String × OpcodeLayout) :=
  (GeneratedBinarySource.canonicalSource.rewrites.tail.map CanonicalSourceGSLT.Rewrite.name).zip
    GeneratedBinarySource.grammar.opcodes

theorem rewrite_inventory_encoded : GeneratedBinarySource.canonicalSource.rewrites =
    encodeCodec "word-spelling" GeneratedBinarySource.grammar.codec ::
      opcodePairs.map (fun pair => encodeOpcode pair.1 pair.2) := by rfl

theorem opcode_pairs_exact : opcodePairs.map Prod.snd = GeneratedBinarySource.grammar.opcodes := by
  rfl

theorem opcode_pairs_valid : ∀ item ∈ opcodePairs, item.2.opcode ≤ 255 ∧
    (item.2.operands.map OperandLayout.role).Nodup := by decide

theorem codec_valid : GeneratedBinarySource.grammar.codec.Valid := by decide

theorem rewrite_definitions_exact : GeneratedBinarySource.canonicalSource.rewrites.mapM definition? =
    some (.codec GeneratedBinarySource.grammar.codec ::
      GeneratedBinarySource.grammar.opcodes.map Definition.opcode) := by
  rw [rewrite_inventory_encoded, List.mapM_cons,
    definition?_encodeCodec "word-spelling" _ codec_valid,
    definitionList?_encodedOpcodes opcodePairs opcode_pairs_valid]
  change some (.codec GeneratedBinarySource.grammar.codec ::
    opcodePairs.map (fun pair => Definition.opcode pair.2)) = _
  rw [← opcode_pairs_exact, List.map_map]
  rfl

theorem opcode_inventory_exact : GeneratedBinarySource.grammar.opcodes.map OpcodeLayout.opcode =
    List.range 26 := by decide

theorem opcode_identity_unique :
    (GeneratedBinarySource.grammar.opcodes.map OpcodeLayout.opcode).Nodup := by
  rw [opcode_inventory_exact]
  exact List.nodup_range

theorem opcode_ordered : GeneratedBinarySource.grammar.opcodes.Pairwise
    (fun left right => left.opcode ≤ right.opcode) := by decide

theorem grammar_assembled : assemble? (.codec GeneratedBinarySource.grammar.codec ::
    GeneratedBinarySource.grammar.opcodes.map Definition.opcode) =
      some GeneratedBinarySource.grammar := by
  apply assemble?_codec_sorted
  · decide
  · exact opcode_identity_unique
  · exact opcode_ordered

theorem admission_guard :
    (!(CanonicalSourceGSLT.compositionValid [GeneratedBinarySource.canonicalSource]) ||
      !GeneratedBinarySource.canonicalSource.equations.isEmpty ||
      !GeneratedBinarySource.canonicalSource.operators.all operatorAllowed ||
      !(GeneratedBinarySource.canonicalSource.operators.map
        (fun operator => (operator.name, operator.arity))).Nodup) = false := by
  rw [canonical_closed]
  cbv

theorem authored_binary_syntax_exact : admit? GeneratedBinarySource.binarySyntax =
    some GeneratedBinarySource.grammar := by
  unfold admit?
  rw [canonical_decoded]
  change classify? GeneratedBinarySource.canonicalSource = _
  unfold classify?
  rw [admission_guard]
  change (GeneratedBinarySource.canonicalSource.rewrites.mapM definition?).bind assemble? = _
  rw [rewrite_definitions_exact]
  change assemble? (.codec GeneratedBinarySource.grammar.codec ::
    GeneratedBinarySource.grammar.opcodes.map Definition.opcode) = _
  exact grammar_assembled

end Mettapedia.Languages.VibeITP.Native.BinarySyntaxAdmission
