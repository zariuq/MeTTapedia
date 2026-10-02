import Mettapedia.GSLT.Parsing.BinaryRecordSource
import Mettapedia.GSLT.Parsing.SourceSExprAdmission
import Mettapedia.Languages.VibeITP.Native.GeneratedBinaryLex
import Mettapedia.Languages.VibeITP.Native.BinarySyntaxAdmission

/-!
Independent admission of the verbatim authored binary component. The exact
text factorization connects this component to the single authored package;
operational component admission remains a separate source boundary.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000
set_option Elab.async false
set_option synthInstance.maxSize 10000

namespace Mettapedia.Languages.VibeITP.Native.BinarySourceAdmission

open Mettapedia.GSLT.Parsing

theorem authored_binary_syntax_safe :
    SExprTokenRoundTrip.safe GeneratedBinarySource.binarySyntax := by
  simp only [GeneratedBinarySource.binarySyntax, SExprTokenRoundTrip.safe,
    SExprTokenRoundTrip.childrenSafe]
  decide

theorem authored_binary_source_parsed :
    Algorithms.MeTTa.Simple.Parser.parseSExprWithDetailed MeTTailCore.MeTTaSyntax.petta
      GeneratedBinarySource.authoredBinaryText = .ok GeneratedBinarySource.binarySyntax :=
  SourceSExprAdmission.parsed_of_forms GeneratedBinarySource.authoredBinaryText
    GeneratedBinarySource.binarySyntax GeneratedBinaryScan.split_forms_exact
    (SourceSExprAdmission.single_of_tokens GeneratedBinarySource.authoredBinaryText
      GeneratedBinarySource.binarySyntax authored_binary_syntax_safe
      GeneratedBinaryLex.tokenized_exact)

theorem authored_binary_syntax_exact :
    BinaryRecordSource.admit? GeneratedBinarySource.binarySyntax =
      some GeneratedBinarySource.grammar := BinarySyntaxAdmission.authored_binary_syntax_exact

theorem authored_binary_source_exact :
    BinaryRecordSource.binaryText? GeneratedBinarySource.authoredBinaryText =
      some GeneratedBinarySource.grammar :=
  BinaryRecordSource.binaryText?_of_parsed GeneratedBinarySource.authoredBinaryText
    GeneratedBinarySource.binarySyntax GeneratedBinarySource.grammar
    authored_binary_source_parsed authored_binary_syntax_exact

private theorem text_of_characters_factorization
    (source leading component trailing : List Char)
    (factorization : source = leading ++ component ++ trailing) :
    String.ofList source = String.ofList leading ++ String.ofList component ++
      String.ofList trailing := by
  rw [factorization, String.ofList_append, String.ofList_append]

theorem authored_characters_factorization : GeneratedBinarySource.authoredSourceChars =
    GeneratedBinarySource.authoredPrefixChars ++ GeneratedBinarySource.authoredBinaryChars ++
      GeneratedBinarySource.authoredSuffixChars := by rfl

theorem authored_text_factorization : GeneratedBinarySource.authoredSourceText =
    GeneratedBinarySource.authoredPrefixText ++ GeneratedBinarySource.authoredBinaryText ++
      GeneratedBinarySource.authoredSuffixText :=
  text_of_characters_factorization GeneratedBinarySource.authoredSourceChars
    GeneratedBinarySource.authoredPrefixChars GeneratedBinarySource.authoredBinaryChars
    GeneratedBinarySource.authoredSuffixChars authored_characters_factorization

theorem admitted_word_codec_valid : GeneratedBinarySource.grammar.codec.Valid :=
  BinarySyntaxAdmission.codec_valid

theorem admitted_opcode_inventory_exact :
    GeneratedBinarySource.grammar.opcodes.map BinaryRecordCodec.OpcodeLayout.opcode =
      List.range 26 := BinarySyntaxAdmission.opcode_inventory_exact

theorem admitted_opcode_identity_unique :
    (GeneratedBinarySource.grammar.opcodes.map BinaryRecordCodec.OpcodeLayout.opcode).Nodup := by
  rw [admitted_opcode_inventory_exact]
  exact List.nodup_range

end Mettapedia.Languages.VibeITP.Native.BinarySourceAdmission
