import Mettapedia.Languages.Metamath.MM2CompressedProofExecution
import Mettapedia.Languages.Metamath.SourceGSLTCompressedTheorem

/-!
# Authored-source agreement for compact MM2 compressed indices

This module is a comparison boundary.  The target remains independently
executable and does not import the source semantics; the theorems here relate
its compact index denotation to the authored Metamath decoder.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofSourceBridge

open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.SourceGSLTCompressedTheorem

/-- The source decoder's first terminal byte and the compact target code name
the same zero-based heap index. -/
theorem single_index_source_target_agree :
    decodeProgram [[65]] =
      some [.step (compressedIndexValue [] 0)] := by
  simpa only [compressedIndexCode_zero_value] using decode_single_index

/-- A prefix may cross lexical words without expansion.  The authored source
decoder and the compact target representation both denote index twenty. -/
theorem cross_word_index_source_target_agree :
    decodeProgram [[85], [65]] =
      some [.step (compressedIndexValue [1] 0)] := by
  simpa only [compressedIndexCode_twenty_value] using
    decode_multibyte_index_across_words

/-- The source rejects a proof ending inside an index; the target therefore
must retain its explicit incomplete-prefix fault rather than interpreting the
open prefix as a step. -/
theorem incomplete_prefix_source_rejects :
    decodeProgram [[85]] = none :=
  decode_incomplete_index_rejected

/-- The source assigns `?` its own incomplete-proof action.  The target agrees
by excluding it from the strict invalid-byte class and licensing it in the
between-steps phase. -/
theorem question_source_target_classification_agrees :
    decodeProgram [[63]] = some [.unknown] ∧
      compressedInvalidByteRow 63 ∉ compressedInvalidByteRows ∧
      compressedQuestionAllowedPhaseRow
          (.symbol "mm-compressed-between-steps") ∈
        compressedQuestionAllowedPhaseRows := by
  exact ⟨decode_unknown_is_explicit, by decide, by decide⟩

/-- Under the strict Appendix-B profile, a non-code byte is rejected by the
source decoder and is present in the target's explicit invalid-byte class. -/
theorem strict_invalid_byte_source_target_agrees :
    decodeProgram [[97]] = none ∧
      compressedInvalidByteRow 97 ∈ compressedInvalidByteRows := by
  exact ⟨decode_noncode_byte_rejected, by decide⟩

/-- A `Z` without a preceding completed proof step is rejected on both sides:
the source decoder returns none, while the target classifies between-steps as
a disallowed save phase. -/
theorem save_without_step_source_target_agrees :
    decodeProgram [[90]] = none ∧
      compressedSaveDisallowedPhaseRow
          (.symbol "mm-compressed-between-steps") ∈
        compressedSaveDisallowedPhaseRows := by
  exact ⟨decode_save_without_step_rejected, by decide⟩

#print axioms single_index_source_target_agree
#print axioms cross_word_index_source_target_agree
#print axioms incomplete_prefix_source_rejects
#print axioms question_source_target_classification_agrees
#print axioms strict_invalid_byte_source_target_agrees
#print axioms save_without_step_source_target_agrees

end Mettapedia.Languages.Metamath.MM2CompressedProofSourceBridge
