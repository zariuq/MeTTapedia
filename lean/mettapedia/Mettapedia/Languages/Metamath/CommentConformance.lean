import Mettapedia.Languages.Metamath.GroundedSemantics
import Mettapedia.Languages.Metamath.Fixtures
import Metamath.PrefixWitnessCheckBytes

/-!
# Metamath Comment Conformance (Grounded to mm-lean4)

This module pins comment behavior to the verified `mm-lean4` parser semantics.
-/

namespace Mettapedia.Languages.Metamath.CommentConformance

open Mettapedia.Languages.Metamath.GroundedSemantics
open Mettapedia.Languages.Metamath.Fixtures

def minimalAxiomWithInlineCommentBytes : ByteArray :=
  "$c wff $. $( hello $) $v ph $. wph $f wff ph $. ax1 $a wff ph $.".toUTF8

def nestedCommentDelimiterBytes : ByteArray := "$( bad $( nested $) $)".toUTF8

def unclosedCommentBytes : ByteArray := "$( unclosed".toUTF8

/- Positive: inline comments are accepted and carry no parse error code. -/
example : (checkBytesDB minimalAxiomWithInlineCommentBytes).error = false := by
  native_decide

example : parseErrorCode? minimalAxiomWithInlineCommentBytes = none := by
  native_decide

example :
    (checkBytesDB minimalAxiomWithInlineCommentBytes).error =
      (checkBytesDB minimalAxiomBytes).error := by
  native_decide

/- Negative: nested/unclosed comments are rejected with the expected codes. -/
example : (checkBytesDB nestedCommentDelimiterBytes).error = true := by
  native_decide

example :
    parseErrorCode? nestedCommentDelimiterBytes =
      some Metamath.Verify.ParseErrorCode.nestedCommentDelimiter := by
  native_decide

example : (checkBytesDB unclosedCommentBytes).error = true := by
  native_decide

example :
    parseErrorCode? unclosedCommentBytes =
      some Metamath.Verify.ParseErrorCode.unclosedComment := by
  native_decide

/- Bridge fact from mm-lean4 ghost semantics:
   comment wrappers are transparent for proof ghosts. -/
theorem proofGhost_comment_transparent
    (db : Metamath.Verify.DB) (p : Metamath.Verify.TokenParser) :
    Metamath.PrefixWitnessCheckBytes.ProofGhost db (.comment p) =
      Metamath.PrefixWitnessCheckBytes.ProofGhost db p := rfl

end Mettapedia.Languages.Metamath.CommentConformance
