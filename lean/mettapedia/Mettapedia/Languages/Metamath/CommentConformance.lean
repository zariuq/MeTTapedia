import Mettapedia.Languages.Metamath.GroundedSemantics
import Mettapedia.Languages.Metamath.Fixtures
import Metamath.PrefixProvability.Checker

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

attribute [local cbv_opaque] Std.HashMap.insert Std.HashSet.insert
  Std.HashMap.toList Std.HashSet.toList
attribute [local cbv_eval] Metamath.Verify.ParserState.feed.eq_def
  Std.HashSet.forIn_eq_forIn_toList
  Std.HashMap.toList_emptyWithCapacity Std.HashSet.toList_emptyWithCapacity
  hashMap_insert_toList_all singletonHashSet_toList

set_option maxRecDepth 10000 in
theorem minimalAxiomWithInlineComment_parsedDB_eq :
    checkBytesDB minimalAxiomWithInlineCommentBytes = minimalAxiomDB := by
  cbv

/- Positive: inline comments are accepted and carry no parse error code. -/
example : (checkBytesDB minimalAxiomWithInlineCommentBytes).error = false := by
  rw [minimalAxiomWithInlineComment_parsedDB_eq]
  rfl

example : parseErrorCode? minimalAxiomWithInlineCommentBytes = none := by
  change (checkBytesDB minimalAxiomWithInlineCommentBytes).parseErrorCode? = none
  rw [minimalAxiomWithInlineComment_parsedDB_eq]
  rfl

example :
    (checkBytesDB minimalAxiomWithInlineCommentBytes).error =
      (checkBytesDB minimalAxiomBytes).error := by
  rw [minimalAxiomWithInlineComment_parsedDB_eq, minimalAxiomBytes_parsedDB_eq]

/- Negative: nested/unclosed comments are rejected with the expected codes. -/
example : (checkBytesDB nestedCommentDelimiterBytes).error = true := by
  decide +kernel

example :
    parseErrorCode? nestedCommentDelimiterBytes =
      some Metamath.Verify.ParseErrorCode.nestedCommentDelimiter := by
  decide +kernel

example : (checkBytesDB unclosedCommentBytes).error = true := by
  decide +kernel

example :
    parseErrorCode? unclosedCommentBytes =
      some Metamath.Verify.ParseErrorCode.unclosedComment := by
  decide +kernel

/- Bridge fact from mm-lean4 ghost semantics:
   comment wrappers are transparent for proof ghosts. -/
theorem proofGhost_comment_transparent
    (db : Metamath.Verify.DB) (p : Metamath.Verify.TokenParser) :
    Metamath.PrefixProvability.Checker.ProofGhost db (.comment p) =
      Metamath.PrefixProvability.Checker.ProofGhost db p := rfl

end Mettapedia.Languages.Metamath.CommentConformance
