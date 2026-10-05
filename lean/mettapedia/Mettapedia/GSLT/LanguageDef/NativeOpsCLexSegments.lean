import Mettapedia.GSLT.LanguageDef.NativeOpsCLex

/-!
# Accumulator-independent C lexer certificates

Each character block is checked against the original lexer transition with an
arbitrary prior token list. Composition uses list algebra, so a later block
never re-evaluates the complete accumulated source or token history.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps.NativeC

structure LexPoint where
  mode : LexMode
  currentRev : List Char
  fault : Option LexFault
  deriving DecidableEq, Repr

def LexPoint.state (point : LexPoint) (tokensRev : List Token) : LexState :=
  ⟨point.mode, point.currentRev, tokensRev, point.fault⟩

def initialPoint : LexPoint := ⟨.idle, [], none⟩

def LexSegmentAgreement (before after : LexPoint) (characters : List Char) (tokens : List Token) : Prop :=
  ∀ prior, characters.foldl step (before.state prior) = after.state (tokens.reverse ++ prior)

theorem lex_segment_empty (point : LexPoint) : LexSegmentAgreement point point [] [] := by
  intro prior
  rfl

theorem lex_segment_compose {before middle after : LexPoint}
    {first second : List Char} {firstTokens secondTokens : List Token}
    (firstChecked : LexSegmentAgreement before middle first firstTokens)
    (secondChecked : LexSegmentAgreement middle after second secondTokens) :
    LexSegmentAgreement before after (first ++ second) (firstTokens ++ secondTokens) := by
  intro prior
  rw [List.foldl_append, firstChecked, secondChecked]
  simp only [List.reverse_append, List.append_assoc]

/-- A finite sequence of checked blocks shares only the declared lexical
boundary. Each block's proof is independent of earlier token history. -/
theorem lex_segments_list (point : LexPoint) (pieces : List (List Char × List Token))
    (checked : ∀ piece ∈ pieces, LexSegmentAgreement point point piece.1 piece.2) :
    LexSegmentAgreement point point (pieces.flatMap Prod.fst) (pieces.flatMap Prod.snd) := by
  induction pieces with
  | nil => exact lex_segment_empty point
  | cons piece rest ih =>
      exact lex_segment_compose (checked piece (List.mem_cons_self))
        (ih (fun other member => checked other (List.mem_cons_of_mem _ member)))

theorem lex_checked_complete {characters : List Char} {tokens : List Token}
    (checked : LexSegmentAgreement initialPoint initialPoint characters tokens) :
    lex characters = .ok tokens := by
  have complete := checked []
  simp only [List.append_nil] at complete
  change finish (characters.foldl step (initialPoint.state [])) = .ok tokens
  rw [complete]
  simp only [initialPoint, LexPoint.state, finish, List.reverse_reverse]

/-- String pieces compose through the character-list join law, so a source
certificate need not reduce the entire decoded concatenation again. -/
theorem lex_completed_string_pieces (pieces : List (String × List Token))
    (scanned : List.Forall (fun piece =>
      piece.1.toList.foldl step initial = completed piece.2) pieces) :
    lex (String.join (pieces.map Prod.fst)).toList = .ok (pieces.flatMap Prod.snd) := by
  have characterScans : List.Forall (fun piece : List Char × List Token =>
      piece.1.foldl step initial = completed piece.2)
      (pieces.map (fun piece => (piece.1.toList, piece.2))) := by
    induction pieces with
    | nil => trivial
    | cons piece rest ih =>
        obtain ⟨first, remaining⟩ := (List.forall_cons _ piece rest).mp scanned
        exact (List.forall_cons _ _ _).mpr ⟨first, ih remaining⟩
  have combined := completed_pieces _ characterScans
  apply lex_of_completed
  simpa only [String.toList_join, List.flatMap_map, Function.comp_def] using combined

theorem comment_split_at_block_boundary :
    LexSegmentAgreement initialPoint ⟨.blockComment, [], none⟩ "x/*".toList [.identifier ['x']] := by
  intro prior
  rfl

theorem closing_comment_respects_prior_tokens :
    LexSegmentAgreement ⟨.blockComment, [], none⟩ initialPoint "body*/ y ".toList [.identifier ['y']] := by
  intro prior
  rfl

theorem split_comment_complete_lex : lex ("x/*".toList ++ "body*/ y ".toList) =
    .ok [.identifier ['x'], .identifier ['y']] :=
  lex_checked_complete (lex_segment_compose comment_split_at_block_boundary closing_comment_respects_prior_tokens)

theorem unfinished_comment_cannot_be_complete :
    lex "x/*".toList = .error .unfinishedComment := by decide +kernel

end Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
