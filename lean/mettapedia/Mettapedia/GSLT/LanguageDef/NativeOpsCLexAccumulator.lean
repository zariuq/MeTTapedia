import Mettapedia.GSLT.LanguageDef.NativeOpsCLexSegments

/-!
# Closed certificates for accumulator-independent C lexer segments

The lexer only prepends emitted tokens. Appending an existing token history
therefore commutes with every character transition and with a complete scan.
A segment can be checked with an empty history and then reused for any prior
history, without evaluating a symbolic accumulator in each generated proof.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps.NativeC

def appendTokenHistory (state : LexState) (history : List Token) : LexState :=
  { state with tokensRev := state.tokensRev ++ history }

theorem idle_append_token_history (state : LexState) (history : List Token) (character : Char) :
    idle (appendTokenHistory state history) character =
      appendTokenHistory (idle state character) history := by
  unfold idle
  split_ifs <;> rfl

theorem step_append_token_history (state : LexState) (history : List Token) (character : Char) :
    step (appendTokenHistory state history) character =
      appendTokenHistory (step state character) history := by
  cases state with
  | mk mode current tokens fault =>
      cases mode <;> dsimp only [step, appendTokenHistory]
      all_goals split_ifs
      all_goals first | rfl | (dsimp only [idle, emit]; split_ifs <;> rfl)

theorem scan_append_token_history (state : LexState) (history : List Token)
    (characters : List Char) :
    characters.foldl step (appendTokenHistory state history) =
      appendTokenHistory (characters.foldl step state) history := by
  induction characters generalizing state with
  | nil => rfl
  | cons character rest ih =>
      simp only [List.foldl_cons, step_append_token_history, ih]

theorem segment_agreement_iff_empty_history (before after : LexPoint)
    (characters : List Char) (tokens : List Token) :
    LexSegmentAgreement before after characters tokens ↔
      characters.foldl step (before.state []) = after.state tokens.reverse := by
  constructor
  · intro checked
    simpa only [List.append_nil] using checked []
  · intro checked history
    change characters.foldl step (appendTokenHistory (before.state []) history) = _
    rw [scan_append_token_history, checked]
    rfl

/-- A split inside a comment preserves all earlier emitted tokens. -/
theorem closed_comment_segment_has_arbitrary_history :
    LexSegmentAgreement ⟨.blockComment, [], none⟩ initialPoint
      ['*', '/', 'x', ' '] [.identifier ['x']] := by
  apply (segment_agreement_iff_empty_history _ _ _ _).mpr
  decide +kernel

/-- A wrong emitted token cannot pass a closed segment certificate. -/
theorem closed_segment_rejects_extra_token :
    ¬ LexSegmentAgreement initialPoint initialPoint ['x', ' ']
      [.identifier ['x'], .identifier ['y']] := by
  rw [segment_agreement_iff_empty_history]
  decide +kernel

end Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
