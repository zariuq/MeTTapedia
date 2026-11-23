import Mettapedia.GSLT.Parsing.SourceAccumulatorScan

/-! Prefix checking for scanner steps that retain the pending form.
The history extension theorem supplies the universal statement for a closed
check on each recorded prefix. Form completion is checked separately. -/

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace Mettapedia.GSLT.Parsing.SourceAccumulatorScan

open SourceScanSegments
open private ProgramScanState stepScan parserDialectOf
  pushChar markStarted grammarLineCommentStartChar? grammarSExprOpenChar
  grammarSExprCloseChar from Algorithms.MeTTa.Simple.Parser
open private ProgramScanState.line ProgramScanState.depth
  ProgramScanState.inComment ProgramScanState.inString ProgramScanState.escaped
  ProgramScanState.started ProgramScanState.startLine ProgramScanState.currRev
  ProgramScanState.formsRev ProgramScanState.err from Algorithms.MeTTa.Simple.Parser

/-- Reattach previously accumulated characters and earlier forms. -/
def appendHistory (state : ScanState) (chars : List Char) (forms : List (Nat × String)) : ScanState :=
  makeScanState (ProgramScanState.line state) (ProgramScanState.depth state)
    (ProgramScanState.inComment state) (ProgramScanState.inString state)
    (ProgramScanState.escaped state) (ProgramScanState.started state)
    (ProgramScanState.startLine state) (ProgramScanState.currRev state ++ chars)
    (ProgramScanState.formsRev state ++ forms) (ProgramScanState.err state)

/-- The input does not finish and reset the pending form. -/
def keepsPending (state : ScanState) (character : Char) : Bool :=
  if (ProgramScanState.err state).isSome then true
  else if (ProgramScanState.inComment state) then !(character == '\n' && (ProgramScanState.depth state) == 0)
  else if (ProgramScanState.inString state) then true
  else if character = ';' then true
  else if character = '\n' then (ProgramScanState.depth state) != 0
  else if character = ')' then (ProgramScanState.depth state) != 1
  else true

theorem step_appendHistory (state : ScanState) (character : Char)
    (chars : List Char) (forms : List (Nat × String))
    (stable : keepsPending state character = true) :
    step (appendHistory state chars forms) character =
      appendHistory (step state character) chars forms := by
  obtain ⟨line, depth, comment, quoted, escaped, started, start, current, previous, error⟩ := state
  have commentStart :
      grammarLineCommentStartChar? MeTTailCore.MeTTaSyntax.petta.toGrammarSpec =
        some ';' := rfl
  have openChar :
      grammarSExprOpenChar MeTTailCore.MeTTaSyntax.petta.toGrammarSpec = '(' := rfl
  have closeChar :
      grammarSExprCloseChar MeTTailCore.MeTTaSyntax.petta.toGrammarSpec = ')' := rfl
  have sameComment : some ';' = some character ↔ character = ';' := by simp [eq_comm]
  simp only [keepsPending] at stable
  unfold step
  simp only [stepScan, appendHistory, makeScanState, commentStart, openChar, closeChar,
    parserDialectOf, sameComment]
  by_cases failed : error.isSome = true
  · simp [failed]
  simp only [failed, Bool.false_eq_true, if_false] at stable ⊢
  by_cases commenting : comment = true
  · simp only [commenting, if_true] at stable ⊢
    by_cases newline : character = '\n'
    · have nonzero : depth ≠ 0 := by simpa [newline] using stable
      simp [newline, nonzero]
    · simp [newline]
  simp only [commenting, Bool.false_eq_true, if_false] at stable ⊢
  by_cases quoting : quoted = true
  · simp only [quoting, if_true, pushChar]
    by_cases escaping : escaped = true
    · by_cases newline : character = '\n' <;> simp [escaping, newline]
    · by_cases escape : character = MeTTailCore.MeTTaSyntax.petta.lexer.escapeChar
      · simp [escaping, escape]
      · by_cases delimiter : character = MeTTailCore.MeTTaSyntax.petta.lexer.stringDelimiter
        · simp only [escaping, Bool.false_eq_true, if_false, if_neg escape, if_pos delimiter, List.cons_append]
        · by_cases newline : character = '\n'
          · simp only [escaping, Bool.false_eq_true, if_false, if_neg escape, if_neg delimiter, if_pos newline,
              List.cons_append]
          · simp only [escaping, Bool.false_eq_true, if_false, if_neg escape, if_neg delimiter, if_neg newline,
              List.cons_append]
  simp only [quoting, Bool.false_eq_true, if_false] at stable ⊢
  by_cases semicolon : character = ';'
  · simp [semicolon, pushChar]
  simp only [semicolon, if_false] at stable ⊢
  by_cases newline : character = '\n'
  · have nonzero : depth ≠ 0 := by simpa [newline] using stable
    simp [newline, nonzero, pushChar]
  simp only [newline, if_false] at stable ⊢
  by_cases delimiter : character = MeTTailCore.MeTTaSyntax.petta.lexer.stringDelimiter
  · cases started <;> simp [delimiter, markStarted, pushChar]
  simp only [delimiter, if_false]
  by_cases opening : character = '('
  · cases started <;> simp [opening, markStarted, pushChar]
  simp only [opening, if_false]
  by_cases closing : character = ')'
  · have notOne : depth ≠ 1 := by simpa [closing] using stable
    by_cases emptyDepth : depth = 0
    · simp [closing, emptyDepth]
    · have remainsOpen : depth - 1 ≠ 0 := by omega
      simp [closing, emptyDepth, remainsOpen, pushChar]
  · by_cases whitespace : character.isWhitespace = true <;>
      cases started <;> simp [closing, whitespace, markStarted, pushChar]

def scanPending : ScanState → List Char → Option ScanState
  | state, [] => some state
  | state, character :: rest =>
      if keepsPending state character then scanPending (step state character) rest else none

theorem scanPending_appendHistory (input : List Char) (start result : ScanState)
    (chars : List Char) (forms : List (Nat × String))
    (replay : scanPending start input = some result) :
    input.foldl step (appendHistory start chars forms) =
      appendHistory result chars forms := by
  induction input generalizing start with
  | nil =>
      simp only [scanPending, Option.some.injEq] at replay
      subst start
      rfl
  | cons character rest ih =>
      unfold scanPending at replay
      split at replay
      · rename_i stable
        rw [List.foldl_cons, step_appendHistory start character chars forms stable]
        exact ih _ replay
      · contradiction

/-- A checked prefix returns its boundary point and the reversed characters
it retained. A completed form or scanner error requires a separate receipt. -/
def pendingResult (point : Point) (input : List Char) : Option (Point × List Char) := do
  let state ← scanPending (point.state [] []) input
  if (ProgramScanState.err state).isNone && (ProgramScanState.formsRev state).isEmpty then
    some (⟨ProgramScanState.line state, ProgramScanState.depth state,
      ProgramScanState.inComment state, ProgramScanState.inString state,
      ProgramScanState.escaped state, ProgramScanState.started state,
      ProgramScanState.startLine state⟩, ProgramScanState.currRev state)
  else none

private theorem pendingResult_sound (before after : Point) (input expected : List Char)
    (checked : pendingResult before input = some (after, expected)) :
    scanPending (before.state [] []) input = some (after.state expected []) := by
  unfold pendingResult at checked
  cases result : scanPending (before.state [] []) input with
  | none => simp [result] at checked
  | some state =>
      obtain ⟨line, depth, comment, quoted, escaped, started, start, current, forms, error⟩ := state
      cases error <;> cases forms <;> simp [result] at checked
      obtain ⟨rfl, rfl⟩ := checked
      rfl

theorem agreement_of_pendingResult (before after : Point) (input retained : List Char)
    (checked : pendingResult before input = some (after, retained.reverse)) :
    Agreement before after input retained := by
  intro current forms
  have replay := pendingResult_sound before after input retained.reverse checked
  have frames := scanPending_appendHistory input _ _ current forms replay
  simpa only [appendHistory, Point.state, makeScanState, List.nil_append] using frames

example : pendingResult initialPoint ['('] =
    some ({ initialPoint with depth := 1, started := true }, ['(']) := by decide +kernel

example : pendingResult (closingPoint 1) [')'] = none := by decide +kernel

end Mettapedia.GSLT.Parsing.SourceAccumulatorScan
