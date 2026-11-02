import Mettapedia.GSLT.Parsing.SourceAccumulatorScan

/-! Closing and publishing checked scanner segments with preceding forms. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.SourceScanFinished

open SourceScanSegments SourceAccumulatorScan
open private stepScan parserDialectOf pushChar finalizeCurr grammarLineCommentStartChar?
  grammarSExprOpenChar grammarSExprCloseChar splitProgramForms ParserDialect.grammarSpec from Algorithms.MeTTa.Simple.Parser

theorem close_form (line start : Nat) (current : List Char) (forms : List (Nat × String)) (source : String)
    (text : String.ofList (')' :: current).reverse = source)
    (trimmed : source.trimAscii.toString = source) (nonempty : source.isEmpty = false) :
    step (makeScanState line 1 false false false true start current forms none) ')' =
      makeScanState line 0 false false false false line [] ((start, source) :: forms) none := by
  simp only [step, stepScan, makeScanState, parserDialectOf, grammarLineCommentStartChar?,
    grammarSExprOpenChar, grammarSExprCloseChar, pushChar, finalizeCurr]
  simp only [text, trimmed, nonempty]
  rfl

theorem scanned_form (start finish : Nat) (input retained : List Char) (source : String)
    (replay : Agreement ⟨start, 0, false, false, false, false, start⟩
      ⟨finish, 1, false, false, false, true, start⟩ input retained)
    (text : String.ofList (retained ++ [')']) = source)
    (trimmed : source.trimAscii.toString = source) (nonempty : source.isEmpty = false)
    (forms : List (Nat × String)) :
    (input ++ [')']).foldl step (makeScanState start 0 false false false false start [] forms none) =
      makeScanState finish 0 false false false false finish [] ((start, source) :: forms) none := by
  rw [List.foldl_append]
  have prefixRun := replay [] forms
  simp only [List.append_nil] at prefixRun
  dsimp only [Point.state] at prefixRun
  rw [prefixRun]
  simp only [List.foldl_cons, List.foldl_nil]
  apply close_form finish start retained.reverse forms source _ trimmed nonempty
  simpa only [List.reverse_cons, List.reverse_reverse] using text

theorem newline_between (line : Nat) (forms : List (Nat × String)) :
    step (makeScanState line 0 false false false false line [] forms none) '\n' =
      makeScanState (line + 1) 0 false false false false (line + 1) [] forms none := by
  have comment : grammarLineCommentStartChar? (ParserDialect.grammarSpec (parserDialectOf MeTTailCore.MeTTaSyntax.petta)) = some ';' := rfl
  have emptyTrim : "".trimAscii.toString = "" := trimAscii_of_boundary "" rfl rfl
  have emptyFlag : "".trimAscii.isEmpty = true := by
    rw [← String.Slice.isEmpty_copy]
    change "".trimAscii.toString.isEmpty = true
    rw [emptyTrim]
    rfl
  simp [step, stepScan, makeScanState, comment, finalizeCurr, emptyFlag]

theorem split_of_finished (source : String) (line : Nat) (forms : List (Nat × String))
    (scanned : source.toList.foldl step initialScanState =
      makeScanState line 0 false false false false line [] forms none) :
    splitProgramForms (parserDialectOf MeTTailCore.MeTTaSyntax.petta) source = .ok forms.reverse := by
  have actual : source.toList.foldl (stepScan (parserDialectOf MeTTailCore.MeTTaSyntax.petta)) initialScanState =
      makeScanState line 0 false false false false line [] forms none := scanned
  unfold initialScanState makeScanState at actual
  have emptyTrim : "".trimAscii.toString = "" := trimAscii_of_boundary "" rfl rfl
  have emptyFlag : "".trimAscii.isEmpty = true := by
    rw [← String.Slice.isEmpty_copy]
    change "".trimAscii.toString.isEmpty = true
    rw [emptyTrim]
    rfl
  unfold splitProgramForms
  rw [actual]
  simp [finalizeCurr, emptyFlag]

end Mettapedia.GSLT.Parsing.SourceScanFinished
