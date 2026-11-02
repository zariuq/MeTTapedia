import Mettapedia.GSLT.Parsing.SourceScanFinished
import Mettapedia.GSLT.Parsing.SourceAccumulatorLex
import Mettapedia.GSLT.Parsing.SourceSExprAdmission
import Mettapedia.GSLT.Parsing.SourceSExprSafety
import Mettapedia.Languages.MeTTa.PeTTa.ReadAfterRender
import Batteries.Data.Char.Basic

/-! Segmented checks of the retained CDLP callback and readout text.
Each replay uses the existing scanner and lexer over arbitrary histories. -/
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option Elab.async false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ModeSourceReplay
open Mettapedia.GSLT.Parsing
open SourceScanSegments SourceScanFinished
open Algorithms.MeTTa.Simple.Parser
open private splitProgramForms parserDialectOf tokenizeWith parseSingleSExprWith coalesceEvalPrefixForms ParserDialect.grammarSpec from Algorithms.MeTTa.Simple.Parser

@[local cbv_eval] private theorem getDHead {α : Type} (head : α) (tail : List α) (fallback : α) :
    (head :: tail).getD 0 fallback = head := rfl
@[local cbv_eval] private theorem getDEmpty {α : Type} (index : Nat) (fallback : α) :
    ([] : List α).getD index fallback = fallback := by simp
attribute [local cbv_opaque] List.getD

def sourceText : String := "(= (mode-step ($c $cn $b $bn) $x)\n   (if (== $x $c) ($c (+ $cn 1) $b $bn)\n       (if (> $cn $bn) ($x 1 $c $cn) ($x 1 $b $bn))))\n(= (mode $sorted)\n   (let ($c $cn $b $bn) (foldl-atom $sorted (none 0 none 0) $acc $x (mode-step $acc $x))\n     (if (> $cn $bn) $c $b)))"

def form1Prefix : List Char := [Char.ofNat 40, Char.ofNat 61, Char.ofNat 32, Char.ofNat 40, Char.ofNat 109, Char.ofNat 111, Char.ofNat 100, Char.ofNat 101, Char.ofNat 45, Char.ofNat 115, Char.ofNat 116, Char.ofNat 101, Char.ofNat 112, Char.ofNat 32, Char.ofNat 40, Char.ofNat 36, Char.ofNat 99, Char.ofNat 32, Char.ofNat 36, Char.ofNat 99, Char.ofNat 110, Char.ofNat 32, Char.ofNat 36, Char.ofNat 98, Char.ofNat 32, Char.ofNat 36, Char.ofNat 98, Char.ofNat 110, Char.ofNat 41, Char.ofNat 32, Char.ofNat 36, Char.ofNat 120, Char.ofNat 41, Char.ofNat 10, Char.ofNat 32, Char.ofNat 32, Char.ofNat 32, Char.ofNat 40, Char.ofNat 105, Char.ofNat 102, Char.ofNat 32, Char.ofNat 40, Char.ofNat 61, Char.ofNat 61, Char.ofNat 32, Char.ofNat 36, Char.ofNat 120, Char.ofNat 32, Char.ofNat 36, Char.ofNat 99, Char.ofNat 41, Char.ofNat 32, Char.ofNat 40, Char.ofNat 36, Char.ofNat 99, Char.ofNat 32, Char.ofNat 40, Char.ofNat 43, Char.ofNat 32, Char.ofNat 36, Char.ofNat 99, Char.ofNat 110, Char.ofNat 32, Char.ofNat 49, Char.ofNat 41, Char.ofNat 32, Char.ofNat 36, Char.ofNat 98, Char.ofNat 32, Char.ofNat 36, Char.ofNat 98, Char.ofNat 110, Char.ofNat 41, Char.ofNat 10, Char.ofNat 32, Char.ofNat 32, Char.ofNat 32, Char.ofNat 32, Char.ofNat 32, Char.ofNat 32, Char.ofNat 32, Char.ofNat 40, Char.ofNat 105, Char.ofNat 102, Char.ofNat 32, Char.ofNat 40, Char.ofNat 62, Char.ofNat 32, Char.ofNat 36, Char.ofNat 99, Char.ofNat 110, Char.ofNat 32, Char.ofNat 36, Char.ofNat 98, Char.ofNat 110, Char.ofNat 41, Char.ofNat 32, Char.ofNat 40, Char.ofNat 36, Char.ofNat 120, Char.ofNat 32, Char.ofNat 49, Char.ofNat 32, Char.ofNat 36, Char.ofNat 99, Char.ofNat 32, Char.ofNat 36, Char.ofNat 99, Char.ofNat 110, Char.ofNat 41, Char.ofNat 32, Char.ofNat 40, Char.ofNat 36, Char.ofNat 120, Char.ofNat 32, Char.ofNat 49, Char.ofNat 32, Char.ofNat 36, Char.ofNat 98, Char.ofNat 32, Char.ofNat 36, Char.ofNat 98, Char.ofNat 110, Char.ofNat 41, Char.ofNat 41, Char.ofNat 41]
def form1Chars : List Char := form1Prefix ++ [')']
def form1Text : String := String.ofList form1Chars
def form1Syntax : SExpr := .list [.atom "=", .list [.atom "mode-step", .list [.atom "$c", .atom "$cn", .atom "$b", .atom "$bn"], .atom "$x"], .list [.atom "if", .list [.atom "==", .atom "$x", .atom "$c"], .list [.atom "$c", .list [.atom "+", .atom "$cn", .atom "1"], .atom "$b", .atom "$bn"], .list [.atom "if", .list [.atom ">", .atom "$cn", .atom "$bn"], .list [.atom "$x", .atom "1", .atom "$c", .atom "$cn"], .list [.atom "$x", .atom "1", .atom "$b", .atom "$bn"]]]]

theorem form1Trimmed : form1Text.trimAscii.toString = form1Text := by
  apply trimAscii_of_boundary
  · rw [form1Text, String.toList_ofList]; rfl
  · rw [form1Text, String.toList_ofList, form1Chars, List.getLast?_concat]; rfl
theorem form1Nonempty : form1Text.isEmpty = false :=
  ofList_nonempty form1Chars (by intro impossible; have head := congrArg List.head? impossible; cases head)

theorem form1PrefixScan : SourceAccumulatorScan.Agreement
    ⟨1, 0, false, false, false, false, 1⟩ ⟨3, 1, false, false, false, true, 1⟩
    form1Prefix form1Prefix := by intro current forms; cbv
theorem form1Scanned (forms : List (Nat × String)) :
    form1Text.toList.foldl step (makeScanState 1 0 false false false false 1 [] forms none) =
      makeScanState 3 0 false false false false 3 [] ((1, form1Text) :: forms) none := by
  rw [form1Text, String.toList_ofList]
  exact scanned_form 1 3 form1Prefix form1Prefix form1Text form1PrefixScan rfl form1Trimmed form1Nonempty forms

theorem form1LexReplay : SourceAccumulatorLex.Agreement SourceAccumulatorLex.initialPoint SourceAccumulatorLex.initialPoint
    form1Chars (SExprTokenRoundTrip.tokens form1Syntax) := by intro rest tokens; cbv
theorem form1Tokenized : tokenizeWith (parserDialectOf MeTTailCore.MeTTaSyntax.petta) form1Text =
    SExprTokenRoundTrip.tokens form1Syntax := by
  exact SourceLexSegments.tokenized_of_initial form1Text form1Chars form1Chars [] []
    (SExprTokenRoundTrip.tokens form1Syntax) rfl rfl rfl rfl
    (SourceAccumulatorLex.original_lexer_replay _ _ form1LexReplay)
theorem form1Safe : SExprTokenRoundTrip.safe form1Syntax :=
  (SourceSExprSafety.safeBool_iff form1Syntax).mp (by decide +kernel)
theorem form1Parsed : parseSingleSExprWith (parserDialectOf MeTTailCore.MeTTaSyntax.petta) form1Text = .ok form1Syntax :=
  SourceSExprAdmission.single_of_tokens form1Text form1Syntax form1Safe form1Tokenized

theorem form1NoPrefix : form1Text.startsWith "!" = false := by
  apply Bool.eq_false_iff.mpr
  intro prefixed; rw [String.startsWith_string_iff] at prefixed
  simp [form1Text, form1Chars, form1Prefix] at prefixed
theorem form1NotBang : form1Text ≠ "!" := by
  intro same; have head := congrArg (fun text : String => text.toList.head?) same
  simp [form1Text, form1Chars, form1Prefix] at head

def form2Prefix : List Char := [Char.ofNat 40, Char.ofNat 61, Char.ofNat 32, Char.ofNat 40, Char.ofNat 109, Char.ofNat 111, Char.ofNat 100, Char.ofNat 101, Char.ofNat 32, Char.ofNat 36, Char.ofNat 115, Char.ofNat 111, Char.ofNat 114, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100, Char.ofNat 41, Char.ofNat 10, Char.ofNat 32, Char.ofNat 32, Char.ofNat 32, Char.ofNat 40, Char.ofNat 108, Char.ofNat 101, Char.ofNat 116, Char.ofNat 32, Char.ofNat 40, Char.ofNat 36, Char.ofNat 99, Char.ofNat 32, Char.ofNat 36, Char.ofNat 99, Char.ofNat 110, Char.ofNat 32, Char.ofNat 36, Char.ofNat 98, Char.ofNat 32, Char.ofNat 36, Char.ofNat 98, Char.ofNat 110, Char.ofNat 41, Char.ofNat 32, Char.ofNat 40, Char.ofNat 102, Char.ofNat 111, Char.ofNat 108, Char.ofNat 100, Char.ofNat 108, Char.ofNat 45, Char.ofNat 97, Char.ofNat 116, Char.ofNat 111, Char.ofNat 109, Char.ofNat 32, Char.ofNat 36, Char.ofNat 115, Char.ofNat 111, Char.ofNat 114, Char.ofNat 116, Char.ofNat 101, Char.ofNat 100, Char.ofNat 32, Char.ofNat 40, Char.ofNat 110, Char.ofNat 111, Char.ofNat 110, Char.ofNat 101, Char.ofNat 32, Char.ofNat 48, Char.ofNat 32, Char.ofNat 110, Char.ofNat 111, Char.ofNat 110, Char.ofNat 101, Char.ofNat 32, Char.ofNat 48, Char.ofNat 41, Char.ofNat 32, Char.ofNat 36, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 32, Char.ofNat 36, Char.ofNat 120, Char.ofNat 32, Char.ofNat 40, Char.ofNat 109, Char.ofNat 111, Char.ofNat 100, Char.ofNat 101, Char.ofNat 45, Char.ofNat 115, Char.ofNat 116, Char.ofNat 101, Char.ofNat 112, Char.ofNat 32, Char.ofNat 36, Char.ofNat 97, Char.ofNat 99, Char.ofNat 99, Char.ofNat 32, Char.ofNat 36, Char.ofNat 120, Char.ofNat 41, Char.ofNat 41, Char.ofNat 10, Char.ofNat 32, Char.ofNat 32, Char.ofNat 32, Char.ofNat 32, Char.ofNat 32, Char.ofNat 40, Char.ofNat 105, Char.ofNat 102, Char.ofNat 32, Char.ofNat 40, Char.ofNat 62, Char.ofNat 32, Char.ofNat 36, Char.ofNat 99, Char.ofNat 110, Char.ofNat 32, Char.ofNat 36, Char.ofNat 98, Char.ofNat 110, Char.ofNat 41, Char.ofNat 32, Char.ofNat 36, Char.ofNat 99, Char.ofNat 32, Char.ofNat 36, Char.ofNat 98, Char.ofNat 41, Char.ofNat 41]
def form2Chars : List Char := form2Prefix ++ [')']
def form2Text : String := String.ofList form2Chars
def form2Syntax : SExpr := .list [.atom "=", .list [.atom "mode", .atom "$sorted"], .list [.atom "let", .list [.atom "$c", .atom "$cn", .atom "$b", .atom "$bn"], .list [.atom "foldl-atom", .atom "$sorted", .list [.atom "none", .atom "0", .atom "none", .atom "0"], .atom "$acc", .atom "$x", .list [.atom "mode-step", .atom "$acc", .atom "$x"]], .list [.atom "if", .list [.atom ">", .atom "$cn", .atom "$bn"], .atom "$c", .atom "$b"]]]

theorem form2Trimmed : form2Text.trimAscii.toString = form2Text := by
  apply trimAscii_of_boundary
  · rw [form2Text, String.toList_ofList]; rfl
  · rw [form2Text, String.toList_ofList, form2Chars, List.getLast?_concat]; rfl
theorem form2Nonempty : form2Text.isEmpty = false :=
  ofList_nonempty form2Chars (by intro impossible; have head := congrArg List.head? impossible; cases head)

theorem form2PrefixScan : SourceAccumulatorScan.Agreement
    ⟨4, 0, false, false, false, false, 4⟩ ⟨6, 1, false, false, false, true, 4⟩
    form2Prefix form2Prefix := by intro current forms; cbv
theorem form2Scanned (forms : List (Nat × String)) :
    form2Text.toList.foldl step (makeScanState 4 0 false false false false 4 [] forms none) =
      makeScanState 6 0 false false false false 6 [] ((4, form2Text) :: forms) none := by
  rw [form2Text, String.toList_ofList]
  exact scanned_form 4 6 form2Prefix form2Prefix form2Text form2PrefixScan rfl form2Trimmed form2Nonempty forms

theorem form2LexReplay : SourceAccumulatorLex.Agreement SourceAccumulatorLex.initialPoint SourceAccumulatorLex.initialPoint
    form2Chars (SExprTokenRoundTrip.tokens form2Syntax) := by intro rest tokens; cbv
theorem form2Tokenized : tokenizeWith (parserDialectOf MeTTailCore.MeTTaSyntax.petta) form2Text =
    SExprTokenRoundTrip.tokens form2Syntax := by
  exact SourceLexSegments.tokenized_of_initial form2Text form2Chars form2Chars [] []
    (SExprTokenRoundTrip.tokens form2Syntax) rfl rfl rfl rfl
    (SourceAccumulatorLex.original_lexer_replay _ _ form2LexReplay)
theorem form2Safe : SExprTokenRoundTrip.safe form2Syntax :=
  (SourceSExprSafety.safeBool_iff form2Syntax).mp (by decide +kernel)
theorem form2Parsed : parseSingleSExprWith (parserDialectOf MeTTailCore.MeTTaSyntax.petta) form2Text = .ok form2Syntax :=
  SourceSExprAdmission.single_of_tokens form2Text form2Syntax form2Safe form2Tokenized

theorem form2NoPrefix : form2Text.startsWith "!" = false := by
  apply Bool.eq_false_iff.mpr
  intro prefixed; rw [String.startsWith_string_iff] at prefixed
  simp [form2Text, form2Chars, form2Prefix] at prefixed
theorem form2NotBang : form2Text ≠ "!" := by
  intro same; have head := congrArg (fun text : String => text.toList.head?) same
  simp [form2Text, form2Chars, form2Prefix] at head

theorem exact_characters : sourceText = form1Text ++ "\n" ++ form2Text := by decide +kernel
theorem scanned : sourceText.toList.foldl step initialScanState =
    makeScanState 6 0 false false false false 6 [] [(4, form2Text), (1, form1Text)] none := by
  rw [exact_characters, String.toList_append, String.toList_append, List.foldl_append, List.foldl_append]
  dsimp only [initialScanState]
  rw [form1Scanned]
  change form2Text.toList.foldl step (step (makeScanState 3 0 false false false false 3 [] [(1, form1Text)] none) '\n') = _
  rw [newline_between, form2Scanned]

theorem split_exact : splitProgramForms (parserDialectOf MeTTailCore.MeTTaSyntax.petta) sourceText =
    .ok [(1, form1Text), (4, form2Text)] := split_of_finished sourceText 6 _ scanned

theorem commands_exact : parseSExprCommandsWithDetailed MeTTailCore.MeTTaSyntax.petta sourceText =
    .ok [(1, false, form1Syntax), (4, false, form2Syntax)] := by
  have token : (ParserDialect.grammarSpec (parserDialectOf MeTTailCore.MeTTaSyntax.petta)).evalPrefixToken = "!" := rfl
  have coalesced : coalesceEvalPrefixForms (parserDialectOf MeTTailCore.MeTTaSyntax.petta)
      [(1, form1Text), (4, form2Text)] = [(1, form1Text), (4, form2Text)] := by
    have trimmed : form1Text.trimAscii.copy = form1Text := form1Trimmed
    simp [coalesceEvalPrefixForms, coalesceEvalPrefixForms.go, token, trimmed, form1NotBang]
  unfold parseSExprCommandsWithDetailed
  dsimp only
  rw [split_exact]
  simp only [bind, Except.bind]
  rw [coalesced]
  simp only [List.mapM_cons, List.mapM_nil]
  have firstNo : form1Text.startsWith (ParserDialect.grammarSpec (parserDialectOf MeTTailCore.MeTTaSyntax.petta)).evalPrefixToken = false :=
    by rw [token]; exact form1NoPrefix
  have secondNo : form2Text.startsWith (ParserDialect.grammarSpec (parserDialectOf MeTTailCore.MeTTaSyntax.petta)).evalPrefixToken = false :=
    by rw [token]; exact form2NoPrefix
  simp only [firstNo, secondNo, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
    form1Parsed, form2Parsed, Except.mapError]
  rfl

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ModeSourceReplay

