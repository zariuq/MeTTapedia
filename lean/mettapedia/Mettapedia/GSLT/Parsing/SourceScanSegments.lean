import Algorithms.MeTTa.Simple.Parser
import Batteries.Tactic.OpenPrivate
import Mathlib.Data.List.Basic
import Init.Data.String.Lemmas.Pattern.TakeDrop.Pred

/-!
Compositional replay of the existing source scanner. Segmenting the input
does not change the scanner, lexical state, source text, or acceptance rules.
Small independently checked transitions can therefore replace one expensive
closed reduction without replacing the source parser itself.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.SourceScanSegments

open private ProgramScanState stepScan parserDialectOf splitProgramForms from Algorithms.MeTTa.Simple.Parser
open private ProgramScanState.mk from Algorithms.MeTTa.Simple.Parser
open private pushChar finalizeCurr grammarLineCommentStartChar? grammarSExprOpenChar
  grammarSExprCloseChar from Algorithms.MeTTa.Simple.Parser

abbrev ScanState := ProgramScanState

def makeScanState (line depth : Nat) (inComment inString escaped started : Bool)
    (startLine : Nat) (currRev : List Char) (formsRev : List (Nat × String))
    (err : Option Algorithms.MeTTa.Simple.Parser.ParseError) : ScanState :=
  ProgramScanState.mk line depth inComment inString escaped started startLine currRev formsRev err

def initialScanState : ScanState := makeScanState 1 0 false false false false 1 [] [] none

def step (state : ScanState) (character : Char) : ScanState :=
  stepScan (parserDialectOf MeTTailCore.MeTTaSyntax.petta) state character

theorem close_single_form (line : Nat) (current : List Char) (source : String)
    (text : String.ofList (')' :: current).reverse = source)
    (trimmed : source.trimAscii.toString = source) (nonempty : source.isEmpty = false) :
    step (makeScanState line 1 false false false true 1 current [] none) ')' =
      makeScanState line 0 false false false false line [] [(1, source)] none := by
  simp only [step, stepScan, makeScanState, parserDialectOf, grammarLineCommentStartChar?,
    grammarSExprOpenChar, grammarSExprCloseChar, pushChar, finalizeCurr]
  simp only [text, trimmed, nonempty]
  rfl

theorem close_singleton_form (line : Nat) (current : List Char) (source : String)
    (text : String.ofList (')' :: current).reverse = source)
    (trimmed : source.trimAscii.toString = source) (nonempty : source.isEmpty = false) :
    [')'].foldl step (makeScanState line 1 false false false true 1 current [] none) =
      makeScanState line 0 false false false false line [] [(1, source)] none := by
  rw [List.foldl_cons, List.foldl_nil]
  exact close_single_form line current source text trimmed nonempty

def concatenate : List String → String
  | [] => ""
  | segment :: rest => segment ++ concatenate rest

theorem concatenate_singleton (segment : String) : concatenate [segment] = segment := by
  simp [concatenate]

theorem concatenate_append (left right : List String) :
    concatenate (left ++ right) = concatenate left ++ concatenate right := by
  induction left with
  | nil => simp [concatenate]
  | cons segment rest ih => simp [concatenate, ih, String.append_assoc]

theorem concatenate_ofList (segments : List String) :
    concatenate segments = String.ofList (segments.flatMap String.toList) := by
  induction segments with
  | nil => rfl
  | cons segment rest ih =>
      simp only [concatenate, List.flatMap_cons, String.ofList_append,
        String.ofList_toList, ih]

theorem trimAscii_of_boundary (source : String)
    (first : source.toList.head?.any Char.isWhitespace = false)
    (last : source.toList.getLast?.any Char.isWhitespace = false) :
    source.trimAscii.toString = source := by
  have start := String.dropWhile_eq_toSlice (pat := Char.isWhitespace)
    (s := source) (by rwa [String.startsWith_bool_eq_head?])
  have finish := String.dropEndWhile_eq_toSlice (pat := Char.isWhitespace)
    (s := source) (by rwa [String.endsWith_bool_eq_getLast?])
  simp only [String.trimAscii, String.Slice.trimAscii, String.Slice.trimAsciiStart,
    String.Slice.trimAsciiEnd, String.dropWhile_toSlice, start,
    String.dropEndWhile_toSlice, finish]
  exact String.copy_toSlice

theorem ofList_nonempty (characters : List Char) (nonempty : characters ≠ []) :
    (String.ofList characters).isEmpty = false := by
  rw [String.isEmpty_eq_false_iff]
  intro equal
  have lists := congrArg String.toList equal
  simp only [String.toList_ofList, String.toList_empty] at lists
  exact nonempty lists

inductive TextTree where
  | leaf (text : String)
  | branch (left right : TextTree)

def TextTree.leaves : TextTree → List String
  | .leaf text => [text]
  | .branch left right => left.leaves ++ right.leaves

def TextTree.value : TextTree → String
  | .leaf text => text
  | .branch left right => left.value ++ right.value

theorem TextTree.concatenate_leaves (tree : TextTree) :
    concatenate tree.leaves = tree.value := by
  induction tree with
  | leaf text => exact concatenate_singleton text
  | branch left right leftProof rightProof =>
      simp only [TextTree.leaves, TextTree.value, concatenate_append, leftProof, rightProof]

def scanSegments (state : ScanState) : List String → ScanState
  | [] => state
  | segment :: rest => scanSegments (segment.toList.foldl step state) rest

theorem scanSegments_of_head (state next final : ScanState)
    (segments : List String) (head : String) (tail : List String)
    (shape : segments = head :: tail)
    (transition : head.toList.foldl step state = next)
    (completed : scanSegments next tail = final) : scanSegments state segments = final := by
  rw [shape, scanSegments, transition]
  exact completed

theorem scanSegments_eq_foldl (segments : List String) (state : ScanState) :
    scanSegments state segments = (concatenate segments).toList.foldl step state := by
  induction segments generalizing state with
  | nil => rfl
  | cons segment rest ih =>
      simp only [scanSegments, concatenate, String.toList_append, List.foldl_append, ih]

theorem scanned_source_of_segments (source : String) (segments : List String)
    (state final : ScanState) (text : concatenate segments = source)
    (completed : scanSegments state segments = final) :
    source.toList.foldl step state = final := by
  rw [← text, ← scanSegments_eq_foldl]
  exact completed

theorem scanned_source_of_segments_initial (source : String) (segments : List String)
    (state final : ScanState) (initial : state = initialScanState)
    (text : concatenate segments = source)
    (completed : scanSegments state segments = final) :
    source.toList.foldl step initialScanState = final := by
  rw [← initial]
  exact scanned_source_of_segments source segments state final text completed

theorem concatenate_of_characters (source : String) (segments : List String)
    (characters : List Char) (sourceText : source = String.ofList characters)
    (exactCharacters : segments.flatMap String.toList = characters) :
    concatenate segments = source := by
  rw [sourceText, concatenate_ofList, exactCharacters]

theorem splitProgramForms_of_scanned (source : String) (line : Nat)
    (scanned : source.toList.foldl step initialScanState =
      makeScanState line 0 false false false false line [] [(1, source)] none) :
    splitProgramForms (parserDialectOf MeTTailCore.MeTTaSyntax.petta) source =
      .ok [(1, source)] := by
  have actualScanned : source.toList.foldl
      (stepScan (parserDialectOf MeTTailCore.MeTTaSyntax.petta)) initialScanState =
      makeScanState line 0 false false false false line [] [(1, source)] none := scanned
  unfold initialScanState makeScanState at actualScanned
  have emptyTrim : "".trimAscii.toString = "" := trimAscii_of_boundary "" rfl rfl
  have emptyFlag : "".trimAscii.isEmpty = true := by
    rw [← String.Slice.isEmpty_copy]
    change "".trimAscii.toString.isEmpty = true
    rw [emptyTrim]
    rfl
  unfold splitProgramForms
  rw [actualScanned]
  simp [finalizeCurr, emptyFlag]

theorem empty_segment_preserves_state (state : ScanState) :
    scanSegments state [""] = state := rfl

end Mettapedia.GSLT.Parsing.SourceScanSegments
