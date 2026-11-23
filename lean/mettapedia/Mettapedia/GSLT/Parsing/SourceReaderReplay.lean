import Mettapedia.GSLT.Parsing.SourceScanSegments
import Mettapedia.GSLT.Parsing.SourceLexSegments
import Lean.Elab.Command

/-!
Tables of candidate transitions for the source reader. Row numbers determine the
names of the individual states and transitions. Each transition is checked
against the original reader, and adjacent transitions compose using the
scanner and lexer replay theorems.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.SourceReaderReplay

open Lean Elab Command
open Mettapedia.GSLT.Parsing.SourceScanSegments
open Mettapedia.GSLT.Parsing.SourceLexSegments

private def entry (anchor : Syntax) (stem : String) (index : Nat) : Ident :=
  let numeral := toString index
  let padded := String.ofList (List.replicate (3 - numeral.length) '0') ++ numeral
  mkIdentFrom anchor (Name.mkSimple (stem ++ "_" ++ padded))

declare_syntax_cat scanReplayRow
syntax str num num : scanReplayRow

/-- A row records the input segment, the resulting line, and the resulting
depth for a scan that is inside a plain form. -/
syntax (name := scanReplay) "source_scan_replay " num " [" scanReplayRow,* "]" : command

elab_rules : command
  | `(command| source_scan_replay $start:num [$rows:scanReplayRow,*]) => do
      for (row, offset) in rows.getElems.zipIdx do
        match row with
        | `(scanReplayRow| $segment:str $line:num $depth:num) =>
          withRef row do
            let index := start.getNat + offset
            let part := entry row "segment" index
            let buffer := entry row "reverse" index
            let nextBuffer := entry row "reverse" (index + 1)
            let state := entry row "state" index
            let nextState := entry row "state" (index + 1)
            let proof := entry row "step" index
            let line := quote line.getNat
            let depth := quote depth.getNat
            elabCommand (← `(def $part : String := $segment))
            elabCommand (← `(def $nextBuffer : List Char := ($part : String).toList.reverse ++ $buffer))
            elabCommand (← `(def $nextState : ScanState :=
              makeScanState $line $depth false false false true 1 $nextBuffer [] none))
            elabCommand (← `(theorem $proof :
              ($part : String).toList.foldl step $state = $nextState := by rfl))
        | _ => throwUnsupportedSyntax

declare_syntax_cat lexReplayRow
syntax str "[" str,* "]" : lexReplayRow

/-- A row records the resulting token buffer and the newly emitted tokens in
reverse order. The segment comes from the scanner table at the same index. -/
syntax (name := lexReplay) "source_lex_replay " num " [" lexReplayRow,* "]" : command

elab_rules : command
  | `(command| source_lex_replay $start:num [$rows:lexReplayRow,*]) => do
      for (row, offset) in rows.getElems.zipIdx do
        match row with
        | `(lexReplayRow| $buffer:str [$emitted:str,*]) =>
          withRef row do
            let index := start.getNat + offset
            let part := entry row "segment" index
            let current := entry row "current" index
            let nextCurrent := entry row "current" (index + 1)
            let tokens := entry row "reversedTokens" index
            let nextTokens := entry row "reversedTokens" (index + 1)
            let proof := entry row "step" index
            let currentText : TSyntax `term := ⟨buffer.raw⟩
            let output : Array (TSyntax `term) := emitted.getElems.map (fun item => ⟨item.raw⟩)
            elabCommand (← `(def $nextCurrent : List Char := ($currentText : String).toList.reverse))
            elabCommand (← `(def $nextTokens : List String := [$output,*] ++ $tokens))
            elabCommand (← `(theorem $proof (rest : List Char) :
              lex (($part : String).toList ++ rest) $current $tokens =
                lex rest $nextCurrent $nextTokens := by rfl))
        | _ => throwUnsupportedSyntax

private def suffixIndices (first last finish : TSyntax `num) : CommandElabM (List Nat) := do
  unless first.getNat ≤ last.getNat && last.getNat ≤ finish.getNat do
    throwErrorAt first "expected suffix indices first ≤ last ≤ ending"
  pure (List.range' first.getNat (last.getNat - first.getNat)).reverse

/-- Compose scanner transitions in the half-open interval with a certified
suffix at its upper endpoint. -/
syntax (name := scanReplaySuffix) "source_scan_suffix " num " to " num " ending " num : command

elab_rules : command
  | `(command| source_scan_suffix $first:num to $last:num ending $finish:num) => do
      let finalState := entry finish "state" finish.getNat
      for index in ← suffixIndices first last finish do
        let part := entry first "segment" index
        let state := entry first "state" index
        let nextState := entry first "state" (index + 1)
        let segmentList := entry first "segments" index
        let rest := entry first "segments" (index + 1)
        let transition := entry first "step" index
        let proof := entry first "tail" index
        let nextProof := entry first "tail" (index + 1)
        elabCommand (← `(def $segmentList : List String := $part :: $rest))
        elabCommand (← `(theorem $proof : scanSegments $state $segmentList = $finalState :=
          scanSegments_of_head $state $nextState $finalState
            $segmentList $part $rest rfl $transition $nextProof))

/-- Compose lexer transitions in the half-open interval with a certified
suffix at its upper endpoint. -/
syntax (name := lexReplaySuffix) "source_lex_suffix " num " to " num " ending " num : command

elab_rules : command
  | `(command| source_lex_suffix $first:num to $last:num ending $finish:num) => do
      let finalTokens := entry finish "reversedTokens" finish.getNat
      for index in ← suffixIndices first last finish do
        let part := entry first "segment" index
        let current := entry first "current" index
        let nextCurrent := entry first "current" (index + 1)
        let tokens := entry first "reversedTokens" index
        let nextTokens := entry first "reversedTokens" (index + 1)
        let transition := entry first "step" index
        let input := entry first "input" index
        let rest := entry first "input" (index + 1)
        let proof := entry first "tail" index
        let nextProof := entry first "tail" (index + 1)
        elabCommand (← `(def $input : List Char := ($part : String).toList ++ $rest))
        elabCommand (← `(theorem $proof : lex $input $current $tokens =
            ($finalTokens : List String).reverse :=
          lex_of_head $input ($part : String).toList $rest
            $current $nextCurrent $tokens $nextTokens
            ($finalTokens : List String).reverse rfl ($transition $rest) $nextProof))

end Mettapedia.GSLT.Parsing.SourceReaderReplay
