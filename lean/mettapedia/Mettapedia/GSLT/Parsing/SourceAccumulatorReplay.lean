import Mettapedia.GSLT.Parsing.SourcePendingScan
import Mettapedia.GSLT.Parsing.SourceLexPrefix
import Lean.Elab.Command

/-! Candidate tables for the scanner and quoted lexer. Each row is checked
against the original reader, and checked transitions compose over arbitrary
history and remaining input. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.SourceAccumulatorReplay

open Lean Elab Command

private def entry (anchor : Syntax) (stem : String) (index : Nat) : Ident :=
  let digits := toString index
  let padded := String.ofList (List.replicate (3 - digits.length) '0') ++ digits
  mkIdentFrom anchor (Name.mkSimple (stem ++ "_" ++ padded))

private def indices (first last finish : TSyntax `num) : CommandElabM (List Nat) := do
  unless first.getNat ≤ last.getNat && last.getNat ≤ finish.getNat do
    throwErrorAt first "expected indices first ≤ last ≤ ending"
  pure (List.range' first.getNat (last.getNat - first.getNat))

section Scan
open SourceAccumulatorScan

declare_syntax_cat accumulatorScanPoint
syntax num num term:max term:max : accumulatorScanPoint

/-- A source row gives the current line, depth, quote flag, and start flag.
The corresponding transition checks the other boundary fields as well. -/
syntax (name := scanPoints) "accumulator_scan_points " num " ["
  accumulatorScanPoint,* "]" : command

elab_rules : command
  | `(command| accumulator_scan_points $start:num [$rows:accumulatorScanPoint,*]) => do
      for (row, offset) in rows.getElems.zipIdx do
        match row with
        | `(accumulatorScanPoint| $line:num $depth:num $quoted:term $started:term) =>
          withRef row do
            let point := entry row "point" (start.getNat + offset)
            elabCommand (← `(def $point : Point :=
              ⟨$line, $depth, false, $quoted, false, $started, 1⟩))
        | _ => throwUnsupportedSyntax

/-- Check the half-open interval of scanner transitions using the source
chunks at those indices. The final chunk excludes the closing character. -/
syntax (name := scanRows) "accumulator_scan_rows " num " to " num " ending " num : command

elab_rules : command
  | `(command| accumulator_scan_rows $first:num to $last:num ending $finish:num) => do
      for index in ← indices first last finish do
        let point := entry first "point" index
        let next := entry first "point" (index + 1)
        let block := entry first "block" index
        let step := entry first "step" index
        let chars := if index + 1 == finish.getNat then
            mkIdentFrom first `lastPrefixChars
          else entry first "componentChars" index
        elabCommand (← `(def $block : List Char := $chars))
        elabCommand (← `(theorem $step : Agreement $point $next $block $block :=
          agreement_of_pendingResult $point $next $block $block (by decide +kernel)))

/-- Compose the scanner suffixes in this interval. Its upper endpoint must
already have a checked suffix. -/
syntax (name := scanSuffixes) "accumulator_scan_suffix " num " to " num " ending " num : command

elab_rules : command
  | `(command| accumulator_scan_suffix $first:num to $last:num ending $finish:num) => do
      let final := entry finish "point" finish.getNat
      for index in (← indices first last finish).reverse do
        let point := entry first "point" index
        let next := entry first "point" (index + 1)
        let block := entry first "block" index
        let entireBlock := entry first "componentChars" index
        let step := entry first "step" index
        let scannedPrefix := entry first "prefix" index
        let tail := entry first "prefix" (index + 1)
        let replay := entry first "replay" index
        let nextReplay := entry first "replay" (index + 1)
        let source := entry first "sourceSuffix" index
        let sourceTail := entry first "sourceSuffix" (index + 1)
        let closing := entry first "closing" index
        let nextClosing := entry first "closing" (index + 1)
        elabCommand (← `(def $scannedPrefix : List Char := $block ++ $tail))
        elabCommand (← `(theorem $replay : Agreement $point $final $scannedPrefix $scannedPrefix :=
          agreement_append $point $next $final $block $tail $block $tail $step $nextReplay))
        elabCommand (← `(def $source : List Char := $entireBlock ++ $sourceTail))
        if index + 1 == finish.getNat then
          elabCommand (← `(theorem $closing : $scannedPrefix ++ [')'] = $source := rfl))
        else
          elabCommand (← `(theorem $closing : $scannedPrefix ++ [')'] = $source :=
            (List.append_assoc $block $tail [')']).trans
              (congrArg (fun rest => $block ++ rest) $nextClosing)))

end Scan

section Lex
open SourceAccumulatorLex

declare_syntax_cat accumulatorLexRow
syntax term:max term:max str "[" str,* "]" : accumulatorLexRow

/-- The next quote and escape flags, the unfinished token, and the newly
emitted tokens. All fields are checked, including the unfinished token. -/
syntax (name := lexRows) "accumulator_lex_rows " num " ["
  accumulatorLexRow,* "]" : command

elab_rules : command
  | `(command| accumulator_lex_rows $start:num [$rows:accumulatorLexRow,*]) => do
      for (row, offset) in rows.getElems.zipIdx do
        match row with
        | `(accumulatorLexRow| $quoted:term $escaped:term $current:str [$emitted:str,*]) =>
          withRef row do
            let index := start.getNat + offset
            let point := entry row "point" index
            let next := entry row "point" (index + 1)
            let chars := entry row "componentChars" index
            let tokens := entry row "emitted" index
            let proof := entry row "step" index
            let current : TSyntax `term := ⟨current.raw⟩
            let output : Array (TSyntax `term) := emitted.getElems.map (fun item => ⟨item.raw⟩)
            elabCommand (← `(def $next : Point :=
              ⟨$quoted, $escaped, ($current : String).toList.reverse⟩))
            elabCommand (← `(def $tokens : List String := [$output,*]))
            elabCommand (← `(theorem $proof : Agreement $point $next $chars $tokens :=
              agreement_of_prefix (by decide +kernel)))
        | _ => throwUnsupportedSyntax

/-- Compose the lexer suffixes in this interval. Its upper endpoint must
already have a checked suffix. -/
syntax (name := lexSuffixes) "accumulator_lex_suffix " num " to " num " ending " num : command

elab_rules : command
  | `(command| accumulator_lex_suffix $first:num to $last:num ending $finish:num) => do
      let final := entry finish "point" finish.getNat
      for index in (← indices first last finish).reverse do
        let point := entry first "point" index
        let next := entry first "point" (index + 1)
        let chars := entry first "componentChars" index
        let emitted := entry first "emitted" index
        let input := entry first "input" index
        let rest := entry first "input" (index + 1)
        let tokens := entry first "tokens" index
        let tokenTail := entry first "tokens" (index + 1)
        let step := entry first "step" index
        let replay := entry first "replay" index
        let nextReplay := entry first "replay" (index + 1)
        elabCommand (← `(def $input : List Char := $chars ++ $rest))
        elabCommand (← `(def $tokens : List String := $emitted ++ $tokenTail))
        elabCommand (← `(theorem $replay : Agreement $point $final $input $tokens :=
          agreement_append $point $next $final $chars $rest $emitted $tokenTail $step $nextReplay))

end Lex
end Mettapedia.GSLT.Parsing.SourceAccumulatorReplay
