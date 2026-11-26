import Mettapedia.GSLT.LanguageDef.NativeOpsCBodyTextAgreement
import Mettapedia.GSLT.LanguageDef.NativeOpsCLexAccumulator
import Lean.Elab.Command

/-!
# Checked lexical replay for the native C reader

A row proposes a source slice, its emitted token occurrences, and its lexical
boundaries. Each row is checked against the lexer with an empty history, then
transported to arbitrary histories. Joins require the two boundary states to
agree and keep the input and output orders.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps.NativeC

open Lean Elab Command

/-- A scan, a complete parse, and an accepted body comparison together
establish admission of the original character stream. -/
theorem text_body_agreement_of_parts {names : TypeNames} {representation : Representation}
    {characters : List Char} {tokens : List Token} {native : CFunction}
    {source : NativeOps.Function}
    (scanned : lex characters = .ok tokens)
    (parsed : function? (2 * tokens.length + 4) names tokens = some (native, []))
    (checked : bodyAgreement representation native source = true) :
    textBodyAgreement names representation characters source = true := by
  have read := (functionText_iff names characters native).mpr ⟨tokens, scanned, parsed⟩
  simpa only [textBodyAgreement, read] using checked

private def fieldIdent (site : Syntax) (row : Lean.Name) (field : String) : Ident :=
  mkIdentFrom site (row.appendAfter ("_" ++ field))

declare_syntax_cat nativeCLexPiece
syntax ident "(" term ")" "(" term ")" "(" term ")" "(" term ")" : nativeCLexPiece

/-- Elaborate bounded lexer checks for the supplied transition rows. -/
syntax (name := nativeCLexPieces) "native_c_lex_pieces " "["
  nativeCLexPiece,* "]" : command

elab_rules : command
  | `(command| native_c_lex_pieces [$rows:nativeCLexPiece,*]) => do
      for row in rows.getElems do
        match row with
        | `(nativeCLexPiece| $name:ident ($input:term) ($output:term) ($before:term) ($after:term)) =>
          withRef row do
            let field := fieldIdent name name.getId
            let chars := field "chars"
            let tokens := field "tokens"
            let start := field "before"
            let finish := field "after"
            let proof := field "checked"
            elabCommand (← `(def $chars : List Char := $input))
            elabCommand (← `(def $tokens : List Token := $output))
            elabCommand (← `(def $start : LexPoint := $before))
            elabCommand (← `(def $finish : LexPoint := $after))
            elabCommand (← `(theorem $proof : LexSegmentAgreement $start $finish $chars $tokens :=
              (segment_agreement_iff_empty_history $start $finish $chars $tokens).mpr
                (by decide +kernel)))
        | _ => throwUnsupportedSyntax

private def elaborateLexJoin (name left right : Ident) : CommandElabM Unit := do
  let field := fieldIdent name name.getId
  let leftField := fieldIdent left left.getId
  let rightField := fieldIdent right right.getId
  let chars := field "chars"
  let tokens := field "tokens"
  let start := field "before"
  let finish := field "after"
  let proof := field "checked"
  let leftChars := leftField "chars"
  let rightChars := rightField "chars"
  let leftTokens := leftField "tokens"
  let rightTokens := rightField "tokens"
  let leftStart := leftField "before"
  let rightFinish := rightField "after"
  let leftProof := leftField "checked"
  let rightProof := rightField "checked"
  elabCommand (← `(def $chars : List Char := $leftChars ++ $rightChars))
  elabCommand (← `(def $tokens : List Token := $leftTokens ++ $rightTokens))
  elabCommand (← `(def $start : LexPoint := $leftStart))
  elabCommand (← `(def $finish : LexPoint := $rightFinish))
  elabCommand (← `(theorem $proof : LexSegmentAgreement $start $finish $chars $tokens :=
    lex_segment_compose $leftProof $rightProof))

declare_syntax_cat nativeCLexJoin
syntax ident ident ident : nativeCLexJoin

/-- Compose previously checked slices in order, using their shared boundary. -/
syntax (name := nativeCLexJoins) "native_c_lex_joins " "["
  nativeCLexJoin,* "]" : command

elab_rules : command
  | `(command| native_c_lex_joins [$rows:nativeCLexJoin,*]) => do
      for row in rows.getElems do
        match row with
        | `(nativeCLexJoin| $name:ident $left:ident $right:ident) =>
          withRef row (elaborateLexJoin name left right)
        | _ => throwUnsupportedSyntax

private def indexedLexRow (stem : Ident) (index : Nat) : Ident :=
  let decimal := toString index
  mkIdentFrom stem (stem.getId.appendAfter ("_" ++ String.replicate (3 - decimal.length) '0' ++ decimal))

declare_syntax_cat nativeCLocalTokenRange
syntax num " to " num : nativeCLocalTokenRange

/-- Declare canonical generated temporary tokens over half-open intervals.
The literal is elaborated once per index for reuse in the checked slices. -/
syntax (name := nativeCLocalTokens) "native_c_local_tokens " ident " ["
  nativeCLocalTokenRange,* "]" : command

elab_rules : command
  | `(command| native_c_local_tokens $stem:ident [$ranges:nativeCLocalTokenRange,*]) => do
      for range in ranges.getElems do
        match range with
        | `(nativeCLocalTokenRange| $first:num to $last:num) =>
          withRef range do
            unless first.getNat < last.getNat do
              throwErrorAt range "a native C local token interval must be nonempty"
            for index in List.range' first.getNat (last.getNat - first.getNat) do
              let name := indexedLexRow stem index
              let literal : Term := ⟨(Syntax.mkStrLit s!"gslt_v{index}").raw⟩
              elabCommand (← `(private def $name : Token :=
                .identifier (native_c_characters% $literal)))
        | _ => throwUnsupportedSyntax

private def elaborateLexTree (pieceStem joinStem : Ident) (pieceOffset joinOffset width : Nat) :
    CommandElabM Ident := do
  if width ≤ 1 then
    return indexedLexRow pieceStem pieceOffset
  else
    let half := width / 2
    let left ← elaborateLexTree pieceStem joinStem pieceOffset joinOffset half
    let right ← elaborateLexTree pieceStem joinStem (pieceOffset + half)
      (joinOffset + (half - 1)) (width - half)
    let joined := indexedLexRow joinStem (joinOffset + (width - 2))
    elaborateLexJoin joined left right
    return joined
termination_by width
decreasing_by all_goals omega

/-- Compose a nonempty interval of checked slices in a balanced tree. Slice
numbers give their source order and join numbers follow postorder. Each join
uses the same boundary judgment as an explicit join row. -/
syntax (name := nativeCLexTree) "native_c_lex_tree " ident ident num : command

elab_rules : command
  | `(command| native_c_lex_tree $pieces:ident $joins:ident $count:num) => do
      if count.getNat == 0 then
        throwErrorAt count "a lexical replay tree requires at least one slice"
      let _ ← elaborateLexTree pieces joins 0 0 count.getNat

end Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
