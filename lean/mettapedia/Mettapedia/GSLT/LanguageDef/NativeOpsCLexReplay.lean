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
          withRef row do
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
        | _ => throwUnsupportedSyntax

end Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
