import Algorithms.MeTTa.Simple.Parser
import Batteries.Tactic.OpenPrivate

/-!
Composition rules for checked transitions of the existing MeTTa lexer.
The remaining input stays arbitrary in each transition, so segment boundaries
preserve the lexer's handling of tokens spanning more than one segment.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.SourceLexSegments

open private tokenizeAux tokenizeWith parserDialectOf from Algorithms.MeTTa.Simple.Parser

def lex (input currentRev : List Char) (tokensRev : List String) : List String :=
  tokenizeAux (some ';') '(' ')' '"' '\\' input false false currentRev tokensRev

theorem lex_of_head (input head rest current nextCurrent : List Char)
    (tokens nextTokens result : List String) (shape : input = head ++ rest)
    (transition : lex (head ++ rest) current tokens = lex rest nextCurrent nextTokens)
    (completed : lex rest nextCurrent nextTokens = result) :
    lex input current tokens = result := by
  rw [shape]
  exact transition.trans completed

theorem lex_empty (tokens : List String) : lex [] [] tokens = tokens.reverse := rfl

theorem tokenized_of_initial (source : String) (characters input current : List Char)
    (tokens result : List String) (sourceText : source = String.ofList characters)
    (inputCharacters : input = characters) (currentEmpty : current = [])
    (tokensEmpty : tokens = []) (completed : lex input current tokens = result) :
    tokenizeWith (parserDialectOf MeTTailCore.MeTTaSyntax.petta) source = result := by
  rw [sourceText]
  unfold tokenizeWith
  rw [String.toList_ofList]
  change lex characters [] [] = result
  rw [← inputCharacters, ← currentEmpty, ← tokensEmpty]
  exact completed

end Mettapedia.GSLT.Parsing.SourceLexSegments
