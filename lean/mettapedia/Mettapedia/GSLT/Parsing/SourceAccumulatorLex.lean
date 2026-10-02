import Mettapedia.GSLT.Parsing.SourceLexSegments
import Batteries.Tactic.OpenPrivate

/-!
Quoted-state replay of the original carrier lexer. Each transition is checked
over arbitrary remaining input and arbitrary preceding tokens. Only the
unfinished token belongs to a boundary point; historical token lists never
need to be reduced by a later transition.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.SourceAccumulatorLex

open private tokenizeAux from Algorithms.MeTTa.Simple.Parser

structure Point where
  inString : Bool
  escaped : Bool
  currentRev : List Char
  deriving DecidableEq, Repr

def initialPoint : Point := ⟨false, false, []⟩

def run (point : Point) (input : List Char) (tokensRev : List String) : List String :=
  tokenizeAux (some ';') '(' ')' '"' '\\' input point.inString point.escaped
    point.currentRev tokensRev

def Agreement (before after : Point) (input : List Char) (emitted : List String) : Prop :=
  ∀ rest tokens, run before (input ++ rest) tokens =
    run after rest (emitted.reverse ++ tokens)

theorem agreement_append (before middle after : Point)
    (firstInput secondInput : List Char) (firstEmitted secondEmitted : List String)
    (first : Agreement before middle firstInput firstEmitted)
    (second : Agreement middle after secondInput secondEmitted) :
    Agreement before after (firstInput ++ secondInput) (firstEmitted ++ secondEmitted) := by
  intro rest tokens
  rw [List.append_assoc, first (secondInput ++ rest) tokens,
    second rest (firstEmitted.reverse ++ tokens)]
  simp only [List.reverse_append, List.append_assoc]

theorem agreement_empty (point : Point) : Agreement point point [] [] := by
  intro rest tokens
  rfl

theorem run_empty_initial (tokens : List String) : run initialPoint [] tokens = tokens.reverse := rfl

theorem complete_replay (input : List Char) (emitted : List String)
    (replay : Agreement initialPoint initialPoint input emitted) :
    run initialPoint input [] = emitted := by
  have complete := replay [] []
  simpa only [List.append_nil, run_empty_initial, List.reverse_reverse] using complete

theorem original_lexer_replay (input : List Char) (emitted : List String)
    (replay : Agreement initialPoint initialPoint input emitted) :
    SourceLexSegments.lex input [] [] = emitted :=
  complete_replay input emitted replay

end Mettapedia.GSLT.Parsing.SourceAccumulatorLex
