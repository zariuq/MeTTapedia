import Mettapedia.GSLT.Parsing.ListValueSourceCodec
import Mettapedia.GSLT.Dynamics.AnswerDisplay

/-!
# List-aware answer payloads in the framed display protocol

This instantiates the answer display with the concrete bracket-token printer
and stack reader, rather than assuming a codec for complete answer transcripts.
The result retains ordered occurrences and completion status. Explicit bag and
support views can be taken afterwards; no universal answer effect is imposed.

The payload representation here is lexical tokens. It does not change a CLI
format or establish byte-level escaping or generated native-reader correctness.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.ListValueAnswerCodec

open Mettapedia.Logic.Unification.ListSplice
open Mettapedia.GSLT.Parsing.ListValueSourceCodec
open Mettapedia.GSLT.Dynamics.AnswerDisplay

variable {Leaf Var : Type}

def printAnswers? (values : List (Term Leaf Var)) (completion : Completion) :
    Option (List (Event (List (Token Leaf Var)))) :=
  encode printTokens? values completion

def readAnswers? : List (Event (List (Token Leaf Var))) →
    Option (List (Term Leaf Var) × Completion) :=
  decode (readOne? true)

theorem printAnswers_total (values : List (Term Leaf Var)) (completion : Completion) :
    ∃ events, printAnswers? values completion = some events :=
  encode_total printTokens? printTokens_total values completion

theorem read_printAnswers (values : List (Term Leaf Var)) (completion : Completion)
    (events : List (Event (List (Token Leaf Var))))
    (printed : printAnswers? values completion = some events) :
    readAnswers? events = some (values, completion) :=
  decode_encode printTokens? (readOne? true) readOne_print values completion events printed

theorem answers_round_trip (values : List (Term Leaf Var)) (completion : Completion) :
    (printAnswers? values completion >>= readAnswers?) = some (values, completion) := by
  obtain ⟨events, printed⟩ := printAnswers_total values completion
  simp [printed, read_printAnswers values completion events printed]

theorem printAnswers_injective (left right : List (Term Leaf Var))
    (leftStatus rightStatus : Completion) (events : List (Event (List (Token Leaf Var))))
    (leftPrinted : printAnswers? left leftStatus = some events)
    (rightPrinted : printAnswers? right rightStatus = some events) :
    left = right ∧ leftStatus = rightStatus :=
  encode_injective_on_domain printTokens? (readOne? true) readOne_print
    left right leftStatus rightStatus events leftPrinted rightPrinted

theorem no_answers :
    readAnswers? ([.finish .complete] : List (Event (List (Token Leaf Var)))) =
      some ([], .complete) := rfl

theorem one_empty_list :
    readAnswers? ([.answer [.openList, .closeList], .finish .complete] :
      List (Event (List (Token Leaf Var)))) = some ([.list []], .complete) := rfl

theorem one_empty_expression :
    readAnswers? ([.answer [.openExpr, .closeExpr], .finish .complete] :
      List (Event (List (Token Leaf Var)))) = some ([.expr []], .complete) := rfl

/-- The three empty-looking observations are genuinely different. -/
theorem empty_observations_distinct :
    ([] : List (Term Leaf Var)) ≠ [.list []] ∧
    ([] : List (Term Leaf Var)) ≠ [.expr []] ∧
    ([.list []] : List (Term Leaf Var)) ≠ [.expr []] := by
  constructor
  · intro h; cases h
  constructor
  · intro h; cases h
  · intro h; cases h

theorem one_list_answer (first second : Leaf) :
    readAnswers? [.answer [.openList, .atom first, .atom second, .closeList],
      .finish .complete] =
      some (([Term.list [Term.atom first, Term.atom second]] : List (Term Leaf Var)),
        .complete) := rfl

theorem two_atom_answers (first second : Leaf) :
    readAnswers? [.answer [.atom first], .answer [.atom second], .finish .complete] =
      some (([Term.atom first, Term.atom second] : List (Term Leaf Var)), .complete) := rfl

theorem duplicated_empty_list_answers :
    readAnswers? ([.answer [.openList, .closeList], .answer [.openList, .closeList],
      .finish .complete] : List (Event (List (Token Leaf Var)))) =
      some ([.list [], .list []], .complete) := rfl

theorem incomplete_empty_answer (reason : String) :
    readAnswers? ([.finish (.suspended reason)] : List (Event (List (Token Leaf Var)))) =
      some ([], .suspended reason) := rfl

/-- Brackets in a lexical payload do not become structural delimiters. -/
theorem bracket_symbol_payload :
    readAnswers? ([.answer [.atom "[a,b]"], .finish .complete] :
      List (Event (List (Token String String)))) =
      some ([.atom "[a,b]"], .complete) := rfl

theorem empty_frame_is_not_an_empty_list :
    readAnswers? ([.answer [], .finish .complete] :
      List (Event (List (Token Leaf Var)))) = none := rfl

#print axioms read_printAnswers
#print axioms answers_round_trip
#print axioms printAnswers_injective
#print axioms empty_observations_distinct

end Mettapedia.GSLT.Parsing.ListValueAnswerCodec
