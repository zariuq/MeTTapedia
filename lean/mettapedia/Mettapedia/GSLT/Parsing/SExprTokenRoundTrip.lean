import Algorithms.MeTTa.Simple.Parser
import Batteries.Tactic.OpenPrivate
import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
Token-level round trip for the existing source parser. Fuel is bounded by
the concrete token count and remains independent of expression depth. Lexical
source admission is a separate boundary; this theorem does not treat a token
array as evidence that particular source bytes were lexed correctly.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.SExprTokenRoundTrip

open Algorithms.MeTTa.Simple.Parser (SExpr ParseError)
open private parseSExprOneFuel parseSExprListFuel from Algorithms.MeTTa.Simple.Parser
open private parseSExprOneFuel.eq_3 parseSExprOneFuel.eq_5
  parseSExprListFuel.eq_3 parseSExprListFuel.eq_4 from Algorithms.MeTTa.Simple.Parser

mutual
def tokens : SExpr → List String
  | .atom token => [token]
  | .list children => "(" :: childTokens children ++ [")"]

def childTokens : List SExpr → List String
  | [] => []
  | child :: rest => tokens child ++ childTokens rest
end

theorem tokens_positive (expression : SExpr) : 0 < (tokens expression).length := by
  cases expression <;> simp [tokens]

mutual
def safe : SExpr → Prop
  | .atom token => token ≠ "(" ∧ token ≠ ")"
  | .list children => childrenSafe children

def childrenSafe : List SExpr → Prop
  | [] => True
  | child :: rest => safe child ∧ childrenSafe rest
end

private theorem parse_by_fuel (fuel : Nat) :
    (∀ expression : SExpr, safe expression → ∀ rest : List String,
      (tokens expression).length < fuel →
      parseSExprOneFuel fuel (tokens expression ++ rest) = .ok (expression, rest)) ∧
    (∀ children : List SExpr, childrenSafe children → ∀ rest : List String,
      ∀ accRev : List SExpr, (childTokens children).length + 1 < fuel →
      parseSExprListFuel accRev fuel (childTokens children ++ ")" :: rest) =
        .ok (.list (accRev.reverse ++ children), rest)) := by
  induction fuel with
  | zero =>
      constructor
      · intro expression valid rest enough
        omega
      · intro children valid rest accRev enough
        omega
  | succ fuel ih =>
      constructor
      · intro expression valid rest enough
        cases expression with
        | atom token =>
            simp only [safe] at valid
            exact parseSExprOneFuel.eq_5 fuel token rest valid.1 valid.2
        | list children =>
            have bound : (childTokens children).length + 1 < fuel := by
              simp [tokens] at enough
              omega
            rw [show tokens (.list children) ++ rest =
              "(" :: (childTokens children ++ ")" :: rest) by
                simp [tokens, List.append_assoc]]
            rw [parseSExprOneFuel.eq_3]
            simpa using
              ih.2 children valid rest [] bound
      · intro children valid rest accRev enough
        cases children with
        | nil =>
            simpa only [childTokens, List.nil_append, List.append_nil] using
              parseSExprListFuel.eq_3 accRev fuel rest
        | cons child children =>
            have positive := tokens_positive child
            have childBound : (tokens child).length < fuel := by
              simp [childTokens] at enough
              omega
            have restBound : (childTokens children).length + 1 < fuel := by
              simp [childTokens] at enough
              omega
            have first := ih.1 child valid.1 (childTokens children ++ ")" :: rest) childBound
            have tail := ih.2 children valid.2 rest (child :: accRev) restBound
            have unfoldStep :
                parseSExprListFuel accRev (fuel + 1)
                    (tokens child ++ (childTokens children ++ ")" :: rest)) =
                  (do
                    let (value, remaining) ← parseSExprOneFuel fuel
                      (tokens child ++ (childTokens children ++ ")" :: rest))
                    parseSExprListFuel (value :: accRev) fuel remaining) := by
              apply parseSExprListFuel.eq_4
              · intro empty
                have positive : 0 <
                    (tokens child ++ (childTokens children ++ ")" :: rest)).length := by
                  simp only [List.length_append]
                  omega
                simp [empty] at positive
              · intro remaining same
                cases child with
                | atom token =>
                    have notClose : token ≠ ")" := valid.1.2
                    exact notClose (List.cons.inj same).1
                | list nested =>
                    have head : "(" = ")" := (List.cons.inj same).1
                    contradiction
            rw [show childTokens (child :: children) ++ ")" :: rest =
              tokens child ++ (childTokens children ++ ")" :: rest) by
                simp [childTokens, List.append_assoc]]
            rw [unfoldStep, first]
            change parseSExprListFuel (child :: accRev) fuel
              (childTokens children ++ ")" :: rest) = _
            rw [tail]
            simp [List.reverse_cons, List.append_assoc]

theorem parse_tokens (expression : SExpr) (valid : safe expression)
    (rest : List String) (fuel : Nat) (enough : (tokens expression).length < fuel) :
    parseSExprOneFuel fuel (tokens expression ++ rest) = .ok (expression, rest) :=
  (parse_by_fuel fuel).1 expression valid rest enough

theorem parse_child_tokens (children : List SExpr) (valid : childrenSafe children)
    (rest : List String) (fuel : Nat) (accRev : List SExpr)
    (enough : (childTokens children).length + 1 < fuel) :
    parseSExprListFuel accRev fuel (childTokens children ++ ")" :: rest) =
      .ok (.list (accRev.reverse ++ children), rest) :=
  (parse_by_fuel fuel).2 children valid rest accRev enough

theorem parse_tokens_whole (expression : SExpr) (valid : safe expression) :
    parseSExprOneFuel ((tokens expression).length + 1) (tokens expression) =
      .ok (expression, []) := by
  simpa using parse_tokens expression valid [] ((tokens expression).length + 1) (by omega)

example : tokens (.list [.atom "x", .list [.atom "x"]]) =
    ["(", "x", "(", "x", ")", ")"] := rfl

example : ¬ safe (.atom "(") := by simp [safe]

end Mettapedia.GSLT.Parsing.SExprTokenRoundTrip
