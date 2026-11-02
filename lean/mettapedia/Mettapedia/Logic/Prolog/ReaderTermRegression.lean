import Mettapedia.Logic.Prolog.ReaderTerm

namespace Mettapedia.Logic.Prolog.ReaderTermRegression

open ReaderOperator ReaderTerm SourceSignature

/-- A finite observation of the canonical dependent `LP.Term`, used only by
reader regressions. The parser itself has no intermediate syntax tree. -/
inductive Shape where
  | variable (spelling : String) (occurrence : Nat)
  | nil
  | atom (name : String)
  | integer (value : Int)
  | floatBits (bits : UInt64)
  | string (value : String)
  | clauseReference (reference : Nat)
  | compound (name : String) (arguments : List Shape)
deriving BEq, Repr

def shape : SourceSignature.Term -> Shape
  | .var identity => .variable identity.spelling identity.occurrence
  | .const .nil => .nil
  | .const (.atom name) => .atom name
  | .const (.integer value) => .integer value
  | .const (.floatBits bits) => .floatBits bits
  | .const (.string value) => .string value
  | .const (.clauseReference reference) => .clauseReference reference
  | .app indicator arguments =>
      .compound indicator.name (List.ofFn fun index => shape (arguments index))

def readShape (source : String) : Option Shape :=
  match readOne defaults source with
  | .ok result => some (shape result.term)
  | .error _ => none

#guard readShape "a+b*c." == some (.compound "+" [
  .atom "a", .compound "*" [.atom "b", .atom "c"]
])

#guard readShape "a->b;c." == some (.compound ";" [
  .compound "->" [.atom "a", .atom "b"], .atom "c"
])

-- `yfx` associates left; `xfy` associates right.
#guard readShape "a-b-c." == some (.compound "-" [
  .compound "-" [.atom "a", .atom "b"], .atom "c"
])

#guard readShape "a^b^c." == some (.compound "^" [
  .atom "a", .compound "^" [.atom "b", .atom "c"]
])

-- An `xfx` expression cannot consume another equal-priority occurrence.
#guard readShape "a=b=c." == none

-- Lexical adjacency selects function application. Layout leaves a second
-- primary and is rejected, matching `read_term/3`.
#guard readShape "f(a)." == some (.compound "f" [.atom "a"])
#guard readShape "f()." == some (.compound "f" [])
#guard readShape "f (a)." == none

-- A quoted operator name remains data: it can name a functor, but cannot act
-- as an infix occurrence.
#guard readShape "'+'(1,2)." == some (.compound "+" [
  .integer 1, .integer 2
])
#guard readShape "a '+' b." == none

#guard readShape "[a,b|T]." == some (.compound "[|]" [
  .atom "a", .compound "[|]" [
    .atom "b", .variable "T" 0
  ]
])

#guard readShape "{}." == some (.atom "{}")
#guard readShape "{a+b}." == some (.compound "{}" [
  .compound "+" [.atom "a", .atom "b"]
])

-- Adjacent negative numerals are constants in SWI; layout exposes the unary
-- operator. A leading plus remains an operator in either case.
#guard readShape "-1." == some (.integer (-1))
#guard readShape "- 1." == some (.compound "-" [.integer 1])
#guard readShape "+1." == some (.compound "+" [.integer 1])

#guard readShape "\"ab\"." == some (.string "ab")
#guard readShape "`ab`." == some (.compound "[|]" [
  .integer 97, .compound "[|]" [.integer 98, .nil]
])

#guard readShape "p(X,X,_,_)." == some (.compound "p" [
  .variable "X" 0,
  .variable "X" 0,
  .variable "_" 1,
  .variable "_" 2
])

def consumesExactlyOneTerm : Bool :=
  match ReaderLexer.scan "p(a). q(b)." with
  | .error _ => false
  | .ok tokens =>
      match parseOne defaults tokens with
      | .error _ => false
      | .ok first =>
          shape first.term == .compound "p" [.atom "a"] &&
            match parseOne defaults first.remaining with
            | .ok second =>
                shape second.term == .compound "q" [.atom "b"] &&
                  second.remaining.isEmpty
            | .error _ => false

#guard consumesExactlyOneTerm

end Mettapedia.Logic.Prolog.ReaderTermRegression
