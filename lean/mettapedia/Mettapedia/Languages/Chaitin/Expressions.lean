import Mettapedia.Languages.Chaitin.Syntax

/-!
# Historical Lisp expression constructors

These constructors build ordinary S-expressions accepted by the evaluator.
Function values are quoted proper lists; `letValue` is the expansion produced
by the historical source reader.
-/

namespace Mettapedia.Languages.Chaitin.Expressions

/-- A function application is a proper list whose first member is the function. -/
def call (name : String) (arguments : List SExpr) : SExpr :=
  .list (.symbol name :: arguments)

def quote (expression : SExpr) : SExpr := call "'" [expression]

/-- The quoted lambda values accepted by the historical evaluator. -/
def lambda (parameters : List String) (body : SExpr) : SExpr :=
  .list [.symbol "lambda", .list (parameters.map .symbol), body]

def quotedLambda (parameters : List String) (body : SExpr) : SExpr :=
  quote (lambda parameters body)

/-- This is the core S-expression produced by the historical `let` reader. -/
def letValue (name : String) (value body : SExpr) : SExpr :=
  .list [quotedLambda [name] body, value]

def ifExpr (condition yes no : SExpr) : SExpr := call "if" [condition, yes, no]

def equalExpr (left right : SExpr) : SExpr := call "=" [left, right]

def consExpr (head rest : SExpr) : SExpr := call "cons" [head, rest]

def listExpr : List SExpr → SExpr
  | [] => .symbol "nil"
  | head :: rest => consExpr head (listExpr rest)

/-- The expression for a field uses only ordinary `car` and `cdr`. -/
def fieldExpr : Nat → SExpr → SExpr
  | 0, expression => call "car" [expression]
  | index + 1, expression => fieldExpr index (call "cdr" [expression])

end Mettapedia.Languages.Chaitin.Expressions
