/-!
# Chaitin's 1997 Lisp values and environments

Values are words, unsigned decimal integers, and proper lists. The primitive
operations follow the interpreter supplied by Chaitin with *The Limits of
Mathematics* (Wolfram Library Archive, record 729, revision 1997-07-08).
In particular, atomic `car` and `cdr` return their argument, and `cons` onto
a word or number returns its first argument. Only the word `false` is false.
-/

namespace Mettapedia.Languages.Chaitin

inductive SExpr where
  | symbol (name : String)
  | number (value : Nat)
  | list (values : List SExpr)
deriving Repr

mutual
  def SExpr.decEq : (left right : SExpr) → Decidable (left = right)
    | .symbol left, .symbol right =>
        if same : left = right then .isTrue (same ▸ rfl)
        else .isFalse (fun sameExpr => same (SExpr.symbol.inj sameExpr))
    | .number left, .number right =>
        if same : left = right then .isTrue (same ▸ rfl)
        else .isFalse (fun sameExpr => same (SExpr.number.inj sameExpr))
    | .list left, .list right =>
        match SExpr.listDecEq left right with
        | .isTrue same => .isTrue (same ▸ rfl)
        | .isFalse different => .isFalse (fun same => different (SExpr.list.inj same))
    | .symbol _, .number _ | .symbol _, .list _
    | .number _, .symbol _ | .number _, .list _
    | .list _, .symbol _ | .list _, .number _ => .isFalse (by intro same; cases same)

  def SExpr.listDecEq : (left right : List SExpr) → Decidable (left = right)
    | [], [] => .isTrue rfl
    | [], _ :: _ | _ :: _, [] => .isFalse (by intro same; cases same)
    | left :: lefts, right :: rights =>
        match SExpr.decEq left right, SExpr.listDecEq lefts rights with
        | .isTrue sameHead, .isTrue sameTail => .isTrue (sameHead ▸ sameTail ▸ rfl)
        | .isFalse different, _ => .isFalse (fun same => different (List.cons.inj same).1)
        | _, .isFalse different => .isFalse (fun same => different (List.cons.inj same).2)
end

instance : DecidableEq SExpr := SExpr.decEq

namespace SExpr

def nil : SExpr := .list []

def atom : SExpr → Bool
  | .list (_ :: _) => false
  | _ => true

def car : SExpr → SExpr
  | .list (head :: _) => head
  | value => value

def cdr : SExpr → SExpr
  | .list (_ :: rest) => .list rest
  | value => value

def cons (head : SExpr) : SExpr → SExpr
  | .list rest => .list (head :: rest)
  | _ => head

def elements : SExpr → List SExpr
  | .list values => values
  | _ => []

def numeral : SExpr → Nat
  | .number value => value
  | _ => 0

def boolean (value : Bool) : SExpr := .symbol (if value then "true" else "false")

def truth (value : SExpr) : Bool := decide (value ≠ .symbol "false")

def cadr (value : SExpr) : SExpr := value.cdr.car
def caddr (value : SExpr) : SExpr := value.cdr.cdr.car

/-- Successive `cdr`s, followed by `car`, as used by the Lisp program. -/
def field : Nat → SExpr → SExpr
  | 0, value => value.car
  | index + 1, value => field index value.cdr

def append (left right : SExpr) : SExpr := .list (left.elements ++ right.elements)

mutual
  def render : SExpr → String
    | .symbol name => name
    | .number value => toString value
    | .list values => "(" ++ renderList values ++ ")"

  def renderList : List SExpr → String
    | [] => ""
    | [value] => render value
    | value :: next :: rest => render value ++ " " ++ renderList (next :: rest)
end

def bitValue (bit : Bool) : SExpr := .number (if bit then 1 else 0)

def tape (input : List Bool) : SExpr := .list (input.map bitValue)

/-- On a private tape, exactly the integer zero is read as zero. -/
def tapeBit (value : SExpr) : Bool := decide (value ≠ .number 0)

@[simp] theorem car_nil : car nil = nil := rfl
@[simp] theorem cdr_nil : cdr nil = nil := rfl
@[simp] theorem car_symbol (name : String) : car (.symbol name) = .symbol name := rfl
@[simp] theorem cdr_symbol (name : String) : cdr (.symbol name) = .symbol name := rfl
@[simp] theorem cons_symbol (head : SExpr) (name : String) :
    cons head (.symbol name) = head := rfl
@[simp] theorem cons_list (head : SExpr) (rest : List SExpr) :
    cons head (.list rest) = .list (head :: rest) := rfl
@[simp] theorem truth_false : truth (.symbol "false") = false := by decide
@[simp] theorem truth_nil : truth nil = true := by decide
@[simp] theorem tapeBit_bitValue (bit : Bool) : tapeBit (bitValue bit) = bit := by
  cases bit <;> decide

@[simp] theorem truth_boolean (bit : Bool) : (SExpr.boolean bit).truth = bit := by
  cases bit <;> rfl

end SExpr

abbrev Environment := List (SExpr × SExpr)

/-- `eval` and `try` begin in the clean environment containing only `nil`. -/
def cleanEnvironment : Environment := [(.symbol "nil", SExpr.nil)]

def lookup (environment : Environment) (name : SExpr) : SExpr :=
  match name with
  | .number value => .number value
  | _ =>
      match environment.find? (fun entry => entry.1 == name) with
      | some entry => entry.2
      | none => name

def bindNames : List SExpr → List SExpr → Environment → Environment
  | [], _, environment => environment
  | name :: names, arguments, environment =>
      let value := arguments.headD SExpr.nil
      let tail := bindNames names arguments.tail environment
      (name, value) :: tail.filter (fun entry => entry.1 != name)

def bind (parameters arguments : SExpr) (environment : Environment) : Environment :=
  bindNames parameters.elements arguments.elements environment

@[simp] theorem lookup_number (environment : Environment) (value : Nat) :
    lookup environment (.number value) = .number value := rfl

@[simp] theorem lookup_clean_nil :
    lookup cleanEnvironment (.symbol "nil") = SExpr.nil := by decide

end Mettapedia.Languages.Chaitin
