import Mettapedia.Logic.Prolog.SourceRuntime

/-! Executable discriminators for finite SWI standard order and sorting. -/

namespace Mettapedia.Logic.Prolog.SourceTermOrderRegression

open Mettapedia.Logic
open SourceSignature

abbrev Sigma := SourceSignature.signature

private def answerTermFor? (identity : SourceSignature.Variable)
    (answer : LP.RuntimeQuery.Answer Sigma) : Option (LP.Term Sigma.scoped) :=
  match answer.queryVarMap.find? fun entry =>
      decide (entry.1 = LP.ScopedVar.at 0 identity) with
  | none => none
  | some (_, address) =>
      match LP.RuntimeReadback.Heap.readTerm answer.memory.heap address with
      | .ok term => some term
      | .error _ => none

private def runOne (goal : SourceSignature.Goal)
    (identity : SourceSignature.Variable) : Option (LP.Term Sigma.scoped) := do
  let session ← SourceRuntime.openEmpty [] goal |>.toOption
  match SourceRuntime.pullSession 1024 session with
  | .answer answer _ => answerTermFor? identity answer
  | _ => none

private def x : SourceSignature.Term := var "X" 0
private def xId : SourceSignature.Variable := { spelling := "X", occurrence := 0 }

private inductive Shape where
  | variable (scope : Nat) (spelling : String) (occurrence : Nat)
  | nil
  | atom (name : String)
  | integer (value : Int)
  | floatBits (bits : UInt64)
  | string (value : String)
  | clauseReference (reference : Nat)
  | compound (name : String) (arguments : List Shape)
deriving BEq, Repr

private def renderFloat (bits : UInt64) : String :=
  let raw := toString (Float.ofBits bits)
  if raw.contains 'e' || raw.contains 'E' then raw
  else
    let trimmed := String.ofList (raw.toList.reverse.dropWhile (· = '0')).reverse
    let normalized :=
      if trimmed = "." then "0."
      else if trimmed = "-." then "-0."
      else trimmed
    if normalized.endsWith "." then normalized ++ "0" else normalized

mutual
  private def Shape.render : Shape → String
    | .variable scope spelling occurrence =>
        s!"_{spelling}_{scope}_{occurrence}"
    | .nil => "[]"
    | .atom name => if name == "[]" then "'[]'" else name
    | .integer value => toString value
    | .floatBits bits => renderFloat bits
    | .string value => s!"\"{value}\""
    | .clauseReference reference => s!"<clause>({reference})"
    | .compound "[|]" [head, tail] =>
        s!"[{head.render}{Shape.renderListTail tail}]"
    | .compound "-" [left, right] =>
        s!"{left.render}-{right.render}"
    | .compound name arguments =>
        s!"{name}({String.intercalate "," (arguments.map Shape.render)})"

  private def Shape.renderListTail : Shape → String
    | .nil => ""
    | .compound "[|]" [head, tail] =>
        s!",{head.render}{Shape.renderListTail tail}"
    | tail => s!"|{tail.render}"
end

private def rendered (value : Option Shape) : Option String :=
  value.map Shape.render

private def shape : LP.Term Sigma.scoped → Shape
  | .var identity =>
      .variable identity.scope identity.name.spelling identity.name.occurrence
  | .const .nil => .nil
  | .const (.atom name) => .atom name
  | .const (.integer value) => .integer value
  | .const (.floatBits bits) => .floatBits bits
  | .const (.string value) => .string value
  | .const (.clauseReference reference) => .clauseReference reference
  | .app indicator arguments =>
      .compound indicator.name (List.ofFn fun index => shape (arguments index))

private def runSort (name : String) (input : SourceSignature.Term) :
    Option Shape :=
  (runOne (call name [input, x]) xId).map shape

private def pair (key value : SourceSignature.Term) : SourceSignature.Term :=
  compound "-" [key, value]

def sortMixed : Option Shape :=
  runSort "sort" (list [
    atom "b",
    string "x",
    integer 1,
    floatBits (1.0 : Float).toBits,
    atom "a",
    atom "b"
  ])

#guard sortMixed == some (shape (LP.Term.atScope 0 (list [
  floatBits (1.0 : Float).toBits,
  integer 1,
  string "x",
  atom "a",
  atom "b"
])))

def msortDuplicates : Option Shape :=
  runSort "msort" (list [atom "b", atom "a", atom "a"])

#guard msortDuplicates == some (shape (LP.Term.atScope 0
  (list [atom "a", atom "a", atom "b"])))

def keysortStable : Option Shape :=
  runSort "keysort" (list [
    pair (atom "b") (integer 0),
    pair (atom "a") (integer 1),
    pair (atom "a") (integer 2)
  ])

#guard keysortStable == some (shape (LP.Term.atScope 0 (list [
  pair (atom "a") (integer 1),
  pair (atom "a") (integer 2),
  pair (atom "b") (integer 0)
])))

def sortKeyOne : Option Shape :=
  (runOne (call "sort" [integer 1, atom "@=<", list [
    pair (atom "b") (integer 0),
    pair (atom "a") (integer 1),
    pair (atom "a") (integer 2)
  ], x]) xId).map shape

#guard sortKeyOne == keysortStable

def sortKeyTwo : Option Shape :=
  (runOne (call "sort" [integer 2, atom "@=<", list [
    pair (atom "b") (integer 3),
    pair (atom "a") (integer 1),
    pair (atom "c") (integer 2)
  ], x]) xId).map shape

#guard sortKeyTwo == some (shape (LP.Term.atScope 0 (list [
  pair (atom "a") (integer 1),
  pair (atom "c") (integer 2),
  pair (atom "b") (integer 3)
])))

def sortDescendingUnique : Option Shape :=
  (runOne (call "sort" [integer 0, atom "@>",
    list [atom "a", atom "c", atom "b", atom "c"], x]) xId).map shape

#guard sortDescendingUnique == some (shape (LP.Term.atScope 0
  (list [atom "c", atom "b", atom "a"])))

def sortSignedZero : Option Shape :=
  runSort "sort" (list [
    floatBits (0.0 : Float).toBits,
    floatBits (-0.0 : Float).toBits
  ])

#guard sortSignedZero == some (shape (LP.Term.atScope 0 (list [
  floatBits (-0.0 : Float).toBits,
  floatBits (0.0 : Float).toBits
])))

-- Equal numeric values are not identical standard-order terms: SWI places
-- the float before the integer.
#guard SourceTermOrder.compareFloatBits
  (1.0 : Float).toBits (1.0 : Float).toBits == .eq
#guard SourceTermOrder.compareFloatBits
  (-0.0 : Float).toBits (0.0 : Float).toBits == .lt
#guard SourceTermOrder.compareFloatBits
  (Float.ofBits 0x7ff8000000000000).toBits (1.0 : Float).toBits == .lt

def differentialRows : List (String × Option String) := [
  ("sort_mixed", rendered sortMixed),
  ("msort_duplicates", rendered msortDuplicates),
  ("keysort_stable", rendered keysortStable),
  ("sort_key_one", rendered sortKeyOne),
  ("sort_key_two", rendered sortKeyTwo),
  ("sort_descending_unique", rendered sortDescendingUnique),
  ("sort_signed_zero", rendered sortSignedZero)
]

end Mettapedia.Logic.Prolog.SourceTermOrderRegression
